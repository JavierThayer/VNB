;;; extend-band.scm -- extend a saved band instead of rebuilding it (2026-09-23)
;;;
;;; The design is Ignacio's plan (scratchpad/triage/extend-band-plan.txt), steps 2
;;; to 4; the reference is docs/extend-band-2026-09-23.md.  In one paragraph:
;;;
;;;   An integration RESTORES the band it has, RETRACTS every name a changed
;;;   theorem-library file states (and every retired name), LOADS only the changed
;;;   files -- plus, as the load proceeds, every unchanged file holding a theorem
;;;   whose proof cites a name that vanished or whose statement, bill, oracles or
;;;   provenance changed -- runs the SAME end-of-load block as load.scm
;;;   (`run-load-end!', load.scm), and is disk-saved by the launcher
;;;   (`prover --extend-band').  It REFUSES, asking for a cold load, whenever the
;;;   change reaches anything but theorem-library/ files after this file's own
;;;   position in *vnb-files*.
;;;
;;; What this file defines, in order:
;;;   * the band record: *vnb-band-strict?*, *vnb-band-file-hashes*,
;;;     *vnb-band-files*, written by `xb-mark-band!' at the end of every load;
;;;   * `retract-theorem!' (the public retraction, one name) and
;;;     `xb-retract-names!' (the batch the extension uses);
;;;   * the ORDER CHECK, installed only while an extension loads files;
;;;   * `xb-plan' (the reload set, pure: the suite drives it on synthetic input);
;;;   * `vnb-extend-band!' (the extension itself).
;;;
;;; Loaded by load.scm right after proof-debt, before the first contained proof
;;; file, so it lives in every band.  It uses no top-level macro and compiles.
;;; Every helper is prefixed `xb-'.

;;; =======================================================================
;;; THE BAND RECORD
;;; =======================================================================

;;; #t only at the end of a STRICT load (or a clean extension): no keep-going
;;; mode, no hole, no failed file, no failed qed, inference checking ON with no
;;; refusal, no order violation.  An extension refuses to start from a band
;;; where this is #f -- and from a band built before this file existed, where it
;;; is unbound.
(define *vnb-band-strict?* #f)

;;; (KEY . HEX-MD5) for every file of *vnb-files* (KEY = the list entry), plus
;;; "load.scm#rest" (load.scm with the *vnb-files* form removed, read by the
;;; reader so comments do not count) and "prover" (the launcher).  Content, not
;;; mtimes: `capataz push --rsync' preserves mtimes, and `touch' changes nothing.
(define *vnb-band-file-hashes* '())

;;; The load list the band was built from (a copy of *vnb-files* at mark time).
(define *vnb-band-files* '())

;;; The reason the last mark was not strict, or #f.
(define *xb-not-strict-reason* #f)

(define (xb-hex bv)
  (let loop ((i 0) (acc '()))
    (if (= i (bytevector-length bv))
        (apply string-append (reverse acc))
        (let* ((b (bytevector-u8-ref bv i))
               (s (number->string b 16)))
          (loop (+ i 1) (cons (if (< b 16) (string-append "0" s) s) acc))))))

(define (xb-file-md5 path)
  (and (file-exists? path) (xb-hex (md5-file path))))

(define (xb-scm-path f) (string-append *prover-dir* f ".scm"))

;;; Read load.scm with the READER; return (FILES . REST-HASH): the literal list
;;; of the `(define *vnb-files* '(...))' form, and the md5 of every other form
;;; as `write' prints it.
(define (xb-read-load-scm #!optional path)
  (let* ((path  (if (default-object? path) (string-append *prover-dir* "load.scm") path))
         (forms (call-with-input-file path
                  (lambda (port)
                    (let loop ((acc '()))
                      (let ((x (read port)))
                        (if (eof-object? x) (reverse acc) (loop (cons x acc))))))))
         (list-form? (lambda (x) (and (pair? x) (eq? (car x) 'define)
                                      (pair? (cdr x)) (eq? (cadr x) '*vnb-files*))))
         (lf    (find-first list-form? forms))
         (files (and lf (let ((v (caddr lf)))
                          (if (and (pair? v) (eq? (car v) 'quote)) (cadr v) #f))))
         (rest  (call-with-output-string
                  (lambda (port)
                    (for-each (lambda (x) (if (not (list-form? x))
                                              (begin (write x port) (newline port))))
                              forms)))))
    (if (not (and (list? files) (every string? files)))
        (error "extend-band: cannot read the *vnb-files* list of" path))
    (cons files (xb-hex (md5-string rest)))))

;;; The hashes of a tree: FILES (a load list) plus the two root keys.
(define (xb-tree-hashes files load-rest-hash)
  (append
   (map (lambda (f) (cons f (xb-file-md5 (xb-scm-path f)))) files)
   (list (cons "load.scm#rest" load-rest-hash)
         (cons "prover" (xb-file-md5 (string-append *prover-dir* "prover"))))))

;;; Why the image in hand is not a strict build, or #f.
(define (xb-strictness-defect)
  (cond (*vnb-keep-going?* "the load ran in KEEP-GOING mode (VNB_KEEP_GOING)")
        ((pair? *vnb-qed-holes*) "the band carries keep-going HOLES (*vnb-qed-holes*)")
        ((pair? *vnb-load-failures*) "proof files FAILED during the load")
        ((pair? *vnb-qed-failures*) "qeds FAILED during the load (*vnb-qed-failures*)")
        ((not *dg-check-inferences?*) "inference checking was OFF (VNB_NO_RULE_CHECK)")
        ((> (dg-check-refusal-count) 0) "the rule checkers recorded refusals")
        ((pair? *xb-order-violations*) "the extension recorded order violations")
        (else #f)))

;;; Called at the end of `run-load-end!' (load.scm), so a cold load and an
;;; extension write the same record.  Hashing is done HERE, at the end, over
;;; the tree as it then stands (about 650 files, a second or two).
(define (xb-mark-band!)
  (let ((defect (xb-strictness-defect)))
    (set! *xb-not-strict-reason* defect)
    (set! *vnb-band-strict?* (not defect))
    (set! *vnb-band-files* (list-copy *vnb-files*))
    (set! *vnb-band-file-hashes*
          (let ((lr (xb-read-load-scm)))
            (xb-tree-hashes *vnb-files* (cdr lr))))
    (display ";; band record: ")
    (display (if defect "NOT STRICT -- " "strict, "))
    (if defect (display defect))
    (display (length *vnb-band-file-hashes*))
    (display " file hash(es) recorded\n")
    *vnb-band-strict?*))

;;; =======================================================================
;;; NAMES, SOURCES AND POSITIONS
;;; =======================================================================

(define (xb-string-search-last pattern s)
  ;; `string-search-all', not a loop over `string-search-forward' with a start
  ;; index: MIT 12.1 rejects start indices past the middle of the string
  ;; ("not in the correct range"), measured 2026-09-23.
  (let ((all (string-search-all pattern s)))
    (and (pair? all) (car (last-pair all)))))

;;; A recorded source (a pathname, as `current-load-pathname' gave it, carrying
;;; the ABSOLUTE path of the machine that built the band) -> the load-list key:
;;; relative to the prover root, no extension.  #f when there is none.
(define (xb-rel-source src)
  (and src
       (let* ((s (if (string? src) src (->namestring src)))
              (s (let ((cut (let loop ((ds '("/theorem-library/" "/structure-library/" "/calculus/")))
                              (cond ((null? ds) #f)
                                    ((xb-string-search-last (car ds) s)
                                     => (lambda (i) (+ i 1)))
                                    (else (loop (cdr ds)))))))
                   (cond (cut (string-tail s cut))
                         ((xb-string-search-last "/" s) => (lambda (i) (string-tail s (+ i 1))))
                         (else s))))
              (dot (xb-string-search-last "." s)))
         (if (and dot (member (string-tail s dot) '(".scm" ".com" ".bin")))
             (string-head s dot)
             s))))

;;; The file that STATES name: a -rev companion's is its forward's.
(define (xb-name-file name)
  (let ((fwd (rev-companion-source name)))
    (if fwd
        (xb-name-file fwd)
        (xb-rel-source (hash-table-ref/default *theorem-source* name #f)))))

(define (xb-theorem-library? f) (and (string? f) (string-prefix? "theorem-library/" f)))

(define (xb-position-index files)
  (let ((h (make-equal-hash-table)))
    (let loop ((fs files) (i 0))
      (if (pair? fs)
          (begin (if (not (hash-table-ref/default h (car fs) #f))
                     (hash-table-set! h (car fs) i))
                 (loop (cdr fs) (+ i 1)))))
    h))

;;; The names a proof CITES: the stored citation graph (which drops the proof's
;;; own name and DEFINITIONAL citations) united with a silent re-read of the
;;; saved script (which keeps them -- a changed def-predicate unfold is a
;;; change too).  Same verbs and same NAME-def resolution as the ledger.
(define (xb-citations-of name)
  (let ((g (hash-table-ref/default *proof-citation-graph* name '()))
        (s (hash-table-ref/default *proof-script-table* name '())))
    (let loop ((s s) (acc g))
      (if (null? s)
          acc
          (let ((e (car s)))
            (loop (cdr s)
                  (if (and (pair? e) (memq (car e) *pd-citing-verbs*)
                           (pair? (cdr e)) (symbol? (cadr e)))
                      (let ((c (pd-resolve-citation (car e) (cadr e))))
                        (if (or (eq? c name) (memq c acc)) acc (cons c acc)))
                      acc)))))))

;;; A LIBRARY VIEW: what the plan needs to know about the image, in two tables,
;;; so that the suite can hand the plan a synthetic one.
;;;   files  : name -> load-list key of the file that states it (or absent)
;;;   citers : name -> the names whose proof cites it, directly or through a
;;;            companion (a citation of X-rev or of a view companion of X is
;;;            filed under X as well)
(define (xb-make-view files citers) (cons files citers))
(define (xb-view-files v) (car v))
(define (xb-view-citers v) (cdr v))

(define (xb-view-names-of-file v f)
  (let ((acc '()))
    (hash-table-walk (xb-view-files v)
      (lambda (n file) (if (equal? file f) (set! acc (cons n acc)))))
    acc))

(define (xb-current-view)
  (let ((files  (make-equal-hash-table))
        (citers (make-equal-hash-table)))
    (hash-table-walk *theorem-table*
      (lambda (n stmt)
        (let ((f (xb-name-file n)))
          (if f (hash-table-set! files n f)))))
    (let ((file-under
           (lambda (c t)
             (let up ((c c) (seen '()))
               (if (and (symbol? c) (not (memq c seen)))
                   (begin
                     (hash-table-update!/default citers c
                       (lambda (l) (if (memq t l) l (cons t l))) '())
                     (let ((src (pd-source-of c)))
                       (if src (up src (cons c seen))))))))))
      (for-each (lambda (t)
                  (for-each (lambda (c) (file-under c t)) (xb-citations-of t)))
                (hash-table-keys *proof-script-table*))
      (hash-table-walk *proof-citation-graph*
        (lambda (t cs) (for-each (lambda (c) (file-under c t)) cs))))
    (xb-make-view files citers)))

;;; =======================================================================
;;; RETRACTION
;;; =======================================================================

;;; Every table that holds state PER THEOREM NAME, as found by the audit of
;;; 2026-09-23 (the table is reproduced in docs/extend-band-2026-09-23.md).
;;; MODE is `full' (the name leaves the library: its metadata goes too) or
;;; `reload' (its file is about to be loaded again: metadata that OTHER files
;;; may have written -- topic, warrant, gloss, alias, reference anchor,
;;; rests-on -- is kept, and the reload overwrites what its own file writes).
;;;
;;; NOT cleared, by design: *named-only-macetes* (the declaration may sit in
;;; another file and must survive to suppress the re-installed macete),
;;; *operators* / *functoid-registry* / *constant-registry* (definitions, not
;;; theorems; a def-* form re-registers idempotently), *books* (keyed by book).
;;;
;;; Returns (REMOVED . CITERS): REMOVED an alist (table-name name ...) of what
;;; was actually present and removed; CITERS the installed theorems, outside the
;;; batch, whose proof cites a removed name.  A caller that retracts a cited
;;; name orphans a bill: the extension re-proves those citers, and the public
;;; `retract-theorem!' reports them.
(define (xb-retract-names! names mode)
  (let* ((full?   (eq? mode 'full))
         (removed '())
         (note!   (lambda (tbl n)
                    (let ((e (assq tbl removed)))
                      (if e
                          (if (not (memq n (cdr e))) (set-cdr! e (cons n (cdr e))))
                          (set! removed (cons (list tbl n) removed))))))
         (batch   (make-strong-eqv-hash-table)))
    ;; the batch: the names, their -rev companions, and -- in full mode -- the
    ;; view companions minted from them (transitively)
    (for-each (lambda (n) (hash-table-set! batch n #t)) names)
    (let grow ()
      (let ((added #f))
        (for-each
         (lambda (n)
           (let ((rev (rev-name-of n)))
             (if (and (eq? (rev-companion-source rev) n)
                      (not (hash-table-ref/default batch rev #f)))
                 (begin (hash-table-set! batch rev #t) (set! added #t)))))
         (hash-table-keys batch))
        (if full?
            (hash-table-walk *view-specialized-source*
              (lambda (comp src)
                (if (and (hash-table-ref/default batch src #f)
                         (not (hash-table-ref/default batch comp #f)))
                    (begin (hash-table-set! batch comp #t) (set! added #t))))))
        (if added (grow))))
    (let* ((all  (hash-table-keys batch))
           (in?  (lambda (n) (hash-table-ref/default batch n #f)))
           (del! (lambda (tname tbl n)
                   (if (hash-table-contains? tbl n)
                       (begin (hash-table-delete! tbl n) (note! tname n)))))
           (thy  (library-theorems *library*)))
      ;; the citers, read BEFORE anything is removed
      (define citers
        (let ((acc '()))
          (for-each
           (lambda (t)
             (if (and (not (in? t)) (not (memq t acc))
                      (any in? (xb-citations-of t)))
                 (set! acc (cons t acc))))
           (hash-table-keys *proof-script-table*))
          (hash-table-walk *proof-citation-graph*
            (lambda (t cs)
              (if (and (not (in? t)) (not (memq t acc)) (any in? cs))
                  (set! acc (cons t acc)))))
          (sort acc (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))
      (for-each
       (lambda (n)
         (del! '*theorem-table* *theorem-table* n)
         (del! '*macete-table* *macete-table* n)
         (del! '*theorem-source* *theorem-source* n)
         (del! '*rev-companion-source* *rev-companion-source* n)
         (del! '*view-specialized-source* *view-specialized-source* n)
         (del! '*provenance* *provenance* n)
         (del! '*lemma-fingerprint-memo* *lemma-fingerprint-memo* n)
         (del! '*proof-citation-graph* *proof-citation-graph* n)
         (del! '*proof-debt* *proof-debt* n)
         (del! '*proof-oracles* *proof-oracles* n)
         (del! '*certifications* *certifications* n)
         (del! '*proof-script-table* *proof-script-table* n)
         (del! '*proof-mints-table* *proof-mints-table* n)
         (del! '*proof-live-trace* *proof-live-trace* n)
         (del! '*proof-start-counter* *proof-start-counter* n)
         (del! 'library-theorems thy n)
         (del! '*rkw--def-memo* *rkw--def-memo* n)
         ;; ALIASES ACCUMULATE: `alias!' APPENDS, so a kept alias list would
         ;; gain a second copy of every string its reloaded file writes again
         ;; (found by the band comparison, 2026-09-23: rr-limit-scale and
         ;; rr-limit-sub carried their alias twice after one extension, three
         ;; times after two).  In reload mode the list is removed too, and
         ;; saved for `xb-restore-aliases!', which gives back after the reload
         ;; the strings that some file NOT reloaded states.
         (if (and (not full?) (pair? (hash-table-ref/default *theorem-aliases* n '())))
             (set! *xb-alias-snapshot*
                   (cons (cons n (hash-table-ref *theorem-aliases* n (lambda () '())))
                         *xb-alias-snapshot*)))
         (del! '*theorem-aliases* *theorem-aliases* n)
         (if full?
             (begin
               (del! '*pss-topics* *pss-topics* n)
               (del! '*glosses* *glosses* n)
               (del! '*warrants* *warrants* n)
               (del! '*reference-anchors* *reference-anchors* n)
               (del! '*rests-on-graph* *rests-on-graph* n))))
       all)
      ;; the lists
      (let ((drop (lambda (tname lst key)
                    (filter (lambda (x)
                              (let ((n (key x)))
                                (if (and (symbol? n) (in? n))
                                    (begin (note! tname n) #f)
                                    #t)))
                            lst))))
        (set! *proven-theorem-names*
              (drop '*proven-theorem-names* *proven-theorem-names* (lambda (x) x)))
        (set! *support-theorem-names*
              (drop '*support-theorem-names* *support-theorem-names* (lambda (x) x)))
        (set! *vnb-qed-holes* (drop '*vnb-qed-holes* *vnb-qed-holes* car))
        (set! *vnb-qed-failures* (drop '*vnb-qed-failures* *vnb-qed-failures* car))
        (set! *install-duplicates*
              (drop '*install-duplicates* *install-duplicates* (lambda (x) x)))
        (set! *install-validation-failures*
              (drop '*install-validation-failures* *install-validation-failures* car))
        (set! *inert-macetes* (drop '*inert-macetes* *inert-macetes* car))
        (set-library-axioms! *library*
          (drop 'library-axioms (library-axioms *library*) car)))
      ;; the binder-name owners (value = the theorem that first used the binder)
      (let ((gone '()))
        (hash-table-walk *installed-binder-names*
          (lambda (b owner) (if (in? owner) (set! gone (cons b gone)))))
        (for-each (lambda (b)
                    (note! '*installed-binder-names* (hash-table-ref *installed-binder-names* b (lambda () #f)))
                    (hash-table-delete! *installed-binder-names* b)
                    (if (not (memq b *xb-dropped-binders*))
                        (set! *xb-dropped-binders* (cons b *xb-dropped-binders*))))
                  gone))
      (xb-reset-derived-caches!)
      (cons (reverse (map (lambda (e) (cons (car e) (reverse (cdr e)))) removed))
            citers))))

;;; (NAME . ALIAS-STRINGS) removed by reload-mode retractions (see the note in
;;; `xb-retract-names!').
(define *xb-alias-snapshot* '())

;;; After an extension's reload: an alias string of a reloaded name that is
;;; missing now, and that appears literally in the source of a load-list file
;;; that did NOT reload, was written by that file -- a cold load would have it
;;; -- and is given back.  One that appears nowhere else was dropped from the
;;; reloaded file and stays dropped.  Returns the number given back.
(define (xb-restore-aliases! files reloaded)
  (let ((texts #f) (n 0))
    (define (other-texts)
      (or texts
          (begin
            (set! texts
                  (filter-map
                   (lambda (f)
                     (and (not (member f reloaded))
                          (let ((path (xb-scm-path f)))
                            (and (file-exists? path)
                                 (call-with-input-file path
                                   (lambda (port) (read-string (file-length path) port)))))))
                   files))
            texts)))
    (for-each
     (lambda (e)
       (let ((now (hash-table-ref/default *theorem-aliases* (car e) '())))
         (for-each
          (lambda (str)
            (if (and (string? str) (not (member str now))
                     (any (lambda (t) (string-search-forward str t 0)) (other-texts)))
                (begin
                  (hash-table-set! *theorem-aliases* (car e)
                                   (append (hash-table-ref/default *theorem-aliases* (car e) '())
                                           (list str)))
                  (set! n (+ n 1)))))
          (cdr e))))
     (reverse *xb-alias-snapshot*))
    (set! *xb-alias-snapshot* '())
    n))

;;; The binders whose owner (`*installed-binder-names*': binder -> the FIRST
;;; theorem that bound it) a retraction removed.  A cold load would give such a
;;; binder to the next theorem, in load order, that binds it; `xb-reown-binders!'
;;; does that after an extension has reloaded its files (reported by E2,
;;; 2026-09-23).  Within one file the load order of theorems is not recorded,
;;; so ties are broken by name: the owner can differ from a cold load's only
;;; when two theorems of one file bind the same name, and the table is used
;;; for a warning's wording only.
(define *xb-dropped-binders* '())

(define (xb-reown-binders! #!optional reloaded-files)
  ;; The binders to settle: those whose owner was retracted, and every binder
  ;; of a theorem stated by a reloaded file (such a theorem may now bind a name
  ;; that a LATER file's theorem owns in the band).
  (let* ((reloaded (if (default-object? reloaded-files) '() reloaded-files))
         (todo (make-strong-eqv-hash-table))
         (best (make-strong-eqv-hash-table)))      ; binder -> (position . name)
    (for-each (lambda (b) (hash-table-set! todo b #t)) *xb-dropped-binders*)
    (if (pair? reloaded)
        (hash-table-walk *theorem-table*
          (lambda (n stmt)
            (if (member (xb-name-file n) reloaded)
                (for-each (lambda (pr) (hash-table-set! todo (car pr) #t))
                          (formula-binder-names stmt))))))
    (if (> (hash-table/count todo) 0)
        (hash-table-walk *theorem-table*
          (lambda (n stmt)
            (let ((p (or (xb-name-position n) 1000000)))
              (for-each
               (lambda (pr)
                 (let ((b (car pr)))
                   (if (hash-table-ref/default todo b #f)
                       (let ((cur (hash-table-ref/default best b #f)))
                         (if (or (not cur) (< p (car cur))
                                 (and (= p (car cur))
                                      (string<? (symbol->string n) (symbol->string (cdr cur)))))
                             (hash-table-set! best b (cons p n)))))))
               (formula-binder-names stmt))))))
    ;; the owner the load left stands when it sits in the earliest file (its
    ;; order within the file is the load's own); otherwise the earliest file's
    ;; theorem takes the binder
    (let ((changed 0))
      (hash-table-walk best
        (lambda (b pn)
          (let* ((cur (hash-table-ref/default *installed-binder-names* b #f))
                 (cp  (and cur (xb-name-position cur))))
            (if (not (and cur (hash-table-ref/default *theorem-table* cur #f)
                          (eqv? (or cp 1000000) (car pn))))
                (begin (hash-table-set! *installed-binder-names* b (cdr pn))
                       (set! changed (+ changed 1)))))))
      (set! *xb-dropped-binders* '())
      changed)))

;;; Caches DERIVED from the theorem table, rebuilt lazily when #f.  A retraction
;;; leaves each stale, so each is dropped.
(define (xb-reset-derived-caches!)
  (set! *chk-theorem-index* #f)
  (set! *chk-theorem-index-size* -1)
  (set! *what-now-head-index* #f)
  (set! *what-now-membership-index* #f)
  (set! *witness-producer-index* #f)
  (set! *op-fun-typing-index* #f)
  (cite-index-reset!)
  (set! *page-audit-results* '())
  unspecific)

;;; THE PUBLIC RETRACTION.  (retract-theorem! 'NAME) removes NAME, its -rev
;;; companion and its view companions from every per-name table, metadata
;;; included, and returns the alist of what it removed, with an entry
;;; (citers ...) when installed proofs cite a removed name -- which it also
;;; PRINTS: retracting a cited name orphans their bills, and that must be seen.
(define (retract-theorem! name #!optional mode)
  (let* ((r (xb-retract-names! (list name) (if (default-object? mode) 'full mode)))
         (removed (car r)) (citers (cdr r)))
    (if (pair? citers)
        (begin
          (display ";VNB warning: retract-theorem!: ") (display name)
          (display " is cited by ") (display (length citers))
          (display " installed proof(s), whose bills now name a retracted theorem: ")
          (display citers) (newline)))
    (if (pair? citers)
        (append removed (list (cons 'citers citers)))
        removed)))

;;; =======================================================================
;;; THE ORDER CHECK
;;; =======================================================================
;;;
;;; A cold load cannot use a theorem stated by a file that loads LATER: it is
;;; not installed yet.  A band holds everything, so an extension must check it.
;;; The choke point is the kernel's own: every inference that brings a
;;; theorem into a proof goes through `dg-check-inference!' under one of three
;;; tags -- `theorem-assumption' (the statement; the name is found by
;;; statement, as the checker itself finds it), `macete' and `macete-hyp' (the
;;; name is in the tag).  While an extension loads a file, the checkers of those
;;; three heads are WRAPPED: the wrapper refuses, before delegating, a use of a
;;; theorem whose file sits after the file being loaded.  The refusal is an
;;; ordinary rule-checker refusal (printed, counted, raised) and is also kept
;;; in *xb-order-violations*.  Nothing calls `dg-apply-rule!' here.

(define *xb-order-position* #f)        ; position of the file being loaded, or #f
(define *xb-position-table* #f)        ; load-list key -> position, while extending
(define *xb-order-violations* '())     ; (name file position loading-position), newest first

(define (xb-name-position name)
  (and *xb-position-table*
       (let ((f (xb-name-file name)))
         (and f (hash-table-ref/default *xb-position-table* f #f)))))

;;; #f when NAME may be used here; else the refusal string (and the violation
;;; is recorded).
(define (xb-order-offense name)
  (let ((p (and *xb-order-position* (symbol? name) (xb-name-position name))))
    (and p (> p *xb-order-position*)
         (begin
           (set! *xb-order-violations*
                 (cons (list name (xb-name-file name) p *xb-order-position*)
                       *xb-order-violations*))
           (string-append "ORDER: " (symbol->string name) " is stated in "
                          (xb-name-file name) " (load position "
                          (number->string p) "), after the file being loaded (position "
                          (number->string *xb-order-position*)
                          "); a cold load would not have it")))))

;;; theorem-assumption: a statement held under two names is legal if EITHER
;;; name is early enough.
(define (xb-order-offense-for-statement f)
  (let ((n (chk-installed-theorem-name f)))
    (and n
         (let ((p (xb-name-position n)))
           (and p *xb-order-position* (> p *xb-order-position*)
                (let ((early #f))
                  (hash-table-walk *theorem-table*
                    (lambda (m stmt)
                      (if (and (not early) (chk-same? stmt f))
                          (let ((q (xb-name-position m)))
                            (if (or (not q) (<= q *xb-order-position*))
                                (set! early #t))))))
                  (and (not early) (xb-order-offense n))))))))

(define (xb-order-test rule hyps concl)
  (let ((head (rule-tag-head rule)))
    (cond ((not *xb-order-position*) #f)
          ((memq head '(macete macete-hyp))
           (and (pair? rule) (pair? (cdr rule)) (xb-order-offense (cadr rule))))
          ((eq? head 'theorem-assumption)
           (and (pair? hyps)
                (let loop ((fs (chk-added (car hyps) concl)))
                  (and (pair? fs)
                       (or (xb-order-offense-for-statement (car fs))
                           (loop (cdr fs)))))))
          (else #f))))

(define *xb-order-heads* '(theorem-assumption macete macete-hyp))

;;; Run THUNK with the three checkers wrapped; the originals come back however
;;; THUNK exits.
(define (xb-with-order-check files thunk)
  (let ((originals (map (lambda (h) (cons h (rule-checker-for h))) *xb-order-heads*)))
    (dynamic-wind
     (lambda ()
       (set! *xb-position-table* (xb-position-index files))
       (for-each
        (lambda (e)
          (let ((orig (cdr e)))
            (if orig
                (register-rule-checker! (car e)
                  (lambda (rule hyps concl)
                    (let ((v (xb-order-test rule hyps concl)))
                      (if (string? v) v (orig rule hyps concl))))))))
        originals))
     thunk
     (lambda ()
       (for-each (lambda (e) (if (cdr e) (register-rule-checker! (car e) (cdr e))))
                 originals)
       (set! *xb-position-table* #f)
       (set! *xb-order-position* #f)))))

;;; =======================================================================
;;; THE PLAN (pure: the suite drives it on synthetic input)
;;; =======================================================================
;;;
;;; (xb-plan OLD-FILES NEW-FILES OLD-HASHES NEW-HASHES RETIRE STRICT VIEW)
;;;   OLD-FILES / OLD-HASHES  the band's load list and file record
;;;   NEW-FILES / NEW-HASHES  the tree's
;;;   RETIRE                  names the caller says leave the library
;;;   STRICT                  #t, or a string saying why the band is not strict
;;;   VIEW                    `xb-make-view' tables (name->file, name->citers)
;;; Returns an alist:
;;;   refusals  reasons (strings); non-empty means: cold load
;;;   changed added removed    load-list keys
;;;   reload    the files certain to reload, in NEW-FILES order
;;;   pulled    the files the retired names' citers pulled in
;;;   retire    the retired names (given ones plus those of removed files)
;;;   retract   (NAME . MODE) for every name retracted before the first load
;;;   upper     files that MAY be added during the run (the static fixpoint
;;;             over every name of every reloaded file), beyond `reload'
(define (xb-plan old-files new-files old-hashes new-hashes retire strict view)
  (let* ((refusals '())
         (refuse!  (lambda (s) (set! refusals (cons s refusals))))
         (pos      (xb-position-index new-files))
         (old-pos  (xb-position-index old-files))
         (boundary (hash-table-ref/default pos "extend-band" #f))
         (hash-of  (lambda (al k) (let ((e (assoc k al))) (and e (cdr e)))))
         (removed  (filter (lambda (f) (not (hash-table-ref/default pos f #f))) old-files))
         (added    (filter (lambda (f) (not (hash-table-ref/default old-pos f #f))) new-files))
         (changed  (filter (lambda (f)
                             (and (hash-table-ref/default old-pos f #f)
                                  (let ((a (hash-of old-hashes f)) (b (hash-of new-hashes f)))
                                    (not (and a b (string=? a b))))))
                           new-files))
         (names-of (lambda (f) (xb-view-names-of-file view f)))
         (file-of  (lambda (n) (hash-table-ref/default (xb-view-files view) n #f)))
         (citers   (lambda (n) (hash-table-ref/default (xb-view-citers view) n '())))
         (list-str (lambda (l) (reduce (lambda (b a) (string-append a " " b)) "" l))))
    (if (not (eq? strict #t))
        (refuse! (string-append "the band is not a strict build: "
                                (if (string? strict) strict "no strict marker"))))
    (for-each
     (lambda (k)
       (let ((a (hash-of old-hashes k)) (b (hash-of new-hashes k)))
         (if (not (and a b (string=? a b)))
             (refuse! (string-append (if (string=? k "prover") "the launcher `prover'"
                                         "load.scm outside the *vnb-files* list")
                                     " changed since the band was built")))))
     '("load.scm#rest" "prover"))
    (if (not boundary)
        (refuse! "the load list has no \"extend-band\" entry"))
    (let ((outside (filter (lambda (f) (not (xb-theorem-library? f)))
                           (append changed added removed))))
      (if (pair? outside)
          (refuse! (string-append "changed outside theorem-library/ (kernel, structure-library, "
                                  "calculus/ or a root file): " (list-str outside)))))
    ;; the retained files keep their relative order
    (let ((kept-old (filter (lambda (f) (hash-table-ref/default pos f #f)) old-files))
          (kept-new (filter (lambda (f) (hash-table-ref/default old-pos f #f)) new-files)))
      (if (not (equal? kept-old kept-new))
          (refuse! "a file retained in *vnb-files* moved: the load order changed")))
    (let ((early (filter (lambda (f)
                           (and boundary (xb-theorem-library? f)
                                (<= (hash-table-ref/default pos f 0) boundary)))
                         (append changed added))))
      (if (pair? early)
          (refuse! (string-append "changed before the containment boundary (the \"extend-band\" "
                                  "entry: these vocabulary files load before the proof machinery): "
                                  (list-str early)))))
    (let* ((reload0  (append changed added))
           (retired  (append retire
                             (append-map names-of (filter xb-theorem-library? removed))))
           (in-order (lambda (fs) (filter (lambda (f) (member f fs)) new-files)))
           (pulled   '()))
      ;; a retired name must not still be stated by a file that does not reload
      (for-each
       (lambda (n)
         (let ((f (file-of n)))
           (cond ((not f)
                  (refuse! (string-append "retired name " (symbol->string n)
                                          " has no recorded source")))
                 ((and (hash-table-ref/default pos f #f) (not (member f reload0)))
                  (refuse! (string-append "retired name " (symbol->string n)
                                          " is still stated by the unchanged file " f))))))
       retire)
      ;; the retired names' citers, transitively through companions (the view's
      ;; citers table already files companion citations under the forward)
      (for-each
       (lambda (n)
         (for-each
          (lambda (t)
            (let ((f (file-of t)))
              (cond ((not f)
                     (refuse! (string-append "citer " (symbol->string t) " of retired "
                                             (symbol->string n) " has no recorded source")))
                    ((not (xb-theorem-library? f))
                     (refuse! (string-append "citer " (symbol->string t) " of retired "
                                             (symbol->string n) " lives outside theorem-library/: " f)))
                    ((not (hash-table-ref/default pos f #f)) #f) ; its file left the list: retired itself
                    ((not (or (member f reload0) (member f pulled)))
                     (set! pulled (cons f pulled))))))
          (citers n)))
       retired)
      ;; the upper bound: every name of every reloading file, to a fixpoint
      (let ((upper
             (let loop ((todo (append reload0 pulled)) (seen (append reload0 pulled)))
               (if (null? todo)
                   seen
                   (let ((more '()))
                     (for-each
                      (lambda (n)
                        (for-each
                         (lambda (t)
                           (let ((f (file-of t)))
                             (if (and f (hash-table-ref/default pos f #f)
                                      (not (member f seen)) (not (member f more)))
                                 (set! more (cons f more)))))
                         (citers n)))
                      (append-map names-of todo))
                     (loop more (append seen more)))))))
        (let ((reload (in-order (append reload0 pulled))))
          (list (cons 'refusals (reverse refusals))
                (cons 'changed changed)
                (cons 'added added)
                (cons 'removed removed)
                (cons 'reload reload)
                (cons 'pulled (in-order pulled))
                (cons 'retire retired)
                (cons 'retract
                      (append (map (lambda (n) (cons n 'full)) retired)
                              (map (lambda (n) (cons n 'reload))
                                   (filter (lambda (n) (not (memq n retired)))
                                           (append-map names-of reload)))))
                (cons 'upper (filter (lambda (f) (not (member f reload)))
                                     (in-order upper)))))))))

(define (xb-plan-ref plan key) (cdr (assq key plan)))
(define (xb-plan-refused? plan) (pair? (xb-plan-ref plan 'refusals)))

(define (xb-print-plan plan)
  (let ((files (lambda (label key)
                 (let ((l (xb-plan-ref plan key)))
                   (display ";;   ") (display label) (display ": ")
                   (display (length l)) (newline)
                   (for-each (lambda (f) (display ";;     ") (display f) (newline)) l)))))
    (display ";; extend-band: the plan\n")
    (files "changed files (content differs from the band's record)" 'changed)
    (files "files added to *vnb-files*" 'added)
    (files "files removed from *vnb-files*" 'removed)
    (display ";;   retired names: ") (display (xb-plan-ref plan 'retire)) (newline)
    (files "RELOAD SET (certain), in load order" 'reload)
    (files "  of which pulled in by the citers of retired names" 'pulled)
    (let ((r (xb-plan-ref plan 'retract)))
      (display ";;   retractions before the first load: ") (display (length r))
      (display " name(s), ")
      (display (length (filter (lambda (e) (eq? (cdr e) 'full)) r)))
      (display " retired\n"))
    (files "MAY be added during the run (a reloaded name changes statement, bill, oracles or provenance)" 'upper)
    (let ((rs (xb-plan-ref plan 'refusals)))
      (if (null? rs)
          (display ";; extend-band: the plan is ACCEPTED\n")
          (begin
            (display ";; extend-band: REFUSED -- a cold load is needed (prover --build-band):\n")
            (for-each (lambda (s) (display ";;   ") (display s) (newline)) rs))))))

;;; The plan for the image in hand and the tree on disk.
(define (xb-current-plan retire)
  (let* ((lr     (xb-read-load-scm))
         (new    (car lr))
         (strict (cond ((not *vnb-band-strict?*)
                        (or *xb-not-strict-reason* "no strict marker"))
                       ((xb-strictness-defect) => (lambda (d) d))
                       ((let ((kg (get-environment-variable "VNB_KEEP_GOING")))
                          (and kg (not (string=? kg "")) (not (string=? kg "0"))))
                        "VNB_KEEP_GOING is set for the extension")
                       (else #t)))
         (unknown (let ((acc '()))
                    (hash-table-walk *theorem-table*
                      (lambda (n s) (if (not (xb-name-file n)) (set! acc (cons n acc)))))
                    acc))
         (plan   (xb-plan *vnb-band-files* new *vnb-band-file-hashes*
                          (xb-tree-hashes new (cdr lr)) retire strict (xb-current-view))))
    ;; An installed theorem with no recorded source would survive every
    ;; extension, whatever happens to the file that states it: blocking.
    (if (pair? unknown)
        (cons (cons 'refusals
                    (append (xb-plan-ref plan 'refusals)
                            (list (string-append
                                   (number->string (length unknown))
                                   " installed theorem(s) have no recorded source (installed at a"
                                   " prompt or by a script outside the load), e.g. "
                                   (symbol->string (car unknown))))))
              (cdr plan))
        plan)))

;;; =======================================================================
;;; THE EXTENSION
;;; =======================================================================

;;; Per name, what a citer's stored proof depends on.
(define (xb-sorted-syms l)
  (sort (list-copy l) (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

(define (xb-fingerprint n)
  (vector (hash-table-ref/default *theorem-table* n #f)
          (provenance-of n)
          (xb-sorted-syms (debt-of n))
          (xb-sorted-syms (oracles-of n))))

;;; #f when N is unchanged against its snapshot OLD; else the kind of change.
(define (xb-change-of n old)
  (let ((new (hash-table-ref/default *theorem-table* n #f)))
    (cond ((not new) 'vanished)
          ((not (alpha-equiv? (vector-ref old 0) new)) 'restated)
          ((not (eq? (vector-ref old 1) (provenance-of n))) 'provenance)
          ((not (equal? (vector-ref old 2) (xb-sorted-syms (debt-of n)))) 'bill)
          ((not (equal? (vector-ref old 3) (xb-sorted-syms (oracles-of n)))) 'oracles)
          (else #f))))

(define (xb-refuse-now! reason)
  (error (string-append "vnb-extend-band!: REFUSED during the run -- a cold load is needed: "
                        reason)))

;;; (vnb-extend-band! [RETIRE [DRY-RUN?]])  -- see the header.  A dry run
;;; prints the plan and returns it; it changes no table.  A refused plan is an
;;; ERROR (nothing has been changed yet).  On success returns an alist
;;; (reload-files retracted install-duplicates order-violations).
(define (vnb-extend-band! #!optional retire dry-run?)
  (let* ((retire  (if (default-object? retire) '() retire))
         (dry?    (and (not (default-object? dry-run?)) dry-run?))
         (plan    (xb-current-plan retire)))
    (xb-print-plan plan)
    (cond
     (dry? plan)
     ((xb-plan-refused? plan)
      (error "vnb-extend-band!: REFUSED -- a cold load is needed; the reasons are listed above"))
     (else (xb-execute! plan)))))

;;; The files after position START that specialize EVERY theorem of a structure
;;; through a view: ((FILE . VIEW) ...).  A text test first (the file mentions
;;; `view-as-auto-specialize!' or `def-functor'), then the reader: a top-level
;;; (view-as-auto-specialize! 'V) with no theorem named, or (def-functor 'V ...).
(define (xb-specializers files start)
  (let loop ((fs files) (i 0) (acc '()))
    (if (null? fs)
        (reverse acc)
        (loop (cdr fs) (+ i 1)
              (if (<= i start)
                  acc
                  (let* ((path (xb-scm-path (car fs)))
                         (text (and (file-exists? path)
                                    (call-with-input-file path
                                      (lambda (port) (read-string (file-length path) port))))))
                    (if (and (string? text)
                             (or (string-search-forward "view-as-auto-specialize!" text 0)
                                 (string-search-forward "def-functor" text 0)))
                        (append
                         (reverse
                          (filter-map
                           (lambda (form)
                             (and (pair? form) (list? form)
                                  (cond
                                   ((and (eq? (car form) 'view-as-auto-specialize!)
                                         (= (length form) 2)
                                         (pair? (cadr form)) (eq? (car (cadr form)) 'quote))
                                    (cons (car fs) (cadr (cadr form))))
                                   ((and (eq? (car form) 'def-functor) (>= (length form) 2)
                                         (pair? (cadr form)) (eq? (car (cadr form)) 'quote))
                                    (cons (car fs) (cadr (cadr form))))
                                   (else #f))))
                           (call-with-input-file path
                             (lambda (port)
                               (let rd ((acc '()))
                                 (let ((x (read port)))
                                   (if (eof-object? x) (reverse acc) (rd (cons x acc)))))))))
                         acc)
                        acc)))))))

;;; T (a citer of N, or a view companion of N) reloads: its file F-T must be
;;; a theorem-library file that loads after F (position I), or the extension
;;; cannot be faithful and stops.
(define (xb-pull! t tf n f i new-files pending)
  (cond
   ((and tf (hash-table-ref/default pending tf #f)) #f)
   ((not tf)
    (xb-refuse-now! (string-append (symbol->string t) " (a citer or companion of "
                                   (symbol->string n) ") has no recorded source")))
   ((not (xb-theorem-library? tf))
    (xb-refuse-now! (string-append (symbol->string t) " (a citer or companion of "
                                   (symbol->string n) ") lives in " tf)))
   ((not (member tf new-files)) #f)          ; its file left the list: retired itself
   ((let ((p (hash-table-ref/default *xb-position-table* tf #f)))
      (or (not p) (<= p i)))
    (xb-refuse-now! (string-append (symbol->string t) " (a citer or companion of "
                                   (symbol->string n) ") sits in " tf
                                   ", which loads before " f)))
   (else
    (display ";; extend-band:   pulls in ") (display tf) (newline)
    (hash-table-set! pending tf #t))))

(define (xb-companions-minted-elsewhere n f view)
  (let ((acc '()))
    (hash-table-walk *view-specialized-source*
      (lambda (comp src)
        (if (and (eq? src n)
                 (not (equal? (hash-table-ref/default (xb-view-files view) comp #f) f)))
            (set! acc (cons comp acc)))))
    acc))

;;; After file F (position I) has loaded: every name F stated in the band
;;; (VIEW, taken before any retraction) is compared with its SNAPSHOT
;;; fingerprint.  A name that vanished is retracted in full; for every changed
;;; name, the files of its citers -- and of the view companions another file
;;; minted from it -- join PENDING (or the run stops, see `xb-pull!').
;;;
;;; A name that is NEW (absent from the band) has no citers, but a later file
;;; that SPECIALIZES every theorem of a structure through a view (an
;;; unrestricted `view-as-auto-specialize!', or `def-functor') would, in a cold
;;; load, mint a companion of it.  SPECIALIZERS is the list `xb-specializers'
;;; returns; a matching later specializer joins PENDING (theorem-library) or
;;; stops the run (anything else).
;;; Returns ((NAME . CHANGE) ...), CHANGE `new' included.
(define (xb-after-file! f i view snapshot new-files pending #!optional specializers)
  (let ((changes '())
        (specializers (if (default-object? specializers) '() specializers)))
    (if (pair? specializers)
        (hash-table-walk *theorem-table*
          (lambda (n stmt)
            (if (and (not (hash-table-ref/default snapshot n #f))
                     (not (rev-companion-source n))
                     (equal? (xb-name-file n) f))
                (for-each
                 (lambda (sp)
                   (let ((g (car sp)) (v (lookup-view-as (cdr sp))))
                     (if (and v
                              (> (hash-table-ref/default *xb-position-table* g -1) i)
                              (not (hash-table-ref/default pending g #f))
                              (generic-for-struct?
                               stmt (symbol-append 'IS- (view-as-target-struct v))))
                         (begin
                           (set! changes (cons (cons n 'new) changes))
                           (if (not (xb-theorem-library? g))
                               (xb-refuse-now!
                                (string-append "the new theorem " (symbol->string n)
                                               " would be specialized through the view "
                                               (symbol->string (cdr sp)) " by " g)))
                           (display ";; extend-band: new ") (display n)
                           (display " is specialized by ") (display g)
                           (display " -- it reloads\n")
                           (hash-table-set! pending g #t)))))
                 specializers)))))
    (for-each
     (lambda (n)
       (let* ((old (hash-table-ref/default snapshot n #f))
              (ch  (and old (xb-change-of n old))))
         (if ch
             (begin
               (set! changes (cons (cons n ch) changes))
               (display ";; extend-band: ") (display n) (display " ")
               (display ch) (display " -- its citers reload\n")
               (let ((comps (xb-companions-minted-elsewhere n f view)))
                 (if (eq? ch 'vanished) (xb-retract-names! (list n) 'full))
                 (for-each
                  (lambda (t)
                    (xb-pull! t (hash-table-ref/default (xb-view-files view) t #f)
                              n f i new-files pending))
                  (append (hash-table-ref/default (xb-view-citers view) n '())
                          comps)))))))
     (xb-view-names-of-file view f))
    (reverse changes)))

(define (xb-execute! plan)
  (let* ((new-files (car (xb-read-load-scm)))
         (view      (xb-current-view))
         (snapshot  (let ((h (make-strong-eqv-hash-table)))
                      (hash-table-walk *theorem-table*
                        (lambda (n s) (hash-table-set! h n (xb-fingerprint n))))
                      h))
         (pending   (make-equal-hash-table))
         (retracted-files (make-equal-hash-table))
         (n-retracted 0)
         (loaded    '())
         (t0        (get-universal-time))
         (specializers (xb-specializers new-files
                                        (let ((b (member "extend-band" new-files)))
                                          (- (length new-files) (length b))))))
    (for-each (lambda (f) (hash-table-set! pending f #t)) (xb-plan-ref plan 'reload))
    (set! *xb-alias-snapshot* '())
    ;; RETRACT FIRST, everything the plan names, before any file loads (a new
    ;; proof must not find a support that was removed from a LATER file)
    (let ((full   (map car (filter (lambda (e) (eq? (cdr e) 'full)) (xb-plan-ref plan 'retract))))
          (reload (map car (filter (lambda (e) (eq? (cdr e) 'reload)) (xb-plan-ref plan 'retract)))))
      (if (pair? full)   (xb-retract-names! full 'full))
      (if (pair? reload) (xb-retract-names! reload 'reload))
      (set! n-retracted (+ (length full) (length reload))))
    (for-each (lambda (f) (hash-table-set! retracted-files f #t)) (xb-plan-ref plan 'reload))
    (xb-reset-derived-caches!)
    (set! *case-fold-define-collisions*
          (filter (lambda (e) (and (member (car e) new-files)
                                   (not (hash-table-ref/default pending (car e) #f))))
                  *case-fold-define-collisions*))
    (set! *vnb-files* new-files)
    (set! *xb-order-violations* '())
    (set! *vnb-loading* #t)
    (set! *reject-constant-binders?* #f)     ; as during a cold load (load.scm resets it)
    (xb-with-order-check new-files
      (lambda ()
        (let loop ((fs new-files) (i 0))
          (if (pair? fs)
              (let ((f (car fs)))
                (if (hash-table-ref/default pending f #f)
                    (begin
                      ;; a file pulled in during the run: retract its names now
                      (if (not (hash-table-ref/default retracted-files f #f))
                          (let ((ns (xb-view-names-of-file view f)))
                            (if (pair? ns) (xb-retract-names! ns 'reload))
                            (set! n-retracted (+ n-retracted (length ns)))
                            (hash-table-set! retracted-files f #t)
                            (set! *case-fold-define-collisions*
                                  (filter (lambda (e) (not (equal? (car e) f)))
                                          *case-fold-define-collisions*))))
                      (display ";; extend-band: loading ") (display f)
                      (display " (position ") (display i) (display ")\n")
                      (set! *xb-order-position* i)
                      (let ((t1 (get-universal-time)))
                        ;; Load EXACTLY as the cold load does: the .com when it
                        ;; is fresh, the .scm otherwise (load.scm's rule).  The
                        ;; first version loaded the .scm unconditionally; the
                        ;; first compare mismatch (2026-09-24, taylor-coef-from-
                        ;; derivs) was a driver whose `let' bound two recording
                        ;; calls, and MIT orders a let's initialisers differently
                        ;; in interpreted and compiled code.  Same code, same
                        ;; script.
                        (prover-load--file f (let ((base (string-append *prover-dir* f)))
                                               (if (file-fresh-com? base) base (string-append base ".scm"))))
                        (set! loaded (cons (cons f (- (get-universal-time) t1)) loaded)))
                      (set! *xb-order-position* #f)
                      (if (pair? *xb-order-violations*)
                          (xb-refuse-now!
                           (string-append "order violation(s) in " f ": "
                                          (call-with-output-string
                                            (lambda (p) (write (reverse *xb-order-violations*) p))))))
                      (if (pair? *vnb-qed-failures*)
                          (error "vnb-extend-band!: qed failed while reloading" f
                                 (reverse *vnb-qed-failures*)))
                      ;; what changed among the names this file stated in the band
                      (xb-after-file! f i view snapshot new-files pending specializers)))
                (loop (cdr fs) (+ i 1)))))
        ;; binders whose first owner was retracted go to the next one in load order
        (xb-reown-binders! (map car loaded))
        ;; alias strings written by files that did not reload come back
        (xb-restore-aliases! new-files (map car loaded))))
    ;; the same end-of-load block as load.scm: gates, page audit over ALL
    ;; proofs, reference writers, session reset, band record
    (let ((t-files (- (get-universal-time) t0)))
      (set! *page-audit-results* '())
      (run-load-end!)
      (let ((summary
             (list (cons 'reload-files (reverse (map car loaded)))
                   (cons 'retracted n-retracted)
                   (cons 'install-duplicates (length *install-duplicates*))
                   (cons 'order-violations (length *xb-order-violations*))
                   (cons 'files-s t-files)
                   (cons 'total-s (- (get-universal-time) t0)))))
        (display ";;VNB-EXTEND reload_files=") (display (length loaded))
        (display " retracted=") (display n-retracted)
        (display " install_duplicates=") (display (length *install-duplicates*))
        (display " order_violations=") (display (length *xb-order-violations*))
        (display " files_s=") (display t-files)
        (display " total_s=") (display (- (get-universal-time) t0))
        (display " strict=") (display (if *vnb-band-strict?* 1 0))
        (newline)
        (if (not *vnb-band-strict?*)
            (error "vnb-extend-band!: the extended image is not strict" *xb-not-strict-reason*))
        summary))))
