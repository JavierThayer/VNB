;;; clobber-guard.scm -- the gate CLAUDE.md says does not exist.
;;;
;;; Both the VNB reader and MIT Scheme fold symbols to lowercase, so a proof
;;; file's innocent-looking
;;;
;;;     (define BC '(succ p))
;;;
;;; rebinds the `bc' TACTIC to a term.  Every later (bc 'thm) -- in that file
;;; and in every file loaded after it -- dies with "The object (...) is not
;;; applicable", or worse, quietly does the wrong thing.  Real cases: BC in
;;; bordered-eq-border-proof.scm (broke four suite tests in a different file),
;;; TT in hahn-banach-full-proof.scm and nn-least-element.scm, SP in a Smith
;;; driver, ID in mat-equiv-proof.scm.
;;;
;;; `case-fold-audit' and `constant-binder-audit' both inspect WFF binders and
;;; never Scheme defines, so neither sees it.
;;;
;;; The invariant enforced here is stronger than "do not shadow a tactic", and
;;; needs no registry of tactic names:
;;;
;;;   NO FILE MAY REBIND, TO A NON-PROCEDURE, A NAME THAT WAS A PROCEDURE
;;;   BEFORE IT LOADED.
;;;
;;; That is exactly the bug: `bc' was a procedure, `(define BC '(...))' makes it
;;; a list.  Redefining a procedure with another procedure stays legal, which
;;; matters -- several drivers re-define the shared `proof-leaves' / `any-pred'
;;; helpers, and that is (for now) load-bearing.  It is also the one gap:
;;; `(define (append a b) ...)' -- procedure over procedure -- is NOT caught.
;;;
;;; Loads FIRST, before any other VNB file (load.scm); `prover-load' calls
;;; clobber-guard-check! after each subsequent file.  It used to load at
;;; load.scm:518, and its own header admitted the consequence -- "files loaded
;;; before the snapshot are unguarded".  Measured 2026-08-16: **126 library
;;; files loaded before it, 118 after**, so more than half the library --
;;; including all of `structure-library/' -- was outside the alarm.

;;; The environment proof files are loaded into.  MIT's `load' with no
;;; environment argument uses the CALLER's environment, and load.scm's caller is
;;; this same top level -- so `bc' and friends live in this very frame, and
;;; environment-bound-names sees them (it reports the own frame only).
(define *clobber-guard-env* (the-environment))

(define *clobber-guard-procs* #f)        ; name -> #t, or #f before the snapshot

;; environment-lookup REFUSES a syntactic keyword ("Variable reference to a
;; syntactic keyword: bc*") and errors on an unassigned binding, so it cannot be
;; called bare over environment-bound-names.  Macros are simply never watched:
;; they answer 'unavailable both at snapshot and at check time, consistently.
(define (clobber-guard--value n)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler (lambda (e) (k 'clobber-guard--unavailable))
        (lambda () (environment-lookup *clobber-guard-env* n))))))

(define (clobber-guard--procedure? n)
  (and (environment-bound? *clobber-guard-env* n)
       (procedure? (clobber-guard--value n))))

;;; SEED FROM THE GLOBAL ENVIRONMENT TOO (2026-08-16), and this is the point.
;;; `environment-bound-names' reports the OWN FRAME ONLY -- the comment above
;;; says so -- and at the head of the load that frame holds nine names.  MIT's
;;; own procedures live in the PARENT, so `append', `list', `cons', `length'
;;; were never in the watch set at all, at any snapshot point, early or late.
;;;
;;; They are exactly the names that matter.  Each is simultaneously a live
;;; Scheme procedure and a VNB head symbol, so a proof file's
;;; `(define APPEND '(...))' shadows a procedure the prover itself calls with a
;;; list.  `environment-bound?' DOES search the parent chain, so a shadow in the
;;; top frame is caught by the ordinary check once the name is in the set.
(define (clobber-guard-snapshot!)
  (let ((h (make-strong-eqv-hash-table)))
    (for-each (lambda (n) (if (clobber-guard--procedure? n) (hash-table-set! h n #t)))
              (append (environment-bound-names *clobber-guard-env*)
                      (environment-bound-names system-global-environment)))
    (set! *clobber-guard-procs* h)
    (display ";; clobber-guard: watching ")
    (display (length (hash-table-keys h)))
    (display " procedure bindings")
    (newline)))

;;; ONE PASS OVER THE OWN FRAME does both jobs -- detect casualties, and absorb
;;; what the file newly defined -- and it is what makes watching MIT's ~3900
;;; globals affordable.
;;;
;;; The obvious implementation walks the WATCH SET after every file, re-looking
;;; up each member.  That is 3975 names x ~250 files, each a `bound?' plus a
;;; lookup inside a continuation and an exception handler, and it cost 23 s on
;;; top of a 48 s cold load -- measured, not guessed.
;;;
;;; The direction was simply wrong.  A file can only turn a procedure into a
;;; non-procedure by DEFINING that name, and a definition lands in the top
;;; frame.  So the names that can possibly have changed are exactly the own
;;; frame's -- whether the victim was a VNB tactic or a shadowed MIT global.
;;; Walking the own frame is therefore COMPLETE for the invariant and costs in
;;; proportion to what the file did rather than to how much is being watched.
;;;
;;; The same pass grows the set: a name in the own frame that is a procedure and
;;; not yet watched becomes watched, so VNB's own tactics join as they appear
;;; and the early snapshot loses nothing.
;;;
;;; Report EVERY casualty, not just the first: one bad `define' usually comes
;;; with siblings, and a second 11-minute load to find the next one is a waste.
(define (clobber-guard-check! file)
  (if *clobber-guard-procs*
      (let ((bad '()))
        (for-each
         (lambda (n)
           (let ((watched (hash-table-ref/default *clobber-guard-procs* n #f))
                 (proc?   (clobber-guard--procedure? n)))
             (cond ((and watched (not proc?)) (set! bad (cons n bad)))
                   ((and (not watched) proc?)
                    (hash-table-set! *clobber-guard-procs* n #t)))))
         (environment-bound-names *clobber-guard-env*))
        (if (not (null? bad))
            (begin
              ;; drop them from the watch set: the damage is already reported,
              ;; and leaving them in would re-blame every later file.
              (for-each (lambda (n) (hash-table-delete! *clobber-guard-procs* n)) bad)
              (error
               (string-append
                "clobber-guard: " file
                " rebound a procedure to a non-procedure -- almost certainly a"
                " top-level (define X ...) whose name case-folds onto a tactic"
                " or onto one of MIT Scheme's own procedures."
                "  Use the file's helper prefix instead.  Casualties:")
               (sort bad (lambda (a b) (string<? (symbol->string a)
                                                 (symbol->string b))))))))))

(clobber-guard-snapshot!)

;;; =======================================================================
;;; THE READ-TIME CASE-FOLD LINT (2026-09-20) -- the sister defect, and the
;;; guard above cannot see it.
;;;
;;;     (define r11f-S (list 'SPAN ...))      ... 200 lines later ...
;;;     (define r11f-s (dk-fact! ...))
;;;
;;; MIT Scheme folds symbols to lowercase AT READ TIME, so those are ONE
;;; binding: the later definition silently replaces the earlier, and every
;;; reference in between now sees the wrong value.  The clobber-guard above
;;; cannot catch it (both are procedures, or neither is), and no audit inside
;;; the image can: by the time any Scheme-level check runs, the two spellings
;;; HAVE ALREADY BECOME THE SAME SYMBOL.  The only place they still differ is
;;; the SOURCE TEXT, which is why this lint reads the file.  Three agents lost
;;; probe runs to the pattern in one week (r11f-S / r11f-s, r8f-W / r8f-w).
;;;
;;; TWO STAGES, because the proof corpus is ~8 MB and a load must not pay for
;;; a character walk over it (measured 2026-09-20, on this box):
;;;
;;;   1. TRIGGER.  Slurp the file as a BYTEVECTOR (0.14 s for the whole tree;
;;;      through a character port the same read costs 8 s), decode it, and let
;;;      the COMPILED `string-search-all' find every "(define" at column 0;
;;;      read the spelling after each with a bounded scan.  Stage 1 sees text
;;;      inside comments and strings too, which is harmless: it never reports,
;;;      and a collision needs at least one spelling with an upper case letter
;;;      in it.  2.9 s for 632 files.
;;;   2. VERDICT.  Only when stage 1 saw a spelling with an upper case letter
;;;      (141 of the 632 files) does MIT's own reader run over the text with
;;;      `param:reader-fold-case?' bound to #f.  The reader handles `;',
;;;      `#|...|#', `#;' and strings itself -- that is the point of using it
;;;      rather than a hand-written scanner -- and it finds a top-level define
;;;      however it is indented.  2 s for those 141 files.
;;;
;;; Whole-tree cost 4.9 s, against a cold load of several minutes.
;;;
;;; WARN-ONLY, and it stays warn-only until the backlog is zero: five files
;;; collide today and all five load.  `report-case-fold-defines' prints what
;;; accumulated; the suite pins the procedure's behaviour on a scratch file.
;;;
;;; NOT the same check as `duplicate-define-audit' (audit.scm): that one reads
;;; 16 named ENGINE files with the FOLDING reader and counts a name defined
;;; twice, so it sees a collision in those files as a duplicate and cannot say
;;; which two spellings caused it; this one runs over every file the loader
;;; touches -- the proof corpus above all -- and names the spellings.
(define *case-fold-define-collisions* '())     ; (file (folded spelling ...) ...)

(define (cfd--slurp path)
  (call-with-binary-input-file path
    (lambda (port)
      (let ((bv (read-bytevector 100000000 port)))
        (if (bytevector? bv) (utf8->string bv) "")))))

(define (cfd--delimiter? c)
  (or (char=? c #\space) (char=? c #\tab) (char=? c #\newline)
      (char=? c #\return) (char=? c #\() (char=? c #\))))

;; The spelling that follows the "(define" starting at POS: `(define NAME',
;; `(define (NAME arg ...)' and the curried `(define ((NAME a) b)' alike.
(define (cfd--name-at text pos)
  (let ((n (string-length text)))
    (let skip ((i (+ pos 7)))
      (and (< i n)
           (let ((c (string-ref text i)))
             (cond ((or (char=? c #\space) (char=? c #\tab)
                        (char=? c #\newline) (char=? c #\return) (char=? c #\())
                    (skip (+ i 1)))
                   ((char=? c #\)) #f)
                   (#t (let scan ((j i))
                         (if (or (>= j n) (cfd--delimiter? (string-ref text j)))
                             (and (> j i) (substring text i j))
                             (scan (+ j 1)))))))))))

(define (cfd--has-upper? s)
  (let ((n (string-length s)))
    (let loop ((i 0))
      (and (< i n)
           (or (char-upper-case? (string-ref s i)) (loop (+ i 1)))))))

;; stage 1 -- cheap, over-approximate, never reports
(define (cfd--maybe-mixed? text)
  (let loop ((ps (if (string-prefix? "(define" text)
                     (cons -1 (string-search-all "\n(define" text))
                     (string-search-all "\n(define" text))))
    (and (pair? ps)
         (let ((nm (cfd--name-at text (+ (car ps) 1))))
           (or (and nm (cfd--has-upper? nm)) (loop (cdr ps)))))))

;; stage 2 -- MIT's reader with case folding OFF: the verdict
(define (cfd--define-target form)
  (and (pair? form)
       (symbol? (car form))
       (string-ci=? (symbol->string (car form)) "define")
       (pair? (cdr form))
       (let loop ((t (cadr form)))
         (cond ((symbol? t) (symbol->string t))
               ((pair? t) (loop (car t)))
               (#t #f)))))

(define (cfd--read-names text)
  (let ((port (string->input-port text)))
    (parameterize ((param:reader-fold-case? #f))
      (let loop ((acc '()))
        (let ((f (read port)))
          (if (eof-object? f)
              (reverse acc)
              (loop (let ((nm (cfd--define-target f)))
                      (if nm (cons nm acc) acc)))))))))

;; names -> ((folded spelling spelling ...) ...), one entry per folded name
;; that two different spellings share.
(define (cfd--collisions names)
  (let ((seen (make-equal-hash-table)) (out '()))
    (for-each (lambda (s)
                (let* ((k (string-downcase s))
                       (prev (hash-table-ref/default seen k '())))
                  (if (not (member s prev)) (hash-table-set! seen k (cons s prev)))))
              names)
    (hash-table-walk seen
      (lambda (k v) (if (> (length v) 1) (set! out (cons (cons k (sort v string<?)) out)))))
    (sort out (lambda (a b) (string<? (car a) (car b))))))

;;; The entry point, called from load.scm's per-file loader.  FILE is the
;;; load-relative name (for the message), PATH the source file to read.  A
;;; missing or unreadable file is NOT an error and NOT a finding: a compiled
;;; file still has its .scm beside it, and if it has not, there is nothing to
;;; lint.  Returns the collisions found in this file.
;;; ---------------------------------------------------------------------
;;; THE LOCAL-BINDING CASE-FOLD LINT (2026-09-24, batch 27-B, item 14).  The
;;; same trap one level down: two LOCAL binders in one top-level form whose
;;; spellings differ only by case -- `(let* ((seqg ...) (seqG ...)) ...)' --
;;; are ONE variable, the second shadowing the first.  Batch 22-B met it twice
;;; in one file (seqg / seqG, gk / Gk); the symptoms were a typing leaf that
;;; could not close and a lemma instantiated at the wrong term.  The define
;;; lint above sees top-level names only.
;;;
;;; Per top-level form, read with folding OFF: every name bound by let, let*,
;;; letrec, letrec*, named let, fluid-let, do, lambda, named-lambda and an
;;; internal define (and the parameters of the top-level define itself; not its
;;; name, which is the other lint's), with quote and quasiquote skipped --
;;; formulas are data.  Two DIFFERENT spellings with one folded name in one
;;; form is a finding.  Warn-only; run by `case-fold-define-lint!' on
;;; theorem-library/ and calculus/ files, so load.scm needs no new line; the
;;; roll-up prints with `report-case-fold-defines'.  No cheap trigger: a text
;;; test ("an upper-case letter near a binding keyword") fired on 466 of 505
;;; proof files, since formulas are upper case; every proof file is read.
(define *case-fold-local-collisions* '())   ; (file (form-name (folded sp ...) ...) ...)

;;; Keywords are compared by `memq' on the symbols as the NON-folding reader
;;; returns them: the tree spells them in lower case, and a string comparison
;;; per pair (the first draft) cost 55 s over the tree, mostly in allocation.
(define cfl--let-heads '(let let* letrec letrec* fluid-let))

(define (cfl--params p acc)                 ; symbols of a (possibly improper) list
  (cond ((symbol? p) (cons p acc))
        ((pair? p) (cfl--params (cdr p) (cfl--params (car p) acc)))
        (#t acc)))

(define (cfl--binders x top? acc)
  (if (not (pair? x))
      acc
      (let ((h (car x)))
        (cond
         ((memq h '(quote quasiquote)) acc)
         ((and (memq h cfl--let-heads) (pair? (cdr x)))
          (let* ((named (symbol? (cadr x)))
                 (bs    (if named (if (pair? (cddr x)) (caddr x) '()) (cadr x)))
                 (body  (if named (if (pair? (cddr x)) (cdddr x) '()) (cddr x)))
                 (acc   (if named (cons (cadr x) acc) acc))
                 (acc   (let loop ((bs bs) (acc acc))
                          (cond ((not (pair? bs)) acc)
                                ((pair? (car bs))
                                 (loop (cdr bs)
                                       (cfl--binders-list (cdar bs)
                                                          (cfl--params (caar bs) acc))))
                                (#t (loop (cdr bs) (cfl--params (car bs) acc)))))))
            (cfl--binders-list body acc)))
         ((and (eq? h 'do) (pair? (cdr x)) (list? (cadr x)))
          (cfl--binders-list (cddr x)
            (fold-left (lambda (a b) (if (pair? b) (cfl--params (car b) a) a)) acc (cadr x))))
         ((and (memq h '(lambda named-lambda)) (pair? (cdr x)))
          (cfl--binders-list (cddr x) (cfl--params (cadr x) acc)))
         ((and (eq? h 'define) (pair? (cdr x)))
          (let ((target (cadr x)))
            (cfl--binders-list
             (cddr x)
             (cond ((pair? target)             ; (define (f . args) ...), curried too
                    (let loop ((t target) (acc acc))
                      (if (pair? (car t))
                          (cfl--params (cdr t) (loop (car t) acc))
                          (cfl--params (cdr t) (if top? acc (cfl--params (car t) acc))))))
                   ((symbol? target) (if top? acc (cons target acc)))
                   (#t acc)))))
         (#t (cfl--binders-list x acc))))))

(define (cfl--binders-list l acc)
  (if (pair? l)
      (cfl--binders-list (cdr l) (cfl--binders (car l) #f acc))
      acc))

(define (cfl--form-name form)
  (let ((t (cfd--define-target form)))
    (or t "<top-level form>")))

(define (cfl--form-collisions form)
  (let ((seen (make-strong-eqv-hash-table)) (mixed? #f) (names '()))
    (for-each (lambda (b)
                (if (and (symbol? b) (not (hash-table-ref/default seen b #f)))
                    (let ((s (symbol->string b)))
                      (hash-table-set! seen b #t)
                      (if (not (string=? s (string-downcase s))) (set! mixed? #t))
                      (set! names (cons s names)))))
              (cfl--binders form #t '()))
    (if mixed? (cfd--collisions names) '())))

;;; QUOTED DATA (2026-10-24, the LA-Z3 agent): a statement written as a quoted
;;; S-expression, `(FORSOME x (IN x X))', is read by the folding reader into
;;; `x in x', and the binder walk above never enters a quote.  Each quoted datum
;;; of a form is checked on its own: two symbols in ONE datum that differ only by
;;; case are one symbol.  Data in different quotes are not compared (a helper's
;;; 'X and a statement's 'x elsewhere in the form are separate things).
(define (cfl--quoted-data x acc)
  (cond ((not (pair? x)) acc)
        ((and (memq (car x) '(quote quasiquote)) (pair? (cdr x)))
         (cons (cadr x) acc))
        (#t (cfl--quoted-data (cdr x) (cfl--quoted-data (car x) acc)))))

;;; Only symbols in ARGUMENT position count: a head (`(HAS-INVERSES ..)', `(LIST ..)')
;;; is a constant, which reads the same in either spelling.  A registered constant
;;; met as an argument is passed over for the same reason (the registry exists by the
;;; time any library file is linted).
(define cfl--env (the-environment))        ; clobber-guard.scm is never compiled (load.scm)
(define (cfl--constant-name? s)
  (and (environment-bound? cfl--env '*constant-registry*)
       (hash-table-ref/default (eval '*constant-registry* cfl--env)
                               (string->symbol (string-downcase s)) #f)
       #t))

(define (cfl--datum-symbols d acc)
  (cond ((symbol? d) (if (cfl--constant-name? (symbol->string d)) acc (cons (symbol->string d) acc)))
        ((pair? d)
         (let walk ((l (cdr d)) (acc (if (pair? (car d)) (cfl--datum-symbols (car d) acc) acc)))
           (cond ((pair? l) (walk (cdr l) (cfl--datum-symbols (car l) acc)))
                 ((symbol? l) (cfl--datum-symbols l acc))
                 (#t acc))))
        ((vector? d) (fold-left (lambda (a e) (cfl--datum-symbols e a)) acc (vector->list d)))
        (#t acc)))

;;; One exemption: a FLAT list of symbols that spells a multi-letter name both
;;; ALL-UPPER and all-lower is a deliberate case-insensitive table (a `memq' list
;;; such as '(is-identity IS-IDENTITY)), not a statement.  A single letter, or a
;;; mixed spelling (bd-K / bd-k), is reported even there: '(R n B r) handed to
;;; forall-guarded is exactly the binder list that read r as R (LA-Z, 2026-10-19).
(define (cfl--flat-symbol-list? d)
  (and (list? d) (every symbol? d)))

(define (cfl--dual-listing? col)            ; (folded spelling spelling ...)
  (let ((sp (cdr col)))
    (and (= (length sp) 2)
         (> (string-length (car col)) 1)
         (let ((u (string-upcase (car col))) (l (car col)))
           (and (member u sp) (member l sp) #t)))))

(define (cfl--quoted-collisions form)
  (fold-left
   (lambda (acc d)
     (let ((names (if (cfl--flat-symbol-list? d)   ; a binder list: every entry is a name
                      (fold-left (lambda (a e) (cfl--datum-symbols e a)) '() d)
                      (cfl--datum-symbols d '()))))
       (if (any (lambda (s) (not (string=? s (string-downcase s)))) names)
           (append acc
                   (let ((cols (cfd--collisions names)))
                     (if (cfl--flat-symbol-list? d)
                         (filter (lambda (c) (not (cfl--dual-listing? c))) cols)
                         cols)))
           acc)))
   '()
   (reverse (cfl--quoted-data form '()))))

;;; A LOCAL NAME AGAINST A TOP-LEVEL ONE (2026-10-25, KIT-5 item 7; LA-Z5
;;; finding 1).  The per-form walk compares the binders of ONE top-level form,
;;; so the shape LA-Z5 described -- `I' bound by an outer let* of a define, `i'
;;; by a let* inside a lambda of the same define -- IS reported (the KIT-5 probe
;;; ran the lint on la-z5-card52.scm with its `ivl' renamed back to `I': "in
;;; lz5q-main!: I i -> i").  What no walk compared is a local binder against a
;;; TOP-LEVEL define of the same file: `(define LZ-I ...)' at the top and
;;; `(let ((lz-i ...)) ...)' in a helper are one symbol, and inside the let every
;;; reference meant for the top-level value reads the local one.  The text is now
;;; read once into its forms; the top-level define spellings are collected
;;; first, and each form's binders are tested against them as well.  Such an
;;; entry is labelled "<form> (against a top-level define)".
(define (cfl--read-forms text)
  (let ((port (string->input-port text)))
    (parameterize ((param:reader-fold-case? #f))
      (let loop ((acc '()))
        (let ((f (read port)))
          (if (eof-object? f) (reverse acc) (loop (cons f acc))))))))

(define (cfl--toplevel-collisions form tops)
  (let ((out '()))
    (for-each (lambda (b)
                (if (symbol? b)
                    (let ((s (symbol->string b)))
                      (for-each (lambda (d)
                                  (if (and (not (string=? s d)) (string-ci=? s d))
                                      (let ((c (cfd--collisions (list d s))))
                                        (if (and (pair? c) (not (member (car c) out)))
                                            (set! out (cons (car c) out))))))
                                tops))))
              (cfl--binders form #t '()))
    (reverse out)))

(define (cfl--forms-collisions forms)
  (let ((tops (filter (lambda (s) s) (map cfd--define-target forms))))
    (let loop ((fs forms) (acc '()))
      (if (null? fs)
          (reverse acc)
          (let* ((f (car fs))
                 (cols (if (pair? f) (cfl--form-collisions f) '()))
                 (acc (if (pair? cols) (cons (cons (cfl--form-name f) cols) acc) acc))
                 (qcols (if (pair? f) (cfl--quoted-collisions f) '()))
                 (acc (if (pair? qcols)
                          (cons (cons (string-append (cfl--form-name f) " (a quoted datum)") qcols) acc)
                          acc))
                 (tcols (if (pair? f) (cfl--toplevel-collisions f tops) '())))
            (loop (cdr fs)
                  (if (pair? tcols)
                      (cons (cons (string-append (cfl--form-name f) " (against a top-level define)") tcols) acc)
                      acc)))))))

(define (case-fold-local-lint-text text)
  (cfl--forms-collisions (cfl--read-forms text)))

(define (case-fold-local-lint! file path)
  (let* ((forms
          (and (file-exists? path)
               (call-with-current-continuation
                 (lambda (k)
                   (with-exception-handler (lambda (e) (k #f))
                     (lambda () (cfl--read-forms (cfd--slurp path))))))))
         (hits (if forms
                   (call-with-current-continuation
                     (lambda (k)
                       (with-exception-handler (lambda (e) (k '()))
                         (lambda () (cfl--forms-collisions forms)))))
                   '())))
    ;; the recording-order lint reads the same forms (KIT-5): no second read
    (if forms (recording-order-lint-forms! file forms))
    (when (pair? hits)
      (set! *case-fold-local-collisions*
            (cons (cons file hits) *case-fold-local-collisions*)))
    ;; Per-file lines only for a probe or a wrapper load (as the recording-order lint
    ;; below): a load prints the roll-up (`report-case-fold-defines').
    (when (and (pair? hits)
               (or (not (cfl--proof-file? file)) (string-search-forward "__" file 0)))
      (display ";VNB warning: case-fold lint: ") (display file)
      (display " binds two LOCAL names MIT Scheme reads as ONE:\n")
      (for-each (lambda (h)
                  (for-each (lambda (c)
                              (display ";              in ") (display (car h)) (display ": ")
                              (for-each (lambda (s) (display s) (display "  ")) (cdr c))
                              (display "->  ") (display (car c)) (newline))
                            (cdr h)))
                hits)
      (display ";              The inner binding silently SHADOWS (or replaces) the other; inside one quoted\n")
      (display ";              datum the two spellings are ONE symbol (a statement's x and X read as one variable).\n"))
    (if (pair? hits) hits '())))

;;; =======================================================================
;;; THE RECORDING-ORDER LINT (2026-10-25, KIT-5 item 7; LA-Z6 finding 4).
;;;
;;;     (let ((a (dk-cite! 'x ...)) (b (dk-cite! 'y ...))) ...)
;;;     (chain! (dk-cite! ...) (dk-cite! ...))
;;;
;;; Two RECORDING calls -- calls that take a proof step -- whose order the
;;; language leaves unspecified: the inits of a `let', the arguments of one
;;; application.  MIT evaluates arguments right to left, and compiled and
;;; interpreted code do not agree on the order of a `let''s inits: the first
;;; extend-band compare mismatch (2026-09-24) was such a driver, its page
;;; recorded in one order by the cold load and in the other by the extension.
;;; LA-Z6 met the argument-list form and found it only by reading its own file:
;;; it passed every probe.  `let*', `begin', `cond', `and', `or', `if' fix the
;;; order and are not findings.
;;;
;;; A RECORDING CALL is, syntactically: an application whose head is a surface
;;; tactic (the names `vnb--run!' records, plus the composites and the kit's
;;; thunk-runners such as `dk-landed' and `quietly' when their thunk records),
;;; or whose head symbol ends in `!' and is not a Scheme mutator (`set-car!',
;;; `hash-table-set!', ...) -- the kit's and the drivers' naming convention.
;;; A `lambda' is not evaluated where it stands, so its body never counts toward
;;; the enclosing form (`(dk-have! claim (lambda () ...))' is one call).  Quoted
;;; data are skipped.  WARN-ONLY; run with the case-fold local lint (same read
;;; of the file), on every proof file of a load and every file a probe loads by
;;; a literal path; `report-case-fold-defines' prints the roll-up.
(define *recording-order-findings* '())     ; (file (form-name head (rec-head ...)) ...)

(define cro--tactics
  '(ai apply-thm arith ass bc beta bu-me bu-mi bu-set ce ci comp-me comp-mi crs cut di ew
    fact grind ie if-false if-true ii ineq inst inst+ iota-d iota-e keep lam-b lam-b-h lam-t
    len-r mac mac-h mac-h* macm ni nth-r oi-l oi-r pbc qrfl rfl rs sep-me sep-mi sep-set simp
    slot slot-h sos subst ta te tfi tfi3 ti ue ui wk zero-it
    use-em use-cases prop contra prep type-term preamble obtain focus sp qed mp push-not
    push-not-h in-rr from-context ew-poly backup-one undo))

;;; take a thunk and RUN it: a call records when its thunk does
(define cro--thunk-runners
  '(dk-landed dk-landed* dk-landed-1 dk-landed-find dk-deepest dk-opened quietly vnb-guard
    dk--silently dk--transaction call-with-current-continuation with-exception-handler
    dynamic-wind))

(define cro--mutators
  '(set! set-car! set-cdr! vector-set! string-set! list-set! vector-fill! string-fill!
    hash-table-set! hash-table-update! hash-table-update!/default hash-table-delete!
    hash-table-clear! bytevector-u8-set! set-cdr! 1d-table/put! 2d-put! fluid-let))

(define (cro--bang? s)
  (and (symbol? s)
       (not (memq s cro--mutators))
       (let ((str (symbol->string s)))
         (and (> (string-length str) 1)
              (char=? (string-ref str (- (string-length str) 1)) #\!)))))

(define (cro--lambda? e) (and (pair? e) (memq (car e) '(lambda named-lambda))))

;;; THE SHAPES.  An expression is classified once, here, so the two walks below
;;; agree on what is an expression: a binding list, a cond clause, a lambda's
;;; parameter list are NOT applications (a variable named `ti' or `ii' -- both
;;; tactic names -- heading a binding pair is not a call of the tactic).
;;; (cro--parts E) => (KIND . STUFF):
;;;   (skip)                     quoted data, a lambda (not run where it stands)
;;;   (seq EXPR ...)             subexpressions evaluated in a FIXED order
;;;   (unordered (INIT ...) EXPR ...)  a let's inits (unordered), then the body
;;;   (runner EXPR ...)          a thunk-runner: its lambdas' bodies are RUN
;;;   (app HEAD EXPR ...)        an application; HEAD the symbol or #f
(define (cro--binding-inits bs)
  (if (list? bs) (filter-map (lambda (b) (and (pair? b) (pair? (cdr b)) (cadr b))) bs) '()))

(define (cro--clauses cls)                  ; cond / guard clauses: their expressions
  (append-map (lambda (cl) (if (list? cl) (filter (lambda (e) (not (eq? e '=>))) cl) '())) cls))

(define (cro--parts e)
  (let ((h (car e)) (r (cdr e)))
    (cond
      ((memq h '(quote quasiquote define-record-type define-syntax let-syntax letrec-syntax
                 syntax-rules delay delay-force make-promise cons-stream))
       '(skip))
      ((memq h '(lambda named-lambda case-lambda)) '(skip))
      ((not (list? r)) '(skip))
      ((and (memq h '(let letrec fluid-let)) (pair? r))
       (if (and (eq? h 'let) (symbol? (car r)))
           (if (pair? (cdr r)) (cons 'unordered (cons (cro--binding-inits (cadr r)) (cddr r))) '(skip))
           (cons 'unordered (cons (cro--binding-inits (car r)) (cdr r)))))
      ((and (memq h '(let* letrec* parameterize let-values let*-values)) (pair? r))
       (cons 'seq (append (cro--binding-inits (car r)) (cdr r))))
      ((and (eq? h 'receive) (pair? r)) (cons 'seq (cdr r)))
      ((and (eq? h 'define-values) (pair? r)) (cons 'seq (cdr r)))
      ((and (eq? h 'define) (pair? r))
       (if (pair? (car r)) '(skip) (cons 'seq (cdr r))))   ; (define (f) ..) runs nothing
      ((eq? h 'cond) (cons 'seq (cro--clauses r)))
      ((and (eq? h 'case) (pair? r))
       (cons 'seq (cons (car r) (append-map (lambda (cl) (if (list? cl) (cdr cl) '())) (cdr r)))))
      ((and (eq? h 'guard) (pair? r) (pair? (car r)))
       (cons 'seq (append (cdr r) (cro--clauses (cdar r)))))
      ((and (eq? h 'do) (pair? r) (list? (car r)))
       (cons 'seq (append (append-map (lambda (b) (if (list? b) (cdr b) '())) (car r))
                          (if (and (pair? (cdr r)) (list? (cadr r))) (cadr r) '())
                          (if (pair? (cdr r)) (cddr r) '()))))
      ((memq h '(if and or when unless begin assert the-environment declare-structure vlet bc*))
       (cons 'seq r))
      ((and (symbol? h) (memq h cro--thunk-runners)) (cons 'runner r))
      ((symbol? h) (cons 'app (cons h r)))
      (#t (cons 'app (cons #f e))))))

;;; The recording heads E calls when it is EVALUATED (not inside a lambda it
;;; builds, not inside quoted data), in order of appearance.
(define (cro--recording-heads e)
  (if (not (pair? e))
      '()
      (let ((p (cro--parts e)))
        (case (car p)
          ((skip) '())
          ((seq) (append-map cro--recording-heads (cdr p)))
          ((unordered) (append (append-map cro--recording-heads (cadr p))
                               (append-map cro--recording-heads (cddr p))))
          ((runner) (append-map (lambda (a)
                                  (if (and (pair? a) (memq (car a) '(lambda named-lambda)))
                                      (append-map cro--recording-heads
                                                  (if (eq? (car a) 'lambda) (cddr a) (cddr a)))
                                      (cro--recording-heads a)))
                                (cdr p)))
          (else (let ((h (cadr p)))
                  (append (if (and h (or (memq h cro--tactics) (cro--bang? h))) (list h) '())
                          (append-map cro--recording-heads (cddr p)))))))))

(define (cro--records? e) (pair? (cro--recording-heads e)))

;;; Findings in the expression X of the top-level form NAME, consed onto ACC.
;;; A finding is (NAME HEAD (RECORDING-HEAD ...)): HEAD is `let' / `letrec' /
;;; `fluid-let' for unordered inits, else the head of the application.
(define (cro--finding name head exprs acc)
  (let ((recs (filter cro--records? exprs)))
    (if (and (pair? recs) (pair? (cdr recs)))
        (cons (list name head (append-map cro--recording-heads recs)) acc)
        acc)))

(define (cro--walk x name acc)
  (if (not (pair? x))
      acc
      (let ((p (cro--parts x)))
        (case (car p)
          ((skip)
           ;; a lambda's BODY is code: walk it on its own
           (if (and (memq (car x) '(lambda named-lambda)) (pair? (cdr x)))
               (cro--walk-list (cddr x) name acc)
               (if (and (eq? (car x) 'define) (pair? (cdr x)) (pair? (cadr x)))
                   (cro--walk-list (cddr x) name acc)
                   acc)))
          ((seq runner) (cro--walk-list (cdr p) name acc))
          ((unordered)
           (cro--walk-list (cddr p) name
                           (cro--walk-list (cadr p) name (cro--finding name (car x) (cadr p) acc))))
          (else
           (let ((parts (if (cadr p) (cddr p) (cddr p))))
             (cro--walk-list parts name
                             (cro--finding name (or (cadr p) '<application>) parts acc))))))))

(define (cro--walk-list l name acc)
  (if (pair? l) (cro--walk-list (cdr l) name (cro--walk (car l) name acc)) acc))

(define (recording-order-forms forms)
  (reverse
   (fold-left (lambda (acc f)
                (if (pair? f) (cro--walk f (cfl--form-name f) acc) acc))
              '() forms)))

;;; for the suite: the findings of a TEXT, as (form-name head (recording-head ...))
(define (recording-order-lint-text text)
  (recording-order-forms (cfl--read-forms text)))

(define (recording-order-lint-forms! file forms)
  (let ((hits (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler (lambda (e) (k '()))
                    (lambda () (recording-order-forms forms)))))))
    (if (pair? hits)
        (set! *recording-order-findings* (cons (cons file hits) *recording-order-findings*)))
    ;; PER-FILE LINES ONLY FOR A PROBE.  The backlog on the day the lint was written
    ;; was 148 findings in 68 proof files; printed per file at every load it would
    ;; bury the log, so a load prints the roll-up alone (`report-case-fold-defines')
    ;; and the per-file lines appear for a file a probe ships (label "<dir>__<file>")
    ;; or loads by a wrapper (a label outside theorem-library/ and calculus/).
    (when (and (pair? hits)
               (or (not (cfl--proof-file? file)) (string-search-forward "__" file 0)))
      (display ";VNB warning: recording-order lint: ") (display file)
      (display " evaluates two proof steps in an UNSPECIFIED order:\n")
      (for-each (lambda (h)
                  (display ";              in ") (display (car h)) (display ": (")
                  (display (cadr h)) (display " ...) holds ")
                  (for-each (lambda (s) (display s) (display " ")) (caddr h))
                  (newline))
                hits)
      (display ";              The inits of a `let' and the arguments of a call run in an order the compiler\n")
      (display ";              and the interpreter do not agree on: sequence them with `let*' or `begin'.\n"))
    hits))

(define (recording-order-lint! file path)
  (let ((forms (and (file-exists? path)
                    (call-with-current-continuation
                      (lambda (k)
                        (with-exception-handler (lambda (e) (k #f))
                          (lambda () (cfl--read-forms (cfd--slurp path)))))))))
    (if forms (recording-order-lint-forms! file forms) '())))

(define (cfl--proof-file? file)
  (and (string? file)
       (or (string-prefix? "theorem-library/" file) (string-prefix? "calculus/" file))))

(define (case-fold-define-lint! file path)
  (if (cfl--proof-file? file) (case-fold-local-lint! file path))
  (let ((cols
         (and (file-exists? path)
              (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler (lambda (e) (k '()))
                    (lambda ()
                      (let ((text (cfd--slurp path)))
                        (if (cfd--maybe-mixed? text)
                            (cfd--collisions (cfd--read-names text))
                            '())))))))))
    (when (pair? cols)
      (set! *case-fold-define-collisions*
            (cons (cons file cols) *case-fold-define-collisions*))
      (display ";VNB warning: case-fold lint: ") (display file)
      (display " has two top-level defines MIT Scheme reads as ONE name:\n")
      (for-each (lambda (c)
                  (display ";              ")
                  (for-each (lambda (s) (display s) (display "  ")) (cdr c))
                  (display "->  ") (display (car c)) (newline))
                cols)
      (display ";              The later definition silently REPLACES the earlier one.\n"))
    (if (pair? cols) cols '())))

(define (report-case-fold-defines)
  (if (null? *case-fold-define-collisions*)
      (display ";; case-fold lint: no file defines two names that fold together.\n")
      (begin
        (display ";VNB warning: case-fold lint: ")
        (display (length *case-fold-define-collisions*))
        (display " file(s) define two names that fold together:\n")
        (for-each (lambda (e)
                    (display ";              ") (display (car e)) (display ": ")
                    (for-each (lambda (c) (write (cdr c)) (display " ")) (cdr e))
                    (newline))
                  (reverse *case-fold-define-collisions*))))
  (if (null? *case-fold-local-collisions*)
      (display ";; case-fold lint: no proof file binds two local names that fold together.\n")
      (begin
        (display ";VNB warning: case-fold lint: ")
        (display (length *case-fold-local-collisions*))
        (display " proof file(s) bind two LOCAL names that fold together:\n")
        (for-each (lambda (e)
                    (display ";              ") (display (car e)) (display ": ")
                    (for-each (lambda (h) (display (car h)) (display " ") (write (map cdr (cdr h)))
                                (display " "))
                              (cdr e))
                    (newline))
                  (reverse *case-fold-local-collisions*))))
  ;; KIT-5: the recording-order lint's roll-up
  (if (null? *recording-order-findings*)
      (display ";; recording-order lint: no proof file evaluates two proof steps in an unspecified order.\n")
      (begin
        (display ";VNB warning: recording-order lint: ")
        (display (length *recording-order-findings*))
        (display " proof file(s) evaluate two proof steps in an unspecified order\n")
        (display ";              (backlog; *recording-order-findings* lists them)\n")))
  *case-fold-define-collisions*)
