;;; band-dump.scm -- dump what a saved band holds, one deterministic line per name.
;;;
;;; NOT loaded by load.scm.  It runs AGAINST a band, compiled or not (it uses no
;;; top-level macro; compiled it is about ten times faster):
;;;
;;;   BC_DUMP_PREFIX=/home/ubuntu/probes/band-compare/a \
;;;     mit-scheme --heap 200000 --band /home/ubuntu/prover/vnb.band --quiet \
;;;                --load /home/ubuntu/prover/band-dump.scm < /dev/null
;;;
;;; and writes three files (vnb-band-compare ships this file, runs it on two bands,
;;; and diffs the results; docs/band-compare-2026-09-23.md is the description):
;;;
;;;   PREFIX.content  -- what the band SAYS: per name the statement, the macete and
;;;                      the -rev companion, provenance, source (relative to the
;;;                      prover root, extension dropped), the bill (immediate
;;;                      citations and the debt set, sorted), oracles, the proof
;;;                      script with counter-minted names relabelled, the per-name
;;;                      entries of the warrant / topic / alias / gloss / anchor /
;;;                      rests-on / certification tables and list memberships; then
;;;                      the non-theorem registries (functoids, operators, structures,
;;;                      binder owners, the theory record's axioms / theorems / constants,
;;;                      ...), the global name lists, the recorded load outcome and
;;;                      the band-only gates re-run.  Two bands of the same tree must
;;;                      give byte-identical files: that is the pass.
;;;   PREFIX.history  -- what depends on the ORDER things were loaded in, not on the
;;;                      tree: the eigenvariable counter at each proof's start, the raw
;;;                      (unrelabelled) script, the mint record, the live trace's
;;;                      length, the
;;;                      extension of the file each theorem was loaded from (.scm or
;;;                      .com), and session counters (*fresh-counter*, inferences
;;;                      checked, rules applied).  Diffed and reported, never a fail.
;;;   PREFIX.raw      -- NAME <TAB> FIELD <TAB> canonical text, for the fields hashed
;;;                      in .content, so a differing hash can be read.
;;;
;;; Determinism.  Every hash table is read through a SORTED key list; every value is
;;; printed by `bc-canon', which never prints an object's hash number or address: an
;;; uninterned symbol (a gensym: the schema variables of a macete) is printed as %gN,
;;; N its order of first occurrence in the value; a procedure is printed by what can
;;; be read of it (compiled entry file and index, the names and values of its closure
;;; frames up to the top level); a record by its type name and fields; anything else
;;; by its kind only.  Hashes are MD5 of that text, first 16 hex digits.
;;;
;;; Every helper is prefixed `bc-' (clobber-guard: no tactic or constant is rebound).

;; The environment the library was loaded into (the REPL's, when a band is restored
;; with --load): `the-environment' is not allowed in compiled code, and this file is
;; compiled before it runs (vnb-band-compare compiles a copy on the worker; the
;; interpreted file is about ten times slower on the proof scripts).
(define bc-env (nearest-repl/environment))

(define (bc-bound? sym) (environment-bound? bc-env sym))
(define (bc-val sym default)
  (if (and (bc-bound? sym) (environment-assigned? bc-env sym))
      (environment-lookup bc-env sym)
      default))

(define (bc-try thunk fail)
  (call-with-current-continuation
   (lambda (k) (with-exception-handler (lambda (e) (k fail)) thunk))))

(define bc-prover-dir
  (let ((d (bc-val '*prover-dir* "/home/ubuntu/prover/")))
    (if (and (> (string-length d) 0)
             (not (char=? (string-ref d (- (string-length d) 1)) #\/)))
        (string-append d "/")
        d)))

;;; ---------------------------------------------------------------- hashing
(define (bc-hex-byte b)
  (let ((s (number->string b 16)))
    (if (< b 16) (string-append "0" s) s)))

(define (bc-md5 str)
  (let* ((bv (md5-string str)) (n (bytevector-length bv)))
    (let loop ((i 0) (acc '()))
      (if (= i 8)                       ; 16 hex digits
          (apply string-append (reverse acc))
          (loop (+ i 1) (cons (bc-hex-byte (bytevector-u8-ref bv i)) acc))))))

;;; ---------------------------------------------------------------- the printer
;;; (bc-canon OBJ DEPTH [RELABEL?]) -> string.  DEPTH bounds how far procedures are
;;; opened (a closure's frame values are printed at DEPTH-1; at 0 only its kind and
;;; code are).  RELABEL? additionally renames every interned symbol ending in
;;; _<digits> (a name minted from the global eigenvariable counter) to BASE_#k,
;;; k its order of first occurrence: injective, so the structure survives, but the
;;; absolute counter value -- which depends on how much was proved before -- does not.

(define bc-node-budget 400000)

(define (bc-path-relative s)
  (let ((n (string-length bc-prover-dir)))
    (if (and (>= (string-length s) n) (string=? (substring s 0 n) bc-prover-dir))
        (substring s n (string-length s))
        s)))

(define (bc-counter-suffix-base str)
  ;; strip EVERY trailing _<digits> group: a name minted from an already minted name
  ;; carries two (x_6454_2, seen in road-laws-2.scm and compact-image.scm).
  ;; "b_6420" -> "b" ; "rhpy__6422" -> "rhpy_" ; "x_6454_2" -> "x" ; otherwise #f
  (define (strip-one s)
    (let loop ((i (- (string-length s) 1)))
      (cond ((< i 0) #f)
            ((char-numeric? (string-ref s i)) (loop (- i 1)))
            ((and (char=? (string-ref s i) #\_)
                  (< i (- (string-length s) 1))
                  (> i 0))
             (substring s 0 i))
            (else #f))))
  (let ((once (strip-one str)))
    (and once
         (let loop ((s once))
           (let ((again (strip-one s)))
             (if again (loop again) s))))))

(define (bc-canon obj depth #!optional relabel?)
  (let ((port (open-output-string))
        (gens #f)                       ; made on the first gensym / minted name
        (ngen 0)
        (mints #f)
        (nmint 0)
        (budget bc-node-budget)
        (relabel? (and (not (default-object? relabel?)) relabel?)))
    (define (out s) (write-string s port))
    (define (sym x)
      (cond ((uninterned-symbol? x)
             (if (not gens) (set! gens (make-strong-eqv-hash-table)))
             (let ((k (hash-table-ref/default gens x #f)))
               (if k
                   (out (string-append "%g" (number->string k)))
                   (begin (set! ngen (+ ngen 1))
                          (hash-table-set! gens x ngen)
                          (out (string-append "%g" (number->string ngen)))))))
            ((and relabel? (bc-counter-suffix-base (symbol->string x)))
             => (lambda (base)
                  (if (not mints) (set! mints (make-strong-eqv-hash-table)))
                  (let ((k (hash-table-ref/default mints x #f)))
                    (if k
                        (out (string-append base "_#" (number->string k)))
                        (begin (set! nmint (+ nmint 1))
                               (hash-table-set! mints x nmint)
                               (out (string-append base "_#" (number->string nmint))))))))
            (else (write-string (symbol->string x) port))))
    (define (walk x d)
      (set! budget (- budget 1))
      (cond
        ((< budget 0) (out "#[trunc]"))
        ((symbol? x) (sym x))
        ((null? x) (out "()"))
        ((pair? x)
         (out "(")
         (walk (car x) d)
         (let loop ((r (cdr x)))
           (cond ((null? r) (out ")"))
                 ((pair? r) (out " ") (walk (car r) d) (loop (cdr r)))
                 (else (out " . ") (walk r d) (out ")")))))
        ((number? x) (out (number->string x)))
        ((string? x) (write x port))
        ((char? x) (write x port))
        ((boolean? x) (out (if x "#t" "#f")))
        ((default-object? x) (out "#!default"))
        ((vector? x)
         (out "#(")
         (let loop ((i 0))
           (when (< i (vector-length x))
             (if (> i 0) (out " "))
             (walk (vector-ref x i) d)
             (loop (+ i 1))))
         (out ")"))
        ((bytevector? x) (write x port))
        ((pathname? x) (write (bc-path-relative (->namestring x)) port))
        ((hash-table? x)
         (out "#[hash-table")
         (for-each (lambda (s) (out " ") (out s))
                   (sort (map (lambda (kv)
                                (string-append (bc-canon (car kv) (max 0 (- d 1)))
                                               "=>"
                                               (bc-canon (cdr kv) (max 0 (- d 1)))))
                              (hash-table->alist x))
                         string<?))
         (out "]"))
        ((procedure? x) (proc x d))
        ((environment? x) (out "#[environment]"))
        ((record? x)
         (let ((rtd (bc-try (lambda () (record-type-descriptor x)) #f)))
           (if (not rtd)
               (out "#[record]")
               (begin
                 (out "#[record ")
                 (out (bc-try (lambda () (let ((n (record-type-name rtd)))
                                           (if (symbol? n) (symbol->string n)
                                               (with-output-to-string (lambda () (display n))))))
                              "?"))
                 (for-each
                  (lambda (f)
                    (out " ")
                    (let ((v (bc-try (lambda () ((record-accessor rtd f) x)) 'bc--unreadable)))
                      (walk v d)))
                  (bc-try (lambda () (vector->list (record-type-field-names rtd)))
                          (bc-try (lambda () (record-type-field-names rtd)) '())))
                 (out "]")))))
        ((cell? x) (out "#[cell ") (walk (cell-contents x) d) (out "]"))
        ((weak-pair? x) (out "#[weak-pair]"))
        ((promise? x) (out "#[promise]"))
        (else (out "#[other]"))))
    (define (proc p d)
      (cond
        ((primitive-procedure? p)
         (out "#[primitive ") (write (primitive-procedure-name p) port) (out "]"))
        (else
         (out (if (compiled-procedure? p) "#[compiled" "#[compound"))
         (when (compiled-procedure? p)
           (bc-try (lambda ()
                     (call-with-values
                         (lambda () (compiled-entry/filename-and-index p))
                       (lambda (file index . rest)
                         (out " ")
                         (write (if file (bc-path-relative (->namestring file)) #f) port)
                         (out " ")
                         (write index port))))
                   #f))
         (when (> d 0)
           (for-each (lambda (env) (out " ") (frame env (- d 1)))
                     (bc-frames p)))
         (out "]"))))
    (define (frame env d)
      (out "{")
      (write (bc-try (lambda () (environment-procedure-name env)) '?) port)
      (for-each
       (lambda (v)
         (out " ") (write v port) (out "=")
         (if (and (environment-bound? env v) (environment-assigned? env v))
             (walk (bc-try (lambda () (environment-lookup env v)) 'bc--unreadable) d)
             (out "#[unassigned]")))
       (sort (bc-try (lambda () (environment-bound-names env)) '())
             (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
      (out "}"))
    (walk obj depth)
    (get-output-string port)))

;;; The closure frames of P, innermost first, stopping at the first top-level
;;; environment (the global one, or any frame with more than 40 names: a file's
;;; top level, whose contents are the library, not the closure).
(define (bc-frames p)
  (let ((env0 (bc-try (lambda () (procedure-environment p)) #f)))
    (let loop ((env env0) (acc '()) (k 0))
      (if (or (not env)
              (eq? env system-global-environment)
              (> k 8)
              (let ((names (bc-try (lambda () (environment-bound-names env)) #f)))
                (or (not names) (> (length names) 40))))
          (reverse acc)
          (loop (bc-try (lambda () (and (environment-has-parent? env)
                                        (environment-parent env)))
                        #f)
                (cons env acc)
                (+ k 1))))))

;;; ---------------------------------------------------------------- table access
(define (bc-ref table key)
  (if (hash-table? table) (hash-table-ref/default table key #f) #f))

(define (bc-table sym)
  (let ((t (bc-val sym #f))) (and (hash-table? t) t)))

(define (bc-name<? a b)
  (string<? (bc-canon a 0) (bc-canon b 0)))

(define (bc-sort-names lst)
  ;; decorate once: the printed form is the sort key
  (map cdr (sort (map (lambda (x) (cons (bc-canon x 0) x)) lst)
                 (lambda (a b) (string<? (car a) (car b))))))

(define (bc-uniq-sorted lst)
  (let loop ((l lst) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? acc) (equal? (car acc) (car l))) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define (bc-list-field lst)
  ;; a list of names, as a sorted, deduplicated set: a,b,c ; {} when empty.  No
  ;; spaces, so a content line splits on blanks into key=value fields.
  (cond ((null? lst) "{}")
        ((list? lst)
         (bc-join-with "," (map (lambda (x) (bc-canon x 0))
                                (bc-uniq-sorted (bc-sort-names lst)))))
        (else (bc-canon lst 0))))

;;; ---------------------------------------------------------------- output
(define bc-prefix
  (or (get-environment-variable "BC_DUMP_PREFIX") "/home/ubuntu/probes/band-dump"))

(define bc-content-port #f)
(define bc-history-port #f)
(define bc-raw-port #f)

(define (bc-emit port . parts)
  (for-each (lambda (s) (write-string s port)) parts)
  (newline port))

(define (bc-raw! name field text)
  (bc-emit bc-raw-port (bc-canon name 0) "\t" field "\t" text))

;; Hash a value, recording its canonical text in .raw under NAME/FIELD.
(define (bc-hash-field name field value depth #!optional relabel?)
  (if (not value)
      "-"
      (let ((text (bc-canon value depth (and (not (default-object? relabel?)) relabel?))))
        (bc-raw! name field text)
        (bc-md5 text))))

;;; ---------------------------------------------------------------- the names
(define bc-theorems   (bc-table '*theorem-table*))
(define bc-macetes    (bc-table '*macete-table*))
(define bc-sources    (bc-table '*theorem-source*))
(define bc-revsrc     (bc-table '*rev-companion-source*))
(define bc-viewsrc    (bc-table '*view-specialized-source*))
(define bc-prov       (bc-table '*provenance*))
(define bc-cites      (bc-table '*proof-citation-graph*))
(define bc-debt       (bc-table '*proof-debt*))
(define bc-oracles    (bc-table '*proof-oracles*))
(define bc-scripts    (bc-table '*proof-script-table*))
(define bc-mints      (bc-table '*proof-mints-table*))
(define bc-trace      (bc-table '*proof-live-trace*))
(define bc-startctr   (bc-table '*proof-start-counter*))
(define bc-warrants   (bc-table '*warrants*))
(define bc-topics     (bc-table '*pss-topics*))
(define bc-aliases    (bc-table '*theorem-aliases*))
(define bc-glosses    (bc-table '*glosses*))
(define bc-anchors    (bc-table '*reference-anchors*))
(define bc-restson    (bc-table '*rests-on-graph*))
(define bc-certs      (bc-table '*certifications*))
(define bc-fpmemo     (bc-table '*lemma-fingerprint-memo*))

(define bc-per-name-tables
  (list bc-theorems bc-macetes bc-prov bc-cites bc-debt bc-oracles bc-scripts
        bc-warrants bc-topics bc-aliases bc-glosses bc-anchors bc-restson bc-certs
        bc-sources))

(define bc-proven-list  (bc-val '*proven-theorem-names* '()))
(define bc-support-list (bc-val '*support-theorem-names* '()))
(define bc-named-only   (bc-val '*named-only-macetes* '()))
(define bc-inert        (bc-val '*inert-macetes* '()))
(define bc-late-no      (bc-val '*named-only-late-declarations* '()))

(define (bc-all-names)
  (let ((seen (make-equal-hash-table)))
    (for-each (lambda (t) (when t (for-each (lambda (k) (hash-table-set! seen k #t))
                                             (hash-table-keys t))))
              bc-per-name-tables)
    (for-each (lambda (k) (hash-table-set! seen k #t))
              (append bc-proven-list bc-support-list))
    (bc-sort-names (hash-table-keys seen))))

(define (bc-rev-name name)
  (and (symbol? name) (string->symbol (string-append (symbol->string name) "-rev"))))

;; NAME is a -rev companion folded into its forward's line
(define (bc-folded-rev? name present)
  (let ((fwd (bc-ref bc-revsrc name)))
    (and fwd (hash-table-ref/default present fwd #f)
         (eq? (bc-rev-name fwd) name))))

(define (bc-source-field name)
  (let ((src (bc-ref bc-sources name)))
    (if (not src)
        (values "-" "-")
        (let* ((s (bc-path-relative (if (pathname? src) (->namestring src)
                                        (bc-canon src 0))))
               (n (string-length s))
               (ext (let loop ((i (- n 1)))
                      (cond ((< i 0) "")
                            ((char=? (string-ref s i) #\/) "")
                            ((char=? (string-ref s i) #\.) (substring s (+ i 1) n))
                            (else (loop (- i 1)))))))
          (if (member ext '("scm" "com" "bin"))
              (values (substring s 0 (- n (+ 1 (string-length ext)))) ext)
              (values s (if (string-null? ext) "none" ext)))))))

(define (bc-set-of lst)
  (let ((t (make-equal-hash-table)))
    (for-each (lambda (x) (hash-table-set! t x #t)) lst)
    t))
(define bc-proven-set (bc-set-of bc-proven-list))
(define bc-support-set (bc-set-of bc-support-list))

(define (bc-flags name)
  (let ((fl (append (if (hash-table-ref/default bc-proven-set name #f) '("proven") '())
                    (if (hash-table-ref/default bc-support-set name #f) '("pss") '())
                    (if (assq name bc-named-only) '("named-only") '())
                    (if (assq name bc-inert) '("inert") '())
                    (if (memq name bc-late-no) '("late-named-only") '()))))
    (if (null? fl) "-"
        (let loop ((l (cdr fl)) (s (car fl)))
          (if (null? l) s (loop (cdr l) (string-append s "," (car l))))))))

(define (bc-opt-list table name)
  (let ((v (bc-ref table name))) (if v (bc-list-field v) "-")))

;; The content fields of one name, as a list of "key=value" strings.
(define (bc-name-fields name)
  (call-with-values
      (lambda () (bc-source-field name))
    (lambda (src ext)
      (list
       (string-append "stmt=" (bc-hash-field name "stmt" (bc-ref bc-theorems name) 0))
       (string-append "mac=" (bc-hash-field name "mac" (bc-ref bc-macetes name) 3))
       (string-append "prov=" (let ((p (bc-ref bc-prov name))) (if p (bc-canon p 0) "-")))
       (string-append "src=" src)
       (string-append "vsrc=" (let ((v (bc-ref bc-viewsrc name))) (if v (bc-canon v 0) "-")))
       (string-append "cites=" (bc-opt-list bc-cites name))
       (string-append "debt=" (bc-opt-list bc-debt name))
       (string-append "oracles=" (bc-opt-list bc-oracles name))
       (string-append "script=" (bc-hash-field name "script" (bc-ref bc-scripts name) 0 #t))
       (string-append "warrant=" (bc-hash-field name "warrant" (bc-ref bc-warrants name) 0))
       (string-append "topic=" (let ((v (bc-ref bc-topics name))) (if v (bc-canon v 0) "-")))
       (string-append "alias=" (bc-hash-field name "alias" (bc-ref bc-aliases name) 0))
       (string-append "gloss=" (bc-hash-field name "gloss" (bc-ref bc-glosses name) 0))
       (string-append "anchor=" (bc-hash-field name "anchor" (bc-ref bc-anchors name) 0))
       (string-append "restson=" (bc-opt-list bc-restson name))
       (string-append "cert=" (let ((v (bc-ref bc-certs name))) (if v (bc-canon v 0) "-")))
       (string-append "flags=" (bc-flags name))))))

(define (bc-join-with sep strs)
  ;; one string-append: a loop of pairwise appends is quadratic (13 s on 2700 names)
  (if (null? strs) ""
      (apply string-append
             (car strs)
             (let loop ((l (cdr strs)) (acc '()))
               (if (null? l) (reverse acc) (loop (cdr l) (cons (car l) (cons sep acc))))))))

(define (bc-join strs) (bc-join-with " " strs))

(define (bc-dump-names!)
  (let* ((names (bc-all-names))
         (present (make-equal-hash-table)))
    (for-each (lambda (n) (hash-table-set! present n #t)) names)
    (bc-emit bc-content-port "= names " (number->string (length names)))
    (bc-emit bc-history-port "= names")
    (for-each
     (lambda (name)
       (unless (bc-folded-rev? name present)
         (let* ((rev (bc-rev-name name))
                (rev-folded (and rev (hash-table-ref/default present rev #f)
                                 (bc-folded-rev? rev present)))
                (revcol (if rev-folded
                            (string-append "rev=" (bc-md5 (bc-join (bc-name-fields rev))))
                            "rev=-"))
                (fields (bc-name-fields name)))
           (bc-emit bc-content-port "N " (bc-canon name 0) " "
                    (bc-join (append (list (car fields) (cadr fields) revcol)
                                     (cddr fields))))
           ;; history: order-of-load facts
           (call-with-values
               (lambda () (bc-source-field name))
             (lambda (src ext)
               (bc-emit bc-history-port "H " (bc-canon name 0)
                        " ext=" ext
                        " start=" (let ((v (bc-ref bc-startctr name))) (if v (bc-canon v 0) "-"))
                        " script-raw=" (let ((v (bc-ref bc-scripts name)))
                                         (if v (bc-md5 (bc-canon v 0)) "-"))
                        " mints=" (let ((v (bc-ref bc-mints name)))
                                    (if v (bc-md5 (bc-canon v 0)) "-"))
                        ;; the live trace holds every step's goal and context: printing
                        ;; it costs ~80 ms a proof, so only its length is recorded
                        " trace-steps=" (let ((v (bc-ref bc-trace name)))
                                          (if (list? v) (number->string (length v)) "-"))
                        " fpmemo=" (if (bc-ref bc-fpmemo name) "y" "-")))))))
     names)))

;;; ---------------------------------------------------------------- other registries
;;; Tables keyed by something other than a theorem name: definitions, structures,
;;; views, notation.  One line per key: T TABLE KEY HASH.
(define bc-registry-tables
  '(*functoid-registry* *operators* *constant-registry* *installed-binder-names*
    *structure-table* *structure-decl-table* *accessor-index* *ambiguous-accessors*
    *structure-instances* *view-as-table* *definitional-structure-table*
    *hom-overrides* *functor-projections* *functor-info* *functor-obligations*
    *books* *notation-profiles* *prep-methods* *accessor-display*))

(define (bc-keyed-line label key value)
  (let ((text (bc-canon value 1)))
    (bc-emit bc-raw-port label ":" (bc-canon key 0) "\tvalue\t" text)
    (bc-emit bc-content-port "T " label " " (bc-canon key 0) " " (bc-md5 text))))

;;; The one theory record (*current-theory*): its axiom list, theorem and constant
;;; tables and definition list, one line per entry, keyed by the entry's name.
(define (bc-dump-theory!)
  (let ((th (bc-val '*current-theory* #f)))
    (if (not (and th (bc-bound? 'theory-axioms)))
        (bc-emit bc-content-port "T theory absent")
        (let ((get (lambda (acc) (bc-try (lambda () ((environment-lookup bc-env acc) th)) #f))))
          (for-each
           (lambda (p)
             (let ((label (car p)) (v (get (cdr p))))
               (cond
                 ((hash-table? v)
                  (bc-emit bc-content-port "T " label " count " (number->string (hash-table-size v)))
                  (for-each (lambda (k) (bc-keyed-line label k (hash-table-ref/default v k #f)))
                            (bc-sort-names (hash-table-keys v))))
                 ((list? v)
                  (bc-emit bc-content-port "T " label " count " (number->string (length v)))
                  ;; entries keyed by their car when they have one, sorted by printed key
                  ;; then by printed value (a name may occur twice)
                  (for-each (lambda (kv) (bc-emit bc-content-port (cdr kv)))
                            (sort (map (lambda (e)
                                         (let* ((key (if (pair? e) (car e) e))
                                                (text (bc-canon e 1))
                                                (line (string-append "T " label " " (bc-canon key 0)
                                                                     " " (bc-md5 text))))
                                           (bc-emit bc-raw-port label ":" (bc-canon key 0) "\tvalue\t" text)
                                           (cons line line)))
                                       v)
                                  (lambda (a b) (string<? (car a) (car b))))))
                 (else (bc-emit bc-content-port "T " label " " (bc-canon v 0))))))
           '(("theory-axioms" . theory-axioms)
             ("theory-theorems" . theory-theorems)
             ("theory-constants" . theory-constants)
             ("theory-definitions" . theory-definitions)))))))

(define (bc-dump-registries!)
  (for-each
   (lambda (tsym)
     (let ((t (bc-table tsym)))
       (if (not t)
           (bc-emit bc-content-port "T " (symbol->string tsym) " absent")
           (let ((keys (bc-sort-names (hash-table-keys t))))
             (bc-emit bc-content-port "T " (symbol->string tsym) " count "
                      (number->string (length keys)))
             (for-each
              (lambda (k)
                (let ((text (bc-canon (hash-table-ref/default t k #f) 1)))
                  (bc-emit bc-raw-port (symbol->string tsym) ":" (bc-canon k 0) "\tvalue\t" text)
                  (bc-emit bc-content-port "T " (symbol->string tsym) " "
                           (bc-canon k 0) " " (bc-md5 text))))
              keys)))))
   bc-registry-tables))

;;; ---------------------------------------------------------------- lists
(define (bc-set-line label lst)
  (let ((printed (if (list? lst)
                     (sort (map (lambda (x) (bc-canon x 1)) lst) string<?)
                     (list (bc-canon lst 1)))))
    (bc-emit bc-raw-port label "\tlist\t" (bc-join printed))
    (bc-emit bc-content-port "L " label " count "
             (number->string (length printed)) " "
             (bc-md5 (bc-join printed)))))

(define (bc-dump-lists!)
  (bc-set-line "*proven-theorem-names*" bc-proven-list)
  (bc-set-line "*support-theorem-names*" bc-support-list)
  (bc-set-line "*named-only-macetes*" bc-named-only)
  (bc-set-line "*inert-macetes*" bc-inert)
  (bc-set-line "*named-only-late-declarations*" bc-late-no)
  (bc-set-line "*install-intentional-redefinitions*"
               (bc-val '*install-intentional-redefinitions* '()))
  (bc-set-line "*install-validation-failures*" (bc-val '*install-validation-failures* '()))
  (bc-set-line "*case-fold-define-collisions*" (bc-val '*case-fold-define-collisions* '()))
  (bc-set-line "*page-audit-results*" (bc-val '*page-audit-results* '()))
  ;; the load list is ORDERED: hash it in order
  (let ((files (bc-val '*vnb-files* '())))
    (bc-emit bc-raw-port "*vnb-files*\tlist\t" (bc-canon files 0))
    (bc-emit bc-content-port "L *vnb-files* ordered count "
             (number->string (if (list? files) (length files) -1)) " "
             (bc-md5 (bc-canon files 0)))))

;;; ---------------------------------------------------------------- load outcome, gates
(define (bc-count-line label value)
  (bc-emit bc-content-port "C " label " " value))

(define (bc-gate! label sym)
  ;; re-run a band-only audit; its result as a sorted set
  (if (not (bc-bound? sym))
      (bc-emit bc-content-port "G " label " absent")
      (let ((r (bc-try (lambda () ((environment-lookup bc-env sym))) 'bc--error)))
        (if (eq? r 'bc--error)
            (bc-emit bc-content-port "G " label " error")
            (let ((printed (if (list? r)
                               (sort (map (lambda (e)
                                            (bc-canon (if (and (list? e) (every symbol? e))
                                                          (bc-sort-names e)
                                                          e)
                                                      0))
                                          r)
                                     string<?)
                               (list (bc-canon r 0)))))
              (bc-emit bc-raw-port "gate:" label "\tresult\t" (bc-join printed))
              (bc-emit bc-content-port "G " label " "
                       (if (list? r) (number->string (length r)) "value") " "
                       (bc-md5 (bc-join printed))))))))

(define (bc-dump-outcome!)
  (bc-count-line "theorems" (number->string (hash-table-size bc-theorems)))
  (bc-count-line "macetes" (number->string (hash-table-size bc-macetes)))
  (bc-count-line "proofs (qed, *proof-script-table*)"
                 (number->string (if bc-scripts (hash-table-size bc-scripts) -1)))
  (bc-count-line "proven names" (number->string (length bc-proven-list)))
  (bc-count-line "bills (*proof-debt*)" (number->string (hash-table-size bc-debt)))
  (bc-count-line "modulo 0 (empty bill)"
                 (number->string (length (filter (lambda (kv) (null? (cdr kv)))
                                                 (hash-table->alist bc-debt)))))
  (bc-count-line "pss" (number->string (length bc-support-list)))
  (bc-count-line "rev companions" (number->string (hash-table-size bc-revsrc)))
  (bc-count-line "view companions" (number->string (if bc-viewsrc (hash-table-size bc-viewsrc) -1)))
  (bc-count-line "theorems without source"
                 (number->string (length (filter (lambda (k) (not (bc-ref bc-sources k)))
                                                 (hash-table-keys bc-theorems)))))
  (bc-count-line "strict marker *vnb-band-strict?*"
                 (if (bc-bound? '*vnb-band-strict?*)
                     (bc-canon (bc-val '*vnb-band-strict?* 'unassigned) 0)
                     "absent"))
  (bc-count-line "*vnb-band-file-hashes*"
                 (let ((h (bc-val '*vnb-band-file-hashes* #f)))
                   (cond ((not (bc-bound? '*vnb-band-file-hashes*)) "absent")
                         (else (bc-md5 (bc-canon (if (hash-table? h)
                                                     (sort (map (lambda (kv) (bc-canon kv 0))
                                                                (hash-table->alist h))
                                                           string<?)
                                                     h)
                                                 0))))))
  (bc-count-line "*vnb-band-files*"
                 (if (bc-bound? '*vnb-band-files*)
                     (bc-md5 (bc-canon (bc-val '*vnb-band-files* 'unassigned) 0))
                     "absent"))
  (bc-count-line "*install-duplicates*" (bc-list-field (bc-val '*install-duplicates* '())))
  (bc-count-line "*vnb-qed-failures*" (bc-canon (reverse (bc-val '*vnb-qed-failures* '())) 0))
  (bc-count-line "*vnb-qed-holes*" (bc-canon (reverse (bc-val '*vnb-qed-holes* '())) 0))
  (bc-count-line "*vnb-load-failures*" (bc-canon (reverse (bc-val '*vnb-load-failures* '())) 0))
  (bc-count-line "*vnb-keep-going?*" (bc-canon (bc-val '*vnb-keep-going?* 'absent) 0))
  (bc-count-line "rule-checker refusals"
                 (if (bc-bound? 'dg-check-refusal-count)
                     (number->string ((environment-lookup bc-env 'dg-check-refusal-count)))
                     "absent"))
  (bc-count-line "*dg-check-inferences?*" (bc-canon (bc-val '*dg-check-inferences?* 'absent) 0))
  (bc-count-line "*dg-trusted-rule-heads*" (bc-canon (bc-val '*dg-trusted-rule-heads* 'absent) 0))
  (bc-count-line "*vnb-loading*" (bc-canon (bc-val '*vnb-loading* 'absent) 0))
  (bc-count-line "*ps*" (if (bc-val '*ps* #f) "live" "#f"))
  ;; the gates of load.scm's end block that read only the band (kernel-callers-audit
  ;; reads the SOURCE files on disk and is left out: it is a function of the tree
  ;; the worker holds, not of the band)
  (for-each (lambda (p) (bc-gate! (car p) (cdr p)))
            '(("asserted-duplicate-audit" . asserted-duplicate-audit)
              ("proven-duplicate-audit" . proven-duplicate-audit)
              ("connective-arity-audit" . connective-arity-audit)
              ("free-variable-audit" . free-variable-audit)
              ("sethood-audit" . sethood-audit)
              ("case-fold-audit" . case-fold-audit)
              ("install-grading" . install-validation-failures)
              ("proof-cycle-check" . proof-cycle-check)
              ("rests-on-unknown-deps" . rests-on-unknown-deps)
              ("pss-topics" . pss-names-without-topic)
              ("reference-glosses" . reference-warrants-without-gloss)
              ("functoid-binder-audit" . functoid-binder-audit)
              ("constant-binder-audit" . constant-binder-audit)
              ("accessor-index-audit" . accessor-index-audit)
              ("accessor-type-audit" . accessor-type-audit)
              ("structure-satisfiability-audit" . structure-satisfiability-audit)
              ("statement-satisfiability-audit" . statement-satisfiability-audit)
              ("domain-clash-audit" . domain-clash-audit)
              ("functor-obligation-audit" . functor-obligation-audit)
              ("binder-walker-audit" . binder-walker-audit)
              ("proof-warrants-unproven" . proof-warrants-unproven))))

(define (bc-dump-history-globals!)
  (bc-emit bc-history-port "= session")
  (for-each
   (lambda (sym)
     (bc-emit bc-history-port "S " (symbol->string sym) " "
              (if (bc-bound? sym)
                  (let ((v (bc-val sym 'unassigned)))
                    (cond ((number? v) (number->string v))
                          ((list? v) (string-append "count " (number->string (length v))
                                                    " " (bc-md5 (bc-canon v 0))))
                          ((hash-table? v) (string-append "count " (number->string (hash-table-size v))
                                                          " " (bc-md5 (bc-canon v 0))))
                          (else (bc-canon v 0))))
                  "absent")))
   '(*fresh-counter* *dg-checked-count* *rules-applied* *session-log* *vnb-load-times*
     *vnb-stale-com* *vnb-inert-count* *vnb-inert-at-load* *sp-counter-snapshot*
     *install-duplicates*)))

;;; ---------------------------------------------------------------- main
(define (bc-dump!)
  (let ((t0 (runtime)))
    (set! bc-content-port (open-output-file (string-append bc-prefix ".content")))
    (set! bc-history-port (open-output-file (string-append bc-prefix ".history")))
    (set! bc-raw-port (open-output-file (string-append bc-prefix ".raw")))
    (bc-emit bc-content-port "= band-dump 1")
    (bc-emit bc-content-port "= outcome")
    (bc-dump-outcome!)
    (bc-dump-names!)
    (bc-emit bc-content-port "= registries")
    (bc-dump-registries!)
    (bc-dump-theory!)
    (bc-emit bc-content-port "= lists")
    (bc-dump-lists!)
    (bc-dump-history-globals!)
    (bc-emit bc-content-port "= end")
    (bc-emit bc-history-port "= end")
    (close-port bc-content-port)
    (close-port bc-history-port)
    (close-port bc-raw-port)
    (display ";; band-dump: wrote ") (display bc-prefix)
    (display ".{content,history,raw} in ")
    (display (round (- (runtime) t0))) (display " s cpu") (newline)))

(bc-dump!)
(exit 0)
