;;; glossary.scm -- THE ALPHABETICAL GLOSSARY: every name in VNB, in one list.
;;;
;;; Every other reference document is grouped by something -- OPERATORS.md by
;;; class, STRUCTURE-INDEX.md by structure, TACTICS.md by task, THEOREMS.md by
;;; installation order.  A reader who has met a name and wants to know what it
;;; is has to guess which grouping it fell into.  This document has exactly one
;;; ordering, and it is the one nobody has to learn: A to Z.
;;;
;;; WHAT IS IN IT -- the VOCABULARY, i.e. everything with a name that is not a
;;; result:
;;;
;;;   structure    a declared shape        (RING, METRIC-SPACE)
;;;   refinement   a structure declared `same-shape-as' another (COMMUTATIVE-RING)
;;;   instance     a named structure value (ZZ-RING, RR-MS)
;;;   predicate    IS-RING, IS-HOM-GROUP, CONVERGES, ...
;;;   functoid     a def-functoid term constructor (MATMUL, BALL)
;;;   accessor     a structure slot        (CARR, MUL, DIST)
;;;   defined-fn   a def-constant / def-by-recursion constant (SUM, REDUCE)
;;;   operator     a kernel term-former    (UNION, NTH, SEP)
;;;   primitive    a kernel relation notation! declared (=, IN, <=)
;;;   view         a declared view-as bridge
;;;   tactic       a proof command         (di, mac, ass)
;;;
;;; The RESULTS -- theorems, axioms, supports -- are named too, and there are
;;; some 3200 of them; they have their own catalogs (THEOREMS.md alphabetically
;;; by section, BY-OPERATOR.md by the vocabulary they mention, PROOF-DEBT.md by
;;; what they rest on).  Each glossary entry instead LINKS to the results about
;;; its name, which is the question a glossary reader actually has.
;;;
;;; Loads last: it reads the constant registry, the operator table, the functoid
;;; registry, the structure tables, the view table, the theorem table and the
;;; tactic registry, so every one of them must already be populated.

;;; -----------------------------------------------------------------------
;;; The reverse index, built in ONE pass: head -> the results mentioning it.
;;; `operator-index' (interactive.scm) built this inline and then wrote
;;; BY-OPERATOR.md from it; the pass is 3200 formula walks, so it is computed
;;; once here and handed to whoever asks.

(define (operator-usage-index)
  (let ((tbl (make-equal-hash-table)))
    (for-each
      (lambda (n)
        (for-each (lambda (op)
                    (hash-table-set! tbl op
                      (cons n (hash-table-ref/default tbl op '()))))
                  (macete-all-ops (lookup-theorem n))))
      (hash-table-keys *theorem-table*))
    tbl))

;;; -----------------------------------------------------------------------
;;; An entry.  Six fields, all display-ready; `detail' is the kind-specific
;;; line and may be #f.

(define (make-gloss-entry name kind sig reads file detail)
  (list name kind sig reads file detail))

(define (gloss-name   e) (car e))
(define (gloss-kind   e) (cadr e))
(define (gloss-sig    e) (caddr e))     ; "(s, x, y)" or a tactic call form
(define (gloss-reads  e) (cadddr e))    ; notation! english/noun template
(define (gloss-file   e) (list-ref e 4))
(define (gloss-detail e) (list-ref e 5))

(define (gl--sym<? a b) (string<? (symbol->string a) (symbol->string b)))

(define (gl--basename p)
  (if (string? p)
      (let loop ((i (- (string-length p) 1)))
        (cond ((< i 0) p)
              ((char=? (string-ref p i) #\/)
               ;; keep one directory level: structure-library/matrix.scm
               (let loop2 ((j (- i 1)))
                 (cond ((< j 0) (substring p 1 (string-length p)))
                       ((char=? (string-ref p j) #\/)
                        (substring p (+ j 1) (string-length p)))
                       (else (loop2 (- j 1))))))
              (else (loop (- i 1)))))
      #f))

(define (gl--params-string params)
  (if (or (not params) (null? params))
      ""
      (string-append
       "("
       (let loop ((ps params) (acc ""))
         (if (null? ps)
             acc
             (loop (cdr ps)
                   (string-append acc
                                  (if (string=? acc "") "" ", ")
                                  (if (symbol? (car ps))
                                      (symbol->string (car ps))
                                      (expression->string (car ps)))))))
       ")")))

;;; The notation! reading, if one was declared: the `english' template ("$1
;;; plus $2") or the noun ("Euclidean ring").  A procedure-valued english
;;; cannot be shown as a template, so it is reported as such.
(define (gl--reading name)
  (let ((e (operator-ref name)))
    (and e
         (let ((en (operator-english e)) (nn (operator-noun e)))
           (cond ((string? en) en)
                 ((procedure? en) "(computed by a procedure)")
                 ((string? nn)
                  (string-append (or (operator-article e) "")
                                 (if (and (operator-article e)
                                          (not (string=? (operator-article e) "")))
                                     " " "")
                                 nn))
                 (else #f))))))

(define (gl--indef sym)
  (let ((s (symbol->string sym)))
    (string-append (if (memv (char-downcase (string-ref s 0)) '(#\a #\e #\i #\o #\u))
                       "an " "a ")
                   s)))

(define (gl--truncate s n)
  (if (> (string-length s) n)
      (string-append (substring s 0 n) " ...")
      s))

;;; -----------------------------------------------------------------------
;;; The entries, by source.

(define (gl--structure-entries)
  (append
   (map (lambda (s)
          (let* ((sd    (lookup-structure s))
                 (slots (map car (structure-def-slots sd))))
            (make-gloss-entry
             s 'structure "" (gl--reading s)
             (gl--basename (structure-def-source-file sd))
             (string-append "predicate `is-" (string-downcase (symbol->string s))
                            "`; slots: "
                            (gl--truncate
                             (apply string-append
                                    (map (lambda (x)
                                           (string-append (symbol->string x) " "))
                                         slots))
                             90)))))
        (sort (hash-table-keys *structure-table*) gl--sym<?))
   (map (lambda (s)
          (let ((ds (lookup-definitional-structure s)))
            (make-gloss-entry
             s 'refinement "" (gl--reading s)
             (gl--basename (definitional-structure-source-file ds))
             (string-append "predicate `is-" (string-downcase (symbol->string s))
                            "`; same shape as "
                            (symbol->string (definitional-structure-parent ds))))))
        (sort (hash-table-keys *definitional-structure-table*) gl--sym<?))))

;;; Instances are a POST-PASS, not a source: every declared instance (ZZ-RING,
;;; RR-MS) is also registered as a definitional structure, so a separate source
;;; entry would simply be deduped away.  This re-labels the entry it already has
;;; and adds the parent structure to its detail line.
(define (gl--mark-instance e)
  (let* ((n (gloss-name e))
         (s (and (hash-table-ref/default *structure-instances* n #f)
                 (instance-structure n))))
    (if (not s)
        e
        (make-gloss-entry
         n 'instance (gloss-sig e) (gloss-reads e) (gloss-file e)
         (string-append "an instance of " (symbol->string s)
                        (if (gloss-detail e)
                            (string-append "; " (gloss-detail e))
                            ""))))))

(define (gl--view-entries)
  (map (lambda (k)
         (let ((v (lookup-view-as k)))
           (make-gloss-entry
            k 'view "(s)" #f (gl--basename (view-as-source-file v))
            (string-append (gl--indef (view-as-source-struct v))
                           " viewed as "
                           (gl--indef (view-as-target-struct v))))))
       (sort (hash-table-keys *view-as-table*) gl--sym<?)))

;;; A tactic's registry "signature" is the whole call form -- "(sp goal)" -- so
;;; it goes in the DETAIL line, not in the signature slot, which would print the
;;; name twice.
(define (gl--tactic-entries)
  (map (lambda (e)
         (make-gloss-entry (car e) 'tactic "" #f "tactics-help.scm"
                           (string-append "`" (cadr e) "` -- " (tactics--gloss e))))
       (sort (tactics--all-entries) (lambda (a b) (gl--sym<? (car a) (car b))))))

;;; Every head in the constant registry -- the table free-vars / subst-free
;;; consult, and since 2026-08-04 the one register-operator! feeds, so it is
;;; the complete list of applied heads (head-registry-sweep, audit.scm).
;;; The defining / characterizing axioms a def-constant or def-predicate
;;; installed, by name.  (library-definitions) is an alist name -> ((axname . f) ...).
(define (gl--defining-axioms h)
  (let ((e (assq h (library-definitions *library*))))
    (and e (pair? (cdr e)) (map car (cdr e)))))

;;; -----------------------------------------------------------------------
;;; WHAT CHARACTERIZES A NAME.
;;;
;;; A glossary entry that says only "a kernel term-former" is not a glossary
;;; entry: `BIJECTION' is a class constructor whose whole content is the
;;; biconditional `phi in BIJECTION(X,Y) iff phi in FUN(X,Y) and phi is
;;; injective and onto', and that is what a reader looking it up wants to see.
;;;
;;; Not every head is introduced by a def-*, so `library-definitions' answers for
;;; only some of them.  For the rest, take the results that MENTION the head
;;; (the one-pass usage index) and keep those whose NAME contains it --
;;; bijection-membership, bijection-set-iff, bijection-compose -- which is the
;;; library's own naming convention doing the work.  Rank the DEFINING ones
;;; first: `definitional' provenance means the fact was installed as a
;;; conservative definition, so it IS the characterization; then `primitive'
;;; (a kernel axiom); then by length, shortest name first, which puts
;;; `bijection-membership' ahead of `bijection-compose-is-bijection'.
(define (gl--rank-of name)
  (case (provenance-of name)
    ((definitional) 0)
    ((primitive)    1)
    (else           2)))

(define (gl--char-axioms h mentions)
  (let* ((hs   (string-downcase (symbol->string h)))
         (cand (filter (lambda (n)
                         (and (substring? hs (string-downcase (symbol->string n)))
                              ;; a -rev companion says nothing new
                              (not (substring? "-rev" (symbol->string n)))))
                       mentions)))
    (sort cand
          (lambda (a b)
            (let ((ra (gl--rank-of a)) (rb (gl--rank-of b)))
              (cond ((not (= ra rb)) (< ra rb))
                    ((not (= (string-length (symbol->string a))
                             (string-length (symbol->string b))))
                     (< (string-length (symbol->string a))
                        (string-length (symbol->string b))))
                    (else (gl--sym<? a b))))))))

(define (gl--head-entries)
  (map (lambda (h)
         (let* ((op   (operator-ref h))
                ;; The OPERATOR table's kind wins where there is one: the
                ;; registry's is last-writer-wins, and add-definition!
                ;; re-stamps every def-predicate name `defined-fn' after
                ;; def-predicate stamped it `predicate'.
                (kind (or (and op (operator-kind op)) (constant-head? h)))
                (freg (hash-table-ref/default *functoid-registry* h #f))
                (axs  (gl--defining-axioms h)))
           (make-gloss-entry
            h
            kind
            (gl--params-string (cond (freg (car freg))
                                     (op   (operator-params op))
                                     (else '())))
            (gl--reading h)
            (or (and freg (gl--basename (caddr freg)))
                (and op (gl--basename (operator-file op))))
            (cond
              ;; the functoid's BODY is its definition -- kept whole; the writer
              ;; puts it in a display block.  Truncating a definition to fit a
              ;; line is how a glossary entry stops being one.
              (freg (string-append "def: " (expression->string (cadr freg))))
              (axs  (string-append
                     "defined by "
                     (apply string-append
                            (map (lambda (a)
                                   (string-append "`" (symbol->string a) "` "))
                                 axs))))
              ((eq? kind 'accessor) "a structure slot")
              ((eq? kind 'predicate) "a predicate")
              ((eq? kind 'primitive) "a kernel relation")
              ;; NOT "a kernel term-former": most term-forming heads are library
              ;; vocabulary (BIJECTION is declared in structure-library), and the
              ;; characterizing axiom printed below says what it actually is.
              ((eq? kind 'operator)  "a term-forming head")
              (else #f)))))
       (sort (hash-table-keys *constant-registry*) gl--sym<?)))

;;; -----------------------------------------------------------------------
;;; (glossary) -- the whole vocabulary, alphabetical, as DATA.
;;;
;;; A name that is both a head and something else (a structure whose name is
;;; also a registered constant) keeps the more specific entry; the head list is
;;; consulted last.

(define (glossary-entries)
  (let ((seen (make-equal-hash-table))
        (out  '()))
    (for-each
      (lambda (e)
        (let ((n (gloss-name e)))
          (unless (hash-table-ref/default seen n #f)
            (hash-table-set! seen n #t)
            (set! out (cons e out)))))
      (append (gl--structure-entries)
              (gl--view-entries)
              (gl--tactic-entries)
              (gl--head-entries)))
    (set! out (map gl--mark-instance out))
    (sort (reverse out)
          (lambda (a b)
            (let ((x (string-downcase (symbol->string (gloss-name a))))
                  (y (string-downcase (symbol->string (gloss-name b)))))
              (if (string=? x y)
                  (gl--sym<? (gloss-kind a) (gloss-kind b))
                  (string<? x y)))))))

;;; (glossary) prints the lot; (glossary 'NAME) or (glossary "pat") the matches.
;;; Returns the entries it printed, so it is usable as data.
(define (glossary #!optional pat)
  (let* ((all (glossary-entries))
         (usage (operator-usage-index))
         (sel (cond
                ((default-object? pat) all)
                ((symbol? pat) (filter (lambda (e) (eq? (gloss-name e) pat)) all))
                ((string? pat)
                 (filter (lambda (e) (substring? (string-downcase pat)
                                                 (string-downcase
                                                  (symbol->string (gloss-name e)))))
                         all))
                (else all))))
    (for-each
      (lambda (e)
        (display (gloss-name e))
        (display (gloss-sig e))
        (display "  [") (display (gloss-kind e)) (display "]")
        (if (gloss-file e) (begin (display "  ") (display (gloss-file e))))
        (newline)
        (if (gloss-reads e)
            (begin (display "    reads: ") (display (gloss-reads e)) (newline)))
        (if (gloss-detail e)
            (begin (display "    ") (display (gloss-detail e)) (newline)))
        ;; the characterizing axiom -- the answer to "what IS this?"
        (let* ((mentions (hash-table-ref/default usage (gloss-name e) '()))
               (axs      (gl--char-axioms (gloss-name e) mentions)))
          (when (pair? axs)
            (display "    characterized by ") (display (car axs))
            (display " (") (display (provenance-of (car axs))) (display "):\n      ")
            (display (expression->string (lookup-theorem (car axs))))
            (newline))
          (when (pair? mentions)
            (display "    mentioned by ") (display (length mentions))
            (display " result(s) -- (glossary-uses '")
            (display (gloss-name e)) (display ") lists them\n"))))
      sel)
    (display ";; ") (display (length sel)) (display " of ")
    (display (length all)) (display " glossary entries\n")
    sel))

;;; (glossary-uses 'NAME) -- the results that mention NAME, sorted.  The
;;; companion of the "mentioned by N result(s)" line: the count is useless
;;; without a way to see WHICH.  Same index BY-OPERATOR.md is built from.
(define (glossary-uses name)
  (let ((ns (sort (hash-table-ref/default (operator-usage-index) name '())
                  gl--sym<?)))
    (for-each (lambda (n)
                (display "  ") (display n)
                (display "  [") (display (provenance-of n)) (display "]")
                (newline))
              ns)
    (display ";; ") (display (length ns)) (display " result(s) mention ")
    (display name) (newline)
    ns))

;;; -----------------------------------------------------------------------
;;; GLOSSARY.md

(define (gl--letter-of e)
  (let ((c (char-upcase (string-ref (symbol->string (gloss-name e)) 0))))
    (if (and (char>=? c #\A) (char<=? c #\Z)) c #\*)))

(define (gl--anchor name)
  (string-downcase (symbol->string name)))

(define (write-glossary-md)
  (let* ((path    (string-append *reference-dir* "GLOSSARY.md"))
         (entries (glossary-entries))
         (usage   (operator-usage-index))
         (letters (let loop ((es entries) (acc '()))
                    (cond ((null? es) (reverse acc))
                          ((memv (gl--letter-of (car es)) acc) (loop (cdr es) acc))
                          (else (loop (cdr es) (cons (gl--letter-of (car es)) acc))))))
         (by-kind (lambda (k) (length (filter (lambda (e) (eq? (gloss-kind e) k))
                                              entries)))))
    (with-output-to-file path
      (lambda ()
        (display "# Glossary -- every name in VNB, A to Z\n\n")
        (display "Auto-generated by `(write-glossary-md)`.  ")
        (display (length entries))
        (display " names: ")
        (for-each (lambda (k)
                    (let ((n (by-kind k)))
                      (when (> n 0)
                        (display n) (display " ") (display k) (display ", "))))
                  '(structure refinement instance view predicate functoid accessor
                    defined-fn operator primitive tactic))
        (display "in one alphabetical list.\n\n")
        (display "Every other reference document groups its contents by something --\n")
        (display "`OPERATORS.md` by class, `STRUCTURE-INDEX.md` by structure, `TACTICS.md`\n")
        (display "by task.  This one has the ordering nobody has to learn.\n\n")
        (display "The RESULTS -- theorems, axioms, supports -- are catalogued separately\n")
        (display "(`THEOREMS.md`, `BY-OPERATOR.md`, `PROOF-DEBT.md`); each entry below\n")
        (display "instead reports how many results mention the name, which is the\n")
        (display "glossary reader's question.  At the REPL: `(glossary 'NAME)`, or\n")
        (display "`(glossary \"pat\")` for a substring.\n\n")
        (display "| kind | what it is |\n|---|---|\n")
        (for-each (lambda (p)
                    (display "| `") (display (car p)) (display "` | ")
                    (display (cadr p)) (display " |\n"))
                  '((structure  "a declared shape: RING, METRIC-SPACE")
                    (refinement "declared `same-shape-as` another structure")
                    (instance   "a named structure value: ZZ-RING, RR-MS")
                    (view       "a declared `view-as` bridge")
                    (predicate  "IS-RING, CONVERGES, IS-HOM-GROUP")
                    (functoid   "a `def-functoid` term constructor")
                    (accessor   "a structure slot: CARR, MUL, DIST")
                    (defined-fn "a defined constant or recursion")
                    (operator   "a kernel term-former: UNION, NTH, SEP")
                    (primitive  "a kernel relation: =, IN, <=")
                    (tactic     "an interactive proof command")))
        (newline)
        ;; letter index.  The non-alphabetic head symbols (+, *, <=, ...) are
        ;; bucketed under "Symbols", which is what a reader scanning for `<='
        ;; looks under and what markdown can anchor.
        (display "**")
        (for-each (lambda (c)
                    (let ((s (if (char=? c #\*) "Symbols" (string c))))
                      (display "[") (display s) (display "](#")
                      (display (string-downcase s)) (display ") ")))
                  letters)
        (display "**\n\n")
        (let loop ((es entries) (cur #f))
          (unless (null? es)
            (let* ((e (car es)) (c (gl--letter-of e)))
              (unless (eqv? c cur)
                (display "\n## ")
                (display (if (char=? c #\*) "Symbols" (string c)))
                (display "\n\n"))
              (display "### `") (display (gloss-name e)) (display (gloss-sig e))
              (display "`  *(") (display (gloss-kind e)) (display ")*\n\n")
              (if (gloss-reads e)
                  (begin (display "reads: ") (display (gloss-reads e)) (display "\n\n")))
              (if (gloss-detail e)
                  (let ((d (gloss-detail e)))
                    (if (and (> (string-length d) 5)
                             (string=? (substring d 0 5) "def: "))
                        (begin (display "definition:\n\n```\n")
                               (display (substring d 5 (string-length d)))
                               (display "\n```\n\n"))
                        (begin (display d) (display "\n\n")))))
              ;; WHAT CHARACTERIZES IT.  The defining axiom, in full, is the
              ;; thing a reader looking a name up came for.
              (let* ((mentions (hash-table-ref/default usage (gloss-name e) '()))
                     (axs      (gl--char-axioms (gloss-name e) mentions)))
                (when (pair? axs)
                  (display "characterized by `") (display (car axs))
                  (display "`  *(") (display (provenance-of (car axs))) (display ")*:\n\n")
                  (display "```\n")
                  (display (expression->string (lookup-theorem (car axs))))
                  (display "\n```\n\n")
                  (when (pair? (cdr axs))
                    (display "also: ")
                    (let lp ((ns (cdr axs)) (i 0))
                      (when (and (pair? ns) (< i 8))
                        (display "`") (display (car ns)) (display "` ")
                        (lp (cdr ns) (+ i 1))))
                    (when (> (length (cdr axs)) 8)
                      (display "... (") (display (length (cdr axs)))
                      (display " in all)"))
                    (display "\n\n")))
                (when (pair? mentions)
                  (display "[mentioned by ") (display (length mentions))
                  (display " result(s)](BY-OPERATOR.md#")
                  (display (gl--anchor (gloss-name e)))
                  (display ")\n\n")))
              (if (gloss-file e)
                  (begin (display "declared in `") (display (gloss-file e))
                         (display "`\n\n")))
              (loop (cdr es) c))))))
    (display ";; glossary: ") (display (length entries))
    (display " names -> ") (display path) (newline)
    path))
