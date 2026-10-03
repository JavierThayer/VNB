;;; major-theorems.scm -- the LaTeX list of MAJOR THEOREMS.
;;;
;;; A MAJOR THEOREM is a result that appears in the user's notes as a Theorem,
;;; Proposition, Lemma or Corollary.  The mapping of the notes onto the library
;;; is DATA, hand-written (one file per document, merged into
;;; reference/major-theorems.sexp); this file turns that data into
;;; reference/major-theorems.tex, so that every statement the library makes
;;; about a result of the notes can be read beside the notes' own statement.
;;;
;;; Public entry point:
;;;
;;;   (write-major-theorems-tex! TABLE-PATH OUT-PATH)
;;;
;;; Both paths may be relative; they are resolved against *prover-dir*.  The
;;; output is a fragment, meant to be \input by docs/major-theorems.tex (or by
;;; the manual), and needs from its host preamble:
;;;
;;;   amsmath, amssymb, amsthm     -- math, \begin{proof}
;;;   graphicx                     -- \resizebox, used by \vnbstmt
;;;   longtable                    -- the Deviations table
;;;   \newtheorem thm / prop / cor / lem
;;;
;;; \vnbstmt and \vnbmulti are \providecommand-ed at the head of the generated
;;; file, so the fragment also works under a preamble that does not define them.
;;;
;;; THE TABLE.  A file of `entry' s-expressions, in the order of the notes:
;;;
;;;   (entry (doc "calculus")                   ; calculus | linear-algebra | ...
;;;          (ref "2.11")                       ; the number in the notes
;;;          (kind theorem)                     ; theorem | proposition | lemma | corollary | definition
;;;          (title "Generalized Mean Value Theorem")
;;;          (names generalized-mvt)            ; the library theorem(s); () when absent
;;;          (status proven)                    ; proven | asserted | partial | absent
;;;          (deviation "...")                  ; "" when the library says what the notes say
;;;          (notes-statement "..."))           ; the notes' statement, in prose
;;;
;;; Every field is optional: a missing one takes a default, and a missing
;;; `status' is INFERRED from the library (proven / asserted / absent).  A
;;; top-level form whose head is not `entry' is reported and skipped, so the
;;; concatenation of the mapping agents' files may carry comments in
;;; s-expression form without breaking the run.
;;;
;;; What the generated proof block says comes from the LIVE system, never from
;;; the table: the stored script (*proof-script-table*, filled by `save-proof'
;;; at every qed) for the tactics, `proof-citations-of' for the lemmas,
;;; `oracles-of' for the trusted code and `debt-of' for the bill.  A name with
;;; no stored script (an asserted support, a primitive axiom, a view or -rev
;;; companion) reports what it is instead.

;;; --- small string helpers --------------------------------------------

(define (mt--join strs sep)
  (cond ((null? strs) "")
        ((null? (cdr strs)) (car strs))
        (#t (string-append (car strs) sep (mt--join (cdr strs) sep)))))

;;; Escape for ordinary PROSE (titles, notes statements, deviation texts).
;;; One pass, character by character, so no replacement is re-escaped.
(define (mt--escape-tex s)
  (apply string-append
         (map (lambda (c)
                (cond ((char=? c #\\) "\\textbackslash{}")
                      ((char=? c #\{) "\\{")
                      ((char=? c #\}) "\\}")
                      ((char=? c #\_) "\\_")
                      ((char=? c #\^) "\\textasciicircum{}")
                      ((char=? c #\~) "\\textasciitilde{}")
                      ((char=? c #\%) "\\%")
                      ((char=? c #\&) "\\&")
                      ((char=? c #\#) "\\#")
                      ((char=? c #\$) "\\$")
                      ((char=? c #\<) "$<$")
                      ((char=? c #\>) "$>$")
                      (#t (string c))))
              (string->list s))))

;;; Escape for \texttt{...}: the same specials, but `<' and `>' stay literal
;;; (a typewriter name may contain them and math mode inside \texttt is worse).
(define (mt--escape-tt s)
  (apply string-append
         (map (lambda (c)
                (cond ((char=? c #\\) "\\textbackslash{}")
                      ((char=? c #\{) "\\{")
                      ((char=? c #\}) "\\}")
                      ((char=? c #\_) "\\_")
                      ((char=? c #\^) "\\textasciicircum{}")
                      ((char=? c #\~) "\\textasciitilde{}")
                      ((char=? c #\%) "\\%")
                      ((char=? c #\&) "\\&")
                      ((char=? c #\#) "\\#")
                      ((char=? c #\$) "\\$")
                      (#t (string c))))
              (string->list s))))

(define (mt--tt name)
  (string-append "\\texttt{" (mt--escape-tt (mt--as-string name)) "}"))

;;; The same, but with a zero-width breakpoint after every hyphen.  A typewriter
;;; token neither hyphenates nor breaks at its own hyphens, and a theorem name
;;; is routinely wider than the 4.2 cm name column of the Deviations table: the
;;; column then overfills by up to 90 pt.  `\allowbreak' adds nothing to the
;;; output (the hyphen that ends the first half is the name's own), so a name
;;; that fits is unchanged.
(define (mt--tt-breakable name)
  (string-append
   "\\texttt{"
   (apply string-append
          (map (lambda (c)
                 (if (char=? c #\-) "-\\allowbreak{}" (mt--escape-tt (string c))))
               (string->list (mt--as-string name))))
   "}"))

(define (mt--as-string x)
  (cond ((string? x) x)
        ((symbol? x) (symbol->string x))
        ((number? x) (number->string x))
        (#t (with-output-to-string (lambda () (display x))))))

;;; A LaTeX label fragment: letters, digits, hyphen, colon and dot survive;
;;; everything else becomes a hyphen.
(define (mt--sanitize-label s)
  (list->string
   (map (lambda (c)
          (if (or (char-alphabetic? c) (char-numeric? c)
                  (char=? c #\-) (char=? c #\:) (char=? c #\.))
              c
              #\-))
        (string->list s))))

(define (mt--capitalize s)
  (if (= (string-length s) 0)
      s
      (string-append (string (char-upcase (string-ref s 0)))
                     (substring s 1 (string-length s)))))

(define (mt--hyphens->spaces s)
  (list->string (map (lambda (c) (if (char=? c #\-) #\space c))
                     (string->list s))))

;;; --- paths ------------------------------------------------------------

;;; Resolve PATH against *prover-dir* unless it is already absolute.  The
;;; integrator's call passes "reference/major-theorems.sexp", which must not
;;; depend on the process's working directory.
(define (mt--abs-path path)
  (if (and (> (string-length path) 0) (char=? (string-ref path 0) #\/))
      path
      (string-append *prover-dir* path)))

;;; --- the table --------------------------------------------------------

(define *mt-doc-titles*
  '(("calculus"         . "Calculus")
    ("linear-algebra"   . "Linear algebra")
    ("complex-analysis" . "Complex analysis")))

(define (mt--doc-title doc)
  (let ((hit (assoc doc *mt-doc-titles*)))
    (if hit
        (cdr hit)
        (mt--capitalize (mt--hyphens->spaces doc)))))

;;; The raw value list of FIELD in ENTRY, or #f when the field is absent.
(define (mt--field entry field)
  (let ((hit (assq field (cdr entry))))
    (and hit (cdr hit))))

;;; A one-value field.  `(ref "2.11")' and `(ref 2.11)' both read.
(define (mt--one entry field default)
  (let ((vs (mt--field entry field)))
    (if (or (not vs) (null? vs)) default (car vs))))

(define (mt--string entry field default)
  (let ((v (mt--one entry field #f)))
    (if v (mt--as-string v) default)))

;;; A LIST field.  Tolerates `(names a b)', `(names (a b))' and `(names)'.
(define (mt--list entry field)
  (let ((vs (mt--field entry field)))
    (cond ((not vs) '())
          ((null? vs) '())
          ((and (null? (cdr vs)) (list? (car vs))) (car vs))
          (#t vs))))

;;; Returns the entry list, or #f when the table file is not there.  NOT an
;;; error: the table is hand-written and merged by the integrator, and a load
;;; must not fail because it has not been written yet.  The missing file is
;;; announced on the load log, where a missing generated artifact belongs.
(define (mt--read-table path)
  (let ((full (mt--abs-path path)))
    (if (not (file-exists? full))
        (begin
          (display ";; major-theorems: no table at ") (display full)
          (display " -- nothing written\n")
          #f)
        (call-with-input-file full
          (lambda (port)
            (let loop ((form (read port)) (acc '()) (skipped 0))
              (cond ((eof-object? form)
                     (when (> skipped 0)
                       (display ";; major-theorems: skipped ")
                       (display skipped)
                       (display " non-`entry' top-level form(s)\n"))
                     (reverse acc))
                    ((and (pair? form) (eq? (car form) 'entry))
                     (loop (read port) (cons form acc) skipped))
                    (#t
                     (display ";; major-theorems: not an `entry' form, skipped: ")
                     (write (if (pair? form) (car form) form))
                     (newline)
                     (loop (read port) acc (+ skipped 1))))))))))

;;; --- library queries --------------------------------------------------

(define (mt--formula name)
  (hash-table-ref/default *theorem-table* name #f))

;;; The stored surface script of NAME's proof, or #f.  A view-specialized or
;;; -rev companion has no script of its own; its proof is its source's, so the
;;; lookup follows `pd-source-of' exactly as the ledger does.
(define (mt--script name)
  (or (hash-table-ref/default *proof-script-table* name #f)
      (let ((src (pd-source-of name)))
        (and src (hash-table-ref/default *proof-script-table* src #f)))))

;;; THE SCRIPT, STEP BY STEP (the user, 2026-09-22).  Every recorded surface command
;;; of the stored proof, IN THE ORDER it was used, repeats included: `(di)' for a
;;; command without arguments, `(fact 3 arguments)' for one with three.  The
;;; arguments themselves are not printed (they are formulas and indices into the
;;; state of the run); the cited lemmas are listed separately.  Two uses: a corpus
;;; of tactic sequences, and a guide for a reader who wants to redo the proof.
(define (mt--script-steps script)
  (map (lambda (entry)
         (let* ((verb (car entry))
                (args (if (list? (cdr entry)) (cdr entry) (list (cdr entry))))
                (n    (length args)))
           ;; When the FIRST argument names an installed theorem (fact, mac, mac-h,
           ;; ta, bc*, ...), the name is shown: it is the one argument a reader who
           ;; redoes the proof cannot guess (the user, 2026-09-22).  N still counts
           ;; every argument, the name included.
           (let* ((a1   (and (pair? args) (car args)))
                  (a1s  (cond ((symbol? a1) a1)
                              ((and (pair? a1) (eq? (car a1) 'quote) (pair? (cdr a1))
                                    (symbol? (cadr a1)))
                               (cadr a1))
                              (#t #f)))
                  (cited (and a1s (hash-table-ref/default *theorem-table* a1s #f) a1s)))
             (string-append
              "\\mbox{\\texttt{(" (mt--escape-tt (mt--as-string verb))
              (if cited (string-append " " (mt--escape-tt (mt--as-string cited)) ",") "")
              (cond ((= n 0) "")
                    ((= n 1) " 1 argument")
                    (#t (string-append " " (number->string n) " arguments")))
              ")}}"))))
       script))

;;; The distinct surface commands of SCRIPT, in order of FIRST use.
(define (mt--script-tactics script)
  (let loop ((s script) (seen '()))
    (if (null? s)
        (reverse seen)
        (let ((verb (car (car s))))
          (loop (cdr s) (if (memq verb seen) seen (cons verb seen)))))))

(define (mt--any? p lst)
  (cond ((null? lst) #f)
        ((p (car lst)) #t)
        (#t (mt--any? p (cdr lst)))))

(define (mt--every? p lst)
  (cond ((null? lst) #t)
        ((p (car lst)) (mt--every? p (cdr lst)))
        (#t #f)))

(define (mt--status-of-names names)
  (cond ((null? names) 'absent)
        ((mt--any? (lambda (n) (and (mt--formula n)
                                    (eq? (provenance-of n) 'asserted)))
                   names)
         'asserted)
        ((mt--every? (lambda (n) (mt--formula n)) names) 'proven)
        (#t 'partial)))

;;; --- rendering: the statement ----------------------------------------

;;; `expr->tex-display' (tex-output.scm) breaks a long formula at its logical
;;; skeleton and returns a bare one-row string when one row is enough, so short
;;; statements are unaffected.  \vnbstmt then shrinks the finished box to the
;;; text width ONLY if it would overflow, which is what keeps a wide statement
;;; -- an array row can still be wider than the measure -- off the margin.
;;; VARIABLE NAMES FOR READING (the user, 2026-09-21).  The library spells inner
;;; binders with a trailing underscore (`a_', `x_', `icx_') so that they fold onto
;;; nothing; printed, the underscore is noise.  In the LIST (and only there) a_ ...
;;; f_ are set as alpha, beta, gamma, delta, epsilon, phi, and any other NAME_ as
;;; NAME -- each only when the new spelling names nothing else in that statement:
;;; not another symbol of the formula, not a registered constant, not an atom the
;;; TeX tables know.  The renaming is a plain tree walk over the printed copy; the
;;; installed formula is untouched.
(define *mt-greek-names*
  '((a_ . alpha) (b_ . beta) (c_ . gamma) (d_ . delta) (e_ . epsilon) (f_ . phi)))

(define (mt--symbols-of e acc)
  (cond ((symbol? e) (if (memq e acc) acc (cons e acc)))
        ((pair? e) (mt--symbols-of (cdr e) (mt--symbols-of (car e) acc)))
        (#t acc)))

;;; `lm', `lm1', `lm2' (the library's spelling of "a limit") read as ell, ell_1,
;;; ell_2 (the user, 2026-09-22: "use something other than lm, and make the 1 & 2
;;; subscripts"; the subscripting itself is tex-output.scm's).
(define (mt--limit-name str)
  (let ((n (string-length str)))
    (and (>= n 2)
         (string=? (string-head str 2) "lm")
         (let loop ((i 2))
           (cond ((= i n) (string-append "ell" (string-tail str 2)))
                 ((char-numeric? (string-ref str i)) (loop (+ i 1)))
                 (#t #f))))))

(define (mt--reading-name s)
  (let* ((str0 (symbol->string s))
         (n0   (string-length str0))
         (und? (and (> n0 1) (char=? (string-ref str0 (- n0 1)) #\_)))
         (g    (and und? (assq s *mt-greek-names*))))
    (cond (g (cdr g))
          (#t
           (let* ((str (if und? (string-head str0 (- n0 1)) str0))
                  (lim (mt--limit-name str))
                  (new (or lim str)))
             (and (not (string=? new str0)) (string->symbol new)))))))

;;; The BOUND variables of a formula, in order of first appearance (the only
;;; symbols the page renames: a head or a constant keeps its name).
(define (mt--bound-vars e)
  (let walk ((e e) (acc '()))
    (cond ((not (pair? e)) acc)
          ((and (memq (car e) '(FORALL FORSOME IOTA COMP VNB-LAMBDA SEP BIG-UNION))
                (pair? (cdr e)) (symbol? (cadr e)))
           (walk (cddr e) (if (memq (cadr e) acc) acc (append acc (list (cadr e))))))
          (#t (walk (cdr e) (walk (car e) acc))))))

;;; SINGLE-LETTER NAMES (the user, 2026-10-03: "instead of goua, goub, gouc, why
;;; not a, b, c").  The candidates for a bound variable, best first: the ell
;;; reading of lm / lm1 (2026-09-22); the LAST LETTER of its stem with the
;;; trailing digits kept (goua -> a, cekt_ -> t, lpx_ -> x, x1_ -> x1); the
;;; name with its trailing underscore dropped; the Greek letter of the a_ .. f_
;;; table.  A candidate is taken only when no symbol of the formula already
;;; spells it and it is not a registered constant or a TeX atom; after the
;;; candidates, the first free letter of the alphabet (e and i excluded: the
;;; constants).
(define (mt--letter-candidates s)
  (let* ((str0  (symbol->string s))
         (n0    (string-length str0))
         (und?  (and (> n0 1) (char=? (string-ref str0 (- n0 1)) #\_)))
         (str   (if und? (string-head str0 (- n0 1)) str0))
         (k     (let loop ((i (string-length str)))
                  (if (and (> i 0) (char-numeric? (string-ref str (- i 1)))) (loop (- i 1)) i)))
         (stem  (string-head str k))
         (digits (string-tail str k))
         (lim   (mt--limit-name str))
         (single (and (> (string-length stem) 1)
                      (string-append (string (string-ref stem (- (string-length stem) 1))) digits)))
         (greek (let ((g (assq s *mt-greek-names*))) (and g (symbol->string (cdr g))))))
    (let loop ((cs (list lim single (and und? str) greek)) (out '()))
      (cond ((null? cs) (reverse out))
            ((and (car cs) (not (string=? (car cs) str0)) (not (member (car cs) out)))
             (loop (cdr cs) (cons (car cs) out)))
            (#t (loop (cdr cs) out))))))

(define *mt-letter-pool*
  (map string '(#\a #\b #\c #\d #\f #\g #\h #\k #\m #\n #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z)))

(define (mt--pretty-vars formula)
  (let* ((syms  (mt--symbols-of formula '()))
         (bound (mt--bound-vars formula))
         (ok?   (lambda (new taken)
                  (and (not (memq new taken))
                       (not (hash-table-ref/default *constant-registry* new #f))
                       (not (assq new *tex-atom-table*)))))
         (pairs
          (let loop ((ss bound) (taken syms) (out '()))
            (if (null? ss)
                out
                (let* ((s    (car ss))
                       (cands (map string->symbol
                                   (append (mt--letter-candidates s)
                                           ;; the alphabet, only for a name that is not a single letter already
                                           (if (> (string-length (symbol->string s)) 1) *mt-letter-pool* '()))))
                       (new  (find (lambda (c) (and (not (eq? c s)) (ok? c taken))) cands)))
                  (if new
                      (loop (cdr ss) (cons new taken) (cons (cons s new) out))
                      (loop (cdr ss) taken out)))))))
    (let walk ((e formula))
      (cond ((symbol? e) (let ((p (assq e pairs))) (if p (cdr p) e)))
            ((pair? e) (cons (walk (car e)) (walk (cdr e))))
            (#t e)))))

;;; FLATTENING (the user, 2026-10-03: "A implies (B implies C) would be more
;;; cleanly stated as A and B implies C; there are other flattenings possible").
;;; Display only; three rewrites before the TeX printer sees the statement:
;;;   (1) a binder's conjunctive guard splits,
;;;         forall v. (v in S and P) => R   ~>   forall v. v in S => (P => R),
;;;       so the typed-quantifier sugar of tex-output.scm fires;
;;;   (2) a universal under an antecedent hoists, when its variable is not free
;;;       in the antecedent,
;;;         A => forall y. y in T => B   ~>   forall y. y in T => (A => B),
;;;       so consecutive typed binders merge into one  forall x in S, y in T.;
;;;   (3) curried antecedents merge,  A => (B => C)  ~>  (A and B) => C,
;;;       except the typing guard right under its own binder (the sugar's).
(define (mt--imp? e) (and (pair? e) (eq? (car e) 'IMPLIES) (= (length e) 3)))
(define (mt--and? e) (and (pair? e) (eq? (car e) 'AND) (= (length e) 3)))
(define (mt--forall? e) (and (pair? e) (eq? (car e) 'FORALL) (= (length e) 3)))
(define (mt--guard-of? c v)
  (and (pair? c) (eq? (car c) 'IN) (= (length c) 3) (eq? (cadr c) v)))

(define (mt--flatten e)
  (cond
    ((not (pair? e)) e)
    ((and (memq (car e) '(FORALL FORSOME)) (= (length e) 3) (symbol? (cadr e)))
     (list (car e) (cadr e) (mt--flatten-under (cadr e) (caddr e))))
    ((mt--imp? e) (mt--merge-imp (mt--flatten (cadr e)) (mt--flatten (caddr e))))
    (#t (map mt--flatten e))))

(define (mt--flatten-under v body)
  (cond
    ((and (mt--imp? body) (mt--and? (cadr body)) (mt--guard-of? (cadr (cadr body)) v))
     (mt--flatten-under v (list 'IMPLIES (cadr (cadr body))
                                (list 'IMPLIES (caddr (cadr body)) (caddr body)))))
    ((and (mt--imp? body) (mt--guard-of? (cadr body) v))
     (list 'IMPLIES (cadr body) (mt--flatten (caddr body))))
    (#t (mt--flatten body))))

(define (mt--merge-imp a c)
  (cond
    ((and (mt--forall? c) (not (memq (cadr c) (free-vars a))))
     (let ((y (cadr c)) (body (caddr c)))
       (if (and (mt--imp? body) (mt--guard-of? (cadr body) y))
           (list 'FORALL y (list 'IMPLIES (cadr body) (mt--merge-imp a (caddr body))))
           (list 'FORALL y (mt--merge-imp a body)))))
    ((mt--imp? c) (mt--merge-imp (list 'AND a (cadr c)) (caddr c)))
    (#t (list 'IMPLIES a c))))

(define (mt--statement-tex formula)
  (string-append "\\vnbstmt{" (expr->tex-display (mt--pretty-vars (mt--flatten formula))) "}"))

(define (mt--statement-block names notes-statement)
  (cond
    ((null? names)
     (string-append
      "\\textit{" (mt--escape-tex notes-statement) "}\n"
      "%\n"
      "Not in the library.\n"))
    ((null? (cdr names))
     (let ((f (mt--formula (car names))))
       (if f
           (string-append (mt--statement-tex f) "\n")
           (string-append "\\vnbmissing{" (mt--escape-tt (mt--as-string (car names)))
                          "}\n"))))
    (#t
     ;; Several library names for one result: each PART in a paragraph of its
     ;; own, labelled by its name.  The \\leavevmode ends the theorem HEAD's line
     ;; first (amsthm defers the head into the next paragraph, and the first
     ;; part's label would otherwise be set on the same line as the head).
     (apply string-append "\\leavevmode\n"
            (map (lambda (n)
                   (let ((f (mt--formula n)))
                     (string-append
                      ;; \vnbprf (ragged right) and not a plain \noindent: this
                      ;; is the first paragraph of the theorem body, so amsthm's
                      ;; deferred head lands in it, and justifying head + a wide
                      ;; \texttt name stretches the head's line to an underfull
                      ;; hbox.
                      "\\vnbpart{" (mt--tt n) "}\n"
                      (if f
                          (string-append (mt--statement-tex f) "\n")
                          (string-append "\\vnbmissing{"
                                         (mt--escape-tt (mt--as-string n)) "}\n")))))
                 names)))))

;;; --- rendering: the proof block ---------------------------------------

(define (mt--bill-line name)
  (let ((bill (debt-of name))
        ;; `proven' alone means the proof ran in this image (certificates.scm)
        (word (if (certified-theorem? name) "certified" "proven")))
    (if (null? bill)
        (string-append "\\texttt{" word " modulo 0}")
        (string-append "\\texttt{" word " modulo \\{"
                       (mt--join (map (lambda (n) (mt--escape-tt (mt--as-string n)))
                                      bill)
                                 ", ")
                       "\\}} [trust: "
                       (mt--escape-tex (mt--as-string (debt-trust-level bill)))
                       "]"))))

(define (mt--lemma-item c)
  (string-append (mt--tt c)
                 (if (eq? (provenance-of c) 'asserted) " (asserted)" "")))

;;; The file that states and proves NAME, relative to the tree (*theorem-source*,
;;; the load pathname at install; a compiled file's .com is shown as its .scm).
(define (mt--source-rel name)
  (let ((p (hash-table-ref/default *theorem-source* name #f)))
    (and p
         (let* ((s   (->namestring (pathname-new-type (->pathname p) "scm")))
                (dir *prover-dir*)
                (n   (string-length dir)))
           (if (and (>= (string-length s) n) (string=? (string-head s n) dir))
               (string-tail s n)
               s)))))

;;; "Proof. theorem-library/foo.scm" -- the file, in place of the tactic list
;;; (the user, 2026-10-03: no need to list the tactics; list the proof file).
(define (mt--proof-file-line name note)
  (let ((f (mt--source-rel name)))
    (string-append "\\textbf{Proof.} "
                   (if f (mt--tt-breakable f) "(file not recorded)")
                   (if note (string-append " --- " note) "")
                   ".")))

(define (mt--proof-paragraphs name)
  (let ((script (mt--script name))
        (prov   (provenance-of name)))
    (cond
      ((not (mt--formula name))
       (list (string-append "No theorem named " (mt--tt name)
                            " is installed in the library.")))
      ((eq? prov 'asserted)
       (let* ((w    (warrant-of name))
              (tier (if w (mt--as-string (car w)) "none")))
         (list (string-append "Asserted (warrant: " (mt--escape-tex tier)
                              "); no proof in the library."))))
      ((eq? prov 'primitive)
       (list "A primitive axiom of the trusted base; no proof in the library."))
      ((eq? prov 'definitional)
       (list "Definitional; no proof in the library."))
      ;; installed from its certificate (certificates.scm): the exam ran the
      ;; proof; this image holds its citations, oracles and bill, not its script
      ((and (not script) (certified-theorem? name))
       (let ((lemmas  (proof-citations-of name))
             (oracles (oracles-of name)))
         (list
          (mt--proof-file-line name "certified: the proof ran in the last exam (mailbox/metrics/last-exam.json)")
          (string-append
           "\\textbf{Lemmas.} "
           (if (null? lemmas)
               "none cited by name."
               (string-append (mt--join (map mt--lemma-item lemmas) ", ") ".")))
          (string-append
           "\\textbf{Oracles.} "
           (if (null? oracles)
               "none."
               (string-append (mt--join (map mt--tt oracles) ", ") "."))
           "  \\textbf{Bill:} " (mt--bill-line name) "."))))
      ((not script)
       (list (string-append "Provenance " (mt--tt prov)
                            ", but no proof script is stored under this name.")))
      (#t
       (let* ((lemmas  (proof-citations-of name))
              (oracles (oracles-of name)))
         (list
          (mt--proof-file-line name
            (string-append (number->string (length script))
                           (if (= (length script) 1) " recorded step" " recorded steps")))
          (string-append
           "\\textbf{Lemmas.} "
           (if (null? lemmas)
               "none cited by name."
               (string-append (mt--join (map mt--lemma-item lemmas) ", ") ".")))
          (string-append
           "\\textbf{Oracles.} "
           (if (null? oracles)
               "none."
               (string-append (mt--join (map mt--tt oracles) ", ") "."))
           "  \\textbf{Bill:} " (mt--bill-line name) ".")))))))

(define (mt--proof-block names)
  (cond
    ((null? names)
     (list "There is no library statement, and so no proof."))
    ((null? (cdr names))
     (mt--proof-paragraphs (car names)))
    (#t
     ;; One paragraph group per name, each headed by the name.
     (apply append
            (map (lambda (n)
                   (let ((ps (mt--proof-paragraphs n)))
                     ;; a part of the proof: its own paragraph, set off from the last
                     (cons (string-append "\\vnbproofpart{" (mt--tt n) "}") ps)))
                 names)))))

;;; --- rendering: one entry ---------------------------------------------

;;; `cond' and not `case': the per-file load environment shadows `else', and a
;;; `case' clause cannot be guarded by #t.
(define (mt--env-of-kind kind)
  (cond ((memq kind '(theorem thm))      "thm")
        ((memq kind '(proposition prop)) "prop")
        ((memq kind '(lemma lem))        "lem")
        ((memq kind '(corollary cor))    "cor")
        ((memq kind '(definition defn))  "defn")   ; 2026-09-27: the principal logarithm row
        (#t "thm")))

(define (mt--doc-ref-label entry)
  (string-append "thm:"
                 (mt--sanitize-label
                  (string-append (mt--string entry 'doc "unknown") "-"
                                 (mt--string entry 'ref "?")))))

(define (mt--label entry names)
  (if (null? names)
      (mt--doc-ref-label entry)
      (string-append "thm:" (mt--sanitize-label (mt--as-string (car names))))))

;;; The labels of ENTRIES, in order, made UNIQUE.  One library theorem can
;;; answer two numbered results of the notes -- `taylor-lagrange' does -- and
;;; two \label's with one key is a LaTeX warning and a cross-reference that
;;; points at whichever came last.  A repeat falls back to the doc-and-ref
;;; label, and a repeat of THAT takes a numeric suffix; the fallback is
;;; announced, because a shared name is worth knowing about.
(define (mt--labels entries)
  (let loop ((es entries) (used '()) (out '()))
    (if (null? es)
        (reverse out)
        (let* ((e     (car es))
               (want  (mt--label e (mt--list e 'names)))
               (final
                (if (not (member want used))
                    want
                    (let ((alt (mt--doc-ref-label e)))
                      (display ";; major-theorems: label ") (display want)
                      (display " is taken (one library name answers two results); ")
                      (display "using ") (display alt) (newline)
                      (if (not (member alt used))
                          alt
                          (let bump ((k 2))
                            (let ((try (string-append alt "-" (number->string k))))
                              (if (member try used) (bump (+ k 1)) try))))))))
          (loop (cdr es) (cons final used) (cons final out))))))

(define (mt--write-entry entry label)
  (let* ((doc    (mt--string entry 'doc "unknown"))
         (ref    (mt--string entry 'ref ""))
         (kind   (mt--one entry 'kind 'theorem))
         (title  (mt--string entry 'title ""))
         (names  (mt--list entry 'names))
         (dev    (mt--string entry 'deviation ""))
         (notes  (mt--string entry 'notes-statement ""))
         (env    (mt--env-of-kind kind))
         ;; The NUMBER printed is the notes' own (2026-09-21: the list's running
         ;; counter made the notes' 2.26 appear as "Lemma 1.30"); the document is
         ;; named by the section the entry sits in.
         (head   (if (string=? title "") "Untitled" (mt--escape-tex title))))
    ;; The optional argument is braced: a `]' in a title would otherwise end it.
    (if (not (string=? ref ""))
        (begin (display "\\renewcommand{\\thethm}{") (display (mt--escape-tex ref)) (display "}\n")))
    (display "\\begin{") (display env) (display "}[{")
    (display head)
    (display "}]\\label{") (display label) (display "}\n")
    (display "%\n")
    (display (mt--statement-block names notes))
    (display "%\n")
    (display "\\end{") (display env) (display "}\n")
    (display "%\n")
    (display "\\begin{proof}\n")
    (display "%\n")
    (display "The proofs: the file that holds each, the lemmas it cites, its oracles and its bill.\n")
    (display "%\n")
    (for-each (lambda (p)
                (display "\\vnbprf{") (display p) (display "}\n")
                (display "%\n"))
              (mt--proof-block names))
    (display "\\end{proof}\n")
    (display "%\n")
    (if (not (string=? dev ""))
        (begin
          (display "\\noindent\\textbf{Deviation from the notes.} ")
          (display (mt--escape-tex dev))
          (display "\n")
          (display "%\n")))))

;;; --- rendering: the deviations section --------------------------------

(define (mt--deviation-row? entry)
  (let ((dev    (mt--string entry 'deviation ""))
        (status (mt--one entry 'status
                         (mt--status-of-names (mt--list entry 'names)))))
    (or (not (string=? dev "")) (not (eq? status 'proven)))))

(define (mt--names-cell names)
  (if (null? names)
      "---"
      (mt--join (map mt--tt-breakable names) ", ")))

(define (mt--write-deviations entries)
  (let ((rows (filter mt--deviation-row? entries)))
    (display "\\section{Deviations}\n")
    (display "%\n")
    (if (null? rows)
        (display "Every entry is proven in the library and states what the notes state.\n")
        (begin
          (display "Every entry whose library statement deviates from the notes, or whose\n")
          (display "status is not \\texttt{proven}.\n")
          (display "%\n")
          ;; The two wide columns are RAGGED RIGHT (`array''s >{...} prefix):
          ;; justified 4.2 cm columns holding \texttt names set very loose.
          (display "\\begin{longtable}{@{}ll")
          (display ">{\\raggedright\\arraybackslash}p{4.2cm}")
          (display ">{\\raggedright\\arraybackslash}p{4.2cm}l@{}}\n")
          (display "\\hline\n")
          (display "document & ref & title & library name(s) & status \\\\\n")
          (display "\\hline\n")
          (display "\\endfirsthead\n")
          (display "\\hline\n")
          (display "document & ref & title & library name(s) & status \\\\\n")
          (display "\\hline\n")
          (display "\\endhead\n")
          (for-each
           (lambda (e)
             (let* ((names  (mt--list e 'names))
                    (status (mt--one e 'status (mt--status-of-names names))))
               (display (mt--escape-tex (mt--doc-title (mt--string e 'doc "unknown"))))
               (display " & ")
               (display (mt--escape-tex (mt--string e 'ref "")))
               (display " & ")
               (display (mt--escape-tex (mt--string e 'title "")))
               (display " & ")
               (display (mt--names-cell names))
               (display " & ")
               (display (mt--escape-tex (mt--as-string status)))
               (display " \\\\\n")))
           rows)
          (display "\\hline\n")
          (display "\\end{longtable}\n")))
    (display "%\n")))

(define (mt--count entries doc status)
  (length (filter (lambda (e)
                    (and (string=? (mt--string e 'doc "unknown") doc)
                         (eq? (mt--one e 'status
                                       (mt--status-of-names (mt--list e 'names)))
                              status)))
                  entries)))

(define (mt--write-totals entries docs)
  (display "\\subsection*{Totals}\n")
  (display "%\n")
  (display "\\begin{tabular}{@{}lrrrrr@{}}\n")
  (display "\\hline\n")
  (display "document & entries & proven & asserted & partial & absent \\\\\n")
  (display "\\hline\n")
  (for-each
   (lambda (doc)
     (let ((n (length (filter (lambda (e)
                                (string=? (mt--string e 'doc "unknown") doc))
                              entries))))
       (display (mt--escape-tex (mt--doc-title doc)))
       (display " & ") (display n)
       (display " & ") (display (mt--count entries doc 'proven))
       (display " & ") (display (mt--count entries doc 'asserted))
       (display " & ") (display (mt--count entries doc 'partial))
       (display " & ") (display (mt--count entries doc 'absent))
       (display " \\\\\n")))
   docs)
  (display "\\hline\n")
  (display "\\end{tabular}\n")
  (display "%\n")
  ;; A status outside the four is not silently folded into one of them.
  (let ((other (filter (lambda (e)
                         (not (memq (mt--one e 'status
                                             (mt--status-of-names (mt--list e 'names)))
                                    '(proven asserted partial absent))))
                       entries)))
    (if (not (null? other))
        (begin
          (display "\\smallskip\\noindent ")
          (display (length other))
          (display " entry/entries carry a status outside the four columns above.\n")
          (display "%\n")))))

;;; --- the generated file's own macros ----------------------------------

(define mt--macro-block
  (string-append
   "% \\vnbstmt -- a displayed statement that shrinks to the text width only\n"
   "% when it would overflow it, so short statements are set at normal size and\n"
   "% a wide one never runs into the margin.  Needs graphicx.\n"
   "%\n"
   "% The leading \\leavevmode is not decoration.  amsthm defers the theorem head\n"
   "% (`Theorem 1.1 (Title).') into \\everypar, so it is injected at the start of\n"
   "% the first paragraph of the body; without \\leavevmode the opening \\par is a\n"
   "% no-op on an empty paragraph, the head lands in the SAME paragraph as the\n"
   "% box below, and head-width + \\linewidth overfills every statement by 300 pt.\n"
   "% \\leavevmode starts a paragraph for the head to attach to, and the \\par then\n"
   "% closes it before the box.\n"
   "\\providecommand{\\vnbstmt}[1]{%\n"
   "  \\leavevmode\\par\\nobreak\\smallskip\\noindent\n"
   "  \\resizebox{\\ifdim\\width>\\linewidth\\linewidth\\else\\width\\fi}{!}{$\\displaystyle #1$}%\n"
   "  \\par\\smallskip}\n"
   "\\providecommand{\\vnbmissing}[1]{\\textit{No theorem \\texttt{#1} is installed"
   " in the library.}}\n"
   "% \\vnbprf -- one paragraph of the proof block.  Set RAGGED RIGHT: these are\n"
   "% comma-separated lists of \\texttt identifiers, which neither hyphenate nor\n"
   "% break at their hyphens, so justified setting either overfills the measure or\n"
   "% (under \\sloppy) buys the fit with very loose interword glue.\n"
   "\\providecommand{\\vnbprf}[1]{{\\raggedright #1\\par}}\n"
   "% \\vnbpart -- one PART of a statement that the library gives under several names:\n"
   "% its own paragraph, the name as a run-in label (the user, 2026-09-21).\n"
   "\\providecommand{\\vnbpart}[1]{\\par\\medskip{\\raggedright\\noindent\\textup{\\textbf{Part} #1.}\\par}\\nopagebreak\\smallskip}\n"
   "\\providecommand{\\vnbproofpart}[1]{\\par\\medskip\\noindent\\textbf{Proof of} #1\\textbf{.}\\par\\nopagebreak}\n"))

;;; --- the entry point --------------------------------------------------

;;; Read the table at TABLE-PATH and write the LaTeX fragment to OUT-PATH.
;;; Entries keep the table's order; they are grouped by document in the order
;;; the documents first appear, so one \section is emitted per document.
;;; Returns the output path, or #f when there is no table to read.
;;; A CERTIFIED load (VNB_CERTIFIED=on) holds no script for a certified theorem,
;;; so the fragment it would write says "the exam's image holds the script" for
;;; every proof; written over the exam's fragment and pulled back to the
;;; primary, that cost docs/major-theorems.pdf its proofs (410 pages to 178,
;;; found 2026-10-03).  So: when a theorem of the table is certified with no
;;; script in this image AND the fragment already exists, leave the file as
;;; the last exam wrote it and say so; the exam (every proof run) rewrites it.
(define (mt--scriptless? name)
  (and (certified-theorem? name) (not (mt--script name))))

(define (write-major-theorems-tex! table-path out-path)
  (let ((entries (mt--read-table table-path)))
    (cond
      ((not entries) #f)
      ((and (file-exists? (mt--abs-path out-path))
            (any (lambda (e) (any mt--scriptless? (mt--list e 'names))) entries))
       (display ";; major-theorems: KEPT the exam's ")
       (display out-path)
       (display " -- this image holds no script for a certified theorem of the table\n")
       #f)
      (#t (mt--write-all entries out-path)))))

(define (mt--write-all entries out-path)
  (let* ((labels  (mt--labels entries))
         ;; entry paired with its unique label, so the per-document pass below
         ;; keeps the table's order without recomputing anything.
         (pairs   (map cons entries labels))
         (out     (mt--abs-path out-path))
         (docs    (let loop ((es entries) (seen '()))
                    (if (null? es)
                        (reverse seen)
                        (let ((d (mt--string (car es) 'doc "unknown")))
                          (loop (cdr es)
                                (if (member d seen) seen (cons d seen))))))))
    (with-output-to-file out
      (lambda ()
        (display "% major-theorems.tex -- GENERATED by (write-major-theorems-tex! ...)\n")
        (display "% from the table of major theorems.  Do not hand-edit: every edit is\n")
        (display "% lost at the next load.  The statements, tactics, lemmas, oracles and\n")
        (display "% bills below are read from the LIVE system, not from the table.\n")
        (display "%\n")
        (display "% Requires from the host preamble: amsmath, amssymb, amsthm, graphicx,\n")
        (display "% longtable, and the theorem environments thm / prop / cor / lem.\n")
        (display "%\n")
        (display mt--macro-block)
        (display "%\n")
        (for-each
         (lambda (doc)
           (display "\\section{") (display (mt--escape-tex (mt--doc-title doc)))
           (display "}\n")
           (display "%\n")
           (for-each (lambda (p)
                       (if (string=? (mt--string (car p) 'doc "unknown") doc)
                           (mt--write-entry (car p) (cdr p))))
                     pairs))
         docs)
        (mt--write-deviations entries)
        (mt--write-totals entries docs)))
    (display ";; major-theorems: ") (display (length entries))
    (display " entr(y/ies), ") (display (length docs))
    (display " document(s) -> ") (display out) (newline)
    out))
