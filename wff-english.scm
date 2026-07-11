;;; wff-english.scm -- render a wff as an English sentence.
;;;
;;; Companion to expr->str (sequents.scm, symbolic surface syntax) and
;;; describe-structure (interactive.scm, structures in prose).  This one
;;; verbalizes an arbitrary FORMULA.
;;;
;;; ALTITUDE (the central design choice): verbalize the LOGICAL SKELETON --
;;; quantifiers, connectives, membership/order relations, and IS-X "sort"
;;; predicates -- into prose, but leave atomic mathematical TERMS (arithmetic,
;;; function application like d(x, z)) in SYMBOLIC form via expr->str.  A
;;; theorem is read aloud as e.g.
;;;   "for every x in A, if x is in U then there is some positive real r
;;;    such that B(x, r) is a subset of U"
;;; -- English for the structure, symbols for the algebra.  Pure prose for
;;; d(x, z) <= d(x, y) + d(y, z) would be unreadable, so terms stay symbolic.
;;;
;;; Anything with no English rendering falls back to the symbolic expr->str,
;;; so output is always faithful, never wrong -- just less prosey in spots.
;;;
;;; Entry points:
;;;   (wff->english e)     core: a raw formula sexp -> English string
;;;   (en e)               alias
;;;   (english-of 'name)   verbalize an installed theorem by name

;;; -----------------------------------------------------------------------
;;; Vocabulary.
;;;
;;; Two tables.  *english-sort* holds UNARY "sort" predicates that read as
;;; "<x> is a <phrase>"; storing the bare phrase + article lets the SAME entry
;;; serve both the predication ("eps is a positive real") and the quantifier
;;; QUALIFIER fold ("for every positive real eps").  *english-pred* holds
;;; general predicates (any arity) whose English needs all the arguments
;;; (e.g. is-open(t, V) -> "V is open in t"); these render a predication only,
;;; no qualifier fold.

(define (sym-lc s) (string->symbol (string-downcase (symbol->string s))))

;;; The two tables that used to live here -- *english-sort* (unary sorts, with
;;; their article, for the "for every Euclidean ring a" fold) and *english-pred*
;;; (general predicates) -- are now the `noun'/`article' and `english' slots of
;;; the ONE operator table (operators.scm).  A head's English is declared with
;;; `notation!' NEXT TO ITS DEFINITION, so is-euclidean-ring reads as "a is a
;;; Euclidean ring" because ring.scm says so, not because wff-english.scm keeps
;;; a private list of the heads it happens to know.
;;;
;;; These two remain as the spelling the old call sites use; both write into the
;;; one table.
(define (def-english-sort! sym phrase article)
  (notation! sym 'noun phrase 'article article))

(define (def-english-pred! sym arity proc)
  (notation! sym 'arity arity 'english proc))

;;; -----------------------------------------------------------------------
;;; Helpers.

;;; A term: render with the symbolic printer.
(define (term->english e) (expr->str e 0))

;;; "is a <phrase>" / "is <phrase>" predication for a unary sort entry.
(define (sort-predication x-str entry)
  (let ((phrase (car entry)) (article (cdr entry)))
    (string-append x-str " is "
                   (if (string=? article "") "" (string-append article " "))
                   phrase)))

;;; Quantifier qualifier for a unary sort entry: "positive real eps".
(define (sort-qualifier v-str entry)
  (string-append (car entry) " " v-str))

;;; Is e a unary application of a recognised sort predicate of variable v?
;;; Returns the sort entry or #f.
(define (sort-of-var e v)
  (and (pair? e) (= (length e) 2) (eq? (cadr e) v) (symbol? (car e))
       (operator-sort (car e))))

;;; Render one quantifier binding spec (from collect-quant-bindings) as the
;;; phrase that follows "for every"/"there is some".
(define (binding->english spec)
  (cond
    ;; (in v A) -> "v in A"
    ((and (pair? spec) (= (length spec) 3) (eq? (car spec) 'in) (symbol? (cadr spec)))
     (string-append (symbol->string (cadr spec)) " in " (term->english (caddr spec))))
    ;; (v) or (v1 v2 ...) unrestricted
    ((and (pair? spec) (every symbol? spec))
     (str-join (map symbol->string spec) ", "))
    (else (term->english spec))))

;;; -----------------------------------------------------------------------
;;; Core walker.

(define (wff->english e)
  (formula->english (if (wff? e) (wff-formula e) e)))

(define (en e) (wff->english e))

(define (english-of name)
  (let ((f (hash-table-ref/default *theorem-table* (sym-lc name) #f)))
    (if f (wff->english f)
        (string-append "(no installed theorem named " (symbol->string name) ")"))))

(define (formula->english e)
  (if (not (pair? e))
      (term->english e)
      (let ((h (and (symbol? (car e)) (sym-lc (car e)))))
        (cond
          ((memq h '(forall forsome)) (quantifier->english h e))
          ((and (eq? h 'and) (>= (length e) 3)) (junction->english (cdr e) " and "))
          ((and (eq? h 'or)  (>= (length e) 3)) (junction->english (cdr e) " or "))
          ((and (eq? h 'iff) (= (length e) 3)) (iff->english e))
          ((and (eq? h 'implies) (= (length e) 3)) (implies->english e))
          ((and (eq? h 'not) (= (length e) 2)) (not->english (cadr e)))
          (else (atom->english h e))))))

;;; Conjunction / disjunction: render each operand, join with sep.
(define (junction->english operands sep)
  (str-join (map formula->english operands) sep))

(define (iff->english e)
  (string-append (formula->english (cadr e))
                 " if and only if "
                 (formula->english (caddr e))))

(define (implies->english e)
  (string-append "if " (formula->english (cadr e))
                 ", then " (formula->english (caddr e))))

;;; NOT, with readable special cases for negated relations.
(define (not->english p)
  (if (pair? p)
      (let ((h (and (symbol? (car p)) (sym-lc (car p)))))
        (cond
          ((and (eq? h '=)  (= (length p) 3))
           (string-append (term->english (cadr p)) " is not equal to " (term->english (caddr p))))
          ((and (eq? h 'in) (= (length p) 3))
           (string-append (term->english (cadr p)) " is not in " (term->english (caddr p))))
          (else (string-append "it is not the case that " (formula->english p)))))
      (string-append "it is not the case that " (formula->english p))))

;;; Atomic formula: a recognised predicate, a unary sort, or symbolic fallback.
(define (atom->english h e)
  (let* ((args (cdr e))
         (entry (and h (operator-ref h)))
         (n     (length args))
         ;; the head's declared English, when it is about THESE arguments
         (en    (and entry (operator-english entry)
                     (or (not (operator-arity entry)) (= (operator-arity entry) n))
                     (operator-render-english h (map term->english args))))
         (sort  (and entry (= n 1) (operator-sort h))))
    (cond
      (en en)
      (sort (sort-predication (term->english (car args)) sort))
      ;; unrecognised: keep it honest -- symbolic surface form.
      (else (term->english e)))))

;;; Quantifiers, with two folds: bounded (x in A, already done by
;;; collect-quant-bindings) and unary-sort qualifier (the "positive real eps"
;;; absorption from a leading IMPLIES/AND antecedent on a single variable).
(define (quantifier->english q e)
  (let* ((result   (collect-quant-bindings q e))
         (bindings (car result))
         (body     (cdr result))
         (lead     (if (eq? q 'forall) "for every " "there is some "))
         (joiner   (if (eq? q 'forall) "" " such that ")))
    ;; Try to absorb a leading sort qualifier when there is exactly one
    ;; unrestricted binding: forall v (implies (P v) rest) and
    ;; forsome v (and (P v) rest), with P a recognised unary sort.
    (let ((fold (and (= (length bindings) 1)
                     (pair? (car bindings)) (= (length (car bindings)) 1)
                     (symbol? (caar bindings))
                     (absorb-sort q (caar bindings) body))))
      (if fold
          (string-append lead (car fold)
                         (if (eq? q 'forall) ", " " such that ")
                         (formula->english (cdr fold)))
          (string-append lead
                         (str-join (map binding->english bindings) ", ")
                         (if (eq? q 'forall) ", " joiner)
                         (formula->english body))))))

;;; If body folds as (op (P v) rest) with op matching q and P a unary sort,
;;; return (qualifier-string . rest); else #f.
(define (absorb-sort q v body)
  (and (pair? body)
       (let ((bh (and (symbol? (car body)) (sym-lc (car body)))))
         (and (= (length body) 3)
              (eq? bh (if (eq? q 'forall) 'implies 'and))
              (let ((entry (sort-of-var (cadr body) v)))
                (and entry
                     (cons (sort-qualifier (symbol->string v) entry)
                           (caddr body))))))))

;;; -----------------------------------------------------------------------
;;; (pss-letter 'name) -- a PSS membership recommendation letter.
;;;
;;; PSS membership (the curated set the engine may invoke freely) is largely
;;; a subjective curation call -- but a candidate is far easier to judge read
;;; aloud as English than as an s-expression.  This drafts the letter the
;;; board reads: the candidate verbalized, its current standing, and an
;;; assessment against the five admission gates.  Gates 1-2 are machine-
;;; checkable and auto-filled; gates 3-5 (terminating / general / non-
;;; redundant) are judgment and left for the board to rule on.
(define (pss-letter name)
  (let ((thm (hash-table-ref/default *theorem-table* name #f)))
    (if (not thm)
        (begin (display "No result named `") (display name)
               (display "' is installed.\n"))
        (let* ((prov   (provenance-of name))
               (w      (warrant-of name))
               (member? (memq name *support-theorem-names*))
               (inert?  (assq name *inert-macetes*))
               ;; gate 1: TRUE -- proven, or asserted-with-a-warrant.
               (g1 (or (eq? prov 'proven) (eq? prov 'primitive)
                       (eq? prov 'definitional) w))
               ;; gate 2: SOUND as an auto-firing rewrite -- not S-10 inert.
               (g2 (not inert?)))
          (display "================================================\n")
          (display "RE: PSS membership of `") (display name) (display "'\n")
          (display "================================================\n\n")
          (display "Statement (read aloud):\n  ")
          (display (english-of name)) (newline) (newline)
          (display "Current standing:\n")
          (display "  provenance : ") (display prov)
          (display (if (eq? prov 'asserted) "  (assumed)" "")) (newline)
          (display "  warrant    : ") (display (if w (car w) 'NONE))
          (when w (display " -- ") (display (cdr w))) (newline)
          (display "  in PSS now : ") (display (if member? "yes (sitting member)" "no (candidate)"))
          (newline) (newline)
          (display "Admission gates:\n")
          (display "  [") (display (if g1 "PASS" "FAIL"))
          (display "] 1. True -- proven or warranted")
          (display (if g1 "" "  <-- no proof, no warrant")) (newline)
          (display "  [") (display (if g2 "PASS" "FAIL"))
          (display "] 2. Sound rewrite -- not S-10 inert")
          (display (if g2 "" "  <-- macete form unsound; admit named-only at most")) (newline)
          (display "  [board] 3. Terminating -- oriented, won't loop when fired\n")
          (display "  [board] 4. General -- reused across proofs, not a one-off\n")
          (display "  [board] 5. Non-redundant -- not subsumed by an existing entry\n")
          (newline)
          (display "Recommendation: ")
          (cond
            ((and member? (not g1))
             (display "SITTING MEMBER, but carries no warrant -- please\n")
             (display "  supply one (or a proof) to clear gate 1.\n"))
            ((not g1)
             (display "HOLD -- give it a warrant or a proof first (gate 1).\n"))
            ((not g2)
             (display "DECLINE as an auto-firing rule (gate 2 fails); it may\n")
             (display "  still be cited by name.\n"))
            (member?
             (display "CLEARED on gates 1-2; sitting member in good standing.\n"))
            (else
             (display "CLEARED on gates 1-2; board to rule on 3-5.\n")))))))
