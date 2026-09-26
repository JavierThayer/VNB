;;; empty-cardinality.scm -- the two BACKWARD rungs for "this set is empty, so
;;; its cardinal is 0".
;;;
;;; WHY THIS FILE EXISTS.  The base case of a list-induction on cardinality
;;;
;;;     length(l) = 0, l in tuples(a)  |-  card(make-set(l)) <= 0
;;;
;;; has an obvious two-step reduction: to show card(make-set(l)) <= 0 it is
;;; enough that make-set(l) = {}, and for that it is enough that l = [] -- which
;;; is in the context, by `tuple-length-zero'.  Three moves, and none of them
;;; could be a `bc*': the library concluded `card(_) <= 0' nowhere and
;;; `make-set(_) = EMPTY-SET' nowhere, so the backchain lane fell back to the
;;; six lemmas whose conclusion matches a bare `_ <= _' -- abs-nonneg-le,
;;; nn-not-lt-le, rr-lt-implies-le and friends -- every one of which knows
;;; nothing about cardinality.  That is the lane doing its job (it ranks by what
;;; the CONCLUSION matches) against a library that was missing both rungs.
;;;
;;; Each is one `subst' away from a fact the tree already has -- `card-empty'
;;; (CARD(EMPTY-SET) = 0, primitive, structure-library/cardinality.scm) and
;;; `make-set-empty' (MAKE-SET([]) = EMPTY-SET, primitive, library.scm).  Both
;;; are PROVEN here rather than asserted, and both bill `modulo 0'.
;;;
;;; The forward step is NOT here and cannot be: getting `l = []' out of
;;; `length(l) = 0' is a citation whose relevance comes from the HYPOTHESES, not
;;; from the goal, so no amount of backchaining reaches it.  The base case is
;;; one forward move (`fact tuple-length-zero') and then these two backward.
;;;
;;; Needs: interactive + qed/proof-debt, structure-library/cardinality
;;; (card-empty).  Binders carry the trailing underscore, per the case-fold
;;; convention -- `x' and `l' are far too likely to collide.

;;; -----------------------------------------------------------------------
;;; card-empty-le:  X = {}  =>  card(X) <= 0
;;;
;;; Stated with `<=' rather than `=' because that is the shape a bound wants to
;;; backchain through; the equation is `card-empty' itself, one line above.

(sp '(FORALL x_ (IMPLIES (= x_ EMPTY-SET) (<= (CARD x_) 0))))
;; TWO di's: the first peels the FORALL, and the second the IMPLIES.  One di
;; absorbs a following implication only when it is an `IN' guard on the variable
;; just bound (peel-foralls-raw, primitive-inferences.scm); an equational
;; antecedent is not, so it needs its own call.
(di)
(di)
(subst '(= x_ EMPTY-SET))
(mac 'card-empty)
(arith)
(qed 'card-empty-le)

;;; -----------------------------------------------------------------------
;;; makeset-of-empty-tuple:  L = []  =>  make-set(L) = {}
;;;
;;; `make-set-empty' with the tuple abstracted, so it can be backchained through
;;; from a goal about make-set(L) for a VARIABLE L -- which is what the induction
;;; base actually has.  As a macete `make-set-empty' cannot fire there: it
;;; matches MAKE-SET([]) syntactically, and make-set(l) is not that until the
;;; substitution has already happened.

(sp '(FORALL l_ (IMPLIES (= l_ (LIST)) (= (MAKE-SET l_) EMPTY-SET))))
(di)
(di)
(subst '(= l_ (LIST)))
;; the goal is now make-set-empty verbatim; `ta' brings it into context as an
;; assumption -- it does NOT close the goal -- so `ass' does the closing.
(ta 'make-set-empty)
(ass)
(qed 'makeset-of-empty-tuple)

(topic! 'card-empty-le 'combinatorial)
(topic! 'makeset-of-empty-tuple 'combinatorial)
