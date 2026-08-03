;;; equality-basics.scm -- eq-sym, eq-trans, neq-sym, PROVEN.
;;;
;;; These three were asserted supports in order-lemmas.scm, and between them
;;; they are cited by about a hundred bills -- eq-sym alone by 52, which makes
;;; it the fourth-largest keystone in the library.
;;;
;;; None of them is mathematics.  The base theory ALREADY HAS symmetry and
;;; transitivity of partial equality, as `primitive' axioms in
;;; theorem-library/axioms.scm:
;;;
;;;     equality-symmetry       a = b  =>  b = a
;;;     equality-transitivity   (a = b AND b = c)  =>  a = c
;;;
;;; `eq-sym' is character-for-character `equality-symmetry'.  It was an asserted
;;; DUPLICATE of a fact the theory has for free, and 52 proofs paid debt for it.
;;; `eq-trans' is the CURRIED form of `equality-transitivity' -- which is why it
;;; exists at all: `fact' detaches antecedents one at a time and will not split
;;; a conjunction, so the AND-antecedent form is unusable forward.  That is a
;;; real need, but it is a five-line derivation and not an assumption.
;;;
;;; The lesson generalises past these three: an audit for "asserted facts that
;;; duplicate a PROVEN theorem" was run earlier and reported zero, because it
;;; compared only against `proven'.  Facts duplicating a `primitive' or
;;; `definitional' one were invisible to it.  That is where eq-sym was hiding.

;;; ---- eq-sym: literally the primitive axiom ----------------------------
(sp (make-wff '(FORALL a (FORALL b (IMPLIES (= a b) (= b a))))))
(di) (di) (di)
(fact 'equality-symmetry 'a 'b)
(ass)
(qed 'eq-sym)
(category! 'eq-sym 'plumbing)

;;; ---- eq-trans: the curried form of the primitive ----------------------
(sp (make-wff '(FORALL a (FORALL b (FORALL c
   (IMPLIES (= a b) (IMPLIES (= b c) (= a c))))))))
(di) (di) (di) (di) (di)
(have! '(AND (= a b) (= b c)))
(fact 'equality-transitivity 'a 'b 'c)
(ass)
(qed 'eq-trans)
(category! 'eq-trans 'plumbing)

;;; ---- neq-sym: symmetry of disequality, by contradiction ---------------
(sp (make-wff '(FORALL a (FORALL b (IMPLIES (NOT (= a b)) (NOT (= b a)))))))
(di) (di) (di)
(di)                                    ; goal is a NOT: assume (= b a), goal FALSITY
(fact 'equality-symmetry 'b 'a)         ; -> (= a b)
(ai '(NOT (= a b)))
(qed 'neq-sym)
(category! 'neq-sym 'plumbing)
