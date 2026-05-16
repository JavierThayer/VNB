;;; axioms.scm -- axioms not yet derivable from primitive inferences
;;;
;;; These were listed as "pending" in the manual.  The ones installed here
;;; can be stated in first-order VNB without new expression primitives.
;;;
;;; D-7 SCHEMA characterizations (REVIEW.md D-7) — NOW INSTALLED as kernel
;;; rules in primitive-inferences.scm rather than first-order axioms,
;;; because the body formula `p`/`body` is genuinely a schema variable
;;; that can't appear cleanly in a FOL axiom:
;;;   separation             -> pi-sep-sethood!, pi-sep-mem-intro!, pi-sep-mem-elim!
;;;   comp-membership        -> pi-comp-mem-intro!, pi-comp-mem-elim!
;;;   iota-def               -> pi-iota-def!
;;;   lambda-type            -> pi-lambda-type!
;;;   lambda-beta            -> pi-lambda-beta!
;;; The 2-arg POWER head gets a definitional axiom (power-exp) below:
;;;   POWER(A, B) = FUN(B, A)   -- i.e. A^B = functions B -> A
;;;   (matching `power(2,3) = 2^3 = 8` in the arithmetic evaluator).
;;;
;;; Still pending (require new primitives or schema-level handling):
;;;   equality-substitution  -- substitution schema; needs a primitive inference
;;;   union-set              -- needs UNION-SET (big union) expression primitive
;;;   union-set-membership   -- same
;;;   infinity               -- needs careful set-theoretic statement
;;;   tuples-induction       -- induction schema; needs a primitive inference
;;;   prepend/length-recursive -- needs PREPEND expression primitive

;;; -----------------------------------------------------------------------
;;; Equality
;;;
;;; DERIVED (REVIEW.md R-5): equality-symmetry and equality-transitivity
;;; are derivable from reflexivity (= a a) plus Leibniz substitution
;;; (eq-subst-membership generalizes to arbitrary contexts).  Retained
;;; as named axioms for direct use; eventually demote to proven lemmas.

(theory-add-axiom! *current-theory* 'equality-symmetry
  '(FORALL a (FORALL b
      (IMPLIES (= a b) (= b a)))))

(theory-add-axiom! *current-theory* 'equality-transitivity
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (= a b) (= b c)) (= a c))))))

;;; -----------------------------------------------------------------------
;;; Quasi-equality
;;;
;;; (== a b) holds when a and b are both undefined, or both defined and equal.
;;; When a is defined (= a a is provable) quasi-equality coincides with =.

(theory-add-axiom! *current-theory* 'quasi-eq-reflexivity
  '(FORALL a (== a a)))

(theory-add-axiom! *current-theory* 'quasi-eq-symmetry
  '(FORALL a (FORALL b
      (IMPLIES (== a b) (== b a)))))

(theory-add-axiom! *current-theory* 'quasi-eq-transitivity
  '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (== a b) (== b c)) (== a c))))))

(theory-add-axiom! *current-theory* 'quasi-eq-def
  '(FORALL a (FORALL b
      (IMPLIES (= a a)
               (IFF (== a b) (= a b))))))

;;; -----------------------------------------------------------------------
;;; FUN: derived typing rule
;;;
;;; fun-apply-type: f ∈ FUN(A,B) ∧ x ∈ A ⟹ f(x) ∈ B
;;; DERIVED (REVIEW.md R-7) from fun-codomain-iff (theory.scm):
;;;   IFF (IN f (FUN A B)) (AND (IN f (FUN A)) (FORALL x (IMPLIES (IN x A) (IN (f x) B))))
;;; — the right conjunct of the IFF, instantiated and applied.  Retained
;;; as a named axiom for direct use.

(theory-add-axiom! *current-theory* 'fun-apply-type
  '(FORALL f (FORALL A (FORALL B (FORALL x
      (IMPLIES (AND (IN f (FUN A B)) (IN x A))
               (IN (f x) B)))))))

;;; -----------------------------------------------------------------------
;;; Equality substitution for membership
;;;
;;; If a = b and b ∈ S then a ∈ S.
;;; DERIVED (REVIEW.md R-6): instance of Leibniz substitution with the
;;; predicate λx. (IN x S).  Retained as a named axiom for direct use
;;; in proofs of structural equalities.

(theory-add-axiom! *current-theory* 'eq-subst-membership
  '(FORALL a (FORALL b (FORALL S
      (IMPLIES (AND (= a b) (IN b S))
               (IN a S))))))

;;; -----------------------------------------------------------------------
;;; List sethood
;;;
;;; Every element of TUPLES(A) is a set when A is a set.
;;; DERIVED (REVIEW.md R-8): immediate from membership-implies-sethood
;;; — anything that is a member of any class is a set.  Retained as a named
;;; axiom for direct use in structure instance proofs.

(theory-add-axiom! *current-theory* 'list-sethood
  '(FORALL A (FORALL L
      (IMPLIES (AND (IN A SET) (IN L (TUPLES A)))
               (IN L SET)))))

;;; -----------------------------------------------------------------------
;;; D-7: 2-arg POWER as function-space exponentiation
;;;
;;; (POWER A B) is the class A^B of functions B -> A.  Cardinally,
;;; |A^B| = |A|^|B|, matching the arithmetic evaluator's convention
;;; (power 2 3) = 8 (functions from a 3-set to a 2-set).
;;;
;;; This is a definitional equality.  Sethood follows from fun-set-iff;
;;; membership iff follows from fun-codomain-iff.

(theory-add-axiom! *current-theory* 'power-exp
  '(FORALL A (FORALL B
      (= (POWER A B) (FUN B A)))))
