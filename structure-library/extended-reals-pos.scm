;;; extended-reals-pos.scm -- RR-POS-STAR = [0, +inf], the nonnegative extended reals
;;;
;;; The order-complete object underlying unordered summation and monotone
;;; convergence.  Built on extended-reals.scm: RR-POS-STAR is carved out of RR-STAR as
;;; the nonnegative part together with POS-INF (the existing opaque top of
;;; RR-STAR; deliberately NOT identified with any ordinal -- see the
;;; representation-independence discipline).  The order <= is inherited from
;;; RR-STAR unchanged.
;;;
;;; Why RR-POS-STAR and not RR-STAR: on [0,+inf] addition is TOTAL and well-behaved
;;; (a + inf = inf; no inf - inf indeterminacy), and the order is COMPLETE --
;;; every subset has a supremum, with inf on top making boundedness
;;; automatic.  That order-completeness (ESUP below) is what powers both
;;; monotone convergence in RR-POS-STAR and the total RR-POS-STAR summation operator
;;; (sup of finite partial sums).
;;;
;;; This file provides the carrier, its order facts, the supremum ESUP with
;;; its order-completeness axioms, and -- since it is total on [0,+inf] --
;;; the extended addition `eplus' together with RR-POS-STAR as a commutative monoid
;;; RR-POS-STAR-ADD-MONOID.  The unordered RR-POS-STAR summation operator (ESUP over finite
;;; partial sums) is built on top of these in a later step.
;;;
;;; Dependencies: extended-reals.scm (RR-STAR, POS-INF, NEG-INF, the bounds),
;;; number-systems.scm (RR, <=, 0), numeric-instances.scm (binplus),
;;; monoid.scm (COMM-MONOID), set primitives (SUBSET, EMPTY-SET).
;;;
;;; Note: this class was called RR+* until 2026-08-24.  The `+' and `*' are
;;; operator characters, so the VNB tokenizer split the name into three tokens
;;; and "x in rr+*" was a parse error.  It is now RR-POS-STAR -- the spelling
;;; every axiom below already used (rr-pos-star-membership, ...) -- and the
;;; monoid is RR-POS-STAR-ADD-MONOID.  Same repair as RR-STAR in
;;; extended-reals.scm.

;;; -----------------------------------------------------------------------
;;; Carrier
;;;
;;; x in RR-POS-STAR iff x is a nonnegative real, or x = POS-INF.

(theory-add-axiom! *current-theory* 'rr-pos-star-membership
  '(FORALL x
      (IFF (IN x RR-POS-STAR)
           (OR (AND (IN x RR) (<= 0 x))
               (= x POS-INF)))))

;;; RR-POS-STAR sits inside RR-STAR (nonneg reals are reals; POS-INF is in RR-STAR).
(theory-add-axiom! *current-theory* 'rr-pos-star-subset-rr-star
  '(SUBSET RR-POS-STAR RR-STAR))

;;; The endpoints are in RR-POS-STAR.
(theory-add-axiom! *current-theory* 'zero-in-rr-pos-star
  '(IN 0 RR-POS-STAR))

(theory-add-axiom! *current-theory* 'pos-inf-in-rr-pos-star
  '(IN POS-INF RR-POS-STAR))

;;; NEG-INF is NOT in RR-POS-STAR (it lies below 0).
(theory-add-axiom! *current-theory* 'neg-inf-not-in-rr-pos-star
  '(NOT (IN NEG-INF RR-POS-STAR)))

;;; -----------------------------------------------------------------------
;;; Order: 0 is the least element, POS-INF the greatest.

;;; 0 is the bottom: every element of RR-POS-STAR is >= 0.
(theory-add-axiom! *current-theory* 'rr-pos-star-nonneg
  '(FORALL x (IMPLIES (IN x RR-POS-STAR) (<= 0 x))))

;;; POS-INF is the top: every element of RR-POS-STAR is <= POS-INF.
(theory-add-axiom! *current-theory* 'rr-pos-star-below-pos-inf
  '(FORALL x (IMPLIES (IN x RR-POS-STAR) (<= x POS-INF))))

;;; -----------------------------------------------------------------------
;;; Order-completeness: the supremum operator ESUP
;;;
;;; For any subset S of RR-POS-STAR, ESUP(S) is the least upper bound of S in RR-POS-STAR.
;;; Because POS-INF tops RR-POS-STAR, EVERY subset is bounded, so ESUP(S) always
;;; exists -- this IS the order-completeness of RR-POS-STAR.  The pattern mirrors
;;; SUP-ORD on the ordinals (ordinals.scm): an `in', an `upper', and a
;;; `least' axiom, plus the empty case.
;;;
;;; Uniqueness of the lub is not asserted separately -- it follows from
;;; antisymmetry of <= (esup-upper + esup-least pin ESUP(S) between any two
;;; candidate lubs).
;;;
;;; Monotone convergence falls straight out: for an increasing sequence
;;; f : NN -> RR-POS-STAR, ESUP(IMAGE f) is its least upper bound, i.e. its limit.

;;; ESUP(S) is in RR-POS-STAR.
(theory-add-axiom! *current-theory* 'esup-in
  '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
       (IN (ESUP S) RR-POS-STAR))))

;;; ESUP(S) is an upper bound of S.
(theory-add-axiom! *current-theory* 'esup-upper
  '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
       (FORALL x (IMPLIES (IN x S)
         (<= x (ESUP S)))))))

;;; ESUP(S) is the LEAST upper bound: it lies below any other upper bound b
;;; that is itself in RR-POS-STAR.
(theory-add-axiom! *current-theory* 'esup-least
  '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
       (FORALL b (IMPLIES (AND (IN b RR-POS-STAR)
                               (FORALL x (IMPLIES (IN x S) (<= x b))))
         (<= (ESUP S) b))))))

;;; The empty sup is 0 (the bottom of RR-POS-STAR) -- this is the empty unordered
;;; sum, so summation will inherit the right empty value.
(theory-add-axiom! *current-theory* 'esup-empty
  '(= (ESUP EMPTY-SET) 0))

;;; -----------------------------------------------------------------------
;;; Extended addition `eplus' : RR-POS-STAR x RR-POS-STAR -> RR-POS-STAR
;;;
;;; Total on [0,+inf] -- this is the whole reason for working in RR-POS-STAR rather
;;; than RR-STAR: there is no inf - inf indeterminacy to dodge.  Defined like the
;;; polymorphic operators of numeric-instances.scm: a constant operation
;;; symbol pinned by apply axioms + a typing (closure) axiom, rather than a
;;; VNB-LAMBDA.  Three exhaustive, non-overlapping cases (POS-INF is not a
;;; real, so the finite case and the infinite cases never collide):
;;;
;;;   both finite reals:   eplus(x, y) = binplus(x, y)   (= x + y)
;;;   left infinite:       eplus(POS-INF, y) = POS-INF
;;;   right infinite:      eplus(x, POS-INF) = POS-INF

;;; Finite case: on the reals, eplus agrees with ordinary addition.
(theory-add-axiom! *current-theory* 'eplus-real
  '(FORALL x (FORALL y
     (IMPLIES (AND (IN x RR) (IN y RR))
       (= (eplus x y) (binplus x y))))))

;;; Left-absorbing: POS-INF + anything in RR-POS-STAR is POS-INF.
(theory-add-axiom! *current-theory* 'eplus-pos-inf-left
  '(FORALL y (IMPLIES (IN y RR-POS-STAR)
     (= (eplus POS-INF y) POS-INF))))

;;; Right-absorbing: anything in RR-POS-STAR + POS-INF is POS-INF.
(theory-add-axiom! *current-theory* 'eplus-pos-inf-right
  '(FORALL x (IMPLIES (IN x RR-POS-STAR)
     (= (eplus x POS-INF) POS-INF))))

;;; Closure / totality: eplus maps RR-POS-STAR x RR-POS-STAR into RR-POS-STAR.
(theory-add-axiom! *current-theory* 'eplus-in-fun
  '(IN eplus (FUN (CARTESIAN RR-POS-STAR RR-POS-STAR) RR-POS-STAR)))

;;; -----------------------------------------------------------------------
;;; RR-POS-STAR as a commutative monoid under eplus, identity 0.
;;;
;;; Mirrors NN-ADD-MONOID = [NN, binplus, 0] (numeric-instances.scm).  The
;;; commutative-monoid laws (associativity, commutativity, identity 0) are
;;; carried by IS-COMM-MONOID, taken as an axiom for the library-build phase
;;; -- all three hold for extended addition (the empty/infinite cases are
;;; absorbing, the finite case inherits RR's additive monoid).  This is the
;;; substrate the generalized comm-monoid finite-sum will run over; RR-POS-STAR has
;;; no additive inverses, so the abelian-group FINSUM does NOT apply here.

(theory-add-axiom! *current-theory* 'rr-pos-star-add-monoid-def
  '(= RR-POS-STAR-ADD-MONOID (LIST RR-POS-STAR eplus 0)))

(theory-add-axiom! *current-theory* 'rr-pos-star-is-comm-monoid
  '(IS-COMM-MONOID RR-POS-STAR-ADD-MONOID))

(warrant! 'rr-pos-star-is-comm-monoid 'well-known
  "[0,+inf] under extended addition is the standard commutative monoid of
   measure theory.  Associativity, commutativity and identity 0 hold case by
   case: on the finite reals eplus is ordinary +, which is a commutative
   monoid; any case with a POS-INF argument is absorbing on both sides, so all
   three laws collapse to POS-INF = POS-INF.  See e.g. Folland, Real Analysis,
   on the arithmetic of [0,+inf].")

(register-definitional-structure! 'RR-POS-STAR-ADD-MONOID 'COMM-MONOID)
