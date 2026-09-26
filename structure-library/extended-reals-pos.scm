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

(add-axiom! *library* 'rr-pos-star-membership
  '(FORALL x
      (IFF (IN x RR-POS-STAR)
           (OR (AND (IN x RR) (<= 0 x))
               (= x POS-INF)))))

;;; RR-POS-STAR sits inside RR-STAR (nonneg reals are reals; POS-INF is in RR-STAR).
;;; rr-pos-star-subset-rr-star RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

;;; The endpoints are in RR-POS-STAR.
;;; zero-in-rr-pos-star RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

;;; pos-inf-in-rr-pos-star RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

;;; NEG-INF is NOT in RR-POS-STAR (it lies below 0).
;;; neg-inf-not-in-rr-pos-star RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

;;; -----------------------------------------------------------------------
;;; Order: 0 is the least element, POS-INF the greatest.

;;; 0 is the bottom: every element of RR-POS-STAR is >= 0.
;;; rr-pos-star-nonneg RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

;;; POS-INF is the top: every element of RR-POS-STAR is <= POS-INF.
;;; rr-pos-star-below-pos-inf RETIRED 2026-09-18 (rake batch 5c): proven in theorem-library/rake-rr-pos-star.scm

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

;;; ESUP, DEFINED (2026-09-19, the user's decision; rake batch 6-B).  Until then ESUP was a
;;; bare head characterised by four axioms (esup-in, esup-upper, esup-least, esup-empty).
;;; It is now the DESCRIPTION of the least upper bound, and the four are THEOREMS with
;;; their statements unchanged (theorem-library/rake-esup-defined.scm), from
;;;   esup-exists   every subset of RR-POS-STAR has a least upper bound in RR-POS-STAR
;;;                 (cases: not bounded above in RR -> POS-INF; bounded and inhabited ->
;;;                 the real SUP, by the primitive completeness of RR; empty -> 0),
;;;   esup-unique   by antisymmetry of <= on RR-POS-STAR,
;;;   esup-prop     the defining property, by `iota-d'.
;;; The inner binders are `x' and `b', the binders of esup-upper and esup-least, so the two
;;; laws are the description's conjuncts literally.
(def-functoid 'ESUP '(s_)
  '(IOTA bb_ (AND (IN bb_ RR-POS-STAR)
               (AND (FORALL x (IMPLIES (IN x s_) (<= x bb_)))
                    (FORALL b (IMPLIES (AND (IN b RR-POS-STAR)
                                            (FORALL x (IMPLIES (IN x s_) (<= x b))))
                                 (<= bb_ b)))))))
(notation! 'ESUP 'kind 'functoid 'arity 1
           'english "the least upper bound in [0,+inf] of $1")

;;; -----------------------------------------------------------------------
;;; Extended addition `eplus' : RR-POS-STAR x RR-POS-STAR -> RR-POS-STAR
;;;
;;; Total on [0,+inf] -- this is the whole reason for working in RR-POS-STAR rather
;;; than RR-STAR: there is no inf - inf indeterminacy to dodge.  (Until 2026-09-18 it
;;; was "defined like the polymorphic operators of numeric-instances.scm: a constant
;;; pinned by apply axioms + a typing axiom, rather than a VNB-LAMBDA".  Those axioms
;;; were inconsistent; it IS a VNB-LAMBDA now -- see `eplus-def' below.)  Three
;;; exhaustive, non-overlapping cases (POS-INF is not a real, so the finite case and
;;; the infinite cases never collide; the finite case is for NONNEGATIVE reals):
;;;
;;;   both finite reals:   eplus(x, y) = binplus(x, y)   (= x + y)
;;;   left infinite:       eplus(POS-INF, y) = POS-INF
;;;   right infinite:      eplus(x, POS-INF) = POS-INF

;;; Finite case: on the reals, eplus agrees with ordinary addition.
;;; eplus-real RETIRED 2026-09-18: the four EPLUS axioms were jointly INCONSISTENT (scratchpad/r7v/r7v-p3.scm); EPLUS is now DEFINED (eplus-def below) and this law is proven in theorem-library/rake-eplus-defined.scm

;;; Left-absorbing: POS-INF + anything in RR-POS-STAR is POS-INF.
;;; eplus-pos-inf-left RETIRED 2026-09-18: the four EPLUS axioms were jointly INCONSISTENT (scratchpad/r7v/r7v-p3.scm); EPLUS is now DEFINED (eplus-def below) and this law is proven in theorem-library/rake-eplus-defined.scm

;;; Right-absorbing: anything in RR-POS-STAR + POS-INF is POS-INF.
;;; eplus-pos-inf-right RETIRED 2026-09-18: the four EPLUS axioms were jointly INCONSISTENT (scratchpad/r7v/r7v-p3.scm); EPLUS is now DEFINED (eplus-def below) and this law is proven in theorem-library/rake-eplus-defined.scm

;;; Closure / totality: eplus maps RR-POS-STAR x RR-POS-STAR into RR-POS-STAR.
;;; eplus-in-fun RETIRED 2026-09-18: the four EPLUS axioms were jointly INCONSISTENT (scratchpad/r7v/r7v-p3.scm); EPLUS is now DEFINED (eplus-def below) and this law is proven in theorem-library/rake-eplus-defined.scm
;;;
;;; EPLUS, DEFINED (2026-09-18, rake batch 5c-V).  Until today eplus was a bare constant
;;; pinned by three case equations and a typing axiom, and the four were jointly
;;; INCONSISTENT: `eplus-real' concluded a strict `=' for ALL reals, so it asserted that
;;; eplus(x,0) denotes for every real x, while `eplus-in-fun' made eplus a function
;;; defined exactly on [0,+oo] x [0,+oo]; so every real was in [0,+oo], hence >= 0, and
;;; at -1 the oracle closed 1 < 1 (probe: scratchpad/r7v/r7v-p3.scm).  The definition
;;; below is a quasi-equation naming a lambda; every law is a THEOREM of it
;;; (theorem-library/rake-eplus-defined.scm): eplus-in-fun, eplus-pos-inf-left and
;;; eplus-pos-inf-right with their statements unchanged, and `eplus-real-defined', which
;;; carries the guards 0 <= x, 0 <= y that the old axiom lacked.
;;; NOT def-constant: eplus is already registered (EPLUS is in *wff-term-form-heads*).
(declare-named-only! 'eplus-def
  "left-hand side is a bare constant: as a live rewrite it would turn every mention of eplus into its lambda")
(fluid-let ((*current-provenance* 'definitional))
  (add-axiom! *library* 'eplus-def
    '(== eplus
         (VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR-POS-STAR RR-POS-STAR)
           (IF (OR (= x_ POS-INF) (= y_ POS-INF))
               POS-INF
               (binplus x_ y_))))))

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

;;; A `declare-instance!' since 2026-09-19 (the shape NN-ADD-MONOID has in
;;; numeric-instances.scm): the equation rr-pos-star-add-monoid-def keeps its name and its
;;; statement, becomes `definitional', and the slot macetes @CARR / @OPR / @IDEN exist.  It
;;; was a bare `add-axiom!' carrying a `well-known' warrant, and sat on three bills.
(declare-instance! 'RR-POS-STAR-ADD-MONOID 'COMM-MONOID 'rr-pos-star-add-monoid-def
  '(RR-POS-STAR eplus 0))

;;; rr-pos-star-is-comm-monoid RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-rr-pos-star-monoid.scm



;;; -----------------------------------------------------------------------
;;; The carrier facts and the EPLUS laws that were warranted here on 2026-09-18 are
;;; THEOREMS since the same evening (theorem-library/rake-rr-pos-star.scm,
;;; rake-eplus-defined.scm).  NOTHING is asserted in this file since 2026-09-19: ESUP is
;;; defined, the monoid is a declared instance, and its comm-monoid law is proven
;;; (theorem-library/rake-rr-pos-star-monoid.scm).
