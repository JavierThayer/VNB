;;; sequences.scm -- PROD-ORD, SUM, SUM-AG: products and sums over initial NN-segments
;;;
;;; PROD-ORD(m, f, n)  =  f(0) * f(1) * ... * f(n-1)  in monoid m
;;; SUM(r, f, n)       =  f(0) + f(1) + ... + f(n-1)  in ring r
;;; SUM-AG(ag, f, n)   =  f(0) * f(1) * ... * f(n-1)  in abelian group ag
;;;
;;; All three are defined by primitive recursion on the last argument n.
;;; The defining axioms (<name>-zero, <name>-succ) are installed by
;;; def-by-nn-recursion; further axioms are installed explicitly below.
;;;
;;; SUM-AG and SUM are formally independent because GROUP (and hence
;;; ABELIAN-GROUP) and MONOID have different shapes (4 slots vs 3).
;;; A future bridge could express "additive group of a ring is an abelian
;;; group" to transfer permutation-invariance from SUM-AG back to SUM.
;;;
;;; Dependencies: monoid.scm, group.scm, abelian-group.scm, ring.scm,
;;;               number-systems.scm (NN).

;;; -----------------------------------------------------------------------
;;; PROD-ORD: monoid product over {0, ..., n-1}

;;; Defining recursion (installs prod-ord-zero and prod-ord-succ):
;;;   PROD-ORD(m, f, 0)       = IDEN(m)
;;;   PROD-ORD(m, f, succ(n)) = PROD-ORD(m, f, n) * f(n)

(def-by-nn-recursion 'PROD-ORD '(m f)
  '(IDEN m)                              ; base value
  '(n val)                            ; step vars: n ∈ NN, val = PROD-ORD(m,f,n)
  '((OPR m) val (f n))); PROD-ORD(m,f,succ n) = val * f(n)

;;; Type: result is in the carrier when m is a monoid and f maps NN into it.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from prod-ord-zero,
;;; prod-ord-succ, monoid-left-id, and monoid-carrier-closed-opr.  Installed
;;; as an axiom for direct use; eventually demote to a proven lemma.
(add-axiom! *library* 'prod-ord-type
  '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR m)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (PROD-ORD m f n) (CARR m)))))))))

;;; Singleton: PROD-ORD(m, f, 1) = f(0).
;;; DERIVED (REVIEW.md R-10): prod-ord-succ at n=0 gives
;;; (OPR m)(IDEN m)(f 0), then monoid-left-id closes to (f 0).  Installed
;;; as an axiom for direct use.
(add-axiom! *library* 'prod-ord-singleton
  '(FORALL m
      (IMPLIES (IS-MONOID m)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR m)))
                          (= (PROD-ORD m f 1) (f 0)))))))

;;; -----------------------------------------------------------------------
;;; SUM: ring summation over {0, ..., n-1}
;;;
;;; SUM is the special case of PROD-ORD for the additive monoid of a ring:
;;;   MUL  ->  ADD(r)
;;;   E    ->  ZERO(r)
;;; Defined independently to avoid introducing an explicit ADD-MONOID record.

;;; Defining recursion (installs sum-zero and sum-succ):
;;;   SUM(r, f, 0)       = ZERO(r)
;;;   SUM(r, f, succ(n)) = SUM(r, f, n) + f(n)

(def-by-nn-recursion 'SUM '(r f)
  '(ZERO r)                           ; base value
  '(n val)                            ; step vars
  '((ADD r) val (f n))); SUM(r,f,succ n) = val + f(n)

;;; Type: result is in the carrier.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from sum-zero, sum-succ,
;;; ring-zero-in, and ring-carrier-closed-add.  Installed for direct use.
(add-axiom! *library* 'sum-type
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR r)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (SUM r f n) (CARR r)))))))))

;;; Singleton: SUM(r, f, 1) = f(0).
;;; DERIVED (REVIEW.md R-10): sum-succ at n=0 gives (ADD r)(ZERO r)(f 0),
;;; then a ring's left-zero-add identity closes to (f 0).  Installed for direct use.
(add-axiom! *library* 'sum-singleton
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR r)))
                          (= (SUM r f 1) (f 0)))))))

;;; -----------------------------------------------------------------------
;;; SUM-AG: abelian-group "summation" over {0, ..., n-1}
;;;
;;; Written multiplicatively because ABELIAN-GROUP uses MUL/E (inherited
;;; from GROUP's accessors).  When the abelian group is the additive group
;;; of some structure, the caller reads (OPR ag) as "addition" and (IDEN ag)
;;; as "zero" by convention; nothing in the structure machinery cares.
;;;
;;; Defining recursion (installs sum-ag-zero and sum-ag-succ):
;;;   SUM-AG(ag, f, 0)       = IDEN(ag)
;;;   SUM-AG(ag, f, succ(n)) = (OPR ag)(SUM-AG ag f n, f(n))

(def-by-nn-recursion 'SUM-AG '(ag f)
  '(IDEN ag)                              ; base value
  '(n val)                             ; step vars
  '((OPR ag) val (f n))); SUM-AG(ag,f,succ n) = val * f(n)

;;; Type: result is in the carrier.
;;; Provable by NN induction from sum-ag-zero, sum-ag-succ, and the
;;; carrier-closure of MUL (via abelian-group-is-group + group-IFF +
;;; fun-apply-type).  Installed for direct use; eventually demote.
;;; sum-ag-type MOVED 2026-09-15 (wave 6) to theorem-library/finsum-type-proof.scm, where it is PROVEN modulo 0.  It was an axiom with NO warrant at all.

;;; Singleton: SUM-AG(ag, f, 1) = f(0).
;;; Provable from sum-ag-succ at n=0 + sum-ag-zero + group-left-id
;;; (imported via abelian-group-is-group).  Installed for direct use.
(add-axiom! *library* 'sum-ag-singleton
  '(FORALL ag
      (IMPLIES (IS-ABELIAN-GROUP ag)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR ag)))
                          (= (SUM-AG ag f 1) (f 0)))))))

;;; SUM-AG <-> REDUCE bridge (n >= 1).
;;;
;;;   SUM-AG(ag, f, n) = REDUCE (OPR ag) f n        for n >= 1
;;;
;;; The n = 0 case has no REDUCE counterpart: SUM-AG(ag, f, 0) = IDEN(ag) is
;;; the identity supplied by the abelian-group, and REDUCE has no identity
;;; argument.  Provable by NN induction (base n = 1 from sum-ag-singleton +
;;; reduce-one; step from sum-ag-succ + reduce-succ); installed for direct
;;; use in the library-build phase.  This is the seam where finite-sum
;;; machinery meets the kiddie-routed REDUCE bridges in numeric-instances.
(add-axiom! *library* 'sum-ag-as-reduce
  '(FORALL ag
      (IMPLIES (IS-ABELIAN-GROUP ag)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR ag)))
                          (FORALL n
                            (IMPLIES (AND (IN n NN) (<= 1 n))
                                     (= (SUM-AG ag f n)
                                        (REDUCE (OPR ag) f n)))))))))

;;; -----------------------------------------------------------------------
;;; RING-PROD-N: n-fold ring product
;;;
;;; RING-PROD-N(f, n) = f(0) × f(1) × ... × f(n-1)  as a ring.
;;; Defined by primitive recursion on n using RING-PROD and ZERO-RING.
;;;
;;; The 0-fold product is ZERO-RING (the terminal ring, identity for ×
;;; up to isomorphism).  Each step wraps the accumulated product with
;;; the next ring in the sequence.
;;;
;;; (REVIEW.md G-6) When the hypothesis "all f(i) are rings" fails, the
;;; resulting term is still a syntactically well-formed 6-LIST whose
;;; components may be junk.  Soundness is preserved because the typing
;;; claim ring-prod-n-is-ring then simply doesn't apply (its IS-RING
;;; antecedent is false), so no false ring identity can be derived from
;;; the junk.  Users should not destructure RING-PROD-N(f, n) without
;;; first proving the hypothesis.
;;;
;;; Dependencies: algebraic.scm (RING-PROD, ZERO-RING, IS-RING).

(def-by-nn-recursion 'RING-PROD-N '(f)
  'ZERO-RING                           ; base: RING-PROD-N(f, 0) = ZERO-RING
  '(n val)                             ; step vars
  '(RING-PROD val (f n))) ; RING-PROD-N(f, succ n) = RING-PROD(val, f(n))

;;; Typing: all f(i) are rings → RING-PROD-N(f, n) is a ring.
;;; DERIVED (REVIEW.md R-9): provable by NN induction from ring-prod-is-ring
;;; (step) + zero-ring-is-ring (base).  Installed as an axiom for direct use.
(add-axiom! *library* 'ring-prod-n-is-ring
  '(FORALL f
      (FORALL n (IMPLIES (IN n NN)
        (IMPLIES (FORALL i (IMPLIES (IN i NN) (IS-RING (f i))))
          (IS-RING (RING-PROD-N f n)))))))

;;; Linearity (left scalar pull-out):
;;; SUM(r, lambda i. a * f(i), n) = a * SUM(r, f, n)
;;; Stated schematically for inline use (derivable by induction + distributivity).
;;; The VNB-LAMBDA form below uses the built-in lambda binder.
(add-axiom! *library* 'sum-left-scalar
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL a
                 (IMPLIES (IN a (CARR r))
                          (FORALL f
                            (IMPLIES (IN f (FUN NN (CARR r)))
                                     (FORALL n
                                       (IMPLIES (IN n NN)
                                         (= (SUM r (VNB-LAMBDA i NN ((MUL r) a (f i))) n)
                                            ((MUL r) a (SUM r f n))))))))))))

;;; -----------------------------------------------------------------------
;;; SUM-SET: sum over a finite set, in a ring (notes-16 step 2)
;;;
;;;   SUM-SET(r, S, f)  =  sum_{x in S} f(x)  in ring r
;;;
;;; The additive monoid of a ring is commutative (ring-add-comm), so the
;;; value depends only on the set S of indices, not on any enumeration.
;;; Axiomatised by empty + singleton + disjoint-union; well-defined because
;;; the disjoint-union axiom is symmetric in S1, S2.

;;; sum-set-empty RETIRED 2026-09-18 (the user's decision B): SUM-SET is DEFINED as FINSUM (end of structure-library/finsum.scm) and this law is a theorem of theorem-library/rake-sum-set-defined.scm

;;; sum-set-singleton RETIRED 2026-09-18 (the user's decision B): SUM-SET is DEFINED as FINSUM (end of structure-library/finsum.scm) and this law is a theorem of theorem-library/rake-sum-set-defined.scm

;;; Disjoint-union: S1 cap S2 = empty => sum over S1 cup S2 splits additively.
;;;
;;; RELAXED 2026-09-18 (the user's decision): f is typed on any SUPERSET X of the
;;; union, which is how sum-set-type below is stated.  The earlier form demanded
;;; (IN f (FUN (UNION S1 S2) (CARR r))) -- the exact union as the domain -- so a
;;; finite-set induction whose f is typed on a fixed S could never consume the split
;;; of a subset T u {x} of S; and SUM-SET has no congruence or restriction law that
;;; would move f onto the smaller domain.  That blocked sum-set-left-scalar and
;;; sum-set-right-scalar (rake batch 5, V).  The relaxed form implies the old one at
;;; X := (UNION S1 S2).  No proof in the tree cited the old form.
;;; sum-set-disjoint-union RETIRED 2026-09-18 (the user's decision B): SUM-SET is DEFINED as FINSUM (end of structure-library/finsum.scm) and this law is a theorem of theorem-library/rake-sum-set-defined.scm

;;; Type: result is in the carrier whenever f is defined on a superset of S
;;; with values in CARR(r).  Stated with an explicit superset X to keep the
;;; disjoint-union axiom usable (where f's typing is on UNION(S1, S2) but
;;; the RHS uses sums over S1, S2).
;;; sum-set-type RETIRED 2026-09-18 (the user's decision B): SUM-SET is DEFINED as FINSUM (end of structure-library/finsum.scm) and this law is a theorem of theorem-library/rake-sum-set-defined.scm

;;; Scalar pull-out for finite sums (PSS-promoted 2026-05-27):
;;;   a · (sum_{x ∈ X} f(x))      = sum_{x ∈ X} a · f(x)
;;;   (sum_{x ∈ X} f(x)) · b      = sum_{x ∈ X} f(x) · b
;;; The two laws are separate because the ring may be non-commutative.
;;; See theorem-library/sum-set-left-scalar.scm and
;;; theorem-library/sum-set-right-scalar.scm.

;;; -----------------------------------------------------------------------
;;; PROD-SET: product over a finite set, in a commutative monoid
;;; (notes-16 step 2)
;;;
;;;   PROD-SET(cm, S, f)  =  prod_{x in S} f(x)  in commutative monoid cm
;;;
;;; Mirrors SUM-SET; well-definedness rests on comm-monoid-opr-comm.
;;; PROD-ORD covers the NN-indexed case; PROD-SET extends to arbitrary
;;; finite sets when MUL is commutative.

;;; PROD-SET IS DEFINED since 2026-09-19 (the user's decision):
;;;   (def-functoid 'PROD-SET '(cm S f) '(FINSUM cm f S))      structure-library/finprod.scm
;;; The four axioms that stood here (prod-set-empty, -singleton, -disjoint-union, -type;
;;; nothing in the tree cited them) are THEOREMS of that definition, proven `modulo 0' in
;;; theorem-library/rake-prod-set-defined.scm: `prod-set-empty' with its statement
;;; unchanged; `prod-set-singleton-defined' (adds x in SET and the pointwise typing
;;; f(x) in CARR cm: the axiom's strict `=' asserted that f(x) denotes for arbitrary f);
;;; `prod-set-type-defined' and `prod-set-disjoint-union-defined' (add CARD S in NN: for
;;; an infinite index set the fold is uninterpreted).
