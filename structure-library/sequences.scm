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
(theory-add-axiom! *current-theory* 'prod-ord-type
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
(theory-add-axiom! *current-theory* 'prod-ord-singleton
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
(theory-add-axiom! *current-theory* 'sum-type
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
(theory-add-axiom! *current-theory* 'sum-singleton
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
(theory-add-axiom! *current-theory* 'sum-ag-type
  '(FORALL ag
      (IMPLIES (IS-ABELIAN-GROUP ag)
               (FORALL f
                 (IMPLIES (IN f (FUN NN (CARR ag)))
                          (FORALL n
                            (IMPLIES (IN n NN)
                                     (IN (SUM-AG ag f n) (CARR ag)))))))))

;;; Singleton: SUM-AG(ag, f, 1) = f(0).
;;; Provable from sum-ag-succ at n=0 + sum-ag-zero + group-left-id
;;; (imported via abelian-group-is-group).  Installed for direct use.
(theory-add-axiom! *current-theory* 'sum-ag-singleton
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
(theory-add-axiom! *current-theory* 'sum-ag-as-reduce
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
(theory-add-axiom! *current-theory* 'ring-prod-n-is-ring
  '(FORALL f
      (FORALL n (IMPLIES (IN n NN)
        (IMPLIES (FORALL i (IMPLIES (IN i NN) (IS-RING (f i))))
          (IS-RING (RING-PROD-N f n)))))))

;;; Linearity (left scalar pull-out):
;;; SUM(r, lambda i. a * f(i), n) = a * SUM(r, f, n)
;;; Stated schematically for inline use (derivable by induction + distributivity).
;;; The VNB-LAMBDA form below uses the built-in lambda binder.
(theory-add-axiom! *current-theory* 'sum-left-scalar
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL a
                 (IMPLIES (IN a (CARR r))
                          (FORALL f
                            (IMPLIES (IN f (FUN NN (CARR r)))
                                     (FORALL n
                                       (IMPLIES (IN n NN)
                                         (= (SUM r (VNB-LAMBDA i ((MUL r) a (f i))) n)
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

(theory-add-axiom! *current-theory* 'sum-set-empty
  '(FORALL r (FORALL f
      (== (SUM-SET r EMPTY-SET f) (ZERO r)))))

(theory-add-axiom! *current-theory* 'sum-set-singleton
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL x (FORALL f
                  (= (SUM-SET r (PAIR x x) f) (f x)))))))

;;; Disjoint-union: S1 cap S2 = empty => sum over S1 cup S2 splits additively.
;;; f's typing is stated via the union (FUN (UNION S1 S2) (CARR r)); sum-set-type
;;; covers each piece via the SUBSET clause.
(theory-add-axiom! *current-theory* 'sum-set-disjoint-union
  '(FORALL r
      (IMPLIES (IS-RING r)
               (FORALL S1 (FORALL S2 (FORALL f
                  (IMPLIES (AND (IN S1 SET)
                           (AND (IN S2 SET)
                           (AND (= (INTERSECTION S1 S2) EMPTY-SET)
                                (IN f (FUN (UNION S1 S2) (CARR r))))))
                           (= (SUM-SET r (UNION S1 S2) f)
                              ((ADD r) (SUM-SET r S1 f) (SUM-SET r S2 f))))))))))

;;; Type: result is in the carrier whenever f is defined on a superset of S
;;; with values in CARR(r).  Stated with an explicit superset X to keep the
;;; disjoint-union axiom usable (where f's typing is on UNION(S1, S2) but
;;; the RHS uses sums over S1, S2).
(theory-add-axiom! *current-theory* 'sum-set-type
  '(FORALL r (FORALL X (FORALL S (FORALL f
      (IMPLIES (AND (IS-RING r)
               (AND (IN X SET)
               (AND (SUBSET S X)
                    (IN f (FUN X (CARR r))))))
               (IN (SUM-SET r S f) (CARR r))))))))

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

(theory-add-axiom! *current-theory* 'prod-set-empty
  '(FORALL cm (FORALL f
      (== (PROD-SET cm EMPTY-SET f) (IDEN cm)))))

(theory-add-axiom! *current-theory* 'prod-set-singleton
  '(FORALL cm
      (IMPLIES (IS-COMM-MONOID cm)
               (FORALL x (FORALL f
                  (= (PROD-SET cm (PAIR x x) f) (f x)))))))

(theory-add-axiom! *current-theory* 'prod-set-disjoint-union
  '(FORALL cm
      (IMPLIES (IS-COMM-MONOID cm)
               (FORALL S1 (FORALL S2 (FORALL f
                  (IMPLIES (AND (IN S1 SET)
                           (AND (IN S2 SET)
                           (AND (= (INTERSECTION S1 S2) EMPTY-SET)
                                (IN f (FUN (UNION S1 S2) (CARR cm))))))
                           (= (PROD-SET cm (UNION S1 S2) f)
                              ((OPR cm) (PROD-SET cm S1 f) (PROD-SET cm S2 f))))))))))

(theory-add-axiom! *current-theory* 'prod-set-type
  '(FORALL cm (FORALL X (FORALL S (FORALL f
      (IMPLIES (AND (IS-COMM-MONOID cm)
               (AND (IN X SET)
               (AND (SUBSET S X)
                    (IN f (FUN X (CARR cm))))))
               (IN (PROD-SET cm S f) (CARR cm))))))))
