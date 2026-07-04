;;; finsum-additive.scm -- the ADDITIVE algebra of FINSUM.
;;;
;;; prod-of-sums.scm built FINSUM's MULTIPLICATIVE layer (finsum-insert and the
;;; PROD-RING specializations: fold one more FACTOR).  The binomial-theorem
;;; stress probe (theorem-library/binomial-probe.scm) showed the ADDITIVE half
;;; was missing: nothing distributes a ring element across a FINSUM, nothing
;;; splits a sum of pointwise sums, nothing reindexes.  This file supplies that
;;; half, plus NN-MINUS (the n-k exponent operator) the binomial statement
;;; needs.  CHOOSE itself is defined CONCRETELY in injection.scm (as the count
;;; of m-element subsets), not here.
;;;
;;; TWO tiers, matching the existing finsum-comm-monoid / finsum-fubini family:
;;;
;;;   GENERAL (over IS-COMM-MONOID m, op (MUL m), seed (ID m) -- the honest
;;;   minimal hypotheses, no inverses):  finsum-add and finsum-reindex are
;;;   properties of ANY finite sum, exactly like finsum-fubini.  These are the
;;;   reusable PSS principles.
;;;
;;;   RING-LEVEL (over IS-COMMUTATIVE-RING R, summing in the additive AG whose
;;;   (MUL .) is (ADD R)):  finsum-ring-distrib-left (a ring element distributes
;;;   across a sum -- the AG-endomorphism a|->r*a specialization) and
;;;   finsum-ring-scalar-zz (ring mult is ZZ-bilinear) are genuinely ring facts,
;;;   not pure finsum facts, so they stay here.  The general form of distrib-left
;;;   -- FINSUM commutes with a comm-monoid endomorphism -- waits on a monoid
;;;   homomorphism predicate (none in the library yet; IS-HOM is the metric one).
;;;
;;; Library-build phase: asserted as warranted support [[feedback-library-axioms-fine]];
;;; each warrant names the standard fold-induction that proves it.  The honest
;;; machine proofs (induction on |S| via finsum-insert + comm-monoid rearrange)
;;; are the natural follow-up, like prod-of-sums-expansion itself.
;;;
;;; Dependencies: finsum.scm, prod-of-sums.scm (finsum-insert), views.scm
;;; (COMMUTATIVE-RING-ADDITIVE-AG), ring-power.scm, zz-action.scm, ordinals.scm.

;; typed universal: (tf 'v TYPE BODY) = (FORALL v (IMPLIES TYPE BODY)).  Building
;; the support formulas this way keeps every quantifier level locally balanced,
;; so there is no deep hand-counting of trailing parens.
(define (tf v type body) (list 'FORALL v (list 'IMPLIES type body)))
;; rng, NOT R: the reader case-folds R to r, colliding with the element var r
;; in the finsum-ring-* theorems below (ring conflated with its element).
(define cra '(COMMUTATIVE-RING-ADDITIVE-AG rng))   ; the ring's additive AG
(define (finite S) (list 'AND (list 'IN S 'SET) (list 'IN (list 'CARD S) 'NN)))
;; typed forall with the finiteness premise CURRIED (IN S SET => IN CARD S NN =>
;; body), so a forward `fact' can detach each guard (fact cannot split the AND
;; that `finite' packs).  Equivalent to (tf S (finite S) body); used where the
;; lemma is fact-applied (the (B) bricks).
(define (tfin S body)
  (list 'FORALL S (list 'IMPLIES (list 'IN S 'SET)
    (list 'IMPLIES (list 'IN (list 'CARD S) 'NN) body))))

;;; =======================================================================
;;; Missing arithmetic operator: NN-MINUS  (CHOOSE now lives in injection.scm)
;;; =======================================================================

;; Truncated natural subtraction (monus) for the n-k exponent.  Defined
;; EXPLICITLY as a closed term in existing vocabulary -- NOT by a recursion-
;; shaped postulate.  NN subset ZZ, so for l <= k the integer difference k - l
;; is already the right natural; below it, the conventional 0.  An explicit
;; definition is conservative by construction (eliminable by unfolding): no
;; recursion theorem, no two-index recursion combinator, no consistency debt --
;; the monus recurrences nn-minus(n,0)=n, nn-minus(succ n,succ k)=nn-minus(n,k),
;; nn-minus(0,succ k)=0 are now one-step THEOREMS (IF case split on l<=k +
;; integer arithmetic), not axioms.
(def-constant 'NN-MINUS
  '(nn-minus-def
    (FORALL k (IMPLIES (IN k NN)
      (FORALL l (IMPLIES (IN l NN)
        (= (NN-MINUS k l) (IF (<= l k) (- k l) 0))))))))
;; Typing: monus lands back in NN.  A support (warranted derivable from
;; nn-minus-def) -- IF-reduction alone won't expose it without the case split.
(support 'nn-minus-in-nn
  '(FORALL k (IMPLIES (IN k NN) (FORALL l (IMPLIES (IN l NN) (IN (NN-MINUS k l) NN))))))
(warrant! 'nn-minus-in-nn 'hand-wave
  "From nn-minus-def by IF case split on l<=k: then-branch k-l in NN (since
   k = (k-l)+l with both in NN forces the difference into NN); else-branch 0 in
   NN.  One-step derivation; asserted library-phase rather than mechanized.")

;;; =======================================================================
;;; Index-set plumbing
;;; =======================================================================

;; ORD-SEGMENT(succ n) = ORD-SEGMENT(n) u {n}.  Set-equation form of
;; ord-segment-nn-succ's membership iff -- the shape finsum-insert needs to peel
;; the top index n (ord-segment-self gives n not in ORD-SEGMENT(n)).
(support 'ord-segment-insert
  (tf 'n '(IN n NN)
      '(= (ORD-SEGMENT (succ n))
          (UNION (ORD-SEGMENT n) (PAIR n n)))))
(warrant! 'ord-segment-insert 'well-known
  "Set-extensionality on ord-segment-nn-succ: k in ORD-SEGMENT(succ n) iff k in
   ORD-SEGMENT(n) or k = n; the RHS is membership in the union with the
   singleton {n} = (PAIR n n).")

;;; =======================================================================
;;; Ring-power successor (avoids the succ-vs-(+ . 1) mismatch in ring-power-add)
;;; =======================================================================

;; x^(succ n) = x^n * x.
(support 'ring-power-succ
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'x '(IN x (CARR R))
    (tf 'n '(IN n NN)
     '(= (RING-POWER R x (succ n))
         ((MUL R) (RING-POWER R x n) x))))))
(warrant! 'ring-power-succ 'informal
  "succ n = n + 1; ring-power-add gives x^(n+1) = x^n * x^1 and ring-power-one
   gives x^1 = x.  Successor restatement so the macete fires on `succ'.")

;;; =======================================================================
;;; The additive layer
;;; =======================================================================

;; finsum-add (GENERAL, comm-monoid):  the FINSUM of a pointwise structure-
;; combination is the combination of the FINSUMs --
;;   SUM_z (MUL m)(f z, h z) = (MUL m)( SUM_z f z, SUM_z h z ).
;; Additively (m = an additive AG) this is SUM(f+h)=SUM f+SUM h; multiplicatively
;; (m = the multiplicative monoid) it is the PROD version.  The general
;; linearity principle, like finsum-fubini.
(support 'finsum-add
  (tf 'm '(IS-COMM-MONOID m)
   (tfin 'S
    (tf 'f '(IN f (FUN S (CARR m)))
     (tf 'h '(IN h (FUN S (CARR m)))
      (list '=
        (list 'FINSUM 'm (list 'VNB-LAMBDA 'z (list '(MUL m) '(f z) '(h z))) 'S)
        (list '(MUL m)
              (list 'FINSUM 'm 'f 'S)
              (list 'FINSUM 'm 'h 'S))))))))
(warrant! 'finsum-add 'well-known
  "Induction on |S| via finsum-insert: base is (ID m)*(ID m)=(ID m) (finsum-empty);
   step folds in one z0, regrouping (a*b)*(c*d)=(a*c)*(b*d) by the commutativity
   and associativity of (MUL m) -- which is exactly what IS-COMM-MONOID supplies
   (no inverses used).  Holds for every commutative-monoid-valued finite sum.")

;; finsum-ring-distrib-left: r * SUM_z f z = SUM_z (r * f z).
(support 'finsum-ring-distrib-left
  (tf 'rng '(IS-COMMUTATIVE-RING rng)
   (tf 'r '(IN r (CARR rng))
    (tfin 'S
     (tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) 'r (list 'FINSUM cra 'f 'S))
        (list 'FINSUM cra (list 'VNB-LAMBDA 'z (list '(MUL rng) 'r '(f z))) 'S)))))))
(warrant! 'finsum-ring-distrib-left 'well-known
  "Induction on |S| via finsum-insert: r*(SUM_X f + f z0) = r*SUM_X f + r*f z0
   by ring-left-dist, then the IH.  a |-> r*a is an endomorphism of (R,+), and
   FINSUM commutes with an AG-endomorphism.")

;; finsum-ring-distrib-right: (SUM_z f z) * r = SUM_z (f z * r).  The right-hand
;; mirror of finsum-ring-distrib-left; in a COMMUTATIVE ring the two coincide
;; mathematically, but the SYNTACTIC form (the ring factor on the RIGHT of the
;; sum) is what a proof that has produced (FINSUM ...) * r needs to rewrite
;; WITHOUT first commuting -- and multiplicative commutativity is a looping
;; rewrite, so a directed right-distribution rule earns its place.  (Distinct
;; from finsum-ring-distrib-right-gen, which is over an ARBITRARY ring's
;; RING-ADDITIVE-AG; this one is over the commutative ring's cra.)
(support 'finsum-ring-distrib-right
  (tf 'rng '(IS-COMMUTATIVE-RING rng)
   (tf 'r '(IN r (CARR rng))
    (tfin 'S
     (tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) (list 'FINSUM cra 'f 'S) 'r)
        (list 'FINSUM cra (list 'VNB-LAMBDA 'z (list '(MUL rng) '(f z) 'r)) 'S)))))))
(warrant! 'finsum-ring-distrib-right 'well-known
  "Right-handed finsum-ring-distrib-left: (SUM_X f + f z0)*r = SUM_X f*r + f z0*r
   by ring-right-dist, then the IH.  a |-> a*r is an endomorphism of (R,+).")
(category! 'finsum-ring-distrib-right 'algebra)

;;; =======================================================================
;;; General-ring finite-sum infrastructure (the (B) bricks): pointwise
;;; congruence of FINSUM, and distribution of a ring factor into a finite sum
;;; over an ARBITRARY (not necessarily commutative) ring.  These are the
;;; primitives that let a summand be rewritten under the FINSUM binder and a
;;; scalar be pulled in/out on either side -- the operations the tactic layer
;;; cannot do directly, needed by triple-entry-left/right (matmul-assoc) and,
;;; in principle, to discharge the binomial-theorem warrant.  Warranted PSS
;;; bricks (induction on |S| via finsum-insert), like the lemmas above.
;;; =======================================================================

;; the additive abelian group of a general ring (cf. cra for a commutative ring)
(define rag '(RING-ADDITIVE-AG rng))

;; finsum-congruence: summands equal pointwise on the finite index set => equal
;; finite sums.  This is what licenses rewriting a FINSUM's summand under its
;; binder (VNB has no direct under-binder congruence rule).
(support 'finsum-congruence
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tfin 'S
    (tf 'f '(IN f (FUN S (CARR ag)))
     (tf 'g '(IN g (FUN S (CARR ag)))
      (list 'IMPLIES
        '(FORALL z (IMPLIES (IN z S) (= (f z) (g z))))
        '(= (FINSUM ag f S) (FINSUM ag g S))))))))
(warrant! 'finsum-congruence 'well-known
  "If f(z)=g(z) for every z in the finite index set S, then FINSUM(ag,f,S)=
   FINSUM(ag,g,S).  Induction on |S| via finsum-insert: the peeled term agrees
   (f z0 = g z0) and the rest by the IH.  Equivalently, FINSUM depends only on
   the restriction of the summand to S, so it factors through pointwise equality.")

;; finsum-ring-distrib-left-gen: r * SUM_z f z = SUM_z (r * f z) in ANY ring.
;; The general-ring companion of finsum-ring-distrib-left (which needs a
;; COMMUTATIVE ring); only ring-left-dist is used, so it holds in every ring.
(support 'finsum-ring-distrib-left-gen
  (tf 'rng '(IS-RING rng)
   (tf 'r '(IN r (CARR rng))
    (tfin 'S
     (tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) 'r (list 'FINSUM rag 'f 'S))
        (list 'FINSUM rag (list 'VNB-LAMBDA 'z (list '(MUL rng) 'r '(f z))) 'S)))))))
(warrant! 'finsum-ring-distrib-left-gen 'well-known
  "r*(SUM_z f z) = SUM_z (r * f z) in an arbitrary ring: induction on |S| via
   finsum-insert, r*(SUM_X f + f z0) = r*SUM_X f + r*f z0 by ring-left-dist, then
   the IH.  No commutativity used (a |-> r*a is an additive-group endomorphism).")

;; finsum-ring-distrib-right-gen: (SUM_z f z) * r = SUM_z (f z * r) in ANY ring.
;; The right-handed mirror (ring-right-dist); has no commutative analogue in the
;; library because a comm ring makes it identical to the left version.
(support 'finsum-ring-distrib-right-gen
  (tf 'rng '(IS-RING rng)
   (tf 'r '(IN r (CARR rng))
    (tfin 'S
     (tf 'f '(IN f (FUN S (CARR rng)))
      (list '=
        (list '(MUL rng) (list 'FINSUM rag 'f 'S) 'r)
        (list 'FINSUM rag (list 'VNB-LAMBDA 'z (list '(MUL rng) '(f z) 'r)) 'S)))))))
(warrant! 'finsum-ring-distrib-right-gen 'well-known
  "(SUM_z f z) * r = SUM_z (f z * r) in an arbitrary ring: induction on |S| via
   finsum-insert with ring-right-dist; a |-> a*r is an additive-group endomorphism.")

;; finsum-ring-scalar-zz: r * (c . a) = c . (r * a)   (c in ZZ; . is ZZ-ACT).
;; Ring multiplication is ZZ-linear -- lets a binomial coefficient (a ZZ-ACT
;; scalar) pass through the x*(...) / y*(...) multiplications.
(support 'finsum-ring-scalar-zz
  (tf 'rng '(IS-COMMUTATIVE-RING rng)
   (tf 'r '(IN r (CARR rng))
    (tf 'c '(IN c ZZ)
     (tf 'a '(IN a (CARR rng))
      (list '=
        (list '(MUL rng) 'r (list 'ZZ-ACT cra 'c 'a))
        (list 'ZZ-ACT cra 'c (list '(MUL rng) 'r 'a))))))))
(warrant! 'finsum-ring-scalar-zz 'well-known
  "c.a is the c-fold additive multiple of a (zz-act); ring left-distributivity
   pushes r through each summand, so r*(c.a)=c.(r*a).  Sign cases via
   zz-act-neg.  Ring multiplication is ZZ-bilinear.")

;; finsum-reindex (GENERAL, comm-monoid):  a sum is invariant under a bijective
;; change of index --  SUM_{s in S} f s = SUM_{t in T} f(phi t),  phi : T -> S.
(support 'finsum-reindex
  (tf 'm '(IS-COMM-MONOID m)
   (tfin 'S
    (tf 'T (finite 'T)
     (tf 'phi '(IN phi (BIJECTION T S))
      (tf 'f '(IN f (FUN S (CARR m)))
       (list '=
         (list 'FINSUM 'm 'f 'S)
         (list 'FINSUM 'm (list 'VNB-LAMBDA 'z '(f (phi z))) 'T))))))))
(warrant! 'finsum-reindex 'well-known
  "Compose the chosen enumeration of T with phi to get an enumeration of S;
   SUM-AG along it is the same fold.  Independence of enumeration is
   finsum-comm-monoid-permutation-invariance.  Holds for any comm-monoid sum.")

;;; =======================================================================
;;; ABELIAN-GROUP companions of insert / add / reindex.
;;;
;;; FINSUM is DEFINED over an abelian group (finsum.scm: it uses ID(ag) and
;;; SUM-AG(ag,.)), and finsum-singleton / finsum-empty are stated at
;;; IS-ABELIAN-GROUP.  The comm-monoid forms above (finsum-insert / -add /
;;; -reindex) are the maximally-general PSS principles, but they cannot be
;;; instantiated at an abelian group directly: IS-COMM-MONOID pins a 3-slot
;;; tuple (CARR MUL ID), while an abelian group is a 4-slot (CARR MUL ID INV),
;;; and there is no ABELIAN-GROUP-AS-COMM-MONOID view (abelian-group-as-monoid
;;; reaches only bare MONOID).  So a sum that lives in a genuine abelian group
;;; -- e.g. the binomial sum over COMMUTATIVE-RING-ADDITIVE-AG R -- needs these
;;; abelian-group-level restatements.  Same fold induction; an abelian group is
;;; a commutative monoid on its first three slots, so every warrant below is the
;;; comm-monoid warrant read through that forgetful correspondence.
;;; =======================================================================

;; finsum-insert-ag: peel one index k (k not already in X) off a FINSUM in an
;; abelian group -- the abelian-group form of finsum-insert.  Finiteness of X
;; is CURRIED (tfin) so a forward `fact' can detach each guard.
(support 'finsum-insert-ag
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tfin 'X
    (list 'FORALL 'k (list 'IMPLIES '(IN k SET)
     (list 'IMPLIES '(NOT (IN k X))
      (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN (UNION X (PAIR k k)) (CARR ag)))
        (list '=
          '(FINSUM ag f (UNION X (PAIR k k)))
          '((MUL ag) (FINSUM ag f X) (f k)))))))))))
(warrant! 'finsum-insert-ag 'well-known
  "finsum-insert at m = ag viewed as its commutative monoid (CARR,MUL,ID):
   FINSUM(ag,f,X u {k}) = (MUL ag)(FINSUM(ag,f,X), f k) for k not in X.  Standard
   fold peel; abelian group supplies the monoid laws (no inverses used).")

;; finsum-add-ag: SUM(f (+) h) = SUM f (+) SUM h in an abelian group, where (+)
;; is (MUL ag).  Abelian-group form of finsum-add.
(support 'finsum-add-ag
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tfin 'S
    (tf 'f '(IN f (FUN S (CARR ag)))
     (tf 'h '(IN h (FUN S (CARR ag)))
      (list '=
        (list 'FINSUM 'ag (list 'VNB-LAMBDA 'z (list '(MUL ag) '(f z) '(h z))) 'S)
        (list '(MUL ag)
              (list 'FINSUM 'ag 'f 'S)
              (list 'FINSUM 'ag 'h 'S))))))))
(warrant! 'finsum-add-ag 'well-known
  "finsum-add at m = ag as a commutative monoid: induction on |S| via
   finsum-insert-ag, regrouping (a+b)+(c+d)=(a+c)+(b+d) by commutativity and
   associativity of (MUL ag).  No inverses used.")

;; finsum-reindex-ag: a FINSUM in an abelian group is invariant under a
;; bijective change of index.  Abelian-group form of finsum-reindex.
(support 'finsum-reindex-ag
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tfin 'S
    (tf 'T (finite 'T)
     (tf 'phi '(IN phi (BIJECTION T S))
      (tf 'f '(IN f (FUN S (CARR ag)))
       (list '=
         (list 'FINSUM 'ag 'f 'S)
         (list 'FINSUM 'ag (list 'VNB-LAMBDA 'z '(f (phi z))) 'T))))))))
(warrant! 'finsum-reindex-ag 'well-known
  "finsum-reindex at m = ag as a commutative monoid: compose the chosen
   enumeration of T with phi to enumerate S; the fold is the same.  Holds for
   any abelian-group-valued finite sum.")

;; finsum-ord-peel: peel the TOP index n off a FINSUM over ORD-SEGMENT(succ n),
;; in an abelian group.  This is finsum-insert-ag specialized at X=ORD-SEGMENT(n),
;; k=n -- the case the binomial induction actually uses -- with the set-plumbing
;; premises (ORD-SEGMENT(n) is a finite set of card n, and n not in ORD-SEGMENT(n))
;; discharged inside the warrant, so the tactic layer sees only IS-ABELIAN-GROUP,
;; IN n NN, and the summand typing.  ORD-SEGMENT(succ n) = ORD-SEGMENT(n) u {n}.
(support 'finsum-ord-peel
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tf 'n '(IN n NN)
    (tf 'f '(IN f (FUN (ORD-SEGMENT (succ n)) (CARR ag)))
     (list '=
       '(FINSUM ag f (ORD-SEGMENT (succ n)))
       '((MUL ag) (FINSUM ag f (ORD-SEGMENT n)) (f n)))))))
(warrant! 'finsum-ord-peel 'well-known
  "finsum-insert-ag at X=ORD-SEGMENT(n), k=n: ORD-SEGMENT(succ n)=ORD-SEGMENT(n) u {n}
   (ord-segment-insert), ORD-SEGMENT(n) is a set (ord-segment-is-set) of card n in NN,
   and n not in ORD-SEGMENT(n) (ord-segment-self).  So the sum splits as the sum over
   ORD-SEGMENT(n) plus the peeled top term f(n).")

;; finsum-embed: extension-by-zero / restriction-to-support.  A finite sum is
;; unchanged by dropping index points where the summand is the identity: if
;; S subset S2 and f = ID(ag) at every index of S2 outside S, then the sum of f
;; over S2 equals the sum of f over S.  This is the tool that puts two sums over
;; DIFFERENT ranges onto a COMMON index set so a pointwise principle (finsum-add-ag
;; / finsum-congruence) applies with NO reindexing bijection -- e.g. the binomial
;; Pascal merge, where the split coefficients C(n,k) / C(n,k-1) vanish at the
;; extra boundary index, so each split sum restricts to its natural range.
;; The support S is NOT determined by matching the S2 sum, so this is a forward
;; `fact' lemma (supply S), not a rewrite macete.
(support 'finsum-embed
  (tf 'ag '(IS-ABELIAN-GROUP ag)
   (tfin 'S
    (tfin 'S2
     (tf 'f '(IN f (FUN S2 (CARR ag)))
      (list 'IMPLIES '(SUBSET S S2)
       (list 'IMPLIES
             '(FORALL z (IMPLIES (AND (IN z S2) (NOT (IN z S))) (= (f z) (ID ag))))
        (list '=
          '(FINSUM ag f S2)
          '(FINSUM ag f S)))))))))
(warrant! 'finsum-embed 'well-known
  "Induction on |S2 \\ S| via finsum-insert-ag: each peeled index outside S
   contributes f = ID(ag), absorbed by the group unit law.  So the sum over S2
   collapses to the sum over its support S.")

(category! 'finsum-ord-peel 'algebra)
(category! 'finsum-insert-ag 'algebra)
(category! 'finsum-add-ag 'algebra)
(category! 'finsum-reindex-ag 'algebra)
(category! 'finsum-embed 'algebra)
