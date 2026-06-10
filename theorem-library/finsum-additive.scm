;;; finsum-additive.scm -- the ADDITIVE algebra of FINSUM.
;;;
;;; prod-of-sums.scm built FINSUM's MULTIPLICATIVE layer (finsum-insert and the
;;; PROD-RING specializations: fold one more FACTOR).  The binomial-theorem
;;; stress probe (theorem-library/binomial-probe.scm) showed the ADDITIVE half
;;; was missing: nothing distributes a ring element across a FINSUM, nothing
;;; splits a sum of pointwise sums, nothing reindexes.  This file supplies that
;;; half, plus the two missing arithmetic operators (CHOOSE, NN-MINUS) the
;;; binomial statement needs.
;;;
;;; Stated at the RING-ADDITIVE level -- over IS-COMMUTATIVE-RING R, summing in
;;; (COMMUTATIVE-RING-ADDITIVE-AG R) whose (MUL .) is (ADD R) -- so the binomial
;;; proof consumes them with no view-discharge.  The natural generalizations
;;; (finsum-add / finsum-reindex over a bare IS-ABELIAN-GROUP, finsum commuting
;;; with any AG-endomorphism) are left for later; these are the directly-usable
;;; specializations, exactly as prod-ring-insert specializes finsum-insert.
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
(define cra '(COMMUTATIVE-RING-ADDITIVE-AG R))   ; the ring's additive AG
(define (finite S) (list 'AND (list 'IN S 'SET) (list 'IN (list 'CARD S) 'NN)))

;;; =======================================================================
;;; Missing arithmetic operators
;;; =======================================================================

;; Binomial coefficient via Pascal's rule (no factorial division).
(def-constant 'CHOOSE
  '(choose-n-0    (FORALL n (IMPLIES (IN n NN) (= (CHOOSE n 0) (succ 0)))))
  '(choose-0-succ (FORALL k (IMPLIES (IN k NN) (= (CHOOSE 0 (succ k)) 0))))
  '(choose-succ   (FORALL n (IMPLIES (IN n NN)
                    (FORALL k (IMPLIES (IN k NN)
                      (= (CHOOSE (succ n) (succ k))
                         (+ (CHOOSE n k) (CHOOSE n (succ k))))))))))
(theory-add-axiom! *current-theory* 'choose-in-nn
  '(FORALL n (IMPLIES (IN n NN) (FORALL k (IMPLIES (IN k NN) (IN (CHOOSE n k) NN))))))

;; Truncated natural subtraction (monus) for the n-k exponent.
(def-constant 'NN-MINUS
  '(nn-minus-0    (FORALL n (IMPLIES (IN n NN) (= (NN-MINUS n 0) n))))
  '(nn-minus-succ (FORALL n (IMPLIES (IN n NN)
                    (FORALL k (IMPLIES (IN k NN)
                      (= (NN-MINUS (succ n) (succ k)) (NN-MINUS n k))))))))
(theory-add-axiom! *current-theory* 'nn-minus-in-nn
  '(FORALL n (IMPLIES (IN n NN) (FORALL k (IMPLIES (IN k NN) (IN (NN-MINUS n k) NN))))))

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
   (tf 'x '(IN x (A R))
    (tf 'n '(IN n NN)
     '(= (RING-POWER R x (succ n))
         ((MUL R) (RING-POWER R x n) x))))))
(warrant! 'ring-power-succ 'informal
  "succ n = n + 1; ring-power-add gives x^(n+1) = x^n * x^1 and ring-power-one
   gives x^1 = x.  Successor restatement so the macete fires on `succ'.")

;;; =======================================================================
;;; The additive layer
;;; =======================================================================

;; finsum-add: SUM_z (f z + h z) = (SUM_z f z) + (SUM_z h z).
(support 'finsum-add
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'S (finite 'S)
    (tf 'f '(IN f (FUN S (A R)))
     (tf 'h '(IN h (FUN S (A R)))
      (list '=
        (list 'FINSUM cra (list 'VNB-LAMBDA 'z (list '(ADD R) '(f z) '(h z))) 'S)
        (list '(ADD R)
              (list 'FINSUM cra 'f 'S)
              (list 'FINSUM cra 'h 'S))))))))
(warrant! 'finsum-add 'well-known
  "Induction on |S| via finsum-insert in the additive AG: base 0+0=0
   (finsum-empty); step folds in one z0, regrouping (a+b)+(c+d)=(a+c)+(b+d) by
   additive commutativity/associativity.  The additive twin of the
   multiplicative fold.")

;; finsum-ring-distrib-left: r * SUM_z f z = SUM_z (r * f z).
(support 'finsum-ring-distrib-left
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'r '(IN r (A R))
    (tf 'S (finite 'S)
     (tf 'f '(IN f (FUN S (A R)))
      (list '=
        (list '(MUL R) 'r (list 'FINSUM cra 'f 'S))
        (list 'FINSUM cra (list 'VNB-LAMBDA 'z (list '(MUL R) 'r '(f z))) 'S)))))))
(warrant! 'finsum-ring-distrib-left 'well-known
  "Induction on |S| via finsum-insert: r*(SUM_X f + f z0) = r*SUM_X f + r*f z0
   by ring-left-dist, then the IH.  a |-> r*a is an endomorphism of (R,+), and
   FINSUM commutes with an AG-endomorphism.")

;; finsum-ring-scalar-zz: r * (c . a) = c . (r * a)   (c in ZZ; . is ZZ-ACT).
;; Ring multiplication is ZZ-linear -- lets a binomial coefficient (a ZZ-ACT
;; scalar) pass through the x*(...) / y*(...) multiplications.
(support 'finsum-ring-scalar-zz
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'r '(IN r (A R))
    (tf 'c '(IN c ZZ)
     (tf 'a '(IN a (A R))
      (list '=
        (list '(MUL R) 'r (list 'ZZ-ACT cra 'c 'a))
        (list 'ZZ-ACT cra 'c (list '(MUL R) 'r 'a))))))))
(warrant! 'finsum-ring-scalar-zz 'well-known
  "c.a is the c-fold additive multiple of a (zz-act); ring left-distributivity
   pushes r through each summand, so r*(c.a)=c.(r*a).  Sign cases via
   zz-act-neg.  Ring multiplication is ZZ-bilinear.")

;; finsum-reindex: SUM_{s in S} f s = SUM_{t in T} f(phi t),  phi : T -> S a bij.
(support 'finsum-reindex
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'S (finite 'S)
    (tf 'T (finite 'T)
     (tf 'phi '(IN phi (BIJECTION T S))
      (tf 'f '(IN f (FUN S (A R)))
       (list '=
         (list 'FINSUM cra 'f 'S)
         (list 'FINSUM cra (list 'VNB-LAMBDA 'z '(f (phi z))) 'T))))))))
(warrant! 'finsum-reindex 'well-known
  "Compose the chosen enumeration of T with phi to get an enumeration of S;
   SUM-AG along it is the same fold.  Independence of enumeration is
   finsum-comm-monoid-permutation-invariance.")
