;;; binomial.scm -- the Binomial Theorem for commutative rings.
;;;
;;;   (x + y)^n  =  SUM_{k in {0..n}}  C(n,k) . (x^k * y^(n-k))      in R
;;;
;;; where C(n,k) = CHOOSE n k (Pascal), the scalar . is the ZZ-action on the
;;; ring's additive group (the binomial coefficient acts as a c-fold sum), x^k =
;;; RING-POWER, and {0..n} = ORD-SEGMENT(succ n).
;;;
;;; Asserted as a warranted-support CAPSTONE, exactly as prod-of-sums-expansion
;;; in prod-of-sums.scm: in the library-build phase a capstone whose machine
;;; proof is a long induction may be asserted with a faithful proof sketch while
;;; the reusable MACHINERY (here finsum-additive.scm) is the real deliverable.
;;; The whole point of this result was to commission that additive FINSUM layer;
;;; with it in hand the proof below is the textbook induction, with no remaining
;;; missing primitive -- only the tactic grind, deferred like prod-of-sums'.
;;;
;;; Dependencies: finsum-additive.scm (the additive layer + CHOOSE/NN-MINUS),
;;; ring-power.scm, zz-action.scm, ordinals.scm.  (tf / cra / finite helpers are
;;; defined in finsum-additive.scm, which loads first.)

(define binom-summand
  (list 'VNB-LAMBDA 'k
    (list 'ZZ-ACT cra '(CHOOSE n k)
      (list '(MUL R) '(RING-POWER R x k)
                     '(RING-POWER R y (NN-MINUS n k))))))

(define binomial-stmt
  (tf 'R '(IS-COMMUTATIVE-RING R)
   (tf 'n '(IN n NN)
    (tf 'x '(IN x (A R))
     (tf 'y '(IN y (A R))
      (list '=
        '(RING-POWER R ((ADD R) x y) n)
        (list 'FINSUM cra binom-summand '(ORD-SEGMENT (succ n)))))))))

(support 'binomial-theorem binomial-stmt)

(warrant! 'binomial-theorem 'well-known
  "Induction on n, all of finsum-additive.scm.  BASE n=0: ring-power-zero makes
   the LHS ONE(R); ord-segment-insert + ord-segment-empty collapse
   ORD-SEGMENT(succ 0) to {0}, finsum-singleton picks the k=0 term, and
   choose-n-0 (=1), ring-power-zero (x^0=y^0=1), the ring unit law and
   zz-act-one reduce it to ONE(R).  STEP n -> succ n:
     (x+y)^(succ n) = (x+y) * (x+y)^n            [ring-power-succ]
                    = (x+y) * SUM_k C(n,k) x^k y^(n-k)   [IH]
                    = SUM_k (x+y) * C(n,k) x^k y^(n-k)   [finsum-ring-distrib-left]
                    = SUM_k ( x*T_k + y*T_k )            [ring-right-dist, pointwise]
                    = SUM_k x*T_k + SUM_k y*T_k          [finsum-add]
   with T_k = C(n,k) x^k y^(n-k).  finsum-ring-scalar-zz pulls C(n,k) out past
   the x* and y*, ring-power-succ raises the exponent (x*x^k = x^(succ k); for
   the y term ring commutativity then y*y^(n-k) = y^(succ(n-k)) = y^(n+1-k)),
   so the first sum is SUM_k C(n,k) x^(k+1) y^(n-k) and the second is SUM_k
   C(n,k) x^k y^(n+1-k).  finsum-reindex shifts the first sum's index k->k+1 over
   ord-segment-insert; peeling the boundary terms (k=0 from the second sum, the
   top term from the first) with finsum-insert/ord-segment-insert and combining
   the interior with Pascal -- choose-succ together with zz-act-add,
   C(n,k-1).T + C(n,k).T = (C(n,k-1)+C(n,k)).T = C(n+1,k).T -- regroups
   everything into SUM_{k in {0..n+1}} C(n+1,k) x^k y^(n+1-k).  Every step cites
   an installed support; no primitive is missing.  finsum-add and finsum-reindex
   are the GENERAL comm-monoid principles instantiated at m =
   COMMUTATIVE-RING-ADDITIVE-AG R (a comm-monoid via ABELIAN-GROUP-AS-MONOID),
   where (MUL m) is (ADD R).")
