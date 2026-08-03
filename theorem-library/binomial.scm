;;; binomial.scm -- the Binomial Theorem for commutative rings, over the
;;; INTEGER-RANGE sum SUM (sequences.scm), with a recursively-defined weighted
;;; coefficient COMB-KK that folds Pascal's rule into the recursion.
;;;
;;;   (x + y)^n  =  SUM(R, COMB-KK(R,x,y,n), succ n)  =  sum_{k=0}^{n} C(n,k) x^k y^(n-k)
;;;
;;; This is the IMPS-style formulation (docs/algebra.t): the index k ranges over
;;; ZZ, so k-1 is genuine integer subtraction and the coefficient vanishes for
;;; k<0 / k>m DEFINITIONALLY (comb-kk-null / comb-kk-above).  No reindex
;;; bijection, no truncated-subtraction (monus) boundary cases -- the shift is
;;; carried by the successor recurrence of SUM inside an induction (sum-expansion),
;;; exactly as IMPS's expansion-lemma.  PROVEN in binomial-proof.scm.
;;;
;;; This REPLACES the earlier FINSUM-over-ORD-SEGMENT statement, whose proof
;;; drowned in reindex-bijection + monus plumbing.  Binomial is a leaf capstone
;;; (nothing depends on it), so the representation was free to change (2026-07-04).
;;;
;;; Dependencies: sequences.scm (SUM / sum-zero / sum-succ / sum-singleton),
;;; ring-power.scm, def-by-nn-recursion (ordinals.scm).

;;; -----------------------------------------------------------------------
;;; COMB-KK(R,x,y,m) : ZZ -> CARR R      k |-> C(m,k) . x^k y^(m-k)
;;;   m = 0:     k |-> IF k=0 THEN ONE(R) ELSE ZERO(R)
;;;   succ m:    k |-> x * COMB-KK(.,m)(k-1) + y * COMB-KK(.,m)(k)     [Pascal, ZZ index]
;;; Installs comb-kk-zero and comb-kk-succ (definitional == equations).
(def-by-nn-recursion 'COMB-KK '(R x y)
  '(VNB-LAMBDA k NN (IF (= k 0) (ONE R) (ZERO R)))
  '(m val)
  '(VNB-LAMBDA k NN ((ADD R) ((MUL R) x (val (- k 1))) ((MUL R) y (val k)))))

;;; -----------------------------------------------------------------------
;;; COMB-KK facts (warranted PSS supports; each is a one-step induction on m
;;; from comb-kk-zero/-succ, in the library-build spirit).
;;; -----------------------------------------------------------------------

;; The coefficient family is a total ZZ-indexed function into the carrier.
(support 'comb-kk-in-fun
  (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))
   (tf 'm '(IN m NN) (list 'IN (list 'COMB-KK 'R 'x 'y 'm) '(FUN ZZ (CARR R))))))))
(warrant! 'comb-kk-in-fun 'well-known
  "Each COMB-KK(R,x,y,m) is a total function ZZ -> CARR R: base is IF into
   {ONE,ZERO}; step is a sum of products of carrier elements.  Induction on m.")

;; Vanishing below the range: C(m,k)=0 for k<0.
(support 'comb-kk-null
  (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))
   (tf 'm '(IN m NN)(tf 'k '(IN k ZZ)
    (list 'IMPLIES '(< k 0) (list '= (list (list 'COMB-KK 'R 'x 'y 'm) 'k) '(ZERO R)))))))))
(warrant! 'comb-kk-null 'well-known
  "k<0 => COMB-KK(.,m)(k)=ZERO.  Induction on m: base IF(k=0) is ZERO for k<0;
   step x*val(k-1)+y*val(k) with k-1<0 and k<0 both ZERO by IH.")

;; Vanishing above the range: C(m,k)=0 for k>m.
(support 'comb-kk-above
  (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))
   (tf 'm '(IN m NN)(tf 'k '(IN k ZZ)
    (list 'IMPLIES '(< m k) (list '= (list (list 'COMB-KK 'R 'x 'y 'm) 'k) '(ZERO R)))))))))
(warrant! 'comb-kk-above 'well-known
  "k>m => COMB-KK(.,m)(k)=ZERO.  Induction on m: base k>0 => IF(k=0) is ZERO;
   step k>succ m => both k-1>m and k>m, ZERO by IH.")

;; The single k=0 term of the degree-0 coefficient is ONE.
(support 'comb-kk-0-0
  (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'x '(IN x (CARR R))(tf 'y '(IN y (CARR R))
   (list '= (list (list 'COMB-KK 'R 'x 'y 0) 0) '(ONE R))))))
(warrant! 'comb-kk-0-0 'well-known
  "comb-kk-zero + IF(0=0) picks the then-branch ONE(R).")

;;; -----------------------------------------------------------------------
;;; Small arithmetic / typing shims used by the induction (all warranted;
;;; each is a one-liner over ZZ/NN or a curried closure the tactic layer needs
;;; because `fact' cannot split an AND-antecedent).
;;; -----------------------------------------------------------------------
(support 'bt-succ-minus-1 (tf 'n '(IN n ZZ) '(= (- (succ n) 1) n)))
(warrant! 'bt-succ-minus-1 'well-known "succ n - 1 = n in ZZ.")
(support 'bt-neg1-in-zz '(IN (- 0 1) ZZ))(warrant! 'bt-neg1-in-zz 'well-known "-1 in ZZ.")
(support 'bt-neg1-neg   '(< (- 0 1) 0))(warrant! 'bt-neg1-neg 'well-known "-1 < 0.")
(support 'bt-nn-in-zz   (tf 'n '(IN n NN) '(IN n ZZ)))(warrant! 'bt-nn-in-zz 'well-known "NN subset ZZ.")
(support 'bt-succ-in-nn (tf 'n '(IN n NN) '(IN (succ n) NN)))(warrant! 'bt-succ-in-nn 'well-known "succ closes NN.")
(support 'bt-lt-succ    (tf 'n '(IN n NN) '(< n (succ n))))(warrant! 'bt-lt-succ 'well-known "n < succ n.")
(support 'bt-sum-in-carr-zz
  (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'g '(IN g (FUN ZZ (CARR R)))(tf 'N '(IN N NN)
   '(IN (SUM R g N)(CARR R))))))
(warrant! 'bt-sum-in-carr-zz 'well-known "SUM over the NN indices of a ZZ-fn lands in CARR.")
(support 'bt-mul-comm (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'a '(IN a (CARR R))(tf 'b '(IN b (CARR R))
   (list '= '((MUL R) a b) '((MUL R) b a))))))
(warrant! 'bt-mul-comm 'well-known "commutativity of MUL (the defining property).")
(support 'bt-add-in-carr (tf 'R '(IS-COMMUTATIVE-RING R)(tf 'a '(IN a (CARR R))(tf 'b '(IN b (CARR R))
   '(IN ((ADD R) a b)(CARR R))))))
(warrant! 'bt-add-in-carr 'well-known "curried ring-carrier-closed-add.")
(support 'bt-one-in-carr (tf 'R '(IS-RING R) '(IN (ONE R)(CARR R))))
(warrant! 'bt-one-in-carr 'well-known "ring ONE lies in CARR.")

(category! 'comb-kk-in-fun 'algebra)
(category! 'comb-kk-null 'algebra)
(category! 'comb-kk-above 'algebra)
(category! 'comb-kk-0-0 'algebra)
