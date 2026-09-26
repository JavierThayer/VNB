;;; matact-summand-type-le-proof.scm -- matact-summand-type-le, GUARDED and PROVEN.
;;;
;;; The support at structure-library/mod-seq.scm:314 reads
;;;
;;;   forall md. IS-MODULE(md) => forall m n q P u i c k.
;;;     P in MAT(m,n,CARR(SCAL md)) => u in MAT(n,q,VEC md) =>
;;;     i in [1,m] => c in [1,q] => k <= n =>
;;;       (j |-> P_{ij} . u_{jc})  in  FUN([1,k], CARR(MODULE-VECTOR-AG md))
;;;
;;; with NO `k in NN', and that statement is FALSE as written -- or rather, it
;;; is not provable and the intended argument does not run.  The whole content
;;; is that [1,k] is inside [1,n], which is `interval-widen'
;;; (theorem-library/interval-widen), and interval-widen is GUARDED on BOTH
;;; bounds because the transitivity it uses, `nn-le-trans-guarded', demands that
;;; every term it chains through be a natural.  Nothing in the statement above
;;; types k: `k <= n' says nothing about k (the order is the RR order; a real
;;; k <= n is not thereby a natural).  So the guard `k in NN' goes on, exactly
;;; as interval-widen's own header argues for its b and c, and the theorem is
;;; installed here under the name matact-summand-type-le-guarded.
;;;
;;; The guard costs the citer NOTHING.  Both citation sites
;;; (theorem-library/span-bricks2-proof.scm:92 and :187) instantiate k := n
;;; with `IN n NN' among the premises of the theorem being proved, so `fact'
;;; auto-detaches the new antecedent and the ARGUMENT LIST does not change:
;;; the universal prefix (md, m, n, q, P, u, i, c, k) is byte-identical to the
;;; support's, and only the cited NAME moves.
;;;
;;; PROOF.  peel; `dk-lam-t!' (the sethood leaf is (IN (INTERVAL 1 k) SET),
;;; interval-in-set); peel the pointwise universal, which fixes j in [1,k];
;;; read `n in NN' off the matrix u by mat-rows-in-nn; carry j across to [1,n]
;;; by interval-widen; then the ordinary forward typing chain `dk-typ-close!'
;;; closes  P_{ij} . u_{jc} in CARR(MODULE-VECTOR-AG md)  -- entry-in-carrier
;;; twice (both now type, j being in [1,n]), module-act-type, and the mvag-carr
;;; bridge from VEC md to CARR(MODULE-VECTOR-AG md).
;;;
;;; LOAD WINDOW [theorem-library/interval-widen, theorem-library/span-bricks2-proof).
;;; lo is interval-widen, the latest-loading theorem cited (mat-basics,
;;; interval-basics and ag-view-read-offs all load earlier); hi is
;;; span-bricks2-proof, the first citer.
;;;
;;; Helper prefix: msl-.

(define msl-stmt
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u (FORALL i (FORALL c (FORALL k
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 q))
       (IMPLIES (IN k NN)
       (IMPLIES (<= k n)
         (IN (VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY P i j) (ENTRY u j c)))
             (FUN (INTERVAL 1 k) (CARR (MODULE-VECTOR-AG md)))))))))))))))))))))

(sp (make-wff msl-stmt))
(dk-peel!)
(dk-lam-t!)                             ; sethood closed; focus on the typing leaf
(dk-peel!)                              ; fixes j, lands (IN j (INTERVAL 1 k))
(fact 'mat-rows-in-nn 'n 'q '(VEC md) 'u)             ; (IN n NN)
(let* ((msl-g (dk-goal))                ; (IN ((ACT md) (ENTRY P i j) (ENTRY u j c)) ...)
       (msl-j (cadddr (cadr (cadr msl-g)))))          ; the eigenvariable j
  (fact 'interval-widen 'k 'n 1 msl-j))               ; (IN j (INTERVAL 1 n))
(dk-typ-close!)
(qed 'matact-summand-type-le-guarded)
(topic! 'matact-summand-type-le-guarded 'algebra)
