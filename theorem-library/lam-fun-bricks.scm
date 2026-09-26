;;; lam-fun-bricks.scm -- the lambda FUN-typing bricks of the matrix arc, PROVEN.
;;;
;;; Each theorem below states that a summand lambda  j |-> <ring or module term>
;;; is a member of FUN(INTERVAL(1,b), CARR(...)).  All were asserted supports
;;; whose warrants recited the same chain (entry-in-carrier, MUL closure,
;;; module-act-type, finsum-type, ras-carr / mvag-carr); `dk-lam-fun!'
;;; (driver-kit.scm) IS that chain, so each proof is one call.
;;;
;;; Statements are written exactly as the supports were: the te-typ / ms-typ /
;;; mra-wf builders of triple-entry-proof.scm, matact-assoc-proof.scm and
;;; matact-row-linear-proof.scm are reproduced here verbatim (lfb- prefix).
;;;
;;; Load window [lo, hi): lo is AFTER theorem-library/finsum-fiber (cartesian-nth,
;;; for the two CARTESIAN-domain bricks) -- everything else cited loads earlier
;;; (entry-in-carrier, op-typing, interval-card-in-nn, pair-tuple-sethood,
;;; finsum-type, matrix/mod-seq/elementary-matrix/module).  hi is
;;; theorem-library/triple-entry-proof, the first file that both DEFINES (te-typ)
;;; and cites the tel-/ter- bricks.

(define (lfb-wf v b) (fold-right (lambda (x y) `(FORALL ,x ,y)) b v))
(define (lfb-wi p b) (fold-right (lambda (x y) `(IMPLIES ,x ,y)) b p))

;; PREP (optional) runs after the peel and before dk-lam-fun!: it lands the
;; facts the typing chain cannot find on its own -- since 2026-09-16 (the
;; SIZE/MAT change) the product typings (matmul-type, matact-type) carry the
;; guard `n = 0 implies (m = 0 or k = 0)', and matunit-type carries `n in NN'.
(define (lfb-run name stmt #!optional prep)
  (sp stmt)
  (dk-peel!)
  (if (not (default-object? prep)) (prep))
  (dk-lam-fun!)
  (qed name)
  (topic! name 'algebra))


;; (<= 1 v) in context: land a product guard (IMPLIES (= v 0) ...) by prop.
(define (lfb-guard! v g)
  (lambda ()
    (if (not (dk-asm? (list 'NOT (list '= v 0)))) (dk-nonzero! v))
    (dk-have-prop! g)))

;;; ---- matrix.scm / mod-seq.scm / elementary-matrix.scm bricks ----

(lfb-run 'matprod-summand-type
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL kc (FORALL P (FORALL Q (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN Q (MAT n kc (CARR A)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 kc))
         (IN (VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P i j) (ENTRY Q j c)))
             (FUN (INTERVAL 1 n) (CARR (RING-ADDITIVE-AG A))))))))))))))))))

(lfb-run 'matmul-assoc-summand-type
  '(FORALL A (IMPLIES (IS-RING A) (FORALL M (FORALL N (FORALL K (FORALL L (FORALL P (FORALL Q (FORALL R (FORALL ROW (FORALL COL (IMPLIES (IN P (MAT M N (CARR A))) (IMPLIES (IN Q (MAT N K (CARR A))) (IMPLIES (IN R (MAT K L (CARR A))) (IMPLIES (IN ROW (INTERVAL 1 M)) (IMPLIES (IN COL (INTERVAL 1 L)) (IN (VNB-LAMBDA Z (CARTESIAN (INTERVAL 1 K) (INTERVAL 1 N)) ((MUL A) ((MUL A) (ENTRY P ROW (NTH 2 Z)) (ENTRY Q (NTH 2 Z) (NTH 1 Z))) (ENTRY R (NTH 1 Z) COL))) (FUN (CARTESIAN (INTERVAL 1 K) (INTERVAL 1 N)) (CARR (RING-ADDITIVE-AG A)))))))))))))))))))))

(lfb-run 'matact-summand-type
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL m (FORALL n (FORALL q (FORALL P (FORALL u (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR (SCAL md))))
       (IMPLIES (IN u (MAT n q (VEC md)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 q))
         (IN (VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY P i j) (ENTRY u j c)))
             (FUN (INTERVAL 1 n) (CARR (MODULE-VECTOR-AG md))))))))))))))))))

(lfb-run 'matunit-summand-type
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL P (FORALL k (FORALL l (FORALL i (FORALL c
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN i (INTERVAL 1 m))
       (IMPLIES (IN c (INTERVAL 1 n))
         (IN (VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P i j) (ENTRY (MATUNIT A n k l) j c)))
             (FUN (INTERVAL 1 n) (CARR (RING-ADDITIVE-AG A))))))))))))))))
  ;; matunit-type is guarded on n in NN; n is P's column count
  (lambda () (fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)))

;;; ---- triple-entry-proof.scm: the te-typ family (ring) ----

(define lfb-te-rag '(RING-ADDITIVE-AG A))
(define lfb-te-ff '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((MUL A) ((MUL A) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY R (NTH 1 z) col))))
(define lfb-te-prems '((IN P (MAT m n (CARR A))) (IN Q (MAT n k (CARR A))) (IN R (MAT k l (CARR A))) (IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l))))
(define (lfb-te name lam carr bound ev ep #!optional prep)
  (lfb-run name
    (lfb-wf '(A) (lfb-wi '((IS-RING A)) (lfb-wf (append '(m n k l P Q R row col) ev) (lfb-wi (append lfb-te-prems ep) `(IN ,lam (FUN (INTERVAL 1 ,bound) ,carr))))))
    (if (default-object? prep) (lambda () #t) prep)))

(define lfb-tel-outf '(VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY (MATMUL A P Q) row j) (ENTRY R j col))))
(define lfb-tel-tout `(VNB-LAMBDA c (INTERVAL 1 k) (FINSUM ,lfb-te-rag (VNB-LAMBDA j (INTERVAL 1 n) (,lfb-te-ff (LIST c j))) (INTERVAL 1 n))))
;; GUARDED 2026-09-16 on (<= 1 n), after the col premise.  Without it FALSE:
;; n = 0, m = k = l = 1: Q = [] is in MAT(0,1), P = [[]] is 1-by-0, PQ is
;; 1-by-0 (MATMUL reads its column count off SIZE([]) = [0,0]), so
;; ENTRY(PQ, 1, 1) is undefined and the lambda is not a function on [1,1].
(lfb-te 'tel-outf-type lfb-tel-outf `(CARR ,lfb-te-rag) 'k '() '((<= 1 n))
  (lfb-guard! 'n '(IMPLIES (= n 0) (OR (= m 0) (= k 0)))))
(lfb-te 'tel-tout-type lfb-tel-tout `(CARR ,lfb-te-rag) 'k '() '())
(lfb-te 'tel-inf-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j x))) '(CARR A) 'n '(x) '((IN x (INTERVAL 1 k))))
(lfb-te 'tel-dist-type '(VNB-LAMBDA z (INTERVAL 1 n) ((MUL A) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY Q j x))) z) (ENTRY R x col))) `(CARR ,lfb-te-rag) 'n '(x) '((IN x (INTERVAL 1 k))))
(lfb-te 'tel-red-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) ((MUL A) (ENTRY P row j) (ENTRY Q j x)) (ENTRY R x col))) `(CARR ,lfb-te-rag) 'n '(x) '((IN x (INTERVAL 1 k))))

(define lfb-ter-outf '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P row j) (ENTRY (MATMUL A Q R) j col))))
(define lfb-ter-tout `(VNB-LAMBDA j (INTERVAL 1 n) (FINSUM ,lfb-te-rag (VNB-LAMBDA c (INTERVAL 1 k) (,lfb-te-ff (LIST c j))) (INTERVAL 1 k))))
;; GUARDED 2026-09-16 on (<= 1 k), after the col premise.  Without it FALSE:
;; k = 0, m = n = l = 1: R = [] is in MAT(0,1), Q = [[]] is 1-by-0, QR is
;; 1-by-0, so ENTRY(QR, j, col) is undefined at j = col = 1.
(lfb-te 'ter-outf-type lfb-ter-outf `(CARR ,lfb-te-rag) 'n '() '((<= 1 k))
  (lfb-guard! 'k '(IMPLIES (= k 0) (OR (= n 0) (= l 0)))))
(lfb-te 'ter-tout-type lfb-ter-tout `(CARR ,lfb-te-rag) 'n '() '())
(lfb-te 'ter-gj-type '(VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q x j) (ENTRY R j col))) '(CARR A) 'k '(x) '((IN x (INTERVAL 1 n))))
(lfb-te 'ter-dist-type '(VNB-LAMBDA z (INTERVAL 1 k) ((MUL A) (ENTRY P row x) ((VNB-LAMBDA j (INTERVAL 1 k) ((MUL A) (ENTRY Q x j) (ENTRY R j col))) z))) `(CARR ,lfb-te-rag) 'k '(x) '((IN x (INTERVAL 1 n))))
(lfb-te 'ter-red-type '(VNB-LAMBDA c (INTERVAL 1 k) ((MUL A) ((MUL A) (ENTRY P row x) (ENTRY Q x c)) (ENTRY R c col))) `(CARR ,lfb-te-rag) 'k '(x) '((IN x (INTERVAL 1 n))))

;;; ---- matact-assoc-proof.scm: the ms-typ family (module) ----

(define lfb-ms-vag '(MODULE-VECTOR-AG md))
(define lfb-ms-sc  '(CARR (SCAL md)))
(define lfb-ms-vc  '(CARR (MODULE-VECTOR-AG md)))
(define lfb-ms-ff '(VNB-LAMBDA z (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ((ACT md) ((MUL (SCAL md)) (ENTRY P row (NTH 2 z)) (ENTRY Q (NTH 2 z) (NTH 1 z))) (ENTRY u (NTH 1 z) col))))
(define lfb-ms-prems '((IN P (MAT m n (CARR (SCAL md)))) (IN Q (MAT n k (CARR (SCAL md)))) (IN u (MAT k l (VEC md))) (IN row (INTERVAL 1 m)) (IN col (INTERVAL 1 l))))
(define (lfb-ms name lam carr bound ev ep #!optional prep)
  (lfb-run name
    (lfb-wf '(md) (lfb-wi '((IS-MODULE md)) (lfb-wf (append '(m n k l P Q u row col) ev) (lfb-wi (append lfb-ms-prems ep) `(IN ,lam (FUN (INTERVAL 1 ,bound) ,carr))))))
    (if (default-object? prep) (lambda () #t) prep)))

(define lfb-mal-outf '(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY (MATMUL (SCAL md) P Q) row j) (ENTRY u j col))))
(define lfb-mal-tout `(VNB-LAMBDA c (INTERVAL 1 k) (FINSUM ,lfb-ms-vag (VNB-LAMBDA j (INTERVAL 1 n) (,lfb-ms-ff (LIST c j))) (INTERVAL 1 n))))
;; GUARDED 2026-09-16 on (<= 1 n), after the col premise: tel-outf-type's
;; counterexample over the scalar ring (n = 0, m = k = l = 1: PQ is 1-by-0).
(lfb-ms 'mal-outf-type lfb-mal-outf lfb-ms-vc 'k '() '((<= 1 n))
  (lfb-guard! 'n '(IMPLIES (= n 0) (OR (= m 0) (= k 0)))))
(lfb-ms 'mal-tout-type lfb-mal-tout lfb-ms-vc 'k '() '())
(lfb-ms 'mal-inf-type '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x))) lfb-ms-sc 'n '(x) '((IN x (INTERVAL 1 k))))
(lfb-ms 'mal-dist-type '(VNB-LAMBDA z (INTERVAL 1 n) ((ACT md) ((VNB-LAMBDA j (INTERVAL 1 n) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x))) z) (ENTRY u x col))) lfb-ms-vc 'n '(x) '((IN x (INTERVAL 1 k))))
(lfb-ms 'mal-red-type '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) ((MUL (SCAL md)) (ENTRY P row j) (ENTRY Q j x)) (ENTRY u x col))) lfb-ms-vc 'n '(x) '((IN x (INTERVAL 1 k))))

(define lfb-mar-outf '(VNB-LAMBDA j (INTERVAL 1 n) ((ACT md) (ENTRY P row j) (ENTRY (MATACT md Q u) j col))))
(define lfb-mar-tout `(VNB-LAMBDA j (INTERVAL 1 n) (FINSUM ,lfb-ms-vag (VNB-LAMBDA c (INTERVAL 1 k) (,lfb-ms-ff (LIST c j))) (INTERVAL 1 k))))
;; GUARDED 2026-09-16 on (<= 1 k), after the col premise: ter-outf-type's
;; counterexample (k = 0, m = n = l = 1: u = [], MATACT(md,Q,u) is 1-by-0).
(lfb-ms 'mar-outf-type lfb-mar-outf lfb-ms-vc 'n '() '((<= 1 k))
  (lfb-guard! 'k '(IMPLIES (= k 0) (OR (= n 0) (= l 0)))))
(lfb-ms 'mar-tout-type lfb-mar-tout lfb-ms-vc 'n '() '())
(lfb-ms 'mar-gj-type '(VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q x j) (ENTRY u j col))) lfb-ms-vc 'k '(x) '((IN x (INTERVAL 1 n))))
(lfb-ms 'mar-dist-type '(VNB-LAMBDA z (INTERVAL 1 k) ((ACT md) (ENTRY P row x) ((VNB-LAMBDA j (INTERVAL 1 k) ((ACT md) (ENTRY Q x j) (ENTRY u j col))) z))) lfb-ms-vc 'k '(x) '((IN x (INTERVAL 1 n))))
(lfb-ms 'mar-red-type '(VNB-LAMBDA c (INTERVAL 1 k) ((ACT md) ((MUL (SCAL md)) (ENTRY P row x) (ENTRY Q x c)) (ENTRY u c col))) lfb-ms-vc 'k '(x) '((IN x (INTERVAL 1 n))))

(lfb-run 'matact-assoc-summand-type
  (lfb-wf '(md) (lfb-wi '((IS-MODULE md))
    (lfb-wf '(m n k l P Q u row col) (lfb-wi lfb-ms-prems
      `(IN ,lfb-ms-ff (FUN (CARTESIAN (INTERVAL 1 k) (INTERVAL 1 n)) ,lfb-ms-vc)))))))

;;; ---- matact-row-linear-proof.scm: the two row-linearity summands ----

(define lfb-mra-vc  '(CARR (MODULE-VECTOR-AG md)))
(define lfb-mra-ivl '(INTERVAL 1 n))
(define (lfb-mra-row c) (list 'VNB-LAMBDA 'j lfb-mra-ivl (list '(ACT md) (list 'ENTRY c 1 'j) '(ENTRY u j 1))))
(define lfb-mra-g (list 'VNB-LAMBDA 'z lfb-mra-ivl
                        (list '(OPR (MODULE-VECTOR-AG md)) (list (lfb-mra-row 'c1) 'z) (list (lfb-mra-row 'c2) 'z))))
(define lfb-mra-prems
  '((IN c1 (MAT 1 n (CARR (SCAL md)))) (IN c2 (MAT 1 n (CARR (SCAL md)))) (IN u (MAT n 1 (VEC md)))))
(lfb-run 'mra-combined-summand-type
  (lfb-wf '(md) (lfb-wi '((IS-MODULE md))
    (lfb-wf '(n c1 c2 u) (lfb-wi lfb-mra-prems
      (list 'IN lfb-mra-g (list 'FUN lfb-mra-ivl lfb-mra-vc)))))))

(define lfb-mrs-g (list 'VNB-LAMBDA 'z lfb-mra-ivl (list '(ACT md) 'r (list (lfb-mra-row 'c) 'z))))
(define lfb-mrs-prems
  '((IN r (CARR (SCAL md))) (IN c (MAT 1 n (CARR (SCAL md)))) (IN u (MAT n 1 (VEC md)))))
(lfb-run 'mrs-scaled-summand-type
  (lfb-wf '(md) (lfb-wi '((IS-MODULE md))
    (lfb-wf '(n r c u) (lfb-wi lfb-mrs-prems
      (list 'IN lfb-mrs-g (list 'FUN lfb-mra-ivl lfb-mra-vc)))))))
