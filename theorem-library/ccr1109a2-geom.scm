;;; ccr1109a2-geom.scm -- wave of 2026-11-09/10 (agent CCR-1109-A2), wired 2026-11-10 from scratchpad/ccr1109a2/ccr1109a2-geom.scm.
;;; Library: algebra.

;;; ccr1109a2-geom.scm -- THE GEOMETRIC SUM IN A COMMUTATIVE RING:
;;;   (1 - z) * sum_{k < n} z^k = 1 - z^n
;;; with the finite sum SUM-AG over RING-ADDITIVE-AG(R) and the power RING-POWER.  Only the real and complex
;;; versions existed (geometric-partial-sum-mul, aif-geometric-partial).  Used by CCR.pdf Proposition 1.47 (the
;;; Neumann series, theorem-library/ccr1109a2-nv.scm).  Agent CCR-1109-A2, wave 2026-11-09.
;;; Destination: theorem-library/ccr1109a2-geom.scm.  Library: algebra (commutative rings, finite sums).
;;; LOAD WINDOW: after rake-finsum-laws2 / ag-view-read-offs (ras-carr, ras-op, ras-id), rake-combinatorics
;;; (ring-power-succ), rake-finsum-typing (ring-power-type) and the sum-ag-succ / sum-ag-zero /
;;; sum-ag-type-ring-additive-ag laws; before ccr1109a2-nv.  Helper prefix c9g-.

(define (c9g-pw z n) `(RING-POWER R ,z ,n))
(define c9g-f '(VNB-LAMBDA cgk NN (RING-POWER R cgz cgk)))
(define c9g-ag '(RING-ADDITIVE-AG R))
(define (c9g-sum n) `(SUM-AG ,c9g-ag ,c9g-f ,n))
(define c9g-omz '((ADD R) (ONE R) ((NEG R) cgz)))

(define (c9g-body n)
  `(= ((MUL R) ,c9g-omz ,(c9g-sum n)) ((ADD R) (ONE R) ((NEG R) ,(c9g-pw 'cgz n)))))

(define (c9g-prep!)
  (dk-cite! 'commutative-ring-is-ring 'R)
  (dk-cite! 'ras-carr 'R) (dk-cite! 'ras-op 'R) (dk-cite! 'ras-id 'R))

(sp (make-wff `(FORALL cgn (IMPLIES (IN cgn NN) (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
  (FORALL cgz (IMPLIES (IN cgz (CARR R)) ,(c9g-body 'cgn)))))))))
(let* ((r (dk-ni-fixed! '(R cgz))) (base (cdr (assq 'base r))) (step (cdr (assq 'step r))))
  (dk-focus! base)
  (dk-peel!)
  (c9g-prep!)
  (subst (dk-cite! 'sum-ag-zero c9g-ag c9g-f))
  (subst `(= (IDEN ,c9g-ag) (ZERO R)))
  (subst (dk-cite! 'ring-power-zero 'R 'cgz))
  (crs)
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (cadr (dk-pick (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN))) "n in NN")))
         (ih (dk-pick (lambda (f) (and (dk-head-is? f '=) (dk-contains? f 'SUM-AG))) "the IH"))
         (s (c9g-sum nv))
         (p (c9g-pw 'cgz nv)))
    (c9g-prep!)
    (dk-cite! 'ring-power-type 'R 'cgz nv)
    (dk-have! `(IN ,c9g-f (FUN NN (CARR R)))
      (lambda () (dk-lam-type! (lambda () (let ((w (dk-di-var!))) (dk-cite! 'ring-power-type 'R 'cgz w) (dk-close-if-asm!))))))
    (dk-cite! 'sum-ag-type-ring-additive-ag 'R c9g-f nv)
    (subst (dk-cite! 'sum-ag-succ c9g-ag c9g-f nv))
    (dk-lam-b!)
    (subst `(= (OPR ,c9g-ag) (ADD R)))
    (subst (dk-cite! 'ring-power-succ 'R 'cgz nv))
    (dk-have! `(= ((MUL R) ,c9g-omz ((ADD R) ,s ,p)) ((ADD R) ((MUL R) ,c9g-omz ,s) ((MUL R) ,c9g-omz ,p)))
      (lambda () (crs)))
    (subst `(= ((MUL R) ,c9g-omz ((ADD R) ,s ,p)) ((ADD R) ((MUL R) ,c9g-omz ,s) ((MUL R) ,c9g-omz ,p))))
    (subst ih)
    (crs)))
(qed 'ring-geometric-partial-sum-ind)

(sp (make-wff `(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R) (FORALL cgz (IMPLIES (IN cgz (CARR R))
  (FORALL cgn (IMPLIES (IN cgn NN) ,(c9g-body 'cgn)))))))))
(dk-peel!)
(let ((nv (cadr (dk-pick (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'NN))) "n in NN"))))
  (dk-chain-ass! (dk-cite! 'ring-geometric-partial-sum-ind nv 'R 'cgz))
  (dk-close-if-asm!))
(qed 'ring-geometric-partial-sum)
