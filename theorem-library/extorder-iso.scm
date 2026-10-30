;;; extorder-iso.scm -- calculus.pdf 1.13 in full: x |-> x / (1 - |x|) extends to an order
;;; isomorphism of [-1, 1] onto the extended line RR-STAR, <= PRESERVED AND REFLECTED.
;;; Agent EXT-ORDER, 2026-10-26.  DESTINATION: theorem-library/extorder-iso.scm (or appended
;;; to theorem-library/extinf-iso.scm).  Library: analysis.
;;;
;;; F = VNB-LAMBDA(x, [-1, 1], IF(x = 1, POS-INF, IF(x = -1, NEG-INF, x / (1 - |x|)))), the map
;;; of RA-BASICS (rabasics-extline2.scm), copied literally.
;;;
;;;   rr-star-le-antisymm               <= is antisymmetric on RR-STAR (curried form)
;;;   ccint-rr-star-iso-reflects        F(u) <= F(v)  =>  u <= v   on [-1, 1]
;;;       EXT-INF's two -given-ends theorems with their antecedent NOT (POS-INF <= NEG-INF)
;;;       DISCHARGED by pos-inf-not-below-neg-inf (rr-star-order-thms.scm).
;;;   ccint-rr-star-iso-le-iff          u <= v  iff  F(u) <= F(v)   on [-1, 1]
;;;   ccint-rr-star-order-iso-le        F in BIJECTION([-1, 1], RR-STAR), and the le-iff:
;;;                                     the notes' "order preserving bijection" of [-1, 1]
;;;                                     onto the extended real line, <= both ways.
;;;
;;; CITATIONS: pos-inf-not-below-neg-inf (rr-star-order-thms), rr-star-le-antisymm-given-ends,
;;; ccint-rr-star-iso-reflects-given-ends, ccint-rr-star-iso-mono (extinf-iso),
;;; ccint-rr-star-iso-bijection (rabasics-extline2).
;;; LOAD WINDOW: after theorem-library/extinf-iso and rr-star-order-thms; no citer.
;;; Helper prefix: eoi-.

(define eoi-dom '(CCINT (- 1) 1))
(define eoi-F
  (list 'VNB-LAMBDA 'x eoi-dom
        (list 'IF '(= x 1) 'POS-INF
              (list 'IF '(= x (- 1)) 'NEG-INF (list '/ 'x (list '- 1 '(abs x)))))))

;;; ---------------------------------------------------------------------------
(sp (make-wff '(FORALL x (IMPLIES (IN x RR-STAR) (FORALL y (IMPLIES (IN y RR-STAR)
     (IMPLIES (<= x y) (IMPLIES (<= y x) (= x y)))))))))
(fact 'pos-inf-not-below-neg-inf)
(fact 'rr-star-le-antisymm-given-ends)         ; detaches NOT (POS-INF <= NEG-INF)
(ass)
(qed 'rr-star-le-antisymm)
(topic! 'rr-star-le-antisymm 'analysis)

;;; ---------------------------------------------------------------------------
(define eoi-reflects
  (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u eoi-dom)
    (list 'FORALL 'v (list 'IMPLIES (list 'IN 'v eoi-dom)
      (list 'IMPLIES (list '<= (list eoi-F 'u) (list eoi-F 'v)) '(<= u v)))))))
(sp (make-wff eoi-reflects))
(fact 'pos-inf-not-below-neg-inf)
(fact 'ccint-rr-star-iso-reflects-given-ends)
(ass)
(qed 'ccint-rr-star-iso-reflects)
(topic! 'ccint-rr-star-iso-reflects 'analysis)

;;; ---------------------------------------------------------------------------
(define eoi-le-iff
  (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u eoi-dom)
    (list 'FORALL 'v (list 'IMPLIES (list 'IN 'v eoi-dom)
      (list 'IFF '(<= u v) (list '<= (list eoi-F 'u) (list eoi-F 'v))))))))
(sp (make-wff eoi-le-iff))
(let* ((vs (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)))) (dk-peel!))))
       (u (car vs)) (v (cadr vs)))
  (dk-iff! (lambda (g) (pair? (cadr g)))      ; the consequent F(u) <= F(v)
    (lambda () (dk-cite! 'ccint-rr-star-iso-mono u v) (ass))
    (lambda () (dk-cite! 'ccint-rr-star-iso-reflects u v) (ass))))
(qed 'ccint-rr-star-iso-le-iff)
(topic! 'ccint-rr-star-iso-le-iff 'analysis)

;;; ---------------------------------------------------------------------------
(sp (make-wff (list 'AND (list 'IN eoi-F (list 'BIJECTION eoi-dom 'RR-STAR)) eoi-le-iff)))
(fact 'ccint-rr-star-iso-bijection)
(fact 'ccint-rr-star-iso-le-iff)
(dk-conj-close! (lambda () (ass)))
(qed 'ccint-rr-star-order-iso-le)
(topic! 'ccint-rr-star-order-iso-le 'analysis)
