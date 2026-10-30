;;; rr-star-order-thms.scm -- consequences of the order axioms of RR-STAR (rr-star-order.scm).
;;; Agent EXT-ORDER, 2026-10-26.  DESTINATION: theorem-library/rr-star-order-thms.scm.
;;; Library: analysis.
;;;
;;;   pos-inf-not-below-neg-inf             NOT (POS-INF <= NEG-INF)
;;;       a THEOREM, not an axiom: neg-inf-lower-bound at POS-INF gives NEG-INF <= POS-INF;
;;;       with POS-INF <= NEG-INF antisymmetry gives POS-INF = NEG-INF, against
;;;       pos-inf-neq-neg-inf.  (The one comparison EXT-INF's finding G1 left open.)
;;;   rr-leq-reflexive-via-star             the four RR order axioms of number-systems.scm,
;;;   rr-leq-antisymmetric-via-star         restated literally and proven from their
;;;   rr-leq-transitive-via-star            RR-STAR counterparts through RR subset RR-STAR:
;;;   rr-leq-total-via-star                 they are now special cases.
;;;   rr-star-leq-antisymmetric-unguarded   (<= a b), (<= b a) => a = b, no membership guard
;;;   rr-star-leq-transitive-unguarded      (<= a b), (<= b c) => a <= c, no membership guard
;;;       both through rr-star-leq-domain: its guards are implied by the <= antecedents.
;;;
;;; The -via-star theorems are alpha-equivalent to the primitives rr-leq-* (expected: they
;;; exist to show the inclusion; proven-duplicate-audit may list them -- keep or drop them
;;; at integration, nothing cites them).
;;;
;;; CITATIONS: rr-star-membership, the five rr-star-leq-* primitives (rr-star-order.scm),
;;; neg-inf-lower-bound, pos-inf-in-rr-star, neg-inf-in-rr-star, pos-inf-neq-neg-inf
;;; (theorem-library/rake-infinity-points).  Tactics: prop, driver-kit.
;;; LOAD WINDOW: after theorem-library/rake-infinity-points (1043); no citer in the tree
;;; (extorder-iso.scm cites pos-inf-not-below-neg-inf).  Slot: right after
;;; rake-infinity-points.
;;; Helper prefix: rso-.

(define (rso-star! tm keeper)
  (let ((g (list 'IN tm 'RR-STAR)))
    (if (not (dk-asm? g))
        (dk-have! g
          (lambda ()
            (let ((inst (dk-cite! 'rr-star-membership tm)))
              (if (dk-only! inst keeper) (prop))))))))

(define (rso-and! . fs)
  (let ((c (let loop ((l fs)) (if (null? (cdr l)) (car l) (list 'AND (car l) (loop (cdr l)))))))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (ass))))))))

;;; the variables of the RR typings the peel landed, in order (after splitting)
(define (rso-rr-vars)
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (symbol? (cadr f)) (eq? (caddr f) 'RR)))
                    (dk-asms))))

;;; ---------------------------------------------------------------------------
(sp (make-wff '(NOT (<= POS-INF NEG-INF))))
(di)                                              ; POS-INF <= NEG-INF assumed; FALSITY
(fact 'pos-inf-in-rr-star)
(fact 'neg-inf-in-rr-star)
(dk-cite! 'neg-inf-lower-bound 'POS-INF)          ; NEG-INF <= POS-INF
(rso-and! '(IN POS-INF RR-STAR) '(IN NEG-INF RR-STAR))
(rso-and! '(<= POS-INF NEG-INF) '(<= NEG-INF POS-INF))
(dk-cite! 'rr-star-leq-antisymmetric 'POS-INF 'NEG-INF)   ; POS-INF = NEG-INF
(fact 'pos-inf-neq-neg-inf)
(ai '(NOT (= POS-INF NEG-INF)))
(qed 'pos-inf-not-below-neg-inf)
(topic! 'pos-inf-not-below-neg-inf 'analysis)

;;; ---------------------------------------------------------------------------
;;; the RR order axioms as special cases (statements copied literally from number-systems.scm)
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (<= a a)))))
(dk-peel!)
(let ((a (car (rso-rr-vars))))
  (rso-star! a (list 'IN a 'RR))
  (dk-cite! 'rr-star-leq-reflexive a)
  (ass))
(qed 'rr-leq-reflexive-via-star)
(topic! 'rr-leq-reflexive-via-star 'analysis)

(sp (make-wff '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (IMPLIES (AND (<= a b) (<= b a)) (= a b)))))))
(dk-peel!)
(dk-split-all!)
(let* ((g (dk-goal)) (a (cadr g)) (b (caddr g)))
  (rso-star! a (list 'IN a 'RR))
  (rso-star! b (list 'IN b 'RR))
  (rso-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR))
  (rso-and! (list '<= a b) (list '<= b a))
  (dk-cite! 'rr-star-leq-antisymmetric a b)
  (ass))
(qed 'rr-leq-antisymmetric-via-star)
(topic! 'rr-leq-antisymmetric-via-star 'analysis)

(sp (make-wff '(FORALL a (FORALL b (FORALL c
      (IMPLIES (AND (IN a RR) (AND (IN b RR) (IN c RR)))
               (IMPLIES (AND (<= a b) (<= b c)) (<= a c))))))))
(dk-peel!)
(dk-split-all!)
(let* ((g (dk-goal)) (a (cadr g)) (c (caddr g))
       (b (caddr (car (filter (lambda (f) (and (dk-head-is? f '<=) (eq? (cadr f) a) (not (eq? (caddr f) c))))
                              (dk-asms))))))
  (rso-star! a (list 'IN a 'RR))
  (rso-star! b (list 'IN b 'RR))
  (rso-star! c (list 'IN c 'RR))
  (rso-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR) (list 'IN c 'RR-STAR))
  (rso-and! (list '<= a b) (list '<= b c))
  (dk-cite! 'rr-star-leq-transitive a b c)
  (ass))
(qed 'rr-leq-transitive-via-star)
(topic! 'rr-leq-transitive-via-star 'analysis)

(sp (make-wff '(FORALL a (FORALL b
      (IMPLIES (AND (IN a RR) (IN b RR))
               (OR (<= a b) (<= b a)))))))
(dk-peel!)
(dk-split-all!)
(let* ((g (dk-goal)) (a (cadr (cadr g))) (b (caddr (cadr g))))
  (rso-star! a (list 'IN a 'RR))
  (rso-star! b (list 'IN b 'RR))
  (rso-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR))
  (dk-cite! 'rr-star-leq-total a b)
  (ass))
(qed 'rr-leq-total-via-star)
(topic! 'rr-leq-total-via-star 'analysis)

;;; ---------------------------------------------------------------------------
;;; the guards the domain axiom makes redundant
(sp (make-wff '(FORALL a (FORALL b (IMPLIES (<= a b) (IMPLIES (<= b a) (= a b)))))))
(dk-peel!)
(let* ((g (dk-goal)) (a (cadr g)) (b (caddr g)))
  (dk-cite! 'rr-star-leq-domain a b)               ; a, b in RR-STAR
  (dk-split-all!)
  (rso-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR))
  (rso-and! (list '<= a b) (list '<= b a))
  (dk-cite! 'rr-star-leq-antisymmetric a b)
  (ass))
(qed 'rr-star-leq-antisymmetric-unguarded)
(topic! 'rr-star-leq-antisymmetric-unguarded 'analysis)

(sp (make-wff '(FORALL a (FORALL b (FORALL c (IMPLIES (<= a b) (IMPLIES (<= b c) (<= a c))))))))
(dk-peel!)
(let* ((g (dk-goal)) (a (cadr g)) (c (caddr g))
       (b (caddr (car (filter (lambda (f) (and (dk-head-is? f '<=) (eq? (cadr f) a) (not (eq? (caddr f) c))))
                              (dk-asms))))))
  (dk-cite! 'rr-star-leq-domain a b)
  (dk-cite! 'rr-star-leq-domain b c)
  (dk-split-all!)
  (rso-and! (list 'IN a 'RR-STAR) (list 'IN b 'RR-STAR) (list 'IN c 'RR-STAR))
  (rso-and! (list '<= a b) (list '<= b c))
  (dk-cite! 'rr-star-leq-transitive a b c)
  (ass))
(qed 'rr-star-leq-transitive-unguarded)
(topic! 'rr-star-leq-transitive-unguarded 'analysis)
