;;; rabasics-order.scm -- calculus.pdf 1.1, 1.3, 1.9 (complex-analysis.pdf 1.2): the order basics.
;;;
;;;   rr-lub-unique      For any set S, two least upper bounds of S coincide (calc 1.9, CA 1.2).
;;;   nn-one-le-nonzero  Every natural number of the notes is >= 1 (calc 1.3).  The notes' N starts
;;;                      at 1; VNB's NN contains 0, so the notes' N is NN minus {0}.
;;;   zz-lt-add-right    a < b in ZZ implies a + c < b + c (calc 1.1, additive half).
;;;   zz-lt-mul-right    a < b in ZZ, c a natural number of the notes (c in NN, c /= 0)
;;;                      implies a * c < b * c (calc 1.1, multiplicative half).
;;;
;;; A least upper bound is stated as the notes define it (Definition 1.8): an upper bound
;;; (RR-UPPER-BOUND, which includes membership in RR) that is <= every upper bound.  Uniqueness is
;;; antisymmetry, as in the notes' one-line proof.
;;;
;;; Library: core.  Load window: after theorem-library/zz-order (zz-discrete; it also follows
;;; nn-order-basics, nn-pos-of-nonzero, rr-order-basics); no citer yet.
;;; Helper prefix: rbo-.

(define (rbo-find what pred)
  (let ((l (filter pred (dk-asms))))
    (cond ((null? l) (error "rbo-find: nothing matching" what))
          ((pair? (cdr l)) (error "rbo-find: ambiguous" what))
          (#t (car l)))))

;;; ---------------------------------------------------------------------------
;;; rr-lub-unique
(sp (make-wff
  '(FORALL s (FORALL a1 (FORALL a2
     (IMPLIES (RR-UPPER-BOUND s a1)
      (IMPLIES (FORALL c (IMPLIES (RR-UPPER-BOUND s c) (<= a1 c)))
       (IMPLIES (RR-UPPER-BOUND s a2)
        (IMPLIES (FORALL c (IMPLIES (RR-UPPER-BOUND s c) (<= a2 c)))
         (= a1 a2))))))))))
(dk-peel!)
(define rbo-x (cadr (dk-goal)))
(define rbo-y (caddr (dk-goal)))
(define (rbo-least-of v)
  (rbo-find 'leastness
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (let ((b (caddr a)))
                       (and (pair? b) (eq? (car b) 'IMPLIES)
                            (pair? (caddr b)) (eq? (car (caddr b)) '<=)
                            (equal? (cadr (caddr b)) v)))))))
(define (rbo-ub-of v)
  (rbo-find 'upper-bound
    (lambda (a) (and (pair? a) (eq? (car a) 'RR-UPPER-BOUND) (equal? (caddr a) v)))))
(dk-project! (list 'IN rbo-x 'RR) 'rr-upper-bound (rbo-ub-of rbo-x))
(dk-project! (list 'IN rbo-y 'RR) 'rr-upper-bound (rbo-ub-of rbo-y))
(inst+ (rbo-least-of rbo-x) rbo-y)
(inst+ (rbo-least-of rbo-y) rbo-x)
(dk-have! (list 'AND (list 'IN rbo-x 'RR) (list 'IN rbo-y 'RR)))
(dk-have! (list 'AND (list '<= rbo-x rbo-y) (list '<= rbo-y rbo-x)))
(fact 'rr-leq-antisymmetric rbo-x rbo-y)
(ass)
(qed 'rr-lub-unique)

;;; ---------------------------------------------------------------------------
;;; nn-one-le-nonzero
(sp (make-wff
  '(FORALL c (IMPLIES (IN c NN) (IMPLIES (NOT (= c 0)) (<= 1 c))))))
(dk-peel!)
(define rbo-c (caddr (dk-goal)))
(fact 'nn-pos-of-nonzero rbo-c)
(fact 'nn-subset-zz rbo-c)
(fact 'zz-discrete rbo-c)
(ass)
(qed 'nn-one-le-nonzero)

;;; ---------------------------------------------------------------------------
;;; zz-lt-add-right
(sp (make-wff
  '(FORALL a (IMPLIES (IN a ZZ) (FORALL b (IMPLIES (IN b ZZ) (FORALL c (IMPLIES (IN c ZZ)
     (IMPLIES (< a b) (< (+ a c) (+ b c)))))))))))
(dk-peel!)
(let* ((g (dk-goal)) (a (cadr (cadr g))) (b (cadr (caddr g))) (c (caddr (cadr g))))
  (fact 'zz-in-rr a) (fact 'zz-in-rr b) (fact 'zz-in-rr c)
  (dk-ineq! (list '< a b)))
(qed 'zz-lt-add-right)

;;; ---------------------------------------------------------------------------
;;; zz-lt-mul-right
(sp (make-wff
  '(FORALL a (IMPLIES (IN a ZZ) (FORALL b (IMPLIES (IN b ZZ) (FORALL c (IMPLIES (IN c NN)
     (IMPLIES (< a b) (IMPLIES (NOT (= c 0)) (< (* a c) (* b c))))))))))))
(dk-peel!)
(let* ((g (dk-goal)) (a (cadr (cadr g))) (b (cadr (caddr g))) (c (caddr (cadr g))))
  (fact 'zz-in-rr a) (fact 'zz-in-rr b) (fact 'nn-in-rr c)
  (fact 'nn-pos-of-nonzero c)
  (dk-have! (list 'AND (list '< 0 c) (list '< a b)))
  (fact 'rr-lt-scale-pos c a b)
  (dk-have! (list 'AND (list 'IN a 'RR) (list 'IN c 'RR)))
  (dk-have! (list 'AND (list 'IN b 'RR) (list 'IN c 'RR)))
  (fact 'rr-mul-comm a c)
  (fact 'rr-mul-comm b c)
  (subst (list '= (list '* a c) (list '* c a)))
  (subst (list '= (list '* b c) (list '* c b)))
  (ass))
(qed 'zz-lt-mul-right)

(display ";; RBO qed failures: ") (display *vnb-qed-failures*) (newline)
;; (probe trailer removed at integration 2026-10-27) (page-audit!)
;; (probe trailer removed at integration 2026-10-27) (report-page-audit)
