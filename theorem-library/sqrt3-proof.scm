;;; sqrt3-proof.scm -- sqrt(3) is irrational, on the naturals:
;;;     forall p,q in NN.  q /= 0  =>  p*p /= 3*(q*q).
;;;
;;; A direct port of sqrt2-proof.scm's infinite descent, 2 -> 3, with nn-even-square
;;; replaced by nn-3-div-square (nn-mod3-proof.scm).  Every witness named by `obtain',
;;; typing and algebra by have!/from-context! (driver-kit), the factor-3 cancellation
;;; by nn-3-cancel and the order step by nn-lt-triple.  Asserts nothing of its own.
;;;
;;; Loads after nn-least-element (minimize!), nn-mod3-proof, and sqrt2-proof.

;;; =======================================================================
;;; sqrt(3) IRRATIONAL, on NN:  forall p,q in NN. q/=0 => p*p /= 3*(q*q).
;;; A port of sqrt2-proof.scm's descent, 2 -> 3, nn-even-square -> nn-3-div-square.
(define (s3-mul! a b)
  (have! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN))) (fact 'nn-mul-closed a b))
(define (s3-guard pv)
  (list 'AND (list 'IN pv 'NN)
        (list 'FORSOME 'q_
          (list 'AND (list 'IN 'q_ 'NN)
                (list 'AND (list 'NOT (list '= 'q_ 0))
                      (list '= (list '* pv pv) (list '* 3 (list '* 'q_ 'q_))))))))

(sp (make-wff '(FORALL p (IMPLIES (IN p NN)
                 (FORALL q (IMPLIES (IN q NN)
                   (IMPLIES (NOT (= q 0)) (NOT (= (* p p) (* 3 (* q q)))))))))))
(di)(di)(di)(di)(di)(di)

(define s3-R    (minimize! '(pv) (s3-guard 'pv) 'pv))
(define s3-w    (car (car s3-R)))
(define s3-T    (cadr s3-R))
(define s3-N    (caddr s3-R))
(define s3-main (proof-state-focus *ps*))
(define s3-minf (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) (dk-asms-of s3-main)))

(when s3-T (dk-focus! s3-T) (di) (di) (sk--split!) (ass))
(when s3-N
  (dk-focus! s3-N) (ew 'p)
  (for-each (lambda (leaf) (dk-focus! leaf)
              (let ((g (dk-goal-of leaf)))
                (if (and (pair? g) (eq? (car g) 'IN)) (ass) (begin (ew 'q) (from-context!)))))
            (dk-opened (lambda () (di)))))
(dk-focus! s3-main)

(define s3-q0  (obtain (lambda () (ai (s3-guard s3-w)))))
(define s3-weq (list '= (list '* s3-w s3-w) (list '* 3 (list '* s3-q0 s3-q0))))

;; 3 | w  ->  w = 3k
(s3-mul! s3-q0 s3-q0)
(have! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s3-w s3-w) '(* 3 m))))
       (lambda () (ew (list '* s3-q0 s3-q0)) (from-context!)))
(define s3-k   (obtain (lambda () (fact 'nn-3-div-square s3-w))))
(define s3-keq (list '= s3-w (list '* 3 s3-k)))

;; q0*q0 = 3*(k*k)
(s3-mul! s3-k s3-k)
(s3-mul! 3 (list '* s3-k s3-k))
(have! (list '= (list '* 3 (list '* s3-q0 s3-q0)) (list '* 3 (list '* 3 (list '* s3-k s3-k))))
       (lambda () (subst (list '= (list '* 3 (list '* s3-q0 s3-q0)) (list '* s3-w s3-w)))
                  (subst s3-keq) (crs)))
(fact 'nn-3-cancel (list '* s3-q0 s3-q0) (list '* 3 (list '* s3-k s3-k)))

;; 3 | q0  ->  q0 = 3 m0
(have! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s3-q0 s3-q0) '(* 3 m))))
       (lambda () (ew (list '* s3-k s3-k)) (from-context!)))
(define s3-m0  (obtain (lambda () (fact 'nn-3-div-square s3-q0))))
(define s3-meq (list '= s3-q0 (list '* 3 s3-m0)))

;; k*k = 3*(m0*m0)
(s3-mul! s3-m0 s3-m0)
(s3-mul! 3 (list '* s3-m0 s3-m0))
(have! (list '= (list '* 3 (list '* s3-k s3-k)) (list '* 3 (list '* 3 (list '* s3-m0 s3-m0))))
       (lambda () (subst (list '= (list '* 3 (list '* s3-k s3-k)) (list '* s3-q0 s3-q0)))
                  (subst s3-meq) (crs)))
(fact 'nn-3-cancel (list '* s3-k s3-k) (list '* 3 (list '* s3-m0 s3-m0)))

;; nonzero chain
(have! (list 'NOT (list '= s3-m0 0))
   (lambda () (di)
     (have! (list '= s3-q0 0) (lambda () (subst s3-meq) (subst (list '= s3-m0 0)) (crs)))
     (ai (list 'NOT (list '= s3-q0 0)))))
(have! (list 'NOT (list '= (list '* s3-w s3-w) 0))
   (lambda ()
     (fact 'nn-mul-nonzero s3-q0 s3-q0)
     (have! (list 'AND '(IN 3 NN) (list 'IN (list '* s3-q0 s3-q0) 'NN)))
     (fact 'nn-mul-nonzero 3 (list '* s3-q0 s3-q0))
     (subst s3-weq) (ass)))
(have! (list 'NOT (list '= s3-w 0))
   (lambda () (di)
     (have! (list '= (list '* s3-w s3-w) 0) (lambda () (subst (list '= s3-w 0)) (crs)))
     (ai (list 'NOT (list '= (list '* s3-w s3-w) 0)))))
(have! (list 'NOT (list '= s3-k 0))
   (lambda () (di)
     (have! (list '= s3-w 0) (lambda () (subst s3-keq) (subst (list '= s3-k 0)) (crs)))
     (ai (list 'NOT (list '= s3-w 0)))))

;; GUARD(k): k is a smaller solution
(have! (s3-guard s3-k)
   (lambda ()
     (for-each (lambda (leaf) (dk-focus! leaf)
                 (let ((g (dk-goal-of leaf)))
                   (if (and (pair? g) (eq? (car g) 'IN)) (ass) (begin (ew s3-m0) (from-context!)))))
               (dk-opened (lambda () (di))))))

;; contradiction: minimality gives w<=k, but k<3k=w
(inst+ s3-minf s3-k)
(fact 'nn-lt-triple s3-k)                ; k < 3k
(have! (list '< s3-k s3-w) (lambda () (subst s3-keq) (ass)))
(fact 'nn-in-rr s3-k) (fact 'nn-in-rr s3-w)
(fact 'rr-lt-le-trans s3-k s3-w s3-k)
(have! (list 'AND (list '< s3-k s3-w) (list '<= s3-w s3-k)))
(detach! (list 'IMPLIES (list 'AND (list '< s3-k s3-w) (list '<= s3-w s3-k)) (list '< s3-k s3-k)))
(mac-h '< (list '< s3-k s3-k))
(let ((c (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (dk-asms-of (proof-state-focus *ps*)))))
  (if c (ai c)))
(have! (list '= s3-k s3-k) (lambda () (fact 'nn-succ-closed s3-k) (rfl)))
(ai (list 'NOT (list '= s3-k s3-k)))
(qed 'sqrt3-irrational)

