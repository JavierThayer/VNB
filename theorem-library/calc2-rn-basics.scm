;;; calc2-rn-basics.scm -- the read-offs of RN(n) (structure-library/rn-vocab.scm).
;;; CALC-2, 2026-10-19.  Helper prefix: c2b-.

(define (c2b-open) (dk-open-leaves))

;;; the components of the RN(n) tuple are sets: what certifies the LIST.
(define (c2b-certify!)
  (fact 'rr-is-normed-field)
  (fact 'normed-field-as-commutative-ring-is-commutative-ring 'RR-NORMED-FIELD)
  (fact 'rr-is-set)
  (fact 'interval-in-set 1 'n)
  (dk-have! '(IN (FUN (INTERVAL 1 n) RR) SET)
    (lambda () (mac 'fun-set-iff) (dk-conj-close! (lambda () (ass))))))

;;; (1) the vectors
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (== (VEC (RN n)) (FUN (INTERVAL 1 n) RR))))))
(dk-peel!)
(c2b-certify!)
(mac 'RN)
(slot 'VEC)
(nth-r)
(qrfl)
(qed 'rn-vec)

;;; the generic read-off: certify, unfold RN, read the slot, reduce, beta to a fixpoint.
(define (c2b-readoff! accessor)
  (dk-peel!)
  (c2b-certify!)
  (mac 'RN)
  (slot accessor)
  (nth-r))

(define (c2b-dump tag)
  (display ";; C2B ") (display tag) (display " goal: ") (display (dk-goal)) (newline)
  (for-each (lambda (l) (display ";; C2B   open: ") (display (dk-goal-of l)) (newline)) (c2b-open)))

;;; (2) vector addition, coordinatewise
(define c2b-V '(FUN (INTERVAL 1 n) RR))
(define c2b-I '(INTERVAL 1 n))
(sp (make-wff (forall-guarded '(n x y i)
   (list '(IN n NN) (list 'IN 'x c2b-V) (list 'IN 'y c2b-V) (list 'IN 'i c2b-I))
   '(= (((VADD (RN n)) x y) i) (+ (x i) (y i))))))
(c2b-readoff! 'VADD)
(dk-lam-b!)
(dk-type! '(x i))
(dk-type! '(y i))
(rfl)
(qed 'rn-vadd-apply)

;;; (3) the scalar action, coordinatewise
(sp (make-wff (forall-guarded '(n r x i)
   (list '(IN n NN) '(IN r RR) (list 'IN 'x c2b-V) (list 'IN 'i c2b-I))
   '(= (((ACT (RN n)) r x) i) (* r (x i))))))
(c2b-readoff! 'ACT)
(dk-lam-b!)
(dk-type! '(x i))
(rfl)
(qed 'rn-act-apply)

;;; (4) negation, coordinatewise
(sp (make-wff (forall-guarded '(n x i)
   (list '(IN n NN) (list 'IN 'x c2b-V) (list 'IN 'i c2b-I))
   '(= (((VNEG (RN n)) x) i) (- (x i))))))
(c2b-readoff! 'VNEG)
(dk-lam-b!)
(dk-type! '(x i))
(rfl)
(qed 'rn-vneg-apply)

;;; (5) the zero vector, coordinatewise
(sp (make-wff (forall-guarded '(n i)
   (list '(IN n NN) (list 'IN 'i c2b-I))
   '(= ((VZERO (RN n)) i) 0))))
(c2b-readoff! 'VZERO)
(dk-lam-b!)
(rfl)
(qed 'rn-vzero-apply)

;;; (6) the norm
(sp (make-wff (forall-guarded '(n x)
   (list '(IN n NN) (list 'IN 'x c2b-V))
   '(== ((VNRM (RN n)) x) (RN-MAXABS x n)))))
(c2b-readoff! 'VNRM)
(dk-lam-b!)
(qrfl)
(qed 'rn-vnrm-apply)

;;; (7) the scalars
(sp (make-wff (forall-guarded '(n) (list '(IN n NN))
   '(== (SCAL (RN n)) (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)))))
(c2b-readoff! 'SCAL)
(qrfl)
(qed 'rn-scal)

;;; (8) the unit vectors
(sp (make-wff (forall-guarded '(n i)
   (list '(IN n NN) (list 'IN 'i c2b-I))
   '(= ((RN-UNIT n i) i) 1))))
(dk-peel!)
(mac 'RN-UNIT)
(dk-lam-b!)
(dk-if-branch! #t '(IF (= i i) 1 0) (lambda () (fact 'interval-elt-in-nn 1 'n 'i) (rfl)) (lambda () (rfl)))
(qed 'rn-unit-at-same)

(sp (make-wff (forall-guarded '(n i j)
   (list '(IN n NN) (list 'IN 'i c2b-I) (list 'IN 'j c2b-I) '(NOT (= j i)))
   '(= ((RN-UNIT n i) j) 0))))
(dk-peel!)
(mac 'RN-UNIT)
(dk-lam-b!)
(dk-if-branch! #f '(IF (= j i) 1 0) #f (lambda () (rfl)))
(qed 'rn-unit-at-other)

;;; (9) typing of the operations: each is a lambda on INTERVAL(1, n) once the slot is read
(define (c2b-lam-type-close!)
  (dk-lam-type!
    (lambda ()
      (dk-di-var!)
      (let ((g (dk-goal)))
        (if (dk-head-is? (cadr g) 'IF)
            (dk-case-if! (cadr g) (lambda (t? v) (in-rr)))
            (dk-type! (cadr g)))))
    (lambda () (fact 'interval-in-set 1 'n) (ass))))

(sp (make-wff (forall-guarded '(n x y)
   (list '(IN n NN) (list 'IN 'x c2b-V) (list 'IN 'y c2b-V))
   (list 'IN '((VADD (RN n)) x y) c2b-V))))
(c2b-readoff! 'VADD)
(dk-lam-b!)
(c2b-lam-type-close!)
(qed 'rn-vadd-in-vec)

(sp (make-wff (forall-guarded '(n r x)
   (list '(IN n NN) '(IN r RR) (list 'IN 'x c2b-V))
   (list 'IN '((ACT (RN n)) r x) c2b-V))))
(c2b-readoff! 'ACT)
(dk-lam-b!)
(c2b-lam-type-close!)
(qed 'rn-act-in-vec)

(sp (make-wff (forall-guarded '(n x)
   (list '(IN n NN) (list 'IN 'x c2b-V))
   (list 'IN '((VNEG (RN n)) x) c2b-V))))
(c2b-readoff! 'VNEG)
(dk-lam-b!)
(c2b-lam-type-close!)
(qed 'rn-vneg-in-vec)

(sp (make-wff (forall-guarded '(n) (list '(IN n NN))
   (list 'IN '(VZERO (RN n)) c2b-V))))
(c2b-readoff! 'VZERO)
(c2b-lam-type-close!)
(qed 'rn-vzero-in-vec)

(sp (make-wff (forall-guarded '(n i) (list '(IN n NN) (list 'IN 'i c2b-I))
   (list 'IN '(RN-UNIT n i) c2b-V))))
(dk-peel!)
(mac 'RN-UNIT)
(c2b-lam-type-close!)
(qed 'rn-unit-in-vec)
