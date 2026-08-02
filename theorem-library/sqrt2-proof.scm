;;; sqrt2-proof.scm -- sqrt(2) is irrational, stated on the naturals:
;;;
;;;     forall p,q in NN.  q /= 0  =>  p*p /= 2*(q*q).
;;;
;;; Infinite descent by `minimize!' on the numerator.  Suppose a solution
;;; exists; take one with p least.  p*p = 2*q*q is even, so p is even
;;; (nn-even-square), p = 2k; then q*q = 2*k*k, so q is even, q = 2m, and
;;; k*k = 2*m*m -- a smaller solution with k /= 0 and k < 2k = p, contradicting
;;; minimality.
;;;
;;; The only arithmetic content is nn-even-square (nn-parity-proof.scm).  Every
;;; witness is named by `obtain' (free-variable diff -- no navigation by assumption
;;; shape, which is what rotted the previous driver); the typing bookkeeping and
;;; the algebra go through `have!' / `from-context!' (driver-kit).  Asserts nothing
;;; of its own: nn-mul-nonzero and nn-2-cancel are now proven library theorems.
;;;
;;; Loads after nn-parity-proof / nn-integral (nn-even-square, nn-lt-double) and
;;; after interactive / driver-kit / minimize / sketch (obtain, sk--split!).

;; establish (IN (a*b) NN): cut the AND-antecedent, then nn-mul-closed detaches it.
(define (s2-mul! a b)
  (have! (list 'AND (list 'IN a 'NN) (list 'IN b 'NN)))
  (fact 'nn-mul-closed a b))

;; the descent guard: pv is a numerator with a companion denominator q_.
(define (s2-guard pv)
  (list 'AND (list 'IN pv 'NN)
        (list 'FORSOME 'q_
          (list 'AND (list 'IN 'q_ 'NN)
                (list 'AND (list 'NOT (list '= 'q_ 0))
                      (list '= (list '* pv pv) (list '* 2 (list '* 'q_ 'q_))))))))

(sp (make-wff '(FORALL p (IMPLIES (IN p NN)
                 (FORALL q (IMPLIES (IN q NN)
                   (IMPLIES (NOT (= q 0)) (NOT (= (* p p) (* 2 (* q q)))))))))))
(di) (di) (di) (di) (di)                 ; p ; INp ; q ; INq ; q/=0
(di)                                     ; assume p*p = 2*(q*q) ; goal FALSITY

;; The least-counterexample FRAME via `use-infinite-descent' (driver-kit): it runs
;; minimize! on the numerator, discharges the TYPE obligation generically, and the
;; NONEMPTY obligation via the thunk below (witness (p,q) from context), then hands
;; back the minimal numerator and the minimality hypothesis.
(define s2-D (use-infinite-descent 'pv (s2-guard 'pv) 'pv
              (lambda ()                         ; NONEMPTY: forsome pv. GUARD(pv), witness p (companion q)
                (ew 'p)
                (for-each (lambda (leaf)
                            (dk-focus! leaf)
                            (let ((g (dk-goal-of leaf)))
                              (if (and (pair? g) (eq? (car g) 'IN)) (ass) (begin (ew 'q) (from-context!)))))
                          (dk-opened (lambda () (di)))))))
(define s2-w    (cdr (assq 'witness s2-D)))   ; the minimal numerator, an eigenconstant
(define s2-minf (cdr (assq 'minimal s2-D)))   ; minimality: forall pv. GUARD(pv) => s2-w <= pv

;; ---- descent ----------------------------------------------------------
(define s2-q0  (obtain (lambda () (ai (s2-guard s2-w)))))         ; companion denominator
(define s2-weq (list '= (list '* s2-w s2-w) (list '* 2 (list '* s2-q0 s2-q0))))

;; w even -> w = 2k
(s2-mul! s2-q0 s2-q0)
(have! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s2-w s2-w) '(* 2 m))))
       (lambda () (ew (list '* s2-q0 s2-q0)) (from-context!)))
(define s2-k   (obtain (lambda () (fact 'nn-even-square s2-w))))
(define s2-keq (list '= s2-w (list '* 2 s2-k)))

;; q0*q0 = 2*(k*k)
(s2-mul! s2-k s2-k)
(s2-mul! 2 (list '* s2-k s2-k))
(have! (list '= (list '* 2 (list '* s2-q0 s2-q0)) (list '* 2 (list '* 2 (list '* s2-k s2-k))))
       (lambda () (subst (list '= (list '* 2 (list '* s2-q0 s2-q0)) (list '* s2-w s2-w)))
                  (subst s2-keq) (crs)))
(fact 'nn-2-cancel (list '* s2-q0 s2-q0) (list '* 2 (list '* s2-k s2-k)))    ; q0q0 = 2kk

;; q0 even -> q0 = 2 m0
(have! (list 'FORSOME 'm (list 'AND '(IN m NN) (list '= (list '* s2-q0 s2-q0) '(* 2 m))))
       (lambda () (ew (list '* s2-k s2-k)) (from-context!)))
(define s2-m0  (obtain (lambda () (fact 'nn-even-square s2-q0))))
(define s2-meq (list '= s2-q0 (list '* 2 s2-m0)))

;; k*k = 2*(m0*m0)
(s2-mul! s2-m0 s2-m0)
(s2-mul! 2 (list '* s2-m0 s2-m0))
(have! (list '= (list '* 2 (list '* s2-k s2-k)) (list '* 2 (list '* 2 (list '* s2-m0 s2-m0))))
       (lambda () (subst (list '= (list '* 2 (list '* s2-k s2-k)) (list '* s2-q0 s2-q0)))
                  (subst s2-meq) (crs)))
(fact 'nn-2-cancel (list '* s2-k s2-k) (list '* 2 (list '* s2-m0 s2-m0)))    ; kk = 2 m0m0

;; ---- nonzero chain: m0 /= 0, w /= 0, k /= 0 ---------------------------
(have! (list 'NOT (list '= s2-m0 0))
   (lambda () (di)
     (have! (list '= s2-q0 0) (lambda () (subst s2-meq) (subst (list '= s2-m0 0)) (crs)))
     (ai (list 'NOT (list '= s2-q0 0)))))
(have! (list 'NOT (list '= (list '* s2-w s2-w) 0))
   (lambda ()
     (fact 'nn-mul-nonzero s2-q0 s2-q0)
     (have! (list 'AND '(IN 2 NN) (list 'IN (list '* s2-q0 s2-q0) 'NN)))
     (fact 'nn-mul-nonzero 2 (list '* s2-q0 s2-q0))
     (subst s2-weq) (ass)))
(have! (list 'NOT (list '= s2-w 0))
   (lambda () (di)
     (have! (list '= (list '* s2-w s2-w) 0) (lambda () (subst (list '= s2-w 0)) (crs)))
     (ai (list 'NOT (list '= (list '* s2-w s2-w) 0)))))
(have! (list 'NOT (list '= s2-k 0))
   (lambda () (di)
     (have! (list '= s2-w 0) (lambda () (subst s2-keq) (subst (list '= s2-k 0)) (crs)))
     (ai (list 'NOT (list '= s2-w 0)))))

;; ---- GUARD(k): k is a smaller solution --------------------------------
(have! (s2-guard s2-k)
   (lambda ()
     (for-each (lambda (leaf)
                 (dk-focus! leaf)
                 (let ((g (dk-goal-of leaf)))
                   (if (and (pair? g) (eq? (car g) 'IN)) (ass)
                       (begin (ew s2-m0) (from-context!)))))
               (dk-opened (lambda () (di))))))

;; ---- contradiction: minimality gives w<=k, but k<2k=w -----------------
(inst+ s2-minf s2-k)                     ; GUARD(k) => w <= k, detached
(fact 'nn-lt-double s2-k)                ; k < 2k
(have! (list '< s2-k s2-w) (lambda () (subst s2-keq) (ass)))
(fact 'nn-in-rr s2-k) (fact 'nn-in-rr s2-w)
(fact 'rr-lt-le-trans s2-k s2-w s2-k)    ; lands (k<w AND w<=k) => k<k  (AND antecedent)
(have! (list 'AND (list '< s2-k s2-w) (list '<= s2-w s2-k)))
(detach! (list 'IMPLIES (list 'AND (list '< s2-k s2-w) (list '<= s2-w s2-k)) (list '< s2-k s2-k)))
(mac-h '< (list '< s2-k s2-k))
(let ((c (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'AND))) (dk-asms-of (proof-state-focus *ps*)))))
  (if c (ai c)))
(have! (list '= s2-k s2-k) (lambda () (fact 'nn-succ-closed s2-k) (rfl)))
(ai (list 'NOT (list '= s2-k s2-k)))

(qed 'sqrt2-irrational)
