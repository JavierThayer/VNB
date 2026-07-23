;;; nn-integral.scm -- the NN arithmetic support layer.
;;;
;;; NN inherits its arithmetic from ZZ.  NN <= ZZ, and ZZ is an ordered integral
;;; domain (zz-is-integral-domain), so every cancellation / zero-divisor fact NN
;;; was missing is the ZZ fact restricted to naturals.  Nothing here is asserted:
;;; the ZZ facts are TRANSPORTED to the surface (transport.scm), and each NN fact
;;; is proved by the inclusion nn-subset-zz.
;;;
;;;   zz-mul-cancel-zero  a,b in ZZ, a*b = 0, b /= 0  =>  a = 0     [transport!]
;;;   nn-mul-nonzero      a,b in NN, a /= 0, b /= 0    =>  a*b /= 0
;;;   nn-mul-cancel       a,b,c in NN, c /= 0, a*c=b*c =>  a = b
;;;   nn-2-cancel         2x = 2y => x = y                          [instance]
;;;
;;; These retire the reference assertions the sqrt(2) descent had to make.
;;; nn-lt-double (k /= 0 => k < 2k) is ORDER, not arithmetic, and belongs to an
;;; NN order calculus that does not exist yet; it is attempted from NN <= RR at
;;; the end and kept as `reference' if the surface bookkeeping resists.
;;;
;;; Loads after transport, cancellation, and the ZZ facts.

(define (ni-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (ni-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (ni-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (ni-goalof s) (wff-formula (sequent-node-assertion s)))
(define (ni-from-context!)
  (let ((g (ni-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (ni-from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g))) (arith))
      (else (ass)))))
(define (ni-cut! form #!optional thunk)
  (let* ((new  (dk-opened (lambda () (cut form))))
         (side (or (ni-any (lambda (s) (alpha-equiv? (ni-goalof s) form)) new)
                   (error "ni-cut!: no side goal for" form)))
         (main (or (ni-any (lambda (s) (not (eq? s side))) new)
                   (error "ni-cut!: no main branch for" form))))
    (dk-focus! side)
    (if (default-object? thunk) (ni-from-context!) (thunk))
    (dk-focus! main) main))
(define (ni-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** nn-integral: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (ni-goalof l))) (newline)
                    (for-each (lambda (w) (display "      | ")
                                (display (expression->string (wff-formula w))) (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 8 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "nn-integral: unfinished" name))))

;;; =======================================================================
;;; ZZ has no zero divisors, IN THE SURFACE LANGUAGE -- transported from the
;;; generic integral-domain law at ZZ-RING.  a,b in ZZ, a*b = 0, b /= 0 => a = 0.
(transport! 'integral-domain-cancel-zero 'ZZ-RING 'zz-is-integral-domain 'zz-mul-cancel-zero)

;;; =======================================================================
;;; nn-mul-nonzero : a,b in NN, a /= 0, b /= 0 => a*b /= 0.
(sp (make-wff '(FORALL a (IMPLIES (IN a NN) (IMPLIES (NOT (= a 0))
                 (FORALL b (IMPLIES (IN b NN) (IMPLIES (NOT (= b 0))
                   (NOT (= (* a b) 0))))))))))
(di)(di)(di)(di)(di)(di)                 ; a INa a/=0 b INb b/=0
(fact 'nn-subset-zz 'a)                  ; a in ZZ
(fact 'nn-subset-zz 'b)                  ; b in ZZ
(di)                                     ; assume a*b = 0 ; goal FALSITY
(fact 'zz-mul-cancel-zero 'a 'b)         ; a*b=0, b/=0 => a=0
(ai '(NOT (= a 0)))                      ; contradicts a /= 0
(ni-qed! 'nn-mul-nonzero)

;;; =======================================================================
;;; nn-mul-cancel : a,b,c in NN, c /= 0, a*c = b*c => a = b.
;;; In ZZ: (a-b)*c = a*c - b*c = 0, and c /= 0, so a-b = 0, so a = b.
(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (FORALL c (IMPLIES (IN c NN)
                     (IMPLIES (NOT (= c 0))
                       (IMPLIES (= (* a c) (* b c)) (= a b)))))))))))
(di)(di)(di)(di)(di)(di)(di)             ; a INa b INb c INc c/=0 ; assume ac=bc
(fact 'nn-subset-zz 'a)
(fact 'nn-subset-zz 'b)
(fact 'nn-subset-zz 'c)
;; a-b in ZZ
(fact 'zz-neg-closed 'b)                 ; -b in ZZ
(ni-cut! '(AND (IN a ZZ) (IN (- b) ZZ)))
(fact 'zz-add-closed 'a '(- b))          ; a + (-b) = a - b in ZZ
;; (a-b)*c = 0 : distribute, then use a*c = b*c.
(ni-cut! '(= (* (+ a (- b)) c) 0)
         (lambda ()
           (ni-cut! '(= (* (+ a (- b)) c) (+ (* a c) (- (* b c)))) (lambda () (crs)))  ; distribute
           (subst '(= (* (+ a (- b)) c) (+ (* a c) (- (* b c)))))   ; (a-b)c -> ac - bc
           (subst '(= (* a c) (* b c)))  ; ac -> bc
           (crs)))                       ; bc - bc = 0
;; a-b = 0  (zz-mul-cancel-zero at x := a-b, y := c)
(fact 'zz-mul-cancel-zero '(+ a (- b)) 'c)   ; (a-b)*c=0, c/=0 => a-b=0
;; a = b  from  a + -b = 0 :  a = b + (a-b) = b + 0 = b.
(ni-cut! '(= a (+ b (+ a (- b)))) (lambda () (crs)))   ; a = b + (a-b), identity
(subst '(= a (+ b (+ a (- b)))))         ; goal a=b -> (b + (a-b)) = b
(subst '(= (+ a (- b)) 0))               ; (a-b) -> 0
(crs)                                     ; (b + 0) = b
(ni-qed! 'nn-mul-cancel)

;;; =======================================================================
;;; nn-2-cancel : 2x = 2y => x = y.  Instance of nn-mul-cancel (commute to x*2).
(sp (make-wff '(FORALL x (IMPLIES (IN x NN) (FORALL y (IMPLIES (IN y NN)
                 (IMPLIES (= (* 2 x) (* 2 y)) (= x y))))))))
(di)(di)(di)(di)(di)                     ; x INx y INy ; assume 2x=2y
(ni-cut! '(= (* x 2) (* 2 x)) (lambda () (crs)))   ; commute identities, into context
(ni-cut! '(= (* y 2) (* 2 y)) (lambda () (crs)))
(ni-cut! '(= (* x 2) (* y 2))            ; x*2 = 2x = 2y = y*2
         (lambda ()
           (subst '(= (* x 2) (* 2 x)))  ; x*2 -> 2x
           (subst '(= (* y 2) (* 2 y)))  ; y*2 -> 2y
           (ass)))
(fact 'nn-mul-cancel 'x 'y 2)            ; x*2 = y*2, 2/=0 => x = y  (2/=0 ground)
(ass)
(ni-qed! 'nn-2-cancel)

;;; The strict twin of rr-le-from-diff-nonneg -- the one lemma the order calculus
;;; was missing.  0 < y-x  =>  x < y.  Belongs in structure-library/order-lemmas
;;; (RR order); stated here for now, warranted well-known like its nonstrict twin.
(support 'rr-lt-from-diff-pos
  '(FORALL x (IMPLIES (IN x RR) (FORALL y (IMPLIES (IN y RR)
     (IMPLIES (< 0 (- y x)) (< x y)))))))
(warrant! 'rr-lt-from-diff-pos 'well-known
  "0 < y-x gives x < y -- the strict `move everything to one side'; add x to
   both sides of 0 < y-x and simplify.  Strict twin of rr-le-from-diff-nonneg.")

;;; =======================================================================
;;; nn-lt-double : k /= 0 => k < 2*k.  PROVEN by `calc' -- the notes-27 directive
;;; grounded as the order/equational chain  k = k+0 < k+k = 2*k, with 0<k from
;;; nn-pos-of-nonzero (discreteness, order-lemmas).  crs on the = links, the
;;; NN->RR bridge + ineq (a real Farkas certificate) on the strict link, the
;;; order composer folding them through co-lt-eq-trans / co-eq-lt-trans.  This
;;; replaced a 14-line hand chain that billed trust:none (via nn-mul-closed);
;;; the calc proof bills trust:well-known.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN) (IMPLIES (NOT (= k 0)) (< k (* 2 k)))))))
(di)(di)(di)
(fact 'nn-pos-of-nonzero 'k)             ; 0 < k
(calc 'k '(= (+ k 0)) '(< (+ k k)) '(= (* 2 k)))
(ni-qed! 'nn-lt-double)
