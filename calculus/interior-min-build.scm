;;; calculus/interior-min-build.scm -- prove interior-min-deriv-zero FROM
;;; interior-max-deriv-zero, by applying it to g = -f.  NOT in load.scm.
;;; Run: mit-scheme --quiet --load load.scm \
;;;        --load calculus/interior-min-build.scm --eval '(exit)'

(define (mz-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (mz-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (mz-find pred) (let loop ((as (mz-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (mz-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (mz-split)
  (let loop ((n 0)) (let ((a (mz-find (mz-head? 'AND))))
    (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (mz-focus! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw)) (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s) (error "mz-focus!: none equal" (expression->string raw)))))
(define (mz-grind!)
  (let loop ((g 0)) (quietly (lambda () (ass-all)))
    (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
                                      (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND))))
                        (proof-leaves))))
      (when (and al (< g 40)) (set-proof-state-focus! *ps* al) (di) (loop (+ g 1))))))
(define (mz-have! mem main) (cut mem) (mz-focus! mem) (in-rr) (mz-focus! main))
(define (mz-dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display " leaves=")(display (length (proof-leaves)))(newline)
  (display ";;;   goal=")(write (mz-gf))(newline))

;;; --- supports (assert; deriv-neg sits with deriv-sum/product/chain) ---
(add-to-pss 'deriv-neg
  '(FORALL f (FORALL a (FORALL L
     (IMPLIES (IS-DIFF-AT f a L)
       (IS-DIFF-AT (VNB-LAMBDA z (- (f z))) a (- L)))))))
(warrant! 'deriv-neg 'reference
  "Derivative of -f is -f': f(x)-f(a)=phi(x)(x-a) gives (-f)(x)-(-f)(a)=(-phi)(x)(x-a), -phi continuous at a, value -L.")
(add-to-pss 'rr-le-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- v) (- u))))))))
(warrant! 'rr-le-neg 'well-known "u<=v => -v<=-u.")
(add-to-pss 'rr-neg-eq-zero
  '(FORALL u (IMPLIES (IN u RR) (IMPLIES (= (- u) 0) (= u 0)))))
(warrant! 'rr-neg-eq-zero 'well-known "-u=0 => u=0.")

;;; --- the proof -------------------------------------------------------
(sp '(FORALL f (FORALL a (FORALL b (FORALL theta (FORALL L
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR)
              (AND (IN theta RR) (AND (< a theta) (< theta b))))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (<= (f theta) (f x))))
     (IMPLIES (IS-DIFF-AT f theta L)
       (= L 0))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)))
(mz-split)
(quietly (lambda () (di)(di)))        ; MIN cond, IS-DIFF-AT
(define G (list 'VNB-LAMBDA 'z (list '- (list 'f 'z))))
(define MIN (mz-find (lambda (a) (and ((mz-head? 'FORALL) a)
                                      (let ((s (expression->string a))) (substring? "ccint" s))))))
(mz-dump "after strip")
(display ";;;   G=")(write G)(newline)(display ";;;   MIN=")(write MIN)(newline)

;; (1) IS-DIFF-AT G theta (- l)
(quietly (lambda () (fact 'deriv-neg 'f 'theta 'l)))
;; expose (IN l RR) (folded inside the now-consumed IS-DIFF-AT f theta l)
(quietly (lambda () (mac-h 'IS-DIFF-AT '(IS-DIFF-AT f theta l)) (mz-split)))
(mz-dump "after deriv-neg + expose (in l RR)")

;; (2) IN G (FUN RR RR)
(cut (list 'IN G '(FUN RR RR)))
(mz-focus! (list 'IN G '(FUN RR RR)))
(lam-t)
(quietly (lambda () (di) (di) (in-rr)))
(mz-dump "after typing G")

;; (3) MAX condition for G: forall x in CCINT(a,b). (G x) <= (G theta)
(define MAXG (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                  (list '<= (list G 'x) (list G 'theta)))))
(mz-focus! '(= l 0))
(cut MAXG)
(mz-focus! MAXG)
(di) (di)                              ; x, x in CCINT
(quietly (lambda () (inst+ MIN 'x)))   ; f(theta) <= f(x)  (uses x in CCINT, still present)
(mac-h 'ccint-membership '(IN x (CCINT a b)))   ; now expose x in RR
(mz-split)
(lam-b)                                ; (G x)->-(f x), (G theta)->-(f theta)
(define MGBODY (list '<= (list '- '(f x)) (list '- '(f theta))))
(mz-have! '(IN (f x) RR) MGBODY)
(mz-have! '(IN (f theta) RR) MGBODY)
(quietly (lambda () (fact 'rr-le-neg '(f theta) '(f x))))  ; -(f x) <= -(f theta)
(quietly (lambda () (ass-all)))
(mz-dump "after MAXG")

;; (4) interior-max-deriv-zero on G -> (- l) = 0
(mz-focus! '(= l 0))
(cut '(= (- l) 0))
(mz-focus! '(= (- l) 0))
(bc* 'interior-max-deriv-zero ((f G) (a 'a) (b 'b) (theta 'theta)))
(mz-grind!)
(mz-dump "after interior-max on G")

;; (5) l = 0
(mz-focus! '(= l 0))
(quietly (lambda () (fact 'rr-neg-eq-zero 'l) (ass-all)))
(mz-dump "FINAL")
