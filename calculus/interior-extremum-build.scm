;;; calculus/interior-extremum-build.scm
;;; ====================================================================
;;; Build/iterate Prop 2.10 interior-max-deriv-zero to qed modulo small
;;; well-known supports (product-sign + continuity sign-preservation).
;;; NOT part of load.scm.  Run (fast):
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;       --load calculus/interior-extremum-build.scm --eval '(exit)'
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred)
  (let loop ((as (asms)))
    (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (--- title) (newline)(display ";;; ===== ")(display title)(display " =====")(newline))
(define (dump tag)
  (display ";;; [")(display tag)(display "]  done?=")(display (proof-done? *ps*))(newline)
  (display ";;;   GOAL: ")(write (gf))(newline)
  (display ";;;   ASMS:")(newline)
  (for-each (lambda (a) (display ";;;     ")(write a)(newline)) (asms)))
(define (split-ands)
  (let loop ((n 0))
    (let ((a (find-asm (head? 'AND))))
      (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))

;;; ---- supports (well-known) -----------------------------------------
(--- "install supports")
(add-to-pss 'rr-prod-nonpos-pos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< 0 v) (<= (* u v) 0)) (<= u 0)))))))
(warrant! 'rr-prod-nonpos-pos 'well-known "u*v<=0 with v>0 forces u<=0.")

(add-to-pss 'rr-prod-nonpos-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (AND (< v 0) (<= (* u v) 0)) (<= 0 u)))))))
(warrant! 'rr-prod-nonpos-neg 'well-known "u*v<=0 with v<0 forces u>=0.")

(add-to-pss 'continuous-nonpos-right
  '(FORALL g (FORALL th (FORALL bb
     (IMPLIES (AND (IN g (FUN RR RR)) (AND (IN th RR) (AND (IN bb RR) (< th bb))))
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< th x) (< x bb))) (<= (g x) 0)))
       (<= (g th) 0))))))))
(warrant! 'continuous-nonpos-right 'well-known
  "Continuous at th and <=0 on a right-neighborhood (th,bb) => <=0 at th.")

(add-to-pss 'continuous-nonneg-left
  '(FORALL g (FORALL aa (FORALL th
     (IMPLIES (AND (IN g (FUN RR RR)) (AND (IN aa RR) (AND (IN th RR) (< aa th))))
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< aa x) (< x th))) (<= 0 (g x))))
       (<= 0 (g th)))))))))
(warrant! 'continuous-nonneg-left 'well-known
  "Continuous at th and >=0 on a left-neighborhood (aa,th) => >=0 at th.")

;;; diff-order helpers (well-known RR order facts; NOT closure axioms)
(add-to-pss 'rr-le-diff-nonpos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (<= u v) (<= (- u v) 0)))))))
(warrant! 'rr-le-diff-nonpos 'well-known "u<=v => u-v<=0.")
(add-to-pss 'rr-lt-diff-pos
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< 0 (- v u))))))))
(warrant! 'rr-lt-diff-pos 'well-known "u<v => 0<v-u.")
(add-to-pss 'rr-lt-diff-neg
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (< u v) (< (- u v) 0)))))))
(warrant! 'rr-lt-diff-neg 'well-known "u<v => u-v<0.")

;;; focus helpers (from prop-3-14-proof.scm)
(define (focus-leaf-goal! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf-goal!: none equal to" (expression->string raw)))))
(define (focus-leaf-asm! substr)
  (let ((s (any-pred (lambda (s) (any-pred (lambda (w) (sub? substr (expression->string (wff-formula w))))
                                           (sequent-node-assumptions s)))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "focus-leaf-asm!: none with asm" substr))))
(define (mentions? sym form)
  (cond ((eq? form sym) #t)
        ((pair? form) (or (mentions? sym (car form)) (mentions? sym (cdr form))))
        (else #f)))

;;; ---- the proof -----------------------------------------------------
(--- "pose interior-max-deriv-zero")
(sp '(FORALL f (FORALL a (FORALL b (FORALL theta (FORALL L
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR)
              (AND (IN theta RR) (AND (< a theta) (< theta b))))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (<= (f x) (f theta))))
     (IMPLIES (IS-DIFF-AT f theta L)
       (= L 0))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)))   ; f,a,b,theta,L
(split-ands)                                  ; break H0
(quietly (lambda () (di)(di)))                ; H1 (CCINT forall), H2 (IS-DIFF-AT)
(dump "after strip")

(--- "unfold IS-DIFF-AT hyp + skolemize phi")
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f theta L))
(split-ands)
(let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))
(split-ands)
(dump "after skolemize phi")

(--- "capture skolem + key asms")
(define phi* (cadddr (find-asm (head? 'IS-CONTINUOUS-AT))))
(define IDENT (find-asm (lambda (a) (and ((head? 'FORALL) a) (mentions? phi* a)))))
(define H1 (find-asm (lambda (a) (and ((head? 'FORALL) a)
                                       (mentions? 'CCINT a)))))
(display ";;;   phi*=")(write phi*)(newline)
(display ";;;   IDENT=")(write IDENT)(newline)
(display ";;;   H1=")(write H1)(newline)

(--- "PIVOT TEST: right-neighborhood leaf  phi*(x) <= 0")
(define C1 (list 'FORALL 'x
             (list 'IMPLIES (list 'AND '(IN x RR)
                              (list 'AND (list '< 'theta 'x) (list '< 'x 'b)))
               (list '<= (list phi* 'x) 0))))
(cut C1)
(focus-leaf-goal! C1)
(di) (di) (split-ands)
(dump "C1: x in RR, theta<x, x<b; goal phi*(x)<=0")

;; (a) instantiate the Caratheodory identity at x
(inst+ IDENT 'x)
(dump "C1a: after inst+ IDENT at x (expect identity at x in ctx)")

;; (b) typing test: is (- x theta) in RR reachable by crs?
(cut (list 'IN (list '- 'x 'theta) 'RR))
(focus-leaf-goal! (list 'IN (list '- 'x 'theta) 'RR))
(crs)
(dump "C1b: after crs on (- x theta) in RR  [done?=#t on this leaf => crs types subtraction]")

