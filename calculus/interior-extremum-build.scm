;;; calculus/interior-extremum-build.scm
;;; ====================================================================
;;; Build/iterate Prop 2.10 interior-max-deriv-zero to qed modulo small
;;; well-known supports (product-sign + continuity sign-preservation).
;;; NOT part of load.scm.  Run (fast):
;;;   mit-scheme --quiet --load load.scm \
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

;; curried antecedents (no AND) so it can be applied FORWARD by `fact` -- its
;; conclusion (g th) is higher-order, so bc* would loop the matcher.
(add-to-pss 'continuous-nonpos-right
  '(FORALL g (FORALL th (FORALL bb
     (IMPLIES (IN g (FUN RR RR)) (IMPLIES (IN th RR) (IMPLIES (IN bb RR) (IMPLIES (< th bb)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< th x) (< x bb))) (<= (g x) 0)))
       (<= (g th) 0)))))))))))
(warrant! 'continuous-nonpos-right 'well-known
  "Continuous at th and <=0 on a right-neighborhood (th,bb) => <=0 at th.")

(add-to-pss 'continuous-nonneg-left
  '(FORALL g (FORALL aa (FORALL th
     (IMPLIES (IN g (FUN RR RR)) (IMPLIES (IN aa RR) (IMPLIES (IN th RR) (IMPLIES (< aa th)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< aa x) (< x th))) (<= 0 (g x))))
       (<= 0 (g th))))))))))))
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

;; sweep: run in-rr on every open (IN <term> ring) leaf
(define (types!)
  (let loop ((guard 0))
    (let ((leaf (any-pred
                 (lambda (s)
                   (let ((g (wff-formula (sequent-node-assertion s))))
                     (and (not (sequent-node-grounded? s))
                          (pair? g) (eq? (car g) 'IN)
                          (memq (caddr g) '(RR ZZ QQ CC)))))
                 (proof-leaves))))
      (when (and leaf (< guard 30))
        (set-proof-state-focus! *ps* leaf)
        (in-rr)
        (loop (+ guard 1))))))
;; establish (IN term D) in ctx via cut+in-rr, then refocus the main goal
(define (have! mem main)
  (cut mem) (focus-leaf-goal! mem) (in-rr) (focus-leaf-goal! main))
;; split every open AND goal and close assumption-closable leaves
(define (grind-goals!)
  (let loop ((g 0))
    (quietly (lambda () (ass-all)))
    (let ((andleaf (any-pred (lambda (s)
                               (let ((gg (wff-formula (sequent-node-assertion s))))
                                 (and (not (sequent-node-grounded? s))
                                      (pair? gg) (eq? (car gg) 'AND))))
                             (proof-leaves))))
      (when (and andleaf (< g 40))
        (set-proof-state-focus! *ps* andleaf) (di) (loop (+ g 1))))))

(--- "C1: right-neighborhood sign  phi*(x) <= 0  on (theta,b)")
(define C1 (list 'FORALL 'x
             (list 'IMPLIES (list 'AND '(IN x RR)
                              (list 'AND (list '< 'theta 'x) (list '< 'x 'b)))
               (list '<= (list phi* 'x) 0))))
(define XT '(- x theta))                 ; x - theta
(define FF (list '- '(f x) '(f theta)))  ; f(x) - f(theta)
(define PROD (list '* (list phi* 'x) XT))
(define MAING1 (list '<= (list phi* 'x) 0))   ; C1 inner goal
(cut C1)
(focus-leaf-goal! C1)
(di) (di) (split-ands)                   ; x in RR, theta<x, x<b ; goal MAING1
;; typings in context (so the forward facts detach cleanly)
(have! '(IN (f x) RR) MAING1)
(have! '(IN (f theta) RR) MAING1)
(have! (list 'IN (list phi* 'x) 'RR) MAING1)
(have! (list 'IN XT 'RR) MAING1)
;; a < x  (transitivity; bc* -- fact won't detach the AND antecedent)
(cut '(< a x))
(focus-leaf-goal! '(< a x))
(bc* 'rr-lt-trans ((y 'theta)))
(grind-goals!)
(focus-leaf-goal! MAING1)
;; remaining order facts (single-antecedent -> forward fact is fine)
(quietly (lambda ()
  (fact 'rr-lt-implies-le 'a 'x)         ; a <= x
  (fact 'rr-lt-implies-le 'x 'b)         ; x <= b
  (fact 'rr-lt-diff-pos 'theta 'x)))     ; 0 < x - theta
;; x in CCINT(a,b)
(cut '(IN x (CCINT a b)))
(focus-leaf-goal! '(IN x (CCINT a b)))
(mac 'ccint-membership)                  ; -> AND(in x RR, a<=x, x<=b)
(grind-goals!)
(focus-leaf-goal! MAING1)
;; f(x)<=f(theta), Caratheodory at x, FF<=0
(quietly (lambda ()
  (inst+ H1 'x)                          ; f(x) <= f(theta)
  (inst+ IDENT 'x)                       ; (= FF PROD)
  (fact 'rr-le-diff-nonpos '(f x) '(f theta))))  ; FF <= 0
;; PROD <= 0  (flip IDENT so PROD rewrites to FF)
(cut (list '<= PROD 0))
(focus-leaf-goal! (list '<= PROD 0))
(quietly (lambda () (fact 'eq-symm FF PROD)))  ; (= PROD FF) in ctx
(subst (list '= PROD FF))                ; (<= PROD 0) -> (<= FF 0)
(quietly (lambda () (ass-all)))
;; phi*(x) <= 0 by product-sign
(focus-leaf-goal! MAING1)
(bc* 'rr-prod-nonpos-pos ((v XT)))
(grind-goals!)
(dump "C1 done?")

(--- "C2: left-neighborhood sign  0 <= phi*(x)  on (a,theta)")
(define C2 (list 'FORALL 'x
             (list 'IMPLIES (list 'AND '(IN x RR)
                              (list 'AND (list '< 'a 'x) (list '< 'x 'theta)))
               (list '<= 0 (list phi* 'x)))))
(define MAING2 (list '<= 0 (list phi* 'x)))
(focus-leaf-goal! '(= l 0))
(cut C2)
(focus-leaf-goal! C2)
(di) (di) (split-ands)                   ; x in RR, a<x, x<theta ; goal MAING2
(have! '(IN (f x) RR) MAING2)
(have! '(IN (f theta) RR) MAING2)
(have! (list 'IN (list phi* 'x) 'RR) MAING2)
(have! (list 'IN XT 'RR) MAING2)
;; x < b  (x < theta < b)
(cut '(< x b))
(focus-leaf-goal! '(< x b))
(bc* 'rr-lt-trans ((y 'theta)))
(grind-goals!)
(focus-leaf-goal! MAING2)
(quietly (lambda ()
  (fact 'rr-lt-implies-le 'a 'x)         ; a <= x  (a<x in ctx)
  (fact 'rr-lt-implies-le 'x 'b)         ; x <= b
  (fact 'rr-lt-diff-neg 'x 'theta)))     ; x - theta < 0
(cut '(IN x (CCINT a b)))
(focus-leaf-goal! '(IN x (CCINT a b)))
(mac 'ccint-membership)
(grind-goals!)
(focus-leaf-goal! MAING2)
(quietly (lambda ()
  (inst+ H1 'x)
  (inst+ IDENT 'x)
  (fact 'rr-le-diff-nonpos '(f x) '(f theta))))   ; FF <= 0
(cut (list '<= PROD 0))
(focus-leaf-goal! (list '<= PROD 0))
(quietly (lambda () (fact 'eq-symm FF PROD)))
(subst (list '= PROD FF))
(quietly (lambda () (ass-all)))
(focus-leaf-goal! MAING2)
(bc* 'rr-prod-nonpos-neg ((v XT)))       ; v<0, PROD<=0 => 0<=phi*(x)
(grind-goals!)
(dump "C2 done?")

(--- "finish: pinch phi*(theta)=0, then l=0")
(focus-leaf-goal! '(= l 0))
(quietly (lambda () (fact 'rr-zero-in)))                 ; 0 in RR
;; phi*(theta) <= 0  via continuous-nonpos-right + C1  (forward; bc* would loop on (g th))
(quietly (lambda () (fact 'continuous-nonpos-right phi* 'theta 'b)))
;; 0 <= phi*(theta)  via continuous-nonneg-left + C2
(quietly (lambda () (fact 'continuous-nonneg-left phi* 'a 'theta)))
;; l = 0 by antisymmetry, using phi*(theta) = l
(quietly (lambda () (fact 'eq-symm (list phi* 'theta) 'l)))   ; (= l (phi* theta)) in ctx
(bc* 'rr-leq-antisymmetric)              ; (= l 0) -> (<= l 0),(<= 0 l) (+ typings)
(grind-goals!)
(focus-leaf-goal! '(<= l 0))
(subst (list '= 'l (list phi* 'theta)))  ; -> (<= (phi* theta) 0)
(quietly (lambda () (ass-all)))
(focus-leaf-goal! '(<= 0 l))
(subst (list '= 'l (list phi* 'theta)))  ; -> (<= 0 (phi* theta))
(quietly (lambda () (ass-all)))
(dump "FINISH")

