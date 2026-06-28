;;; theorem-library/interior-extremum-proof.scm
;;; ====================================================================
;;; Prop 2.10 (interior max): interior-max-deriv-zero, MACHINE-PROVEN.
;;;
;;; At an interior maximum theta of f on [a,b], if f is differentiable there
;;; with derivative L, then L=0.  Caratheodory route: skolemize the factor phi
;;; (f(x)-f(theta)=phi(x)(x-theta), phi continuous at theta, phi(theta)=L); the
;;; extremum f(x)<=f(theta) makes phi<=0 just right of theta (C1) and phi>=0
;;; just left (C2) via the product-sign lemmas; continuity pinches phi(theta)=0,
;;; and antisymmetry gives L=phi(theta)=0.
;;;
;;; Supports: continuous-nonpos-right / continuous-nonneg-left (mean-value.scm);
;;; rr-prod-nonpos-pos/neg, rr-le-diff-nonpos, rr-lt-diff-pos/neg (order-lemmas);
;;; the (in-rr) typing tactic (interactive.scm) discharges all (.. in RR) goals.
;;; Loads after mean-value.scm.  Uses bc* -> excluded from compile by load.scm.
;;; ====================================================================

(define (iez-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (iez-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (iez-find-asm pred)
  (let loop ((as (iez-asms)))
    (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (iez-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (iez-mentions? sym form)
  (cond ((eq? form sym) #t)
        ((pair? form) (or (iez-mentions? sym (car form)) (iez-mentions? sym (cdr form))))
        (else #f)))
(define (iez-split-ands)
  (let loop ((n 0))
    (let ((a (iez-find-asm (iez-head? 'AND))))
      (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (iez-focus! raw)
  (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw))
                     (proof-leaves))))
    (if s (begin (set-proof-state-focus! *ps* s) s)
        (error "iez-focus!: none equal to" (expression->string raw)))))
;; establish (IN term D) in ctx via cut+in-rr, then refocus the main goal
(define (iez-have! mem main)
  (cut mem) (iez-focus! mem) (in-rr) (iez-focus! main))
;; split every open AND goal and close assumption-closable leaves
(define (iez-grind!)
  (let loop ((g 0))
    (quietly (lambda () (ass-all)))
    (let ((andleaf (any-pred (lambda (s)
                               (let ((gg (wff-formula (sequent-node-assertion s))))
                                 (and (not (sequent-node-grounded? s))
                                      (pair? gg) (eq? (car gg) 'AND))))
                             (proof-leaves))))
      (when (and andleaf (< g 40))
        (set-proof-state-focus! *ps* andleaf) (di) (loop (+ g 1))))))

(sp '(FORALL f (FORALL a (FORALL b (FORALL theta (FORALL L
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR)
              (AND (IN theta RR) (AND (< a theta) (< theta b))))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (<= (f x) (f theta))))
     (IMPLIES (IS-DIFF-AT f theta L)
       (= L 0))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)))   ; f,a,b,theta,L
(iez-split-ands)                             ; break H0
(quietly (lambda () (di)(di)))               ; H1 (CCINT forall), H2 (IS-DIFF-AT)
;; unfold IS-DIFF-AT, skolemize the Caratheodory factor phi
(mac-h 'IS-DIFF-AT '(IS-DIFF-AT f theta L))
(iez-split-ands)
(let ((fs (iez-find-asm (iez-head? 'FORSOME)))) (and fs (ai fs)))
(iez-split-ands)
(define iez-phi (cadddr (iez-find-asm (iez-head? 'IS-CONTINUOUS-AT))))
(define IDENT (iez-find-asm (lambda (a) (and ((iez-head? 'FORALL) a) (iez-mentions? iez-phi a)))))
(define H1 (iez-find-asm (lambda (a) (and ((iez-head? 'FORALL) a) (iez-mentions? 'CCINT a)))))
(define XT '(- x theta))
(define FF (list '- '(f x) '(f theta)))
(define PROD (list '* (list iez-phi 'x) XT))

;; ---- C1: right-neighborhood sign  phi(x) <= 0  on (theta,b) ----
(define C1 (list 'FORALL 'x
             (list 'IMPLIES (list 'AND '(IN x RR)
                              (list 'AND (list '< 'theta 'x) (list '< 'x 'b)))
               (list '<= (list iez-phi 'x) 0))))
(define MAING1 (list '<= (list iez-phi 'x) 0))
(cut C1)
(iez-focus! C1)
(di) (di) (iez-split-ands)
(iez-have! '(IN (f x) RR) MAING1)
(iez-have! '(IN (f theta) RR) MAING1)
(iez-have! (list 'IN (list iez-phi 'x) 'RR) MAING1)
(iez-have! (list 'IN XT 'RR) MAING1)
(cut '(< a x))
(iez-focus! '(< a x))
(bc* 'rr-lt-trans ((y 'theta)))
(iez-grind!)
(iez-focus! MAING1)
(quietly (lambda ()
  (fact 'rr-lt-implies-le 'a 'x)
  (fact 'rr-lt-implies-le 'x 'b)
  (fact 'rr-lt-diff-pos 'theta 'x)))
(cut '(IN x (CCINT a b)))
(iez-focus! '(IN x (CCINT a b)))
(mac 'ccint-membership)
(iez-grind!)
(iez-focus! MAING1)
(quietly (lambda ()
  (inst+ H1 'x)
  (inst+ IDENT 'x)
  (fact 'rr-le-diff-nonpos '(f x) '(f theta))))
(cut (list '<= PROD 0))
(iez-focus! (list '<= PROD 0))
(quietly (lambda () (fact 'eq-symm FF PROD)))
(subst (list '= PROD FF))
(quietly (lambda () (ass-all)))
(iez-focus! MAING1)
(bc* 'rr-prod-nonpos-pos ((v XT)))
(iez-grind!)

;; ---- C2: left-neighborhood sign  0 <= phi(x)  on (a,theta) ----
(define C2 (list 'FORALL 'x
             (list 'IMPLIES (list 'AND '(IN x RR)
                              (list 'AND (list '< 'a 'x) (list '< 'x 'theta)))
               (list '<= 0 (list iez-phi 'x)))))
(define MAING2 (list '<= 0 (list iez-phi 'x)))
(iez-focus! '(= l 0))
(cut C2)
(iez-focus! C2)
(di) (di) (iez-split-ands)
(iez-have! '(IN (f x) RR) MAING2)
(iez-have! '(IN (f theta) RR) MAING2)
(iez-have! (list 'IN (list iez-phi 'x) 'RR) MAING2)
(iez-have! (list 'IN XT 'RR) MAING2)
(cut '(< x b))
(iez-focus! '(< x b))
(bc* 'rr-lt-trans ((y 'theta)))
(iez-grind!)
(iez-focus! MAING2)
(quietly (lambda ()
  (fact 'rr-lt-implies-le 'a 'x)
  (fact 'rr-lt-implies-le 'x 'b)
  (fact 'rr-lt-diff-neg 'x 'theta)))
(cut '(IN x (CCINT a b)))
(iez-focus! '(IN x (CCINT a b)))
(mac 'ccint-membership)
(iez-grind!)
(iez-focus! MAING2)
(quietly (lambda ()
  (inst+ H1 'x)
  (inst+ IDENT 'x)
  (fact 'rr-le-diff-nonpos '(f x) '(f theta))))
(cut (list '<= PROD 0))
(iez-focus! (list '<= PROD 0))
(quietly (lambda () (fact 'eq-symm FF PROD)))
(subst (list '= PROD FF))
(quietly (lambda () (ass-all)))
(iez-focus! MAING2)
(bc* 'rr-prod-nonpos-neg ((v XT)))
(iez-grind!)

;; ---- finish: pinch phi(theta)=0, then L=0 ----
(iez-focus! '(= l 0))
(quietly (lambda () (fact 'rr-zero-in)))
(quietly (lambda () (fact 'continuous-nonpos-right iez-phi 'theta 'b)))   ; phi(theta) <= 0
(quietly (lambda () (fact 'continuous-nonneg-left iez-phi 'a 'theta)))    ; 0 <= phi(theta)
(quietly (lambda () (fact 'eq-symm (list iez-phi 'theta) 'l)))            ; (= l (phi theta))
(bc* 'rr-leq-antisymmetric)
(iez-grind!)
(iez-focus! '(<= l 0))
(subst (list '= 'l (list iez-phi 'theta)))
(quietly (lambda () (ass-all)))
(iez-focus! '(<= 0 l))
(subst (list '= 'l (list iez-phi 'theta)))
(quietly (lambda () (ass-all)))
(qed 'interior-max-deriv-zero)
(category! 'interior-max-deriv-zero 'analysis)
