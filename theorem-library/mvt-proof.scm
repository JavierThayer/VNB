;;; theorem-library/mvt-proof.scm -- the Mean Value Theorem, MACHINE-PROVEN.
;;; Strategy: apply Rolle's theorem to the auxiliary
;;;     h(z) = f(z)*(b-a) - z*(f(b)-f(a))
;;; which satisfies h(a)=h(b); Rolle gives an interior theta with h'(theta)=0,
;;; and h'(theta) = f'(theta)(b-a) - (f(b)-f(a)), so f'(theta)(b-a)=f(b)-f(a).
;;; Loads after rolle-proof.scm.  Uses apply-thm (capture-safe instantiation of
;;; Rolle at the lambda AUX) + forward `fact`; no bc*, so it compiles normally.
;;; Proven modulo the warranted calc-101 supports below
;;; (mvt-aux-cont/-diff, rr-diff-zero-eq, diff-value-real).
;;; ====================================================================

;;; --- file-local proof helpers ---
(define (mv-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (mv-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (mv-find pred) (let loop ((as (mv-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (mv-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (mv-ment? sym form) (cond ((eq? form sym) #t)
  ((pair? form) (or (mv-ment? sym (car form)) (mv-ment? sym (cdr form)))) (else #f)))
(define (mv-split) (let loop ((n 0)) (let ((a (mv-find (mv-head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (mv-focus! raw) (let ((s (any-pred (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw)) (proof-leaves))))
  (if s (begin (set-proof-state-focus! *ps* s) s) (error "mv-focus!: none equal" (expression->string raw)))))
(define (mv-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (set-proof-state-focus! *ps* al) (di) (loop (+ g 1))))))
(define (mv-have! mem main) (cut mem) (mv-focus! mem) (in-rr) (mv-focus! main))

;;; rolle-neutral: Rolle with interval vars lo,hi (not a,b), so it can be applied
;;; to an auxiliary that mentions a,b without capture.  One-liner from rolle.
(sp '(FORALL h (FORALL lo (FORALL hi
     (IMPLIES (AND (IN h (FUN RR RR)) (AND (IN lo RR) (AND (IN hi RR) (< lo hi))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT lo hi))
                 (IS-CONTINUOUS-AT RR-MS RR-MS h x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< lo x) (< x hi))
                 (FORSOME L (IS-DIFF-AT h x L))))
     (IMPLIES (= (h lo) (h hi))
       (FORSOME theta (AND (< lo theta) (AND (< theta hi)
                      (IS-DIFF-AT h theta 0))))))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)(di)))   ; h,lo,hi + 4 hyps
(quietly (lambda () (fact 'rolle 'h 'lo 'hi)))       ; lands rolle's conclusion = the goal
(quietly (lambda () (ass-all)))
(qed 'rolle-neutral)

;;; the auxiliary h(z) = f(z)*(b-a) - z*(f(b)-f(a))
(define AUX '(VNB-LAMBDA z (- (* (f z) (- b a)) (* z (- (f b) (f a))))))

;;; --- warranted calc-101 supports ---
(add-to-pss 'mvt-aux-diff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x (list 'FORALL 'L
    (list 'IMPLIES '(IS-DIFF-AT f x L)
      (list 'IS-DIFF-AT AUX 'x '(- (* L (- b a)) (- (f b) (f a)))))))))))
(warrant! 'mvt-aux-diff 'reference
  "h=(b-a)f-(f(b)-f(a))id is a linear combination of f and identity; its
   derivative (b-a)L-(f(b)-f(a)) follows from deriv-product/sum/const/identity.")
(category! 'mvt-aux-diff 'analysis)
(add-to-pss 'mvt-aux-cont
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x
    (list 'IMPLIES '(IS-CONTINUOUS-AT RR-MS RR-MS f x)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS AUX 'x)))))))
(warrant! 'mvt-aux-cont 'reference
  "h is a sum/product of f, constants and the identity, hence continuous where f is.")
(category! 'mvt-aux-cont 'analysis)
(add-to-pss 'rr-diff-zero-eq
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (= 0 (- u v)) (= u v)))))))
(warrant! 'rr-diff-zero-eq 'well-known "0=u-v => u=v.")
(category! 'rr-diff-zero-eq 'analysis)
(add-to-pss 'diff-value-real
  '(FORALL f (FORALL a (FORALL L (IMPLIES (IS-DIFF-AT f a L) (IN L RR))))))
(warrant! 'diff-value-real 'definitional
  "IS-DIFF-AT's definition includes (IN L RR) as a conjunct.")
(category! 'diff-value-real 'analysis)

;;; --- pose MVT ---
(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (< a x) (< x b)) (FORSOME L (IS-DIFF-AT f x L))))
       (FORSOME theta (AND (< a theta) (AND (< theta b)
         (FORSOME L (AND (IS-DIFF-AT f theta L)
           (= (* L (- b a)) (- (f b) (f a)))))))))))))))
(quietly (lambda () (di)(di)(di)))         ; f,a,b
(mv-split)                                 ; typing AND
(quietly (lambda () (di)(di)))             ; continuity hyp, diff hyp
(define GOAL (mv-gf))
(define CONTHYP (mv-find (lambda (a) (and ((mv-head? 'FORALL) a) (mv-ment? 'is-continuous-at a)))))
(define DIFFHYP (mv-find (lambda (a) (and ((mv-head? 'FORALL) a) (mv-ment? 'is-diff-at a)))))

;;; AUX in FUN RR RR
(cut (list 'IN AUX '(FUN RR RR)))
(mv-focus! (list 'IN AUX '(FUN RR RR)))
(lam-t)
(quietly (lambda () (di) (di) (in-rr)))
(mv-focus! GOAL)

;; (1) AUX continuous on [a,b]
(define AUXCONT (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
                  (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS AUX 'x))))
(cut AUXCONT)
(mv-focus! AUXCONT)
(di) (di)
(quietly (lambda () (inst+ CONTHYP 'x) (fact 'mvt-aux-cont 'f 'a 'b 'x) (ass-all)))
(mv-focus! GOAL)

;; (2) AUX differentiable on (a,b)
(define AUXDIFF (list 'FORALL 'x (list 'IMPLIES '(AND (< a x) (< x b))
                  (list 'FORSOME 'L (list 'IS-DIFF-AT AUX 'x 'L)))))
(cut AUXDIFF)
(mv-focus! AUXDIFF)
(di) (di)                              ; x ; (AND (< a x)(< x b))
(quietly (lambda () (inst+ DIFFHYP 'x)))
(let ((fs (mv-find (lambda (z) (and ((mv-head? 'FORSOME) z) (mv-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'f))))))
  (ai fs))
(let ((Lx (cadddr (mv-find (lambda (z) (and ((mv-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) 'x)))))))
  (quietly (lambda () (fact 'mvt-aux-diff 'f 'a 'b 'x Lx)))
  (ew (list '- (list '* Lx '(- b a)) '(- (f b) (f a))))
  (quietly (lambda () (ass-all))))
(mv-focus! GOAL)

;; (3) AUX(a)=AUX(b)
(mv-have! '(IN (f a) RR) GOAL)
(mv-have! '(IN (f b) RR) GOAL)
(cut (list '= (list AUX 'a) (list AUX 'b)))
(mv-focus! (list '= (list AUX 'a) (list AUX 'b)))
(lam-b)
(crs)
(mv-focus! GOAL)

;; (4) Rolle on AUX (FORWARD: its conclusion is a FORSOME) -> theta, AUX'(theta)=0.
;; apply-thm instantiates Rolle at the lambda AUX (capture-safe), landing the full
;; instantiated implication chain; detach the 4 hypotheses (all in context).
(define RTYP (list 'AND (list 'IN AUX '(FUN RR RR)) (list 'AND '(IN a RR) (list 'AND '(IN b RR) '(< a b)))))
(cut RTYP)
(mv-focus! RTYP)
(quietly (lambda () (ass-all)))
(mv-focus! GOAL)
(apply-thm 'rolle AUX 'a 'b)
;; NB: mv-ment? uses eq?, fine for symbols; the AUX *list* is a fresh copy after
;; subst-free, so match the embedded 'VNB-LAMBDA symbol instead.
(let loop ((n 0))
  (let ((ri (mv-find (lambda (z) (and ((mv-head? 'IMPLIES) z) (mv-ment? 'VNB-LAMBDA z))))))
    (when (and ri (< n 6)) (detach! ri) (loop (+ n 1)))))
(ai (mv-find (lambda (z) (and ((mv-head? 'FORSOME) z) (mv-ment? 'VNB-LAMBDA z) (mv-ment? 'is-diff-at z)))))
(mv-split)
(define TH (caddr (mv-find (lambda (z) (and ((mv-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
              (mv-find (lambda (y) (and ((mv-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'b)))))))))

;; (5) extract: f diff at theta with LT; mvt-aux-diff gives AUX'(theta)=MEXPR;
;; derivative-unique (vs the Rolle 0) gives 0=MEXPR; rr-diff-zero-eq finishes.
(cut (list 'AND (list '< 'a TH) (list '< TH 'b)))
(mv-focus! (list 'AND (list '< 'a TH) (list '< TH 'b)))
(quietly (lambda () (ass-all)))
(mv-focus! GOAL)
(quietly (lambda () (inst+ DIFFHYP TH)))
(let ((fs (mv-find (lambda (z) (and ((mv-head? 'FORSOME) z) (mv-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'f))))))
  (ai fs))
(define LT (cadddr (mv-find (lambda (z) (and ((mv-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) TH))))))
(quietly (lambda () (fact 'diff-value-real 'f TH LT)))   ; IN LT RR (derivative value is real)
(define MEXPR (list '- (list '* LT '(- b a)) '(- (f b) (f a))))
(quietly (lambda () (fact 'mvt-aux-diff 'f 'a 'b TH LT)))   ; IS-DIFF-AT AUX theta MEXPR
;; derivative-unique (FORWARD) needs the two diffs as a single AND in context
;; (forward fact won't detach a conjunctive antecedent), so cut the AND first.
(let ((dd (list 'AND (list 'IS-DIFF-AT AUX TH 0) (list 'IS-DIFF-AT AUX TH MEXPR))))
  (cut dd) (mv-focus! dd)
  (quietly (lambda () (di) (ass-all)))   ; di splits the AND; both conjuncts in ctx
  (mv-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique AUX TH 0 MEXPR))))  ; => (= 0 MEXPR)
;; rr-diff-zero-eq (FORWARD): u=LT*(b-a), v=f(b)-f(a); 0=(u-v)=MEXPR => u=v.
(mv-have! (list 'IN (list '* LT '(- b a)) 'RR) GOAL)
(mv-have! (list 'IN '(- (f b) (f a)) 'RR) GOAL)
(quietly (lambda () (fact 'rr-diff-zero-eq (list '* LT '(- b a)) '(- (f b) (f a)))))

;; finish: ew theta=TH, split the conjunction, focus the inner FORSOME, ew L=LT.
(ew TH)
(quietly (lambda () (mv-grind!)))            ; split ANDs; closes a<TH, TH<b leaves by ass
(let ((fl (any-pred (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
            (and (not (sequent-node-grounded? s)) (pair? g) (eq? (car g) 'FORSOME)))) (proof-leaves))))
  (when fl (set-proof-state-focus! *ps* fl)))
(ew LT)
(quietly (lambda () (mv-grind!) (ass-all)))
(qed 'mvt)
