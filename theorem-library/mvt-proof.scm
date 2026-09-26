;;; theorem-library/mvt-proof.scm -- the Mean Value Theorem, MACHINE-PROVEN.
;;; Strategy: apply Rolle's theorem to the auxiliary
;;;     h(z) = f(z)*(b-a) - z*(f(b)-f(a))
;;; which satisfies h(a)=h(b); Rolle gives an interior theta with h'(theta)=0,
;;; and h'(theta) = f'(theta)(b-a) - (f(b)-f(a)), so f'(theta)(b-a)=f(b)-f(a).
;;; Loads after rolle-proof.scm.  Applies Rolle to the lambda AUX with forward
;;; `fact` (capture-avoidance handles AUX's free a,b vs Rolle's bound a,b);
;;; no bc*, so it compiles normally.
;;; Proven modulo 0 since 2026-09-14: the two calc-101 auxiliaries (mvt-aux-cont,
;;; mvt-aux-diff) are THEOREMS in theorem-library/mvt-aux-guarded.scm, guarded on a, b in RR
;;; (mvt-aux-cont/-diff, rr-diff-zero-eq, diff-value-real).
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): diff-value-real -- theorem-library/mvt-cluster-readoffs.scm
;;; RETIRED 2026-09-14 (proven): mvt-aux-diff -- theorem-library/mvt-aux-guarded.scm (statement now GUARDED on a, b in RR)
;;; RETIRED 2026-09-14 (proven): mvt-aux-cont -- theorem-library/mvt-aux-guarded.scm (statement now GUARDED on a, b in RR)

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
  (if s (begin (dk-focus! s) s) (error "mv-focus!: none equal" (expression->string raw)))))
(define (mv-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (dk-focus! al) (di) (loop (+ g 1))))))
(define (mv-have! mem main) (cut mem) (mv-focus! mem) (in-rr) (mv-focus! main))

;;; rolle-neutral -- REMOVED 2026-09-20 (batch 11, proven-duplicate-audit).
;;; It was `rolle' re-proved with the interval binders spelled lo,hi instead of
;;; a,b, "so it can be applied to an auxiliary that mentions a,b without
;;; capture".  It was alpha-equal to `rolle' and had NO call site: `subst-free'
;;; renames a captured binder by itself, so the precaution bought nothing.

;;; the auxiliary h(z) = f(z)*(b-a) - z*(f(b)-f(a))
(define AUX '(VNB-LAMBDA z RR (- (* (f z) (- b a)) (* z (- (f b) (f a))))))

;;; --- the calc-101 auxiliaries: were supports here; now theorems (mvt-aux-guarded.scm) ---

;;; --- pose MVT ---
(sp '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (< a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
     (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< a x) (< x b))) (FORSOME L (IS-DIFF-AT f x L))))
       (FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta b)
         (FORSOME L (AND (IS-DIFF-AT f theta L)
           (= (* L (- b a)) (- (f b) (f a))))))))))))))))
(quietly (lambda () (di)(di)(di)))         ; f,a,b
(mv-split)                                 ; typing AND
(quietly (lambda () (di)(di)))             ; continuity hyp, diff hyp
(define GOAL (mv-gf))
(define CONTHYP (mv-find (lambda (a) (and ((mv-head? 'FORALL) a) (mv-ment? 'is-continuous-at a)))))
(define DIFFHYP (mv-find (lambda (a) (and ((mv-head? 'FORALL) a) (mv-ment? 'is-diff-at a)))))

;;; AUX in FUN RR RR
(cut (list 'IN AUX '(FUN RR RR)))
(mv-focus! (list 'IN AUX '(FUN RR RR)))
(dk-lam-t!)
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
(define AUXDIFF (list 'FORALL 'x (list 'IMPLIES '(AND (IN x RR) (AND (< a x) (< x b)))
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
;; `fact` instantiates Rolle at the lambda AUX -- the kernel renames Rolle's bound
;; a,b to avoid capturing AUX's free a,b, then the a,b args apply cleanly, landing
;; the full instantiated implication chain; detach the 4 hypotheses (all in ctx).
(define RTYP (list 'AND (list 'IN AUX '(FUN RR RR)) (list 'AND '(IN a RR) (list 'AND '(IN b RR) '(< a b)))))
(cut RTYP)
(mv-focus! RTYP)
(quietly (lambda () (ass-all)))
(mv-focus! GOAL)
(quietly (lambda () (fact 'rolle AUX 'a 'b)))
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
;; Rolle's witness is typed now, so the interior-position AND that DIFFHYP wants
;; carries (IN theta RR) and every conjunct is already in context.
(define THINT (list 'AND (list 'IN TH 'RR) (list 'AND (list '< 'a TH) (list '< TH 'b))))
(cut THINT)
(mv-focus! THINT)
(quietly (lambda () (mv-grind!)))
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
  (when fl (dk-focus! fl)))
(ew LT)
(quietly (lambda () (mv-grind!) (ass-all)))
(qed 'mvt)
