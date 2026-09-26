;;; calculus/mvt-build.scm -- prove the Mean Value Theorem from Rolle.
;;; NOT in load.scm.  Run: mit-scheme --quiet --load load.scm \
;;;   --load calculus/mvt-build.scm --eval '(exit)'

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
(define (mv-open-leaves) (filter (lambda (s) (not (sequent-node-grounded? s))) (proof-leaves)))
(define (mv-dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display " leaves=")(display (length (proof-leaves)))
  (display " open=")(display (length (mv-open-leaves)))(newline)
  (display ";;;   goal=")(write (mv-gf))(newline)
  (for-each (lambda (s) (display ";;;   OPEN ")(write (wff-formula (sequent-node-assertion s)))(newline))
            (mv-open-leaves)))

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
(define AUX '(VNB-LAMBDA z RR (- (* (f z) (- b a)) (* z (- (f b) (f a))))))

;;; auxiliary calc-101 properties (warranted; follow from the asserted
;;; deriv-product/sum/const/identity and sum/product-continuous algebra)
(add-to-pss 'mvt-aux-diff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x (list 'FORALL 'L
    (list 'IMPLIES '(IS-DIFF-AT f x L)
      (list 'IS-DIFF-AT AUX 'x '(- (* L (- b a)) (- (f b) (f a)))))))))))
(warrant! 'mvt-aux-diff 'reference
  "h=(b-a)f-(f(b)-f(a))id is a linear combination of f and identity; its
   derivative (b-a)L-(f(b)-f(a)) follows from deriv-product/sum/const/identity.")
(add-to-pss 'mvt-aux-cont
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x
    (list 'IMPLIES '(IS-CONTINUOUS-AT RR-MS RR-MS f x)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS AUX 'x)))))))
(warrant! 'mvt-aux-cont 'reference
  "h is a sum/product of f, constants and the identity, hence continuous where f is.")

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
(mv-dump "after strip")

;;; AUX in FUN RR RR
(cut (list 'IN AUX '(FUN RR RR)))
(mv-focus! (list 'IN AUX '(FUN RR RR)))
(dk-lam-t!)
(quietly (lambda () (di) (di) (in-rr)))
(mv-focus! GOAL)

(add-to-pss 'rr-diff-zero-eq
  '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (= 0 (- u v)) (= u v)))))))
(warrant! 'rr-diff-zero-eq 'well-known "0=u-v => u=v.")

(add-to-pss 'diff-value-real
  '(FORALL f (FORALL a (FORALL L (IMPLIES (IS-DIFF-AT f a L) (IN L RR))))))
(warrant! 'diff-value-real 'informal
  "IS-DIFF-AT's definition includes (IN L RR) as a conjunct.")

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
(mv-dump "after AUX continuity/diff/endpoints")

;; (4) Rolle on AUX (FORWARD: its conclusion is a FORSOME) -> theta, AUX'(theta)=0
(define RTYP (list 'AND (list 'IN AUX '(FUN RR RR)) (list 'AND '(IN a RR) (list 'AND '(IN b RR) '(< a b)))))
(cut RTYP)
(mv-focus! RTYP)
(quietly (lambda () (ass-all)))
(mv-focus! GOAL)
;; spec applies rolle directly to AUX,a,b -- capture-safe, lands the full
;; instantiated implication chain; then detach the 4 hypotheses (all in ctx).
(apply-thm 'rolle AUX 'a 'b)
(display ";;; after apply-thm: asm-heads=")
(write (map (lambda (z) (if (pair? z) (car z) z)) (mv-asms)))(newline)
;; NB: mv-ment? uses eq?, fine for symbols; the AUX *list* is a fresh copy
;; after subst-free, so match the embedded 'VNB-LAMBDA symbol instead.
(let loop ((n 0))
  (let ((ri (mv-find (lambda (z) (and ((mv-head? 'IMPLIES) z) (mv-ment? 'VNB-LAMBDA z))))))
    (when (and ri (< n 6)) (detach! ri) (loop (+ n 1)))))
(ai (mv-find (lambda (z) (and ((mv-head? 'FORSOME) z) (mv-ment? 'VNB-LAMBDA z) (mv-ment? 'is-diff-at z)))))
(mv-split)
(define TH (caddr (mv-find (lambda (z) (and ((mv-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
              (mv-find (lambda (y) (and ((mv-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'b)))))))))
(display ";;; TH=")(write TH)(newline)
(mv-dump "after Rolle, theta skolemized")

;; (5) extract: f diff at theta with Lt; mvt-aux-diff; derivative-unique vs 0
(cut (list 'AND (list '< 'a TH) (list '< TH 'b)))
(mv-focus! (list 'AND (list '< 'a TH) (list '< TH 'b)))
(quietly (lambda () (ass-all)))
(mv-focus! GOAL)
(quietly (lambda () (inst+ DIFFHYP TH)))
(let ((fs (mv-find (lambda (z) (and ((mv-head? 'FORSOME) z) (mv-ment? 'is-diff-at z) (eq? (cadr (caddr z)) 'f))))))
  (ai fs))
(define LT (cadddr (mv-find (lambda (z) (and ((mv-head? 'IS-DIFF-AT) z) (eq? (cadr z) 'f) (equal? (caddr z) TH))))))
(display ";;; LT=")(write LT)(newline)
(quietly (lambda () (fact 'diff-value-real 'f TH LT)))   ; IN LT RR (derivative value is real)
(define MEXPR (list '- (list '* LT '(- b a)) '(- (f b) (f a))))
(quietly (lambda () (fact 'mvt-aux-diff 'f 'a 'b TH LT)))   ; IS-DIFF-AT AUX theta MEXPR
;; derivative-unique (FORWARD): needs the two diffs as a single AND in context
;; (forward fact won't detach a conjunctive antecedent), so cut the AND first.
(let ((dd (list 'AND (list 'IS-DIFF-AT AUX TH 0) (list 'IS-DIFF-AT AUX TH MEXPR))))
  (cut dd) (mv-focus! dd)
  (quietly (lambda () (di) (ass-all)))   ; di splits the AND; both conjuncts in ctx
  (mv-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique AUX TH 0 MEXPR))))  ; => (= 0 MEXPR)
;; rr-diff-zero-eq (FORWARD): u=LT*(b-a), v=f(b)-f(a); 0=(u - v)=MEXPR => u=v.
(mv-have! (list 'IN (list '* LT '(- b a)) 'RR) GOAL)
(mv-have! (list 'IN '(- (f b) (f a)) 'RR) GOAL)
(quietly (lambda () (fact 'rr-diff-zero-eq (list '* LT '(- b a)) '(- (f b) (f a)))))
(let* ((MEXPR (list '- (list '* LT '(- b a)) '(- (f b) (f a))))
       (haz (lambda (form) (and (mv-find (lambda (z) (equal? z form))) #t))))
  (display ";;; pre-ew:")
  (display " 0=MEXPR=")(write (haz (list '= 0 MEXPR)))
  (display " MEXPR=0=")(write (haz (list '= MEXPR 0)))
  (display " IN-u=")(write (haz (list 'IN (list '* LT '(- b a)) 'RR)))
  (display " IN-v=")(write (haz (list 'IN '(- (f b) (f a)) 'RR)))
  (display " have-eq=")(write (haz (list '= (list '* LT '(- b a)) '(- (f b) (f a)))))(newline))
;; ew theta=TH, split the conjunction, focus the inner FORSOME, ew L=LT.
(ew TH)
(quietly (lambda () (mv-grind!)))            ; split ANDs; closes a<TH, TH<b leaves by ass
(let ((fl (any-pred (lambda (s) (let ((g (wff-formula (sequent-node-assertion s))))
            (and (not (sequent-node-grounded? s)) (pair? g) (eq? (car g) 'FORSOME)))) (proof-leaves))))
  (when fl (dk-focus! fl)))
(ew LT)
(quietly (lambda () (mv-grind!) (ass-all)))
(mv-dump "FINAL")
