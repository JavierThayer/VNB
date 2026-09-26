;;; calculus/subseq-conv-build.scm -- BUILD SCRATCH (not loaded)
;;; Prove subseq-of-convergent: a subsequence of a convergent sequence
;;; converges to the same limit.  Modulo strictly-mono-ge-id.

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred) (let loop ((as (asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (has? sym form) (cond ((equal? form sym) #t)
  ((pair? form) (or (has? sym (car form)) (has? sym (cdr form)))) (else #f)))
(define (--- t) (newline)(display ";;; ===== ")(display t)(display " =====")(newline))
(define (dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display "  GOAL: ")(write (gf))(newline))
(define (split-ands) (let loop ((n 0)) (let ((a (find-asm (head? 'AND))))
  (cond ((and a (< n 12)) (ai a) (loop (+ n 1))) (else n)))))
(define (leaves) (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                         (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (fpred p) (let loop ((gs (leaves)))
  (cond ((null? gs) #f)
        ((p (wff-formula (sequent-node-assertion (car gs)))) (dk-focus! (car gs)) #t)
        (else (loop (cdr gs))))))
(define (fhead h) (fpred (lambda (a) (and (pair? a) (eq? (car a) h)))))
(define (lheads) (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n)))) (if (pair? a)(car a) a))) (leaves)))

(sp (make-wff
     '(FORALL s (FORALL f (FORALL phi (FORALL L
        (IMPLIES (CONVERGES-TO s f L)
          (IMPLIES (STRICTLY-MONO-NN phi)
            (CONVERGES-TO s (SUBSEQ f phi) L)))))))))
(quietly (lambda () (di)(di)(di)(di)(di)(di)))
(define s* (cadr (find-asm (head? 'CONVERGES-TO))))
(define Hconv (find-asm (head? 'CONVERGES-TO)))
(define f* (caddr Hconv))
(define L* (cadddr Hconv))
(define phi* (cadr (find-asm (head? 'STRICTLY-MONO-NN))))
(dump "after strip")
(display ";;; s*=")(write s*)(display " f*=")(write f*)(display " phi*=")(write phi*)(display " L*=")(write L*)(newline)

;; unfold H_conv: IS-MS, f-typing, L-typing, conv-inner(∀ε...)
(quietly (lambda () (mac-h 'CONVERGES-TO Hconv) (split-ands)))
(define convinner (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? f* a)(has? '<= a)(has? 'POS-RR a)))))
(dump "after unfold H_conv")
(display ";;; convinner=")(write convinner)(newline)

;; unfold goal CONVERGES-TO, dispatch structural conjuncts
(quietly (lambda () (mac 'CONVERGES-TO)))
(quietly (lambda ()
  (let loop ((n 0))
    (when (< n 8)
      (cond ((fhead 'AND) (di) (loop (+ n 1)))
            ((fhead 'IS-METRIC-SPACE) (ass) (loop (+ n 1)))
            ((fpred (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) (list 'FUN 'NN (list 'X s*))))))
             ;; could be SUBSEQ-typing or L-typing; try ass first, else bc*
             (if (has? 'SUBSEQ (gf)) (begin (bc* 'subseq-is-fun)(di)(ass-all)) (ass))
             (loop (+ n 1)))
            (else 'done))))))
(--- "after structural dispatch")
(display ";;; leaf-heads: ")(write (lheads))(newline)

;; the eps goal
(fhead 'FORALL)
(quietly (lambda () (di)(di)))
(define eps* (cadr (find-asm (head? 'POS-RR))))
(define Hmono (find-asm (head? 'STRICTLY-MONO-NN)))
;; establish (AND a b) in ctx (a,b already present), then refocus goal g
(define (estab a b g)
  (cut (list 'AND a b))
  (fpred (lambda (x) (equal? x (list 'AND a b)))) (di)
  (fpred (lambda (x) (equal? x a))) (ass)
  (fpred (lambda (x) (equal? x b))) (ass)
  (fpred (lambda (x) (equal? x g))))

;; N0 from convinner @ eps
(quietly (lambda () (inst+ convinner eps*)
  (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs))) (split-ands)))
(define N0* (let ((a (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) 'NN)))))) (and a (cadr a))))
(define convN0 (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? f* a)(has? '<= a)(not (has? 'POS-RR a))))))
;; ew N0; close N0 in NN; intro n_
(quietly (lambda () (ew N0*) (di)))
(fpred (lambda (a) (equal? a (list 'IN N0* 'NN)))) (quietly (lambda () (ass)))
(fhead 'FORALL)
(quietly (lambda () (di)(di)(di)))
(define gg (gf))                        ; the estimate goal  (<= ((d s) ((subseq f phi) n_) l) eps)
(define n_* (cadr (cadr (cadr gg))))    ; (cadr gg)=((d s) T1 T2); T1=(cadr..); n_=(cadr T1)
(dump "estimate goal")
(display ";;; N0*=")(write N0*)(display " n_*=")(write n_*)(newline)

;; phi(n_) >= n_
(quietly (lambda () (fact 'strictly-mono-ge-id phi* n_*)))
;; phi(n_) in NN: need phi in FUN(NN,NN) -> unfold STRICTLY-MONO-NN; fun-apply-type
(quietly (lambda () (mac-h 'STRICTLY-MONO-NN Hmono) (split-ands)))
(estab (list 'IN phi* (list 'FUN 'NN 'NN)) (list 'IN n_* 'NN) gg)
(quietly (lambda () (fact 'fun-apply-type phi* 'NN 'NN n_*)))
(display ";;; phi(n_) in NN? ")(write (and (find-asm (lambda(a)(equal? a (list 'IN (list phi* n_*) 'NN)))) #t))
(display "  n_<=phi(n_)? ")(write (and (find-asm (lambda(a)(equal? a (list '<= n_* (list phi* n_*))))) #t))(newline)

;; N0 <= phi(n_): nn-in-rr typing + rr-le-trans
(quietly (lambda () (fact 'nn-in-rr N0*) (fact 'nn-in-rr n_*) (fact 'nn-in-rr (list phi* n_*))))
(estab (list '<= N0* n_*) (list '<= n_* (list phi* n_*)) gg)
(quietly (lambda () (fact 'rr-le-trans N0* n_* (list phi* n_*))))
(display ";;; N0<=phi(n_)? ")(write (and (find-asm (lambda(a)(equal? a (list '<= N0* (list phi* n_*))))) #t))(newline)

;; conv-N0 @ phi(n_)  ->  d(f(phi n_),L) <= eps
(estab (list 'IN (list phi* n_*) 'NN) (list '<= N0* (list phi* n_*)) gg)
(quietly (lambda () (and convN0 (inst+ convN0 (list phi* n_*)))))
(display ";;; d(f(phi n_),L)<=eps? ")
(write (and (find-asm (lambda(a)(equal? a (list '<= (list (list 'D s*) (list f* (list phi* n_*)) L*) eps*)))) #t))(newline)

;; rewrite SUBSEQ in goal, close
(quietly (lambda () (mac 'SUBSEQ) (lam-b) (lam-b) (ass)))
(dump "after close")
(display ";;; PROOF DONE? ")(write (proof-done? *ps*))(display "  ungrounded: ")
(write (length (dg-ungrounded-nodes (proof-state-dg *ps*))))(newline)
(--- "END v2")
