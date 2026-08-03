;;; calculus/tychonoff-middle-build.scm -- BUILD SCRATCH (not loaded)
;;; Drive seq-compact-countable-product to QED, modulo the keystone
;;; coordinatewise-diagonal-subseq + product-convergence-coordinatewise.

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred)
  (let loop ((as (asms))) (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (has? sym form)
  (cond ((equal? form sym) #t)
        ((pair? form) (or (has? sym (car form)) (has? sym (cdr form)))) (else #f)))
(define (--- t) (newline)(display ";;; ===== ")(display t)(display " =====")(newline))
(define (dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display "  GOAL: ")(write (gf))(newline))
(define (leaves) (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                         (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (fpred p) (let loop ((gs (leaves)))
  (cond ((null? gs) #f)
        ((p (wff-formula (sequent-node-assertion (car gs)))) (set! *ps* (focus-on *ps* (car gs))) #t)
        (else (loop (cdr gs))))))
(define (fhead h) (fpred (lambda (a) (and (pair? a) (eq? (car a) h)))))
(define (lheads) (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n)))) (if (pair? a)(car a) a))) (leaves)))
(define (split-ands) (let loop ((n 0)) (let ((a (find-asm (head? 'AND))))
  (cond ((and a (< n 10)) (ai a) (loop (+ n 1))) (else n)))))
(define wdef '(VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1)))))

(sp (make-wff
     '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
        (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
          (SEQ-COMPACT (PRODUCT-METRIC ms)))))))
(quietly (lambda () (di)(di)(di)))
(define ms* (cadr (find-asm (head? 'IS-MS-SEQUENCE))))
(define Hsc (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(has? 'SEQ-COMPACT a)))))
(dump "after strip")

;; unfold SEQ-COMPACT goal, then PRODUCT-METRIC -> -W everywhere in the goal
(quietly (lambda () (mac 'SEQ-COMPACT) (mac 'PRODUCT-METRIC)))
(dump "after mac SEQ-COMPACT + PRODUCT-METRIC")

;; (1) IS-MS conjunct + intro f for the forall; split the top AND
(quietly (lambda () (di)))
(dump "after di on goal AND")
(display ";;; leaf-heads: ")(write (lheads))(newline)
;; close IS-MS(-W) leaf: product-is-metric-space @ wdef
(fhead 'IS-METRIC-SPACE)
(quietly (lambda ()
  (fact 'product-metric-default-summable)
  (fact 'product-is-metric-space ms* wdef)
  (ass) (ass-all)))
(display ";;; after IS-MS leaf, leaf-heads: ")(write (lheads))(newline)
;; focus the forall-f leaf, intro f
(fhead 'FORALL)
(quietly (lambda () (di)(di)))
(dump "after intro f")
(define f* (let ((a (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IN)(has? 'FUN a)(has? 'PRODUCT-METRIC-W a)))))) (and a (cadr a))))
(display ";;; f*=")(write f*)(newline)
(--- "END v2")
