;;; calculus/tychonoff-build.scm -- BUILD SCRATCH (not loaded)
;;; Drive compact-countable-product (countable Tychonoff headline) to QED,
;;; modulo the keystone coordinatewise-diagonal-subseq.  Iterating; dumps.

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred)
  (let loop ((as (asms)))
    (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (contains? sym form)
  (cond ((equal? form sym) #t)
        ((pair? form) (or (contains? sym (car form)) (contains? sym (cdr form))))
        (else #f)))
(define (--- t) (newline)(display ";;; ===== ")(display t)(display " =====")(newline))
(define (dump tag)
  (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display "  GOAL: ")(write (gf))(newline))
(define (leaf-goals)
  (filter (lambda (n) (null? (sequent-node-in-arrows n)))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (leaf-pred? p)
  (let loop ((gs (leaf-goals)))
    (cond ((null? gs) #f)
          ((p (wff-formula (sequent-node-assertion (car gs))))
           (set! *ps* (focus-on *ps* (car gs))) #t)
          (else (loop (cdr gs))))))
(define (leaf-head? h) (leaf-pred? (lambda (a) (and (pair? a) (eq? (car a) h)))))
(define (leaf-heads)
  (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n)))) (if (pair? a)(car a) a)))
       (leaf-goals)))

(define wdef '(VNB-LAMBDA n (/ 1 (power 2 (+ n 1)))))   ; the default summable weight

;;; ---------- the goal ----------
(sp (make-wff
     '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
        (IMPLIES (FORALL n (IMPLIES (IN n NN) (IS-COMPACT (ms n))))
          (IS-COMPACT (PRODUCT-METRIC ms)))))))
(quietly (lambda () (di)(di)(di)))
(define ms* (cadr (find-asm (head? 'IS-MS-SEQUENCE))))
(define Hcomp (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(contains? 'IS-COMPACT a)))))
(define Hms   (find-asm (head? 'IS-MS-SEQUENCE)))
(dump "after strip")
(display ";;; ms*=")(write ms*)(display " Hcomp=")(write Hcomp)(newline)

;;; ---------- sub-lemma: forall n in NN, SEQ-COMPACT (ms n) ----------
(--- "(A) cut and prove  forall n, SEQ-COMPACT (ms n)")
(define SC (list 'FORALL 'n (list 'IMPLIES (list 'IN 'n 'NN) (list 'SEQ-COMPACT (list ms* 'n)))))
(quietly (lambda () (cut SC)))
(leaf-pred? (lambda (a) (equal? a SC)))
(quietly (lambda () (di)(di)))                 ; intro n, n in NN ; goal SEQ-COMPACT (ms n)
(define n* (let ((a (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) 'NN)))))) (and a (cadr a))))
(dump "SC body: intro n")
(display ";;; n*=")(write n*)(newline)
;; IS-COMPACT (ms n) into context; IS-MS (ms n) by unfolding IS-MS-SEQUENCE then inst+
(quietly (lambda ()
  (and Hcomp (inst+ Hcomp n*))
  (let ((h (find-asm (head? 'IS-MS-SEQUENCE)))) (and h (mac-h 'IS-MS-SEQUENCE h)))
  (let ((h (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(contains? 'IS-METRIC-SPACE a))))))
    (and h (inst+ h n*)))))
(display ";;; have IS-COMPACT(ms n)? ")(write (and (find-asm (lambda(a)(equal? a (list 'IS-COMPACT (list ms* n*))))) #t))
(display "  IS-MS(ms n)? ")(write (and (find-asm (lambda(a)(equal? a (list 'IS-METRIC-SPACE (list ms* n*))))) #t))(newline)
;; rewrite goal SEQ-COMPACT (ms n) -> IS-COMPACT (ms n) via the iff (-rev), then ass
(quietly (lambda () (mac 'compact-iff-seq-compact-rev) (ass) (ass-all)))
(dump "SC body: after mac iff-rev + ass")
(display ";;; SC body closed? leaf-heads: ")(write (leaf-heads))(newline)

;;; ---------- back on main: IS-COMPACT (PRODUCT-METRIC ms) ----------
(--- "(B) main: IS-MS + SEQ-COMPACT of the product, then iff")
(leaf-head? 'IS-COMPACT)
(dump "main goal refocus")
;; IS-MS (PRODUCT-METRIC ms): product-is-metric-space at wdef
(quietly (lambda ()
  (fact 'product-metric-default-summable)               ; SUMMABLE-WEIGHT wdef
  (fact 'product-is-metric-space ms* wdef)))            ; -> IS-MS (PRODUCT-METRIC-W ms wdef)
(display ";;; IS-MS(PRODUCT-METRIC-W ms wdef)? ")
(write (and (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'IS-METRIC-SPACE)(contains? 'PRODUCT-METRIC-W a)))) #t))(newline)
;; SEQ-COMPACT (PRODUCT-METRIC ms): seq-compact-countable-product (detaches IS-MS-SEQUENCE + SC)
(quietly (lambda () (fact 'seq-compact-countable-product ms*)))
(display ";;; SEQ-COMPACT(PRODUCT-METRIC ms)? ")
(write (and (find-asm (lambda (a) (and (pair? a)(eq? (car a) 'SEQ-COMPACT)(contains? 'PRODUCT-METRIC a)(not (contains? 'PRODUCT-METRIC-W a))))) #t))(newline)
(dump "main: before closing iff")
;; IS-MS (PRODUCT-METRIC ms): cut it; prove by unfolding PRODUCT-METRIC (goal-side)
;; then ass from the IS-MS(-W) hyp.  Keeps the main goal in PRODUCT-METRIC form.
(quietly (lambda () (cut (list 'IS-METRIC-SPACE (list 'PRODUCT-METRIC ms*)))))
(leaf-pred? (lambda (a) (equal? a (list 'IS-METRIC-SPACE (list 'PRODUCT-METRIC ms*)))))
(quietly (lambda () (mac 'PRODUCT-METRIC) (ass) (ass-all)))
(leaf-head? 'IS-COMPACT)
(dump "main: IS-MS(PRODUCT-METRIC ms) established")
;; goal IS-COMPACT(PRODUCT-METRIC ms) -> SEQ-COMPACT via iff (discharge IS-MS), ass
(quietly (lambda () (mac 'compact-iff-seq-compact) (ass) (ass-all)))
(dump "main: after iff + ass")

(display ";;; PROOF DONE? ")(write (proof-done? *ps*))(newline)
(display ";;; ungrounded: ")(write (length (dg-ungrounded-nodes (proof-state-dg *ps*))))
(display "  leaf-heads: ")(write (leaf-heads))(newline)
(--- "END")
