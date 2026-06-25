;;; theorem-library/tychonoff-proof.scm
;;; ====================================================================
;;; compact-countable-product (countable Tychonoff headline) -- PROVEN.
;;;
;;; A countable product of COMPACT metric spaces is compact, via the metric/
;;; sequential route.  Mechanical reduction to the keystone:
;;;   - each factor compact => seq-compact            (compact-iff-seq-compact)
;;;   - so the product is seq-compact                 (seq-compact-countable-product)
;;;   - the product is a metric space                 (product-is-metric-space @ wdef)
;;;   - seq-compact => compact                        (compact-iff-seq-compact)
;;; The cross-coordinate diagonalisation lives entirely in the warranted keystone
;;; coordinatewise-diagonal-subseq (cited transitively through seq-compact-
;;; countable-product); this file machine-checks the reduction TO it.
;;;
;;; Loads after seq-compact-product (the cited supports) + interactive/proof-debt
;;; (sp/di/mac/fact/qed).  See calculus/tychonoff-build.scm for the annotated
;;; build.  Bill bottoms out at the warranted product supports + the keystone.
;;; ====================================================================

(define (ty--gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (ty--asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (ty--find pred)
  (let loop ((as (ty--asms)))
    (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (ty--head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (ty--has? sym form)
  (cond ((equal? form sym) #t)
        ((pair? form) (or (ty--has? sym (car form)) (ty--has? sym (cdr form))))
        (else #f)))
(define (ty--leaves)
  (filter (lambda (n) (null? (sequent-node-in-arrows n)))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (ty--focus-pred p)
  (let loop ((gs (ty--leaves)))
    (cond ((null? gs) #f)
          ((p (wff-formula (sequent-node-assertion (car gs))))
           (set! *ps* (focus-on *ps* (car gs))) #t)
          (else (loop (cdr gs))))))
(define (ty--focus-head h) (ty--focus-pred (lambda (a) (and (pair? a) (eq? (car a) h)))))

(define ty--wdef '(VNB-LAMBDA n (/ 1 (power 2 (+ n 1)))))

;;; ---- the goal ----
(sp (make-wff
     '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
        (IMPLIES (FORALL n (IMPLIES (IN n NN) (IS-COMPACT (ms n))))
          (IS-COMPACT (PRODUCT-METRIC ms)))))))
(quietly (lambda () (di)(di)(di)))
(define ty--ms (cadr (ty--find (ty--head? 'IS-MS-SEQUENCE))))
(define ty--Hcomp (ty--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(ty--has? 'IS-COMPACT a)))))

;;; (A) sub-lemma: forall n in NN, SEQ-COMPACT (ms n)
(define ty--SC (list 'FORALL 'n (list 'IMPLIES (list 'IN 'n 'NN)
                                      (list 'SEQ-COMPACT (list ty--ms 'n)))))
(quietly (lambda () (cut ty--SC)))
(ty--focus-pred (lambda (a) (equal? a ty--SC)))
(quietly (lambda () (di)(di)))
(define ty--n (let ((a (ty--find (lambda (a) (and (pair? a)(eq? (car a) 'IN)(equal? (caddr a) 'NN))))))
                (and a (cadr a))))
(quietly (lambda ()
  (and ty--Hcomp (inst+ ty--Hcomp ty--n))                 ; IS-COMPACT (ms n)
  (let ((h (ty--find (ty--head? 'IS-MS-SEQUENCE)))) (and h (mac-h 'IS-MS-SEQUENCE h)))
  (let ((h (ty--find (lambda (a) (and (pair? a)(eq? (car a) 'FORALL)(ty--has? 'IS-METRIC-SPACE a))))))
    (and h (inst+ h ty--n)))                              ; IS-METRIC-SPACE (ms n)
  (mac 'compact-iff-seq-compact-rev) (ass) (ass-all)))    ; SEQ-COMPACT(ms n) <- IS-COMPACT(ms n)

;;; (B) main: assemble IS-MS + SEQ-COMPACT of the product, close via the iff
(ty--focus-head 'IS-COMPACT)
(quietly (lambda ()
  (fact 'product-metric-default-summable)                 ; SUMMABLE-WEIGHT wdef
  (fact 'product-is-metric-space ty--ms ty--wdef)         ; IS-MS (PRODUCT-METRIC-W ms wdef)
  (fact 'seq-compact-countable-product ty--ms)))          ; SEQ-COMPACT (PRODUCT-METRIC ms)
;; IS-MS (PRODUCT-METRIC ms): cut, unfold PRODUCT-METRIC (goal-side), ass from the -W hyp
(quietly (lambda () (cut (list 'IS-METRIC-SPACE (list 'PRODUCT-METRIC ty--ms)))))
(ty--focus-pred (lambda (a) (equal? a (list 'IS-METRIC-SPACE (list 'PRODUCT-METRIC ty--ms)))))
(quietly (lambda () (mac 'PRODUCT-METRIC) (ass) (ass-all)))
(ty--focus-head 'IS-COMPACT)
(quietly (lambda () (mac 'compact-iff-seq-compact) (ass) (ass-all)))

(if (proof-done? *ps*)
    (qed 'compact-countable-product)
    (error "tychonoff-proof: proof did not complete"))
