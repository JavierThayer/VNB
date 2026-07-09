;;; calculus/cauchy-subseq-via-combinatorial.scm
;;; ====================================================================
;;; CLEAN ASSEMBLY -- "totally bounded => every sequence has a Cauchy
;;; subsequence" (calculus.pdf Prop 3.31), routed so that the WITNESS for
;;; the subsequence comes from the METRIC-FREE block-family-combinatorial.
;;;
;;; The point of this script (vs calculus/totally-bounded-cauchy-subseq.scm,
;;; which calls the metric `block-family' directly): make visible that the
;;; only metric input is one bridge (tb-rad-ball-cover: TB -> a sequence of
;;; finite ball covers), after which the entire blk witness is produced by
;;; the combinatorial recursion, with no further appeal to distance.
;;;
;;; Spine:
;;;   rad   <- null-rr-seq-exists                 (a positive null radius seq)
;;;   cov   <- tb-rad-ball-cover (s, rad)         (finite cover per level)  [BRIDGE]
;;;   blk   <- block-family-combinatorial(X s, f, cov)   ********** WITNESS **********
;;;   phi   <- diagonalization (blk)             (strictly-mono, tail in blk(k))
;;;   ew phi; HALF1 strictly-mono closes; HALF2 cauchy = 2r estimate (residual).
;;;
;;; NOT part of load.scm; a probe/teaching script.  Run (fast):
;;;   cd ~/prover
;;;   mit-scheme --quiet --load load.scm \
;;;       --load calculus/cauchy-subseq-via-combinatorial.scm --eval '(exit)' \
;;;       > /tmp/csvc.out 2>&1
;;;   grep -E '^;;; ' /tmp/csvc.out
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred)
  (let loop ((as (asms)))
    (cond ((null? as) #f)
          ((pred (car as)) (car as))
          (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (typed-elt cod)
  (let ((a (find-asm (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) cod))))))
    (and a (cadr a))))
(define (--- title) (newline)(display ";;; ===== ")(display title)(display " =====")(newline))
(define (dump tag)
  (display ";;; [")(display tag)(display "]  done?=")(display (proof-done? *ps*))(newline)
  (display ";;;   GOAL: ")(write (gf))(newline))
(define (frontier-heads)
  (let ((leaves (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                        (dg-ungrounded-nodes (proof-state-dg *ps*)))))
    (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n))))
                       (if (pair? a) (car a) a)))
         leaves)))
(define (report-frontier tag)
  (display ";;;   ")(display tag)(display " -- ungrounded LEAF heads: ")
  (write (frontier-heads))(newline))
(define (split-ands)              ; split every top-level AND assumption in context
  (let loop ((n 0))
    (let ((a (find-asm (head? 'AND))))
      (cond ((and a (< n 8)) (ai a) (loop (+ n 1))) (else n)))))
(define (find-subterm pred form)  ; first subterm of `form' satisfying pred
  (cond ((pred form) form)
        ((pair? form)
         (let loop ((xs form))
           (cond ((null? xs) #f)
                 ((find-subterm pred (car xs)) => (lambda (r) r))
                 (else (loop (cdr xs))))))
        (else #f)))
(define (find-subterm-asms pred)  ; first subterm across all assumptions
  (let loop ((as (asms)))
    (cond ((null? as) #f)
          ((find-subterm pred (car as)) => (lambda (r) r))
          (else (loop (cdr as))))))

;;; -----------------------------------------------------------------------
(--- "Pose totally-bounded-has-cauchy-subsequence and strip")
(sp (make-wff
     '(FORALL s
        (IMPLIES (TOTALLY-BOUNDED s)
          (FORALL f
            (IMPLIES (IN f (FUN NN (X s)))
              (FORSOME phi
                (AND (STRICTLY-MONO-NN phi)
                     (IS-CAUCHY-SEQ s (SUBSEQ f phi))))))))))
(quietly (lambda () (di)(di)(di)(di)))      ; s, TB s, f, f:NN->X(s)
(dump "after strip")
(define s* (cadr (find-asm (head? 'TOTALLY-BOUNDED))))
(define f* (typed-elt '(FUN NN (X s))))
(display ";;;   eigenvars  s*=")(write s*)(display "  f*=")(write f*)(newline)

;;; (1) a positive null radius sequence.
(--- "(1) rad <- null-rr-seq-exists, extract pointwise positivity")
(quietly
 (lambda ()
   (fact 'null-rr-seq-exists)
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))))  ; skolemize rad
(define rad* (cadr (find-asm (head? 'NULL-RR-SEQ))))            ; grab BEFORE unfolding
(quietly
 (lambda ()
   (mac-h 'NULL-RR-SEQ (list 'NULL-RR-SEQ rad*))                ; unfold NULL-RR-SEQ rad
   (split-ands)))                                               ; expose POS-RR conjunct
(dump "after rad")
(display ";;;   rad*=")(write rad*)(newline)
(report-frontier "after (1)")

;;; (2) BRIDGE: TB + positive rad  ->  finite ball-cover sequence cov.
(--- "(2) cov <- tb-rad-ball-cover (the ONLY metric step)")
(quietly
 (lambda ()
   (fact 'tb-rad-ball-cover s* rad*)
   (split-ands)                                                ; (X s) in SET  +  FORSOME cov ...
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))   ; skolemize cov
   (split-ands)))                                              ; (i) finite-cover, (ii) members-are-balls
(dump "after bridge")
;; cov is the operator in (i): ...(IS-FINITE-COVER (cov k) (X s))... -> grab (car (cov k)).
(define cov*
  (let ((ifc (find-subterm-asms (head? 'IS-FINITE-COVER))))
    (and ifc (car (cadr ifc)))))
(display ";;;   cov*=")(write cov*)(newline)
(report-frontier "after (2)")

;;; (3) ********** WITNESS STEP **********  the metric-free recursion makes blk.
(--- "(3) blk <- block-family-combinatorial (X s, f, cov)   [WITNESS]")
(quietly
 (lambda ()
   (fact 'block-family-combinatorial (list 'X s*) f* cov*)
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))   ; skolemize blk
   (split-ands)))
(dump "after block-family-combinatorial")
(define blk* (typed-elt '(FUN NN (INF-SUBSETS NN))))
(display ";;;   blk*=")(write blk*)(newline)
(report-frontier "after (3) -- if FUN(NN,INF-SUBSETS NN) typed asm present, blk is in hand")

;;; (4) diagonalize blk.
(--- "(4) phi <- diagonalization (blk)")
(quietly
 (lambda ()
   (if blk* (fact 'diagonalization blk*))
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))   ; skolemize phi
   (split-ands)))
(dump "after diagonalization")
(define phi* (let ((sm (find-asm (head? 'STRICTLY-MONO-NN)))) (and sm (cadr sm))))
(display ";;;   phi*=")(write phi*)(newline)
(report-frontier "after (4)")

;;; (5) witness phi, split the goal.
(--- "(5) ew phi, split goal AND")
(quietly (lambda () (if phi* (ew phi*)) (di)))
(display ";;;   open goals now: ")
(for-each (lambda (g) (display "[")(display (sequent-node-number g))(display "] ")
                      (write (wff-formula (sequent-node-assertion g)))(display "  "))
          (proof-open-goals *ps*))
(newline)

;;; HALF 1: STRICTLY-MONO-NN(phi) -- closes from diagonalization output.
(--- "HALF 1: STRICTLY-MONO-NN")
(let loop ((gs (proof-open-goals *ps*)))
  (cond ((null? gs) (display ";;; (no strictly-mono subgoal)\n"))
        ((let ((a (wff-formula (sequent-node-assertion (car gs)))))
           (and (pair? a) (eq? (car a) 'STRICTLY-MONO-NN)))
         (set! *ps* (focus-on *ps* (car gs))))
        (else (loop (cdr gs)))))
(quietly (lambda () (ass-all)))
(report-frontier "after HALF1 (strictly-mono gone => closed)")

;;; HALF 2: IS-CAUCHY-SEQ -- the residual 2r estimate.
(--- "HALF 2: IS-CAUCHY-SEQ -- the residual estimate (capture + tail + ball-2r + null)")
(let loop ((gs (proof-open-goals *ps*)))
  (cond ((null? gs) (display ";;; (no cauchy subgoal)\n"))
        ((let ((a (wff-formula (sequent-node-assertion (car gs)))))
           (and (pair? a) (eq? (car a) 'IS-CAUCHY-SEQ)))
         (set! *ps* (focus-on *ps* (car gs))))
        (else (loop (cdr gs)))))
(dump "HALF2 goal")
(report-frontier "HALF2 frontier")
(display ";;;   RESIDUAL: for m,n>=k, phi(m),phi(n) in blk(k) (diagonalization tail);\n")
(display ";;;   capture+bridge(ii) put both f(phi m),f(phi n) in one BALL(s,c_k,rad k);\n")
(display ";;;   ball-2r-triangle => d < 2 rad(k); NULL-RR-SEQ(rad) => rad(k)<=eps/2.\n")
(display ";;;   Same wall as totally-bounded-cauchy-subseq.scm (the `ew' on inner\n")
(display ";;;   FORSOME N); unchanged by this re-routing.\n")

(--- "END assembly")
