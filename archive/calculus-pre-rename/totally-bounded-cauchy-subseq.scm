;;; calculus/totally-bounded-cauchy-subseq.scm
;;; ====================================================================
;;; STRESS TEST -- the assembly half of "totally bounded => every sequence
;;; has a Cauchy subsequence" (calculus.pdf Prop 3.31), driven by hand to
;;; map the obstacle.  NOT part of load.scm; a probe/teaching script.
;;;
;;; Run (fast; full output -- do NOT pipe through head, it SIGPIPEs the run):
;;;   cd ~/prover
;;;   mit-scheme --quiet --load load.scm \
;;;       --load calculus/totally-bounded-cauchy-subseq.scm --eval '(exit)' \
;;;       > /tmp/tbcs.out 2>&1
;;;   grep -E '^;;; ' /tmp/tbcs.out
;;;
;;; rad-parametrised workhorse (theorem-library/cauchy-subsequence):
;;;   TB s, f : NN->X(s), rad a positive null real sequence
;;;     ==>  exists strictly-monotone phi with SUBSEQ(f,phi) Cauchy.
;;;
;;; FINDINGS this probe establishes:
;;;  * The forward assembly is fully driveable BY HAND: `fact' cites a PSS
;;;    universal, instantiates it and auto-detaches in-context antecedents;
;;;    `ai' skolemizes the resulting existential.  block-family's FORSOME blk
;;;    and diagonalization's FORSOME (diagonal) both land cleanly in context.
;;;  * The STRICTLY-MONO-NN half closes to QED from diagonalization's output.
;;;  * SCOUT CANNOT drive the rest: its alphabet (grind/closers/mac/bc*/inst+)
;;;    has NO existential-GOAL introduction.  Proving FORSOME phi (and, inside
;;;    IS-CAUCHY-SEQ, FORSOME N) needs `ew' (exists-witness), a move scout does
;;;    not propose.  inst+ chooses witnesses for universal HYPOTHESES, not for
;;;    existential GOALS.  => a candidate future lane: an `ew' suggester that
;;;    offers context-typed terms as existential-goal witnesses (the dual of
;;;    vnb--scout-inst-candidates).
;;; ====================================================================

(define (gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (find-asm pred)            ; first assumption formula satisfying pred
  (let loop ((as (asms)))
    (cond ((null? as) #f)
          ((pred (car as)) (car as))
          (else (loop (cdr as))))))
(define (head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
;; the bound element of an  (IN x CODOMAIN)  assumption whose codomain prints =cod
(define (typed-elt cod)
  (let ((a (find-asm (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) cod))))))
    (and a (cadr a))))
(define (--- title)
  (newline)(display ";;; ===== ")(display title)(display " =====")(newline))
(define (dump tag)
  (display ";;; [")(display tag)(display "]  open-goals=")
  (display (length (proof-open-goals *ps*)))
  (display "  done?=")(display (proof-done? *ps*))(newline)
  (display ";;;   GOAL: ")(write (gf))(newline))
;; the TRUE open frontier: heads of ungrounded LEAF nodes (null in-arrows), the
;; distinction scout learned -- ancestor nodes stay ungrounded until all their
;; descendants ground, so a raw open-goals count never drops when one leaf closes.
(define (frontier-heads)
  (let ((leaves (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                        (dg-ungrounded-nodes (proof-state-dg *ps*)))))
    (map (lambda (n) (let ((a (wff-formula (sequent-node-assertion n))))
                       (if (pair? a) (car a) a)))
         leaves)))
(define (report-frontier tag)
  (display ";;;   ")(display tag)(display " -- ungrounded LEAF heads: ")
  (write (frontier-heads))(newline))

;;; -----------------------------------------------------------------------
(sp (make-wff
     '(FORALL s
        (IMPLIES (TOTALLY-BOUNDED s)
          (FORALL f
            (IMPLIES (IN f (FUN NN (X s)))
              (FORALL rad
                (IMPLIES (NULL-RR-SEQ rad)
                  (FORSOME phi
                    (AND (STRICTLY-MONO-NN phi)
                         (IS-CAUCHY-SEQ s (SUBSEQ f phi))))))))))))

(quietly
 (lambda ()
   (di)(di)(di)(di)(di)(di)))          ; strip 3 FORALL + 3 IMPLIES
(--- "after forward strip")
(dump "1")
(define s*   (cadr (find-asm (head? 'TOTALLY-BOUNDED))))
(define f*   (typed-elt '(FUN NN (X s))))
(define rad* (cadr (find-asm (head? 'NULL-RR-SEQ))))
(display ";;;   eigenvars  s*=")(write s*)(display "  f*=")(write f*)
(display "  rad*=")(write rad*)(newline)

;;; (A) block-family forward, then skolemize + split.
(quietly
 (lambda ()
   (fact 'block-family s* f* rad*)
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))   ; skolemize blk
   (let ((a (find-asm (head? 'AND)))) (and a (ai a)))          ; split top AND
   (let ((a (find-asm (head? 'AND)))) (and a (ai a)))))        ; split nested AND
(--- "after block-family (skolemized + split)")
(dump "2")
(define blk* (typed-elt '(FUN NN (INF-SUBSETS NN))))
(display ";;;   blk*=")(write blk*)(newline)

;;; (B) diagonalization forward at blk*, then skolemize + split the diagonal.
(quietly
 (lambda ()
   (if blk* (fact 'diagonalization blk*))
   (let ((fs (find-asm (head? 'FORSOME)))) (and fs (ai fs)))   ; skolemize diagonal
   (let ((a (find-asm (head? 'AND)))) (and a (ai a)))
   (let ((a (find-asm (head? 'AND)))) (and a (ai a)))))
(--- "after diagonalization (skolemized + split)")
(dump "3")
(define phi* (typed-elt '(FUN NN NN)))      ; the diagonal, typed NN->NN
(display ";;;   phi*=")(write phi*)(newline)

;;; (C) witness phi in the goal, split the conjunction.
(quietly (lambda () (if phi* (ew phi*)) (di)))
(--- "after witnessing phi + splitting goal AND")
(display ";;;   open goals now: ")
(for-each (lambda (g) (display "[")(display (sequent-node-number g))(display "] ")
                      (write (wff-formula (sequent-node-assertion g)))(display "  "))
          (proof-open-goals *ps*))
(newline)

;;; ----- HALF 1: STRICTLY-MONO-NN(phi*) -- close from diagonalization's output.
(--- "HALF 1: STRICTLY-MONO-NN")
;; focus the strictly-mono subgoal
(let ((g (find-asm (lambda (x) #f))) ) #f)   ; no-op; focus via open goals below
(let loop ((gs (proof-open-goals *ps*)))
  (cond ((null? gs) (display ";;; (no strictly-mono subgoal found)\n"))
        ((let ((a (wff-formula (sequent-node-assertion (car gs)))))
           (and (pair? a) (eq? (car a) 'STRICTLY-MONO-NN)))
         (set! *ps* (focus-on *ps* (car gs))))
        (else (loop (cdr gs)))))
(report-frontier "before HALF1")
(quietly (lambda () (mac 'STRICTLY-MONO-NN) (di) (ass-all)))
(dump "HALF1 after (mac STRICTLY-MONO-NN)(di)(ass-all)")
(report-frontier "after  HALF1 (strictly-mono-nn gone => it closed)")

;;; ----- HALF 2: IS-CAUCHY-SEQ -- focus it, dump, hand it to scout.
(--- "HALF 2: IS-CAUCHY-SEQ -- scout the witness wall")
(let loop ((gs (proof-open-goals *ps*)))
  (cond ((null? gs) (display ";;; (no cauchy subgoal -- already closed?)\n"))
        ((let ((a (wff-formula (sequent-node-assertion (car gs)))))
           (and (pair? a) (eq? (car a) 'IS-CAUCHY-SEQ)))
         (set! *ps* (focus-on *ps* (car gs))))
        (else (loop (cdr gs)))))
(dump "HALF2 IS-CAUCHY-SEQ goal")
(report-frontier "at  HALF2 (the only real leaf left is is-cauchy-seq)")
(display ";;;   scout 4 2 120 on IS-CAUCHY-SEQ ...\n")
(define scout-result (quietly (lambda () (scout 4 2 120))))
(display ";;;   scout (nodes (d b) goal best-partials closing):\n;;;   ")
(write scout-result)(newline)

(--- "END probe")
