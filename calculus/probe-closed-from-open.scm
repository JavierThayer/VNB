;;; probe-closed-from-open.scm
;;; STRESS TEST (not a demo): derive continuous-implies-closed-preimage
;;; HONESTLY -- from continuous-implies-open-preimage + preimage-complement
;;; + the IS-CLOSED unfold -- WITHOUT citing its own namesake support.
;;; Purely algebraic (no eps/delta).  Prints the goal state at each step so
;;; we can see exactly where the machinery snags.
;;;   VNB_SKIP_PROOFS=1 ./prover -i calculus/probe-closed-from-open.scm </dev/null

(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (goal)
  (expression->string (sequent-node-assertion (proof-state-focus *ps*))))
(define (asms)
  (map (lambda (w) (expression->string (wff-formula w)))
       (sequent-node-assumptions (proof-state-focus *ps*))))

(--- "STRESS: closed-preimage from open-preimage + preimage-complement")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL A (IMPLIES (IS-CLOSED t A)
       (IS-CLOSED s (PREIMAGE s f A))))))))))
(di)(di)(di)(di)(di)(di)
(==> "after 6 di, goal" (goal))
(==> "  assumptions"    (asms))

(mac 'IS-CLOSED)
(==> "after (mac IS-CLOSED), goal" (goal))

(==> "DONE-PROBE" 'ok)
