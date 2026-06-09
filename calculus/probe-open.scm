;;; probe-open.scm -- does the HONEST open-preimage proof (from the eps/delta
;;; definition, NOT citing its own support) hit the same diagnosis as the
;;; closed case?  Unfold the goal and look at what each conjunct demands.
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (goal) (expression->string (sequent-node-assertion (proof-state-focus *ps*))))
(define (asms) (map (lambda (w) (expression->string (wff-formula w)))
                    (sequent-node-assumptions (proof-state-focus *ps*))))

(--- "honest open-preimage: strip to the interior obligation")
(sp (make-wff '(FORALL s (FORALL t (FORALL f
   (IMPLIES (IS-CONTINUOUS s t f)
     (FORALL V (IMPLIES (IS-OPEN t V) (IS-OPEN s (PREIMAGE s f V))))))))))
(di)(di)(di)(di)(di)(di)
(==> "goal after 6 di" (goal))
(==> "asms" (asms))

(--- "unfold the IS-OPEN goal")
(mac 'IS-OPEN)
(==> "goal" (goal))

(--- "block 1 check: is is-metric-space(s) reachable, or trapped in folded is-continuous?")
;; try to discharge it straight from the assumption set (no unfold of hyps):
(sp (make-wff '(IS-METRIC-SPACE s)))   ; fresh tiny goal, asms gone -> shows it is NOT free-standing
(==> "is-metric-space(s) as a bare goal -- provable from nothing? (expect not closeable)"
     (proof-done? *ps*))

(==> "DONE-PROBE" 'ok)
