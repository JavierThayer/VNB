(define (gf) (and *ps* (not (proof-done? *ps*)) (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(sp '(FORALL phi (FORALL a (IMPLIES (AND (IN phi (FUN RR RR)) (IN a RR))
        (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS phi a) (IS-CONTINUOUS-AT RR-MS RR-MS phi a))))))
(grind)                       ; hyp continuity -> eps-delta; goal stays folded
(display "GOAL: ") (write (gf)) (newline)
(mac 'IS-CONTINUOUS-AT)        ; unfold goal
(grind) (ass-all)
(bc* 'rr-is-metric-space)
(ass-all)
(display "refold DONE? ") (display (proof-done? *ps*)) (display " focus: ") (write (gf)) (newline)
