;;; probe-314.scm -- how far does Prop 3.14, direction (=>), get?
;;;   IS-CONTINUOUS-AT s t f a  AND  CONVERGES-TO s g a
;;;     =>  CONVERGES-TO t (COMPOSE f g) (f a)
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (goal) (expression->string (sequent-node-assertion (proof-state-focus *ps*))))
(define (asms) (map (lambda (w) (expression->string (wff-formula w)))
                    (sequent-node-assumptions (proof-state-focus *ps*))))

(--- "state 3.14 (=>) and load/split hypotheses")
(sp (make-wff '(IMPLIES (AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a))
                        (CONVERGES-TO t (COMPOSE f g) (f a)))))
(di)
(ai '(AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a)))
(==> "asms after split" (asms))
(==> "goal" (goal))

(--- "unfold the CONVERGES-TO goal")
(mac 'CONVERGES-TO)
(==> "goal" (goal))

(--- "block-1 probe: can we unfold the IS-CONTINUOUS-AT hypothesis? (mac targets goals)")
(mac 'IS-CONTINUOUS-AT)
(==> "goal unchanged? (mac hit no hypothesis)" (goal))

(--- "bright spot: the (COMPOSE f g)(n) inside the goal reduces by raw beta")
(mac 'COMPOSE)
(==> "after mac COMPOSE" (goal))
(lam-b)
(==> "after lam-b (composite application beta-reduced?)" (goal))

(==> "DONE-PROBE" 'ok)
