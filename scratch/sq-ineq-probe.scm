;; probe: x*y <= x^2 + y^2  via sum-of-squares bricks
(load "/home/ubuntu/prover/load")

(display "\n===== START =====\n")
(sp (wff "forall([x in rr, y in rr], x * y <= x ^ 2 + y ^ 2)"))

(display "\n----- after (di) -----\n")
(di) (show)

(display "\n----- after (bc* 'rr-le-from-diff-nonneg) -----\n")
(bc* 'rr-le-from-diff-nonneg) (show)

(display "\n----- after (bc* 'rr-double-nonneg) -----\n")
(bc* 'rr-double-nonneg) (show)

(display "\n===== goal-status: ")
(display (goal-status))
(display " =====\n")
