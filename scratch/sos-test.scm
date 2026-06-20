(display "\n===== ENGINE UNIT TESTS =====\n")
(run-sos-tests)

(display "\n===== E2E (pre-di): x*y <= x^2 + y^2 =====\n")
(sp (wff "forall([x in rr, y in rr], x * y <= x ^ 2 + y ^ 2)"))
(sos "x - y" "x" "y")
(display "goal-status: ") (display (goal-status)) (newline)

(display "\n===== E2E (pre-di): single cert 2xy<=x^2+y^2 =====\n")
(sp (wff "forall([x in rr, y in rr], 2 * x * y <= x ^ 2 + y ^ 2)"))
(sos "x - y")
(display "goal-status: ") (display (goal-status)) (newline)

(display "\n===== E2E (pre-di): AM-GM a^2+b^2+c^2 >= ab+bc+ca =====\n")
(sp (wff "forall([a in rr, b in rr, c in rr], a*b + b*c + c*a <= a^2 + b^2 + c^2)"))
(sos "a - b" "b - c" "c - a")
(display "goal-status: ") (display (goal-status)) (newline)

(display "\n===== NEGATIVE: false goal x^2+y^2 <= x*y must REFUSE =====\n")
(sp (wff "forall([x in rr, y in rr], x ^ 2 + y ^ 2 <= x * y)"))
(sos "x - y" "x" "y")
(display "goal-status (expect open): ") (display (goal-status)) (newline)

(display "\n===== NEGATIVE: insufficient cert must REFUSE =====\n")
(sp (wff "forall([x in rr, y in rr], x * y <= x ^ 2 + y ^ 2)"))
(sos "x")
(display "goal-status (expect open): ") (display (goal-status)) (newline)

(display "\n===== post-di usage with displayed names =====\n")
(sp (wff "forall([x in rr, y in rr], x * y <= x ^ 2 + y ^ 2)"))
(di)
(display "(generators are renamed; use what's displayed)\n")
