;;; rr-ineq-probe.scm -- self-test for the rr-ineq applier prototype.
;;;
;;; Three routine "proof block" inequality goals, one per lane the applier is
;;; meant to dispatch.  For each: set it up, di the hypotheses into context,
;;; (rr-ineq-scan) to SHOW which lanes close it, then (rr-ineq!) to COMMIT the
;;; winner, and report PROVED?.
;;;
;;; Run:
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet \
;;;     --load load.scm \
;;;     --load structure-library/rr-ineq.scm \
;;;     --load calculus/rr-ineq-probe.scm --eval '(exit)'

(define (--- title)
  (newline) (display ";;; ===== ") (display title) (display " =====") (newline))
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (goal) (expression->string (sequent-node-assertion (proof-state-focus *ps*))))

(define pass-count 0)
(define fail-count 0)
(define (expect-proved! label)
  (let ((ok (proof-done? *ps*)))
    (if ok (set! pass-count (+ pass-count 1)) (set! fail-count (+ fail-count 1)))
    (display (if ok ";; PASS " ";; FAIL ")) (display label)
    (display " -- PROVED? ") (display ok) (newline)))

;;; -----------------------------------------------------------------------
(--- "T1  LINEAR lane: x<=y, y<=z |- x<=z   (the (ineq) oracle)")
(sp '(IMPLIES (IN x RR) (IMPLIES (IN y RR) (IMPLIES (IN z RR)
       (IMPLIES (<= x y) (IMPLIES (<= y z) (<= x z)))))))
(di)(di)(di)(di)(di)
(==> "goal" (goal))
(rr-ineq-scan)
(==> "winner" (rr-ineq!))
(expect-proved! "T1 x<=z by transitivity")

;;; -----------------------------------------------------------------------
(--- "T2  CLUSTER lane (nonlinear): 0<=c, x<=y |- c*x <= c*y")
(sp '(IMPLIES (IN c RR) (IMPLIES (IN x RR) (IMPLIES (IN y RR)
       (IMPLIES (<= 0 c) (IMPLIES (<= x y) (<= (* c x) (* c y))))))))
(di)(di)(di)(di)(di)
(==> "goal" (goal))
(rr-ineq-scan)
(==> "winner" (rr-ineq!))
(expect-proved! "T2 c*x<=c*y by rr-le-scale-nonneg")

;;; -----------------------------------------------------------------------
(--- "T3  CLUSTER lane (abs): x in RR |- x <= |x|")
(sp '(IMPLIES (IN x RR) (<= x (abs x))))
(di)
(==> "goal" (goal))
(rr-ineq-scan)
(==> "winner" (rr-ineq!))
(expect-proved! "T3 x<=|x| by rr-le-abs")

;;; -----------------------------------------------------------------------
(--- "T4  NEGATIVE control: no lane closes a non-consequence")
;;; y<=x should NOT prove x<=y (and the oracle must refuse, not fabricate).
(sp '(IMPLIES (IN x RR) (IMPLIES (IN y RR) (IMPLIES (<= y x) (<= x y)))))
(di)(di)(di)
(==> "goal" (goal))
(==> "rr-ineq? (expect #f)" (rr-ineq?))
(let ((w (rr-ineq!)))
  (if w (begin (set! fail-count (+ fail-count 1))
               (display ";; FAIL T4 -- applier wrongly claimed a close!\n"))
      (begin (set! pass-count (+ pass-count 1))
             (display ";; PASS T4 -- correctly refused; state untouched.\n"))))

;;; -----------------------------------------------------------------------
(--- "SUMMARY")
(display ";; rr-ineq prototype self-test: ")
(display pass-count) (display " passed, ")
(display fail-count) (display " failed.\n")
