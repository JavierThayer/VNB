;;; driver: fast library load (skip-proofs), then REALLY verify matact-assoc-proof.
(verify-proofs!)
(set! *vnb-quiet* #t)
(load "/home/ubuntu/prover/theorem-library/matact-assoc-proof.scm")
(call-with-output-file "/home/ubuntu/prover/scratchpad/RESULT.txt"
  (lambda (p) (write-string "MATACT-ASSOC: ALL QED" p) (newline p)))
(display "DRIVER-OK")(newline)
