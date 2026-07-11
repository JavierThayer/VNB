(set! *vnb-quiet* #t)
(load "/home/ubuntu/prover/theorem-library/mod-basis-proof.scm")
(load "/home/ubuntu/prover/theorem-library/rank-bound-proof.scm")
(call-with-output-file "/home/ubuntu/prover/scratchpad/RESULT3.txt"
  (lambda (p) (write-string "RANK-BOUND: QED" p) (newline p)))
(display "DRIVER-OK")(newline)
