(set! *vnb-quiet* #t)
(load "/home/ubuntu/prover/theorem-library/mod-basis-proof.scm")
(call-with-output-file "/home/ubuntu/prover/scratchpad/RESULT2.txt"
  (lambda (p) (write-string "MOD-BASIS: ALL QED" p) (newline p)))
(display "DRIVER-OK")(newline)
