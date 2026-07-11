(load "load.scm")
(set! *vnb-quiet* #t)
(define r (write-operators-md))
(call-with-output-file "/tmp/claude-1000/-home-ubuntu/423ebffe-e6fe-4caf-8686-2808e8178391/scratchpad/CENSUS.txt"
  (lambda (p) (write r p)))
(%exit 0)
