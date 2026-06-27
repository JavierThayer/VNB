(verify-proofs!)
(define (asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (show tag) (display tag) (newline)
  (for-each (lambda (a) (display "  - ") (write a) (newline)) (asms)))
(sp '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
     (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
              (IS-DIFF-AT (VNB-LAMBDA x (+ (f x) (g x))) a (+ L M)))))))))
(di)(di)(di)(di)(di)(di)
(ai 1)
(mac-h 'IS-DIFF-AT 1)
(ai 1)(ai 1)(ai 1)(ai 1)     ; try to drill+skolemize the forsome
(show "after ai-drill on hyp1:")
