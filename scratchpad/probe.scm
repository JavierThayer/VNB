(display "=== inverse-unique transported? ===") (newline)
(for-each (lambda (n)
  (display n) (display " -> ")
  (write (lookup-theorem n)) (newline) (newline))
  '(abelian-group-inverse-unique
    abelian-group-inverse-unique-module-vector-ag
    abelian-group-idempotent-is-id-module-vector-ag
    module-vector-ag-is-abelian-group
    interval-1-0-empty
    entry-of-zeromat
    finsum-interval-peel
    module-act-unital
    module-zero-act))
(display "=== SPAN functoid ===") (newline)
(write (lookup-theorem 'SPAN-def)) (newline)
