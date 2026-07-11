(define names '(fun-apply-type-c finsum-single-support ras-id ring-mul-assoc ring-add-left-id
                ring-mul-zero-left matprod-summand-type zeromat-type matadd-type
                abelian-group-idempotent-is-id abelian-group-inverse-unique
                group-assoc module-act-unital))
(for-each (lambda (n)
  (display ";; ") (display n)
  (display "  prov=") (display (provenance-of n))
  (display "  warrant=") (write (warrant-of n)) (newline))
  names)
;; how many asserted facts in the whole theory have NO warrant?
(let ((tot 0) (unw 0))
  (for-each (lambda (e)
     (when (eq? (provenance-of (car e)) 'asserted)
       (set! tot (+ tot 1))
       (unless (warrant-of (car e)) (set! unw (+ unw 1)))))
   (hash-table->alist *theorem-table*))
  (display ";; asserted facts: ") (display tot)
  (display " ; of those with NO warrant: ") (display unw) (newline))
