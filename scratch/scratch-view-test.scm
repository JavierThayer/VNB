;;; scratch-view-test.scm -- smoke test for def-view-as.

(load "load.scm")

(newline)
(display "============================================================") (newline)
(display "view-as smoke test") (newline)
(display "============================================================") (newline)

;; 1. View table populated?
(display "(1) RING-ADDITIVE-AG declared: ")
(display (and (lookup-view-as 'RING-ADDITIVE-AG) #t)) (newline)

;; 2. Typing axiom exists?
(display "(2) ring-additive-ag-is-abelian-group axiom: ")
(display (and (hash-table-ref/default *theorem-table*
                'ring-additive-ag-is-abelian-group #f) #t))
(newline)

;; 3. Specialized theorem exists with correct accessor reduction?
(display "(3) abelian-group-mul-comm-ring-additive-ag:") (newline)
(display "    ")
(write (hash-table-ref/default *theorem-table*
         'abelian-group-mul-comm-ring-additive-ag #f))
(newline)

;; 4. Functoid macete fires inside a proof?
(display "(4) functoid macete fires in a proof:") (newline)
(sp (make-wff '(= ((MUL (RING-ADDITIVE-AG r)) a b) ((MUL (RING-ADDITIVE-AG r)) b a))))
(display "    before mac: ") (show)
(mac 'RING-ADDITIVE-AG)
(display "    after mac 'RING-ADDITIVE-AG: ") (show)
(mac 'MUL)
(display "    after mac 'MUL: ") (show)
(nth-r)
(display "    after nth-r: ") (show)

(exit)
