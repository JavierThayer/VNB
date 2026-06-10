(define (id--elt carrier)
  (let ((h (bd--any (lambda (w) (let ((f (wff-formula w)))
                                  (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) carrier))))
                    (bd--asms (bd--cur)))))
    (and h (cadr (wff-formula h)))))
(define (di-until-atomic!)
  (let loop ((fuel 8))
    (let ((g (bd--goalof (bd--cur))))
      (when (and (> fuel 0) (pair? g) (memq (car g) '(FORALL IMPLIES))) (di) (loop (- fuel 1))))))
(sp (make-wff '(FORALL X (IN (VNB-LAMBDA x_ x_) (BIJECTION X X)))))
(di)
(define id--carrier (cadr (caddr (bd--goalof (bd--cur)))))
(mac 'bijection-membership-iff)
(di)
(lam-t) (di-until-atomic!) (ass)         ; typing
(di)                                     ; expose injective
(lam-b) (di-until-atomic!) (ass)         ; injective
(lam-b) (di)                             ; surjective: reduce, intro w
(ew (id--elt id--carrier))               ; witness w
(di) (ass) (rfl)                         ; split AND: IN w X / w=w
(display "DONE? ")(display (proof-done? *ps*))(newline)
