;;; id-probe.scm -- bijection-identity, exploratory.  (bd-- helpers are live.)

;; element of the (IN ? carrier) hyp in the focus ctx
(define (id--elt carrier)
  (let ((h (bd--any (lambda (w) (let ((f (wff-formula w)))
                                  (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) carrier))))
                    (bd--asms (bd--cur)))))
    (and h (cadr (wff-formula h)))))

(define (di-until-atomic!)
  (let loop ((fuel 8))
    (let ((g (bd--goalof (bd--cur))))
      (when (and (> fuel 0) (pair? g) (memq (car g) '(FORALL IMPLIES)))
        (di) (loop (- fuel 1))))))

(sp (make-wff '(FORALL X (IN (VNB-LAMBDA x_ x_) (BIJECTION X X)))))
(di)
(define id--carrier (cadr (caddr (bd--goalof (bd--cur)))))   ; the eigenvar for X
(display "carrier=")(write id--carrier)(newline)
(mac 'bijection-membership-iff)
(display "after mac goal=")(write (bd--goalof (bd--cur)))(newline)
(di)
(display "after di1 goal=")(write (bd--goalof (bd--cur)))(newline)

;; conjunct 1: typing  IN (lambda x_ x_) (FUN X X)
(lam-t)
(di-until-atomic!)
(ass)
(display "after typing, open goals=")(display (length (bd--leaves)))(newline)
(display "focus goal=")(write (bd--goalof (bd--cur)))(newline)

;; conjunct 2 lives under another AND
(di)
(display "after di2 focus=")(write (bd--goalof (bd--cur)))(newline)
;; injective
(lam-b)
(display "after lam-b focus=")(write (bd--goalof (bd--cur)))(newline)
(di-until-atomic!)
(display "inj atomic goal=")(write (bd--goalof (bd--cur)))(newline)
(ass)
(display "after inj, focus goal=")(write (bd--goalof (bd--cur)))(newline)

;; surjective
(lam-b)
(display "surj after lam-b=")(write (bd--goalof (bd--cur)))(newline)
(di)
(display "surj after di=")(write (bd--goalof (bd--cur)))(newline)
(let ((wit (id--elt id--carrier)))
  (display "witness=")(write wit)(newline)
  (ew wit))
(display "surj after ew=")(write (bd--goalof (bd--cur)))(newline)
(di-until-atomic!)
(display "surj split, leaves:")(newline)
(for-each (lambda (s)(display "  ")(write (bd--goalof s))(newline)) (bd--leaves))
;; close: IN w X by ass, w=w by rfl
(bd--close!)
(let loop ((fuel 4))
  (when (and (> fuel 0) (not (proof-done? *ps*)))
    (let ((s (bd--any (lambda (s) (let ((g (bd--goalof s))) (and (pair? g)(eq?(car g)'=)))) (bd--leaves))))
      (when s (set-proof-state-focus! *ps* s) (rfl)))
    (loop (- fuel 1))))
(display "DONE? ")(display (proof-done? *ps*))(newline)
