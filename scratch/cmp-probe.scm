;;; cmp-probe.scm -- bijection-compose, full.  bd-- helpers live.
(define (di-until-atomic!)
  (let loop ((fuel 10))
    (let ((g (bd--goalof (bd--cur))))
      (when (and (> fuel 0) (pair? g) (memq (car g) '(FORALL IMPLIES))) (di) (loop (- fuel 1))))))
(define (hyp-find pred) (let ((w (bd--any (lambda (w) (pred (wff-formula w))) (bd--asms (bd--cur))))) (and w (wff-formula w))))
(define (elt-in carrier) (let ((h (hyp-find (lambda (f) (and (pair? f)(eq?(car f)'IN)(equal?(caddr f) carrier)))))) (and h (cadr h))))

;; drive a ctx FORALL*/IMPLIES* hyp H FORWARD: inst each FORALL at the next val,
;; detach each IMPLIES (antecedent in ctx); return + leave the final consequent.
(define (forward-chain! H vals)
  (cond
    ((and (pair? H) (eq? (car H) 'FORALL))
     (inst H (car vals))
     (forward-chain! (bd--subst (caddr H) (cadr H) (car vals)) (cdr vals)))
    ((and (pair? H) (eq? (car H) 'IMPLIES))
     (bd--detach! H)
     (forward-chain! (caddr H) vals))
    (else H)))
;; the surjective theorem, freshly ta'd into ctx (FORALL.. whose conclusion is a FORSOME)
(define (find-surj-thm)
  (hyp-find (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                             (let ((c (bd--concl f))) (and (pair? c) (eq? (car c) 'FORSOME)))))))
;; bring surjectivity for f:dom->cod, witness wit; eliminate -> facts in ctx
(define (surj-elim! dom cod f wit)
  (ta 'bijection-surjective)
  (let* ((thm (find-surj-thm))
         (E (forward-chain! thm (list dom cod f wit))))
    (ai E)))

(sp (make-wff '(FORALL X (FORALL Y (FORALL Z (FORALL phi (FORALL psi
   (IMPLIES (AND (IN phi (BIJECTION X Y)) (IN psi (BIJECTION Y Z)))
            (IN (VNB-LAMBDA x_ (psi (phi x_))) (BIJECTION X Z))))))))))
(di-until-atomic!)
(bd--split-ands!)
(define g0 (bd--goalof (bd--cur)))
(define cX (cadr (caddr g0)))
(define cZ (caddr (caddr g0)))
(define phi-hyp (hyp-find (lambda (f) (and (pair? f)(eq?(car f)'IN)(pair?(caddr f))(eq?(car(caddr f))'BIJECTION)(equal?(cadr(caddr f)) cX)))))
(define psi-hyp (hyp-find (lambda (f) (and (pair? f)(eq?(car f)'IN)(pair?(caddr f))(eq?(car(caddr f))'BIJECTION)(equal?(caddr(caddr f)) cZ)))))
(define cphi (cadr phi-hyp))
(define cpsi (cadr psi-hyp))
(define cY (caddr (caddr phi-hyp)))

(mac 'bijection-membership-iff)
(di)

;; --- conjunct 1: typing  IN (lam x_ (psi (phi x_))) (FUN cX cZ) ---
(lam-t)
(di) (di)
(bc* 'fun-apply-type ((A cY))
   (bc* 'bijection-in-fun () (ass))
   (bc* 'fun-apply-type ((A cX)) (bc* 'bijection-in-fun () (ass)) (ass)))

;; --- conjunct 2: injective ---
(di)
(lam-b)
(di-until-atomic!)
(let* ((g (bd--goalof (bd--cur))) (ae (cadr g)) (be (caddr g))
       (pab (list '= (list cphi ae) (list cphi be))))
  (cut pab)
  (bd--focus-goal! pab)
  (bc* 'bijection-injective ((X cY) (Y cZ) (phi cpsi))
     (ass)
     (bc* 'fun-apply-type ((A cX)) (bc* 'bijection-in-fun () (ass)) (ass))
     (bc* 'fun-apply-type ((A cX)) (bc* 'bijection-in-fun () (ass)) (ass))
     (ass))
  (bd--focus-asm! pab)
  (bc* 'bijection-injective ((X cX) (Y cY) (phi cphi))
     (ass) (ass) (ass) (ass)))

;; --- conjunct 3: surjective ---
(lam-b)
(di)
(let ((we (elt-in cZ)))
  (surj-elim! cY cZ cpsi we)                 ; -> y0 in cY with (cpsi y0) = we
  (let* ((yh (hyp-find (lambda (f) (and (pair? f)(eq?(car f)'=)(pair?(cadr f))(equal?(car(cadr f)) cpsi)(equal?(caddr f) we)))))
         (y0 (cadr (cadr yh))))
    (surj-elim! cX cY cphi y0)                ; -> x0 in cX with (cphi x0) = y0
    (let ((x0 (elt-in cX)))
      (ew x0)
      (di)
      (ass)
      (subst (list '= (list cphi x0) y0))
      (ass))))
(display "DONE? ")(display (proof-done? *ps*))(newline)
