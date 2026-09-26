;;; rake-hb-gap.scm -- hb-gap (theorem-library/hahn-banach-proof.scm:24), the
;;; analytic core of the one-dimension Hahn-Banach step, PROVEN.
;;;
;;;   m a real NVS, s a submodule, f bounded linear on s, v in vec(m):
;;;   there is a scalar alpha with |f(y) + r.alpha| <= ||f||_s * ||y + r.v||
;;;   for every y in s and every real r.
;;;
;;; WHAT IS PROVEN HERE, and in what order.
;;;
;;;  (1) two SCALING lemmas of RR (hbg-scale-pos / hbg-scale-neg).  They carry
;;;      the whole sign analysis: from -fu - bd*tt <= aa <= bd*tt - fu they give
;;;      |rho*fu + rho*aa| <= bd*(|rho|*tt), for rho of either sign.  Stated over
;;;      plain real VARIABLES on purpose: at the use site the arguments contain
;;;      `recip', which `crs' declines, so every ring identity is discharged
;;;      HERE, where the terms are variables.
;;;
;;;  (2) the NVS laws this argument needs that nvs-act-laws.scm does not project:
;;;      the TRIANGLE inequality, HOMOGENEITY of the norm, distribution of the
;;;      action over vector addition, and commutativity of vadd.  Same recipe as
;;;      nvs-act-laws.scm section (2) -- unfold IS-NORMED-VECTOR-SPACE, pick the
;;;      law by the SHAPE of its core, instantiate.  Each comes in a
;;;      carr(scal(m))-guarded form and an RR-guarded companion (nvs-scal-carr).
;;;
;;;  (3) the vector algebra: (y + v) + (-1).v = y, the SHIFT identity
;;;      w + (-1).z = (w+v) + (-1).(z+v), and from it
;;;      ||w + (-1).z|| <= ||w+v|| + ||z+v||; and the rescaling
;;;      y + r.v = r.((1/r).y + v) for r /= 0.
;;;
;;;  (4) hbg-sep: for z, w in s,  -f(z) - c||z+v|| <= c||w+v|| - f(w).
;;;      (f(w)-f(z) = f(w + (-1).z), bounded by c||w + (-1).z||, and the shift.)
;;;
;;;  (5) hbg-core: if a scalar `a' lies between those two families, then
;;;      |f(y) + r*a| <= c||y + r.v|| for every y in s and r in RR.  Three cases:
;;;      r = 0 (nvs-act-zero), and r of either sign, both through u = (1/r).y --
;;;      f(y) = r f(u) by homogeneity and ||y + r.v|| = |r| ||u + v||, after
;;;      which (1) closes it.
;;;
;;;  (6) hb-gap-bound: the separating scalar EXISTS.  It is
;;;      sup { -f(z) - c||z+v|| : z in s }, which is inhabited (z = vzero) and
;;;      bounded above (hbg-sep at w = vzero); rr-sup-upper gives the lower
;;;      family, rr-sup-least the upper one, and hbg-core finishes.  The whole
;;;      statement is parameterised on an arbitrary bound c, NOT on
;;;      DUAL-NORM-ON: that keeps it `modulo 0'.
;;;
;;;  (7) hb-gap itself, the support's statement verbatim, = (6) at
;;;      c := DUAL-NORM-ON(m,s,f).
;;;
;;; TWO FINDINGS ABOUT THE STATEMENT.
;;;
;;;  * The hypothesis `NOT (IN v s)' is NEVER USED.  hb-gap holds for any
;;;    v in vec(m).  (hb-extend-construct genuinely needs it; hb-gap does not.)
;;;  * hb-gap needs "M = DUAL-NORM-ON(m,s,f) IS A BOUND on s", and until
;;;    2026-09-19 the library had no such fact: `dual-norm-on-le-bound' is the
;;;    OTHER direction (M <= every nonnegative bound), and `dual-norm-is-bound'
;;;    is the whole-space functional, with no ON-companion.  The gap is now
;;;    closed by `dual-norm-on-is-bound-nvs', the seventh corollary of the
;;;    DUAL-NORM-ON spec, added to theorem-library/rake-dual-norm-spec.scm at
;;;    this file's request.  Section (7) below cites it in one line.
;;;
;;; BILL.  Every theorem in this file, hb-gap included, is `modulo 0'.
;;;
;;; LOAD WINDOW: [theorem-library/rake-dual-norm-spec, theorem-library/
;;; hahn-banach-proof).  `lo' is forced by `dual-norm-on-nonneg-nvs' and
;;; `dual-norm-on-is-bound-nvs' (rake-dual-norm-spec, the latest citations);
;;; the next floor down is `nvs-act-laws' (nvs-act-collect, -zero, -one,
;;; -in-vec, -scale-assoc, -unital, nvs-scal-carr, nvs-scal-one,
;;; nvs-vadd-assoc), then rake-hb-leaves (rr-mul-le-right), op-typing
;;; (vnrm-real, nvs-vadd-in-vec), rr-abs-basics, subset-lemmas,
;;; binary-minus-laws, fun-apply-type-proof.  `hi' is hahn-banach-proof, the
;;; only citer of hb-gap.  The window is non-empty as of the 2026-09-19 batch-7
;;; reordering, which moved nvs-module-view, nvs-act-laws and the spec file
;;; above hahn-banach-proof.
;;;
;;; No LATE tactic is used (no `contra', no `prep', no `ineq-supply').
;;; Helper prefix: `r8d-'.  Probed on worker-02, 2026-09-19.

(define (r8d-ineq! . r8d-forms)
  (let ((r8d-asms (dk-asms)))
    (apply ineq
           (map (lambda (f)
                  (let loop ((l r8d-asms) (i 1))
                    (cond ((null? l) (error "r8d-ineq!: not in context" f))
                          ((equal? (car l) f) i)
                          (#t (loop (cdr l) (+ i 1))))))
                r8d-forms))))

(define (r8d-check! nm)
  (if (not (proof-done? *ps*))
      (error "rake-hb-gap: proof did not close" nm (expression->string (dk-goal))))
  (qed nm)
  (topic! nm 'analysis))

(define r8d-nvs '(IS-NORMED-VECTOR-SPACE m))

(define (r8d-open! stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (mac-h 'is-normed-vector-space r8d-nvs)
  (dk-split-all!))

(define (r8d-law-core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL))  (r8d-law-core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES)) (r8d-law-core (caddr f)))
        (#t f)))

(define (r8d-project! nm stmt find vars)
  (r8d-open! stmt)
  (let ((law (dk-pick (lambda (f) (find (r8d-law-core f))) nm)))
    (apply dk-apply! law vars)
    (ass))
  (r8d-check! nm))

;;; ---------------------------------------------------------------
;;; hbg-scale-pos
;;; ---------------------------------------------------------------
(sp (make-wff
  '(FORALL bd (IMPLIES (IN bd RR)
   (FORALL tt (IMPLIES (IN tt RR)
   (FORALL fu (IMPLIES (IN fu RR)
   (FORALL aa (IMPLIES (IN aa RR)
   (FORALL rho (IMPLIES (IN rho RR)
    (IMPLIES (<= 0 rho)
    (IMPLIES (<= (- (- fu) (* bd tt)) aa)
    (IMPLIES (<= aa (- (* bd tt) fu))
      (<= (abs (+ (* rho fu) (* rho aa))) (* bd (* rho tt))))))))))))))))))
(dk-peel!)
(fact 'rr-mul-in-rr 'bd 'tt)
(fact 'rr-neg-closed 'fu)
(fact 'rr-sub-in-rr '(- fu) '(* bd tt))
(fact 'rr-sub-in-rr '(* bd tt) 'fu)
(fact 'rr-mul-in-rr 'aa 'rho)
(fact 'rr-mul-in-rr '(- (* bd tt) fu) 'rho)
(fact 'rr-mul-in-rr '(- (- fu) (* bd tt)) 'rho)
(fact 'rr-mul-in-rr 'rho 'fu)
(fact 'rr-mul-in-rr 'rho 'aa)
(fact 'rr-mul-in-rr 'rho 'tt)
(fact 'rr-mul-in-rr 'bd '(* rho tt))
(fact 'rr-add-in-rr '(* rho fu) '(* rho aa))
(fact 'rr-mul-le-right 'aa '(- (* bd tt) fu) 'rho)
(fact 'rr-mul-le-right '(- (- fu) (* bd tt)) 'aa 'rho)
(have! '(= (* aa rho) (* rho aa)) (lambda () (crs)))
(have! '(= (* (- (* bd tt) fu) rho) (- (* bd (* rho tt)) (* rho fu)))
       (lambda () (crs)))
(have! '(= (* (- (- fu) (* bd tt)) rho) (- (- (* rho fu)) (* bd (* rho tt))))
       (lambda () (crs)))
(fact 'rr-abs-bound '(+ (* rho fu) (* rho aa)) '(* bd (* rho tt)))
(have! '(AND (<= (- (* bd (* rho tt))) (+ (* rho fu) (* rho aa)))
             (<= (+ (* rho fu) (* rho aa)) (* bd (* rho tt))))
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (equal? (dk-goal) '(<= (+ (* rho fu) (* rho aa)) (* bd (* rho tt))))
           (r8d-ineq! '(<= (* aa rho) (* (- (* bd tt) fu) rho))
                      '(= (* aa rho) (* rho aa))
                      '(= (* (- (* bd tt) fu) rho) (- (* bd (* rho tt)) (* rho fu)))
                      '(IN (* aa rho) RR) '(IN (* rho aa) RR)
                      '(IN (* (- (* bd tt) fu) rho) RR)
                      '(IN (* bd (* rho tt)) RR) '(IN (* rho fu) RR))
           (r8d-ineq! '(<= (* (- (- fu) (* bd tt)) rho) (* aa rho))
                      '(= (* aa rho) (* rho aa))
                      '(= (* (- (- fu) (* bd tt)) rho) (- (- (* rho fu)) (* bd (* rho tt))))
                      '(IN (* aa rho) RR) '(IN (* rho aa) RR)
                      '(IN (* (- (- fu) (* bd tt)) rho) RR)
                      '(IN (* bd (* rho tt)) RR) '(IN (* rho fu) RR)))))))
(prop)
(r8d-check! 'hbg-scale-pos)

;;; ---------------------------------------------------------------
;;; hbg-scale-neg
;;; ---------------------------------------------------------------
(sp (make-wff
  '(FORALL bd (IMPLIES (IN bd RR)
   (FORALL tt (IMPLIES (IN tt RR)
   (FORALL fu (IMPLIES (IN fu RR)
   (FORALL aa (IMPLIES (IN aa RR)
   (FORALL rho (IMPLIES (IN rho RR)
    (IMPLIES (<= rho 0)
    (IMPLIES (<= (- (- fu) (* bd tt)) aa)
    (IMPLIES (<= aa (- (* bd tt) fu))
      (<= (abs (+ (* rho fu) (* rho aa))) (* bd (* (- rho) tt))))))))))))))))))
(dk-peel!)
(fact 'rr-neg-closed 'rho)
(fact 'rr-mul-in-rr 'bd 'tt)
(fact 'rr-neg-closed 'fu)
(fact 'rr-sub-in-rr '(- fu) '(* bd tt))
(fact 'rr-sub-in-rr '(* bd tt) 'fu)
(fact 'rr-mul-in-rr 'aa '(- rho))
(fact 'rr-mul-in-rr '(- (* bd tt) fu) '(- rho))
(fact 'rr-mul-in-rr '(- (- fu) (* bd tt)) '(- rho))
(fact 'rr-mul-in-rr 'rho 'fu)
(fact 'rr-mul-in-rr 'rho 'aa)
(fact 'rr-mul-in-rr '(- rho) 'tt)
(fact 'rr-mul-in-rr 'bd '(* (- rho) tt))
(fact 'rr-add-in-rr '(* rho fu) '(* rho aa))
(have! '(<= 0 (- rho))
       (lambda () (r8d-ineq! '(<= rho 0) '(IN rho RR) '(IN (- rho) RR))))
(fact 'rr-mul-le-right 'aa '(- (* bd tt) fu) '(- rho))
(fact 'rr-mul-le-right '(- (- fu) (* bd tt)) 'aa '(- rho))
(have! '(= (* aa (- rho)) (- (* rho aa))) (lambda () (crs)))
(have! '(= (* (- (* bd tt) fu) (- rho))
           (+ (* bd (* (- rho) tt)) (* rho fu)))
       (lambda () (crs)))
(have! '(= (* (- (- fu) (* bd tt)) (- rho))
           (- (* rho fu) (* bd (* (- rho) tt))))
       (lambda () (crs)))
(fact 'rr-abs-bound '(+ (* rho fu) (* rho aa)) '(* bd (* (- rho) tt)))
(have! '(AND (<= (- (* bd (* (- rho) tt))) (+ (* rho fu) (* rho aa)))
             (<= (+ (* rho fu) (* rho aa)) (* bd (* (- rho) tt))))
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (equal? (dk-goal) '(<= (+ (* rho fu) (* rho aa)) (* bd (* (- rho) tt))))
           (r8d-ineq! '(<= (* (- (- fu) (* bd tt)) (- rho)) (* aa (- rho)))
                      '(= (* aa (- rho)) (- (* rho aa)))
                      '(= (* (- (- fu) (* bd tt)) (- rho))
                          (- (* rho fu) (* bd (* (- rho) tt))))
                      '(IN (* aa (- rho)) RR) '(IN (* rho aa) RR)
                      '(IN (* (- (- fu) (* bd tt)) (- rho)) RR)
                      '(IN (* bd (* (- rho) tt)) RR) '(IN (* rho fu) RR))
           (r8d-ineq! '(<= (* aa (- rho)) (* (- (* bd tt) fu) (- rho)))
                      '(= (* aa (- rho)) (- (* rho aa)))
                      '(= (* (- (* bd tt) fu) (- rho))
                          (+ (* bd (* (- rho) tt)) (* rho fu)))
                      '(IN (* aa (- rho)) RR) '(IN (* rho aa) RR)
                      '(IN (* (- (* bd tt) fu) (- rho)) RR)
                      '(IN (* bd (* (- rho) tt)) RR) '(IN (* rho fu) RR)))))))
(prop)
(r8d-check! 'hbg-scale-neg)

;;; ---- ||x + y|| <= ||x|| + ||y|| ---------------------------------
(r8d-project! 'hbg-vnrm-triangle
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (<= ((VNRM m) ((VADD m) x_ y_))
           (+ ((VNRM m) x_) ((VNRM m) y_)))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '<=)
                   (pair? (cadr c)) (equal? (car (cadr c)) '(VNRM m))
                   (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(VADD m))))
  '(x_ y_))

;;; ---- ||r.x|| = |r| ||x||, scalar in CARR(SCAL m) ----------------
(r8d-project! 'hbg-vnrm-homog-c
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_)))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c)) (equal? (car (cadr c)) '(VNRM m))
                   (pair? (cadr (cadr c)))
                   (equal? (car (cadr (cadr c))) '(ACT m))))
  '(r_ x_))

;;; ---- r.(x + y) = r.x + r.y, scalar in CARR(SCAL m) --------------
(r8d-project! 'hbg-act-distrib-vec-c
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL m)))
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((ACT m) r_ ((VADD m) x_ y_))
          ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))))
  (lambda (c) (and (pair? c) (eq? (car c) '=)
                   (pair? (cadr c)) (equal? (car (cadr c)) '(ACT m))
                   (pair? (caddr (cadr c)))
                   (equal? (car (caddr (cadr c))) '(VADD m))))
  '(r_ x_ y_))

;;; ---- x + y = y + x ----------------------------------------------
(r8d-open!
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((VADD m) x_ y_) ((VADD m) y_ x_)))))))))
(let ((law (dk-landed-1
            (lambda () (mac-h 'is-commutative '(IS-COMMUTATIVE (VADD m) (VEC m)))))))
  (dk-apply! law 'x_ 'y_)
  (ass))
(r8d-check! 'hbg-vadd-comm)

;;; ---- the RR-guarded companions ----------------------------------
(define (r8d-scalar! r)
  (have! (list 'IN r '(CARR (SCAL m)))
         (lambda () (mac 'nvs-scal-carr) (ass))))

(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((VNRM m) ((ACT m) r_ x_)) (* (abs r_) ((VNRM m) x_)))))))))))
(dk-peel!)
(r8d-scalar! 'r_)
(fact 'hbg-vnrm-homog-c 'm 'r_ 'x_)
(ass)
(r8d-check! 'hbg-vnrm-homog)

(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL r_ (IMPLIES (IN r_ RR)
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
       (= ((ACT m) r_ ((VADD m) x_ y_))
          ((VADD m) ((ACT m) r_ x_) ((ACT m) r_ y_)))))))))))))
(dk-peel!)
(r8d-scalar! 'r_)
(fact 'hbg-act-distrib-vec-c 'm 'r_ 'x_ 'y_)
(ass)
(r8d-check! 'hbg-act-distrib-vec)

;;; ---- 1.x = x -----------------------------------------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL x_ (IMPLIES (IN x_ (VEC m))
       (= ((ACT m) 1 x_) x_)))))))
(dk-peel!)
(have! '(== (ONE (SCAL m)) 1) (lambda () (mac 'nvs-scal-one) (qrfl)))
(subst '(== 1 (ONE (SCAL m))))
(subst (dk-fact! 'nvs-act-unital 'm 'x_))
(rfl)
(r8d-check! 'hbg-act-one)

;;; ---- (y + v) + (-1).v = y ---------------------------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
       (= ((VADD m) ((VADD m) y_ v_) ((ACT m) (- 1) v_)) y_)))))))))
(dk-peel!)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(let ((e1 (dk-fact! 'nvs-act-one 'm 'v_ 'y_)))
  (fact 'eq-sym (cadr e1) (caddr e1))
  (subst (list '= (caddr e1) (cadr e1))))
(subst (dk-fact! 'nvs-act-collect 'm 1 '(- 1) 'v_ 'y_))
(have! '(= (+ 1 (- 1)) 0) (lambda () (crs)))
(subst '(= (+ 1 (- 1)) 0))
(fact 'nvs-act-zero 'm 'v_ 'y_)
(ass)
(r8d-check! 'hbg-neg-one-cancel)

;;; ---- w + (-1).z = (w + v) + (-1).(z + v) ------------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL w_ (IMPLIES (IN w_ (VEC m))
     (FORALL z_ (IMPLIES (IN z_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
       (= ((VADD m) w_ ((ACT m) (- 1) z_))
          ((VADD m) ((VADD m) w_ v_)
                    ((ACT m) (- 1) ((VADD m) z_ v_))))))))))))))
(dk-peel!)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(let* ((r8d-a '((ACT m) (- 1) z_))
       (r8d-b '((ACT m) (- 1) v_))
       (r8d-wv '((VADD m) w_ v_))
       (r8d-zv '((VADD m) z_ v_))
       (r8d-p  (list '(VADD m) 'w_ r8d-a)))
  (fact 'nvs-act-in-vec 'm '(- 1) 'z_)
  (fact 'nvs-act-in-vec 'm '(- 1) 'v_)
  (fact 'nvs-vadd-in-vec 'm 'w_ 'v_)
  (fact 'nvs-vadd-in-vec 'm 'z_ 'v_)
  (fact 'nvs-vadd-in-vec 'm 'w_ r8d-a)
  ;; (1) (-1).(z+v) -> (-1).z + (-1).v
  (subst (dk-fact! 'hbg-act-distrib-vec 'm '(- 1) 'z_ 'v_))
  ;; (2) (w+v) + (A + B) -> ((w+v) + A) + B
  (let ((l2 (dk-fact! 'nvs-vadd-assoc 'm r8d-wv r8d-a r8d-b)))
    (fact 'eq-sym (cadr l2) (caddr l2))
    (subst (list '= (caddr l2) (cadr l2))))
  ;; (3) (w+v) + A -> w + (v + A)
  (subst (dk-fact! 'nvs-vadd-assoc 'm 'w_ 'v_ r8d-a))
  ;; (4) v + A -> A + v
  (subst (dk-fact! 'hbg-vadd-comm 'm 'v_ r8d-a))
  ;; (5) w + (A + v) -> (w + A) + v
  (let ((l5 (dk-fact! 'nvs-vadd-assoc 'm 'w_ r8d-a 'v_)))
    (fact 'eq-sym (cadr l5) (caddr l5))
    (subst (list '= (caddr l5) (cadr l5))))
  ;; (6) (P + v) + (-1).v -> P
  (subst (dk-fact! 'hbg-neg-one-cancel 'm r8d-p 'v_))
  (rfl))
(r8d-check! 'hbg-shift)

;;; ---- ||w + (-1).z|| <= ||w + v|| + ||z + v|| --------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL w_ (IMPLIES (IN w_ (VEC m))
     (FORALL z_ (IMPLIES (IN z_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
       (<= ((VNRM m) ((VADD m) w_ ((ACT m) (- 1) z_)))
           (+ ((VNRM m) ((VADD m) w_ v_))
              ((VNRM m) ((VADD m) z_ v_))))))))))))))
(dk-peel!)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(let* ((r8d-wv '((VADD m) w_ v_))
       (r8d-zv '((VADD m) z_ v_))
       (r8d-nz (list '(ACT m) '(- 1) r8d-zv))
       (r8d-sum (list '(VADD m) r8d-wv r8d-nz)))
  (fact 'nvs-vadd-in-vec 'm 'w_ 'v_)
  (fact 'nvs-vadd-in-vec 'm 'z_ 'v_)
  (fact 'nvs-act-in-vec 'm '(- 1) r8d-zv)
  (fact 'nvs-vadd-in-vec 'm r8d-wv r8d-nz)
  (subst (dk-fact! 'hbg-shift 'm 'w_ 'z_ 'v_))
  (fact 'vnrm-real 'm r8d-wv)
  (fact 'vnrm-real 'm r8d-zv)
  (fact 'vnrm-real 'm r8d-nz)
  (fact 'vnrm-real 'm r8d-sum)
  (have! '(= (abs (- 1)) 1)
         (lambda ()
           (have! '(<= (- 1) 0) (lambda () (r8d-ineq! '(IN (- 1) RR))))
           (subst (dk-fact! 'rr-abs-of-nonpos '(- 1)))
           (crs)))
  (have! (list '= (list '(VNRM m) r8d-nz) (list '(VNRM m) r8d-zv))
         (lambda ()
           (subst (dk-fact! 'hbg-vnrm-homog 'm '(- 1) r8d-zv))
           (subst '(= (abs (- 1)) 1))
           (crs)))
  (fact 'hbg-vnrm-triangle 'm r8d-wv r8d-nz)
  (r8d-ineq! (list '<= (list '(VNRM m) r8d-sum)
                   (list '+ (list '(VNRM m) r8d-wv) (list '(VNRM m) r8d-nz)))
             (list '= (list '(VNRM m) r8d-nz) (list '(VNRM m) r8d-zv))
             (list 'IN (list '(VNRM m) r8d-sum) 'RR)
             (list 'IN (list '(VNRM m) r8d-wv) 'RR)
             (list 'IN (list '(VNRM m) r8d-zv) 'RR)
             (list 'IN (list '(VNRM m) r8d-nz) 'RR)))
(r8d-check! 'hbg-diff-norm)

;;; ---- r.((1/r).y) = y --------------------------------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
     (FORALL r_ (IMPLIES (IN r_ RR)
     (IMPLIES (NOT (= r_ 0))
       (= ((ACT m) r_ ((ACT m) (recip r_) y_)) y_))))))))))
(dk-peel!)
(have! '(AND (IN r_ RR) (NOT (= r_ 0))))
(fact 'rr-recip-closed 'r_)
(fact 'rr-recip-inverse 'r_)
(subst (dk-fact! 'nvs-act-scale-assoc 'm 'r_ '(recip r_) 'y_))
(subst '(= (* r_ (recip r_)) 1))
(fact 'hbg-act-one 'm 'y_)
(ass)
(r8d-check! 'hbg-scale-back)

;;; ---- y + r.v = r.((1/r).y + v) ----------------------------------
(sp (make-wff
  `(FORALL m (IMPLIES ,r8d-nvs
     (FORALL y_ (IMPLIES (IN y_ (VEC m))
     (FORALL v_ (IMPLIES (IN v_ (VEC m))
     (FORALL r_ (IMPLIES (IN r_ RR)
     (IMPLIES (NOT (= r_ 0))
       (= ((VADD m) y_ ((ACT m) r_ v_))
          ((ACT m) r_ ((VADD m) ((ACT m) (recip r_) y_) v_))))))))))))))
(dk-peel!)
(have! '(AND (IN r_ RR) (NOT (= r_ 0))))
(fact 'rr-recip-closed 'r_)
(fact 'nvs-act-in-vec 'm '(recip r_) 'y_)
(fact 'nvs-act-in-vec 'm 'r_ 'v_)
(fact 'nvs-vadd-in-vec 'm 'y_ '((ACT m) r_ v_))
(subst (dk-fact! 'hbg-act-distrib-vec 'm 'r_ '((ACT m) (recip r_) y_) 'v_))
(subst (dk-fact! 'hbg-scale-back 'm 'y_ 'r_))
(rfl)
(r8d-check! 'hbg-scale-decomp)

;;; ---- f(x) is a real ----------------------------------------------
(sp (make-wff
  '(FORALL m (FORALL s (FORALL f (FORALL x_
     (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m s f) (IMPLIES (IN x_ s)
        (IN (f x_) RR)))))))))
(dk-peel!)
(mac-h 'is-linear-functional-on
       (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the functional hypothesis"))
(dk-split-all!)
(fact 'fun-apply-type-c 'f 's 'RR 'x_)
(ass)
(r8d-check! 'hbg-linfun-app-real)

;;; =================================================================
;;; hbg-sep -- the separation inequality
;;; =================================================================
(define (r8d-eigen! vars)
  (let ((fv (free-vars (dk-goal))))
    (for-each (lambda (v)
                (if (not (memq v fv))
                    (error "rake-hb-gap: eigenvariable not in goal" v
                           (expression->string (dk-goal)))))
              vars)))

(define (r8d-bound-hyp)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (let ((c (r8d-law-core f)))
                    (and (pair? c) (eq? (car c) '<=)
                         (pair? (cadr c)) (eq? (car (cadr c)) 'abs)))))
           "the boundedness hypothesis"))

(sp (make-wff
  '(FORALL m (FORALL s (FORALL f (FORALL v (FORALL c
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IS-SUBMODULE m s)
     (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m s f)
     (IMPLIES (IN v (VEC m))
     (IMPLIES (IN c RR)
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ s)
                (<= (abs (f x_)) (* c ((VNRM m) x_)))))
     (IMPLIES (<= 0 c)
       (FORALL z_ (IMPLIES (IN z_ s)
       (FORALL w_ (IMPLIES (IN w_ s)
         (<= (- (- (f z_)) (* c ((VNRM m) ((VADD m) z_ v))))
             (- (* c ((VNRM m) ((VADD m) w_ v))) (f w_)))))))))))))))))))))
(dk-peel!)
(r8d-eigen! '(z_ w_))
(let* ((r8d-nz '((ACT m) (- 1) z_))
       (r8d-d  (list '(VADD m) 'w_ r8d-nz))
       (r8d-n1 '((VNRM m) ((VADD m) w_ v)))
       (r8d-n2 '((VNRM m) ((VADD m) z_ v)))
       (r8d-nd (list '(VNRM m) r8d-d))
       (r8d-fd (list 'f r8d-d)))
  (fact 'rr-one-in)
  (fact 'rr-neg-closed 1)
  (fact 'submodule-subset 'm 's)
  (fact 'subset-mem-fwd 's '(VEC m) 'z_)
  (fact 'subset-mem-fwd 's '(VEC m) 'w_)
  (r8d-scalar! '(- 1))
  (fact 'submodule-act-closed 'm 's '(- 1) 'z_)
  (fact 'submodule-vadd-closed 'm 's 'w_ r8d-nz)
  (fact 'subset-mem-fwd 's '(VEC m) r8d-d)
  (fact 'nvs-vadd-in-vec 'm 'w_ 'v)
  (fact 'nvs-vadd-in-vec 'm 'z_ 'v)
  ;; typings of the reals in play
  (fact 'hbg-linfun-app-real 'm 's 'f 'z_)
  (fact 'hbg-linfun-app-real 'm 's 'f 'w_)
  (fact 'hbg-linfun-app-real 'm 's 'f r8d-nz)
  (fact 'hbg-linfun-app-real 'm 's 'f r8d-d)
  (fact 'rr-abs-closed r8d-fd)
  (fact 'vnrm-real 'm '((VADD m) w_ v))
  (fact 'vnrm-real 'm '((VADD m) z_ v))
  (fact 'vnrm-real 'm r8d-d)
  (fact 'rr-add-in-rr r8d-n1 r8d-n2)
  (fact 'rr-mul-in-rr 'c r8d-nd)
  (fact 'rr-mul-in-rr r8d-nd 'c)
  (fact 'rr-mul-in-rr (list '+ r8d-n1 r8d-n2) 'c)
  (fact 'rr-mul-in-rr 'c r8d-n1)
  (fact 'rr-mul-in-rr 'c r8d-n2)
  (fact 'rr-mul-in-rr '(- 1) '(f z_))
  ;; |f(d)| <= c ||d||
  (dk-apply! (r8d-bound-hyp) r8d-d)
  ;; ||d|| <= ||w+v|| + ||z+v||, scaled by c
  (fact 'hbg-diff-norm 'm 'w_ 'z_ 'v)
  (fact 'rr-mul-le-right r8d-nd (list '+ r8d-n1 r8d-n2) 'c)
  (have! (list '= (list '* r8d-nd 'c) (list '* 'c r8d-nd)) (lambda () (crs)))
  (have! (list '= (list '* (list '+ r8d-n1 r8d-n2) 'c)
                  (list '+ (list '* 'c r8d-n1) (list '* 'c r8d-n2)))
         (lambda () (crs)))
  (fact 'rr-le-abs r8d-fd)
  ;; f(d) = f(w) + f((-1).z),  f((-1).z) = (-1) f(z)
  (mac-h 'is-linear-functional-on
         (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the functional hypothesis"))
  (dk-split-all!)
  (let ((r8d-add (dk-pick (lambda (fm)
                            (and (pair? fm) (eq? (car fm) 'FORALL)
                                 (let ((cc (r8d-law-core fm)))
                                   (and (pair? cc) (eq? (car cc) '=)
                                        (pair? (caddr cc)) (eq? (car (caddr cc)) '+)))))
                          "additivity"))
        (r8d-hom (dk-pick (lambda (fm)
                            (and (pair? fm) (eq? (car fm) 'FORALL)
                                 (let ((cc (r8d-law-core fm)))
                                   (and (pair? cc) (eq? (car cc) '=)
                                        (pair? (caddr cc)) (eq? (car (caddr cc)) '*)))))
                          "homogeneity")))
    (dk-apply! r8d-add 'w_ r8d-nz)
    (dk-apply! r8d-hom '(- 1) 'z_))
  (r8d-ineq!
   (list '= r8d-fd (list '+ '(f w_) (list 'f r8d-nz)))
   (list '= (list 'f r8d-nz) (list '* '(- 1) '(f z_)))
   (list '<= r8d-fd (list 'abs r8d-fd))
   (list '<= (list 'abs r8d-fd) (list '* 'c r8d-nd))
   (list '<= (list '* r8d-nd 'c) (list '* (list '+ r8d-n1 r8d-n2) 'c))
   (list '= (list '* r8d-nd 'c) (list '* 'c r8d-nd))
   (list '= (list '* (list '+ r8d-n1 r8d-n2) 'c)
            (list '+ (list '* 'c r8d-n1) (list '* 'c r8d-n2)))
   (list 'IN r8d-fd 'RR)
   (list 'IN (list 'abs r8d-fd) 'RR)
   (list 'IN '(f w_) 'RR)
   (list 'IN '(f z_) 'RR)
   (list 'IN (list 'f r8d-nz) 'RR)
   (list 'IN '(* (- 1) (f z_)) 'RR)
   (list 'IN r8d-nd 'RR)
   (list 'IN r8d-n1 'RR)
   (list 'IN r8d-n2 'RR)
   (list 'IN (list '+ r8d-n1 r8d-n2) 'RR)
   (list 'IN (list '* 'c r8d-nd) 'RR)
   (list 'IN (list '* r8d-nd 'c) 'RR)
   (list 'IN (list '* (list '+ r8d-n1 r8d-n2) 'c) 'RR)
   (list 'IN (list '* 'c r8d-n1) 'RR)
   (list 'IN (list '* 'c r8d-n2) 'RR)))
(r8d-check! 'hbg-sep)

;;; =================================================================
;;; hbg-core -- the scalar `a' separates, so it bounds every y + r.v
;;; =================================================================
(sp (make-wff
  '(FORALL m (FORALL s (FORALL f (FORALL v (FORALL c (FORALL a
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IS-SUBMODULE m s)
     (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m s f)
     (IMPLIES (IN v (VEC m))
     (IMPLIES (IN c RR)
     (IMPLIES (IN a RR)
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ s)
                (<= (abs (f x_)) (* c ((VNRM m) x_)))))
     (IMPLIES (FORALL u_ (IMPLIES (IN u_ s)
                (<= (- (- (f u_)) (* c ((VNRM m) ((VADD m) u_ v)))) a)))
     (IMPLIES (FORALL u_ (IMPLIES (IN u_ s)
                (<= a (- (* c ((VNRM m) ((VADD m) u_ v))) (f u_)))))
       (FORALL y_ (IMPLIES (IN y_ s)
       (FORALL r_ (IMPLIES (IN r_ RR)
         (<= (abs (+ (f y_) (* r_ a)))
             (* c ((VNRM m) ((VADD m) y_ ((ACT m) r_ v))))))))))))))))))))))))))
(dk-peel!)
(r8d-eigen! '(y_ r_))
(fact 'submodule-subset 'm 's)
(fact 'subset-mem-fwd 's '(VEC m) 'y_)
(fact 'hbg-linfun-app-real 'm 's 'f 'y_)
(fact 'rr-zero-in)

;;; the two sup facts, picked by shape (the FORALL whose core's right/left side
;;; is the scalar `a' itself).
(define (r8d-sup-lower)
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (let ((cc (r8d-law-core fm)))
                    (and (pair? cc) (eq? (car cc) '<=) (eq? (caddr cc) 'a)))))
           "the lower-bound hypothesis"))

(define (r8d-sup-upper)
  (dk-pick (lambda (fm)
             (and (pair? fm) (eq? (car fm) 'FORALL)
                  (let ((cc (r8d-law-core fm)))
                    (and (pair? cc) (eq? (car cc) '<=) (eq? (cadr cc) 'a)))))
           "the upper-bound hypothesis"))

(use-em '(= r_ 0)
  ;; ---- r = 0: y + 0.v = y and the bound hypothesis closes it -------
  (lambda ()
    (subst '(= r_ 0))
    (subst (dk-fact! 'nvs-act-zero 'm 'v 'y_))
    (have! '(= (+ (f y_) (* 0 a)) (f y_)) (lambda () (crs)))
    (subst '(= (+ (f y_) (* 0 a)) (f y_)))
    (dk-apply! (r8d-bound-hyp) 'y_)
    (ass))
  ;; ---- r /= 0: rescale by u = (1/r).y ------------------------------
  (lambda ()
    (have! '(AND (IN r_ RR) (NOT (= r_ 0))))
    (fact 'rr-recip-closed 'r_)
    (let* ((r8d-u  '((ACT m) (recip r_) y_))
           (r8d-uv (list '(VADD m) r8d-u 'v))
           (r8d-tt (list '(VNRM m) r8d-uv))
           (r8d-fu (list 'f r8d-u)))
      (r8d-scalar! '(recip r_))
      (fact 'submodule-act-closed 'm 's '(recip r_) 'y_)
      (fact 'subset-mem-fwd 's '(VEC m) r8d-u)
      (fact 'nvs-vadd-in-vec 'm r8d-u 'v)
      (fact 'vnrm-real 'm r8d-uv)
      (fact 'hbg-linfun-app-real 'm 's 'f r8d-u)
      ;; the two sup facts at u, BEFORE the functional predicate is consumed
      (dk-apply! (r8d-sup-lower) r8d-u)
      (dk-apply! (r8d-sup-upper) r8d-u)
      ;; f(y) = r * f(u)
      (mac-h 'is-linear-functional-on
             (dk-pick (dk-head? 'IS-LINEAR-FUNCTIONAL-ON) "the functional hypothesis"))
      (dk-split-all!)
      (let ((r8d-hom (dk-pick (lambda (fm)
                                (and (pair? fm) (eq? (car fm) 'FORALL)
                                     (let ((cc (r8d-law-core fm)))
                                       (and (pair? cc) (eq? (car cc) '=)
                                            (pair? (caddr cc)) (eq? (car (caddr cc)) '*)))))
                              "homogeneity")))
        (have! (list '= (list '* 'r_ r8d-fu) '(f y_))
          (lambda ()
            (let ((h (dk-apply! r8d-hom 'r_ r8d-u)))
              (fact 'eq-sym (cadr h) (caddr h))
              (subst (list '= (caddr h) (cadr h)))
              (subst (dk-fact! 'hbg-scale-back 'm 'y_ 'r_))
              (rfl)))))
      (fact 'eq-sym (list '* 'r_ r8d-fu) '(f y_))
      (subst (list '= '(f y_) (list '* 'r_ r8d-fu)))
      (subst (dk-fact! 'hbg-scale-decomp 'm 'y_ 'v 'r_))
      (subst (dk-fact! 'hbg-vnrm-homog 'm 'r_ r8d-uv))
      ;; sign of r
      (have! '(AND (IN 0 RR) (IN r_ RR)))
      (fact 'rr-leq-total 0 'r_)
      (use-cases (list '(<= 0 r_) '(<= r_ 0))
        (lambda ()
          (fact 'rr-abs-of-nonneg 'r_)
          (subst '(= (abs r_) r_))
          (fact 'hbg-scale-pos 'c r8d-tt r8d-fu 'a 'r_)
          (ass))
        (lambda ()
          (fact 'rr-abs-of-nonpos 'r_)
          (subst '(= (abs r_) (- r_)))
          (fact 'hbg-scale-neg 'c r8d-tt r8d-fu 'a 'r_)
          (ass))))))
(r8d-check! 'hbg-core)

;;; =================================================================
;;; hb-gap-bound -- the analytic core: a separating scalar exists
;;; =================================================================
(sp (make-wff
  '(FORALL m (FORALL s (FORALL f (FORALL v (FORALL c
     (IMPLIES (IS-NORMED-VECTOR-SPACE m)
     (IMPLIES (IS-SUBMODULE m s)
     (IMPLIES (IS-LINEAR-FUNCTIONAL-ON m s f)
     (IMPLIES (IN v (VEC m))
     (IMPLIES (IN c RR)
     (IMPLIES (FORALL x_ (IMPLIES (IN x_ s)
                (<= (abs (f x_)) (* c ((VNRM m) x_)))))
     (IMPLIES (<= 0 c)
       (FORSOME a_ (AND (IN a_ RR)
         (FORALL y_ (IMPLIES (IN y_ s)
         (FORALL r_ (IMPLIES (IN r_ RR)
           (<= (abs (+ (f y_) (* r_ a_)))
               (* c ((VNRM m) ((VADD m) y_ ((ACT m) r_ v)))))))))))))))))))))))))
(dk-peel!)

(define r8d-set
  '(SEP w_ RR (FORSOME z_ (AND (IN z_ s)
     (= w_ (- (- (f z_)) (* c ((VNRM m) ((VADD m) z_ v)))))))))
(define r8d-sup (list 'SUP r8d-set))
(define r8d-z0 '(VZERO m))

(define (r8d-nrm u) (list '(VNRM m) (list '(VADD m) u 'v)))
(define (r8d-lo u)  (list '- (list '- (list 'f u)) (list '* 'c (r8d-nrm u))))
(define (r8d-hi u)  (list '- (list '* 'c (r8d-nrm u)) (list 'f u)))

(define (r8d-types! u)
  (fact 'subset-mem-fwd 's '(VEC m) u)
  (fact 'nvs-vadd-in-vec 'm u 'v)
  (fact 'vnrm-real 'm (list '(VADD m) u 'v))
  (fact 'hbg-linfun-app-real 'm 's 'f u)
  (fact 'rr-mul-in-rr 'c (r8d-nrm u))
  (fact 'rr-neg-closed (list 'f u))
  (fact 'rr-sub-in-rr (list '- (list 'f u)) (list '* 'c (r8d-nrm u)))
  (fact 'rr-sub-in-rr (list '* 'c (r8d-nrm u)) (list 'f u)))

;;; goal (IN (lo u) SET), for u already typed
(define (r8d-member! u)
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'FORSOME)
                  (begin (ew u)
                         (dk-conj-close!
                          (lambda ()
                            (if (eq? (car (dk-goal)) 'IN) (ass) (rfl)))))
                  (ass)))
            (dk-opened (lambda () (sep-mi)))))

;;; goal (<= xx (hi w)) with (IN xx SET) in context
(define (r8d-elt-le! xx w)
  (let ((mem (dk-pick (lambda (fm) (equal? fm (list 'IN xx r8d-set)))
                      "the SET membership")))
    (sep-me mem))
  (let* ((ex (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORSOME)
                                        (dk-contains? fm xx)))
                      "the SET condition"))
         (zz (dk-skolem! ex))
         (conj (list 'AND (list 'IN zz 's) (list '= xx (r8d-lo zz)))))
    (if (member conj (dk-asms)) (dk-split! conj))
    (r8d-types! zz)
    (fact 'hbg-sep 'm 's 'f 'v 'c zz w)
    (subst (list '= xx (r8d-lo zz)))
    (ass)))

;;; goal (RR-UPPER-BOUND SET (hi w)), for w already typed
(define (r8d-upper! w)
  (mac 'rr-upper-bound)
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'IN)
                  (ass)
                  (let ((xx (dk-di-var!)))
                    (r8d-elt-le! xx w))))
            (dk-opened (lambda () (di)))))

(fact 'submodule-subset 'm 's)
(fact 'submodule-vzero-in 'm 's)
(r8d-types! r8d-z0)

;;; SET is inhabited, bounded above, and a set of reals.
(have! (list 'FORSOME 'x (list 'IN 'x r8d-set))
       (lambda () (ew (r8d-lo r8d-z0)) (r8d-member! r8d-z0)))
(have! (list 'RR-BOUNDED-ABOVE r8d-set)
       (lambda () (mac 'rr-bounded-above)
                  (ew (r8d-hi r8d-z0))
                  (r8d-upper! r8d-z0)))
(have! (list 'SUBSET r8d-set 'RR)
       (lambda () (mac 'subset-def)
                  (let ((xx (dk-di-var!)))
                    (sep-me (list 'IN xx r8d-set))
                    (ass))))

(fact 'rr-sup-in r8d-set)
(fact 'rr-sup-upper r8d-set)
(fact 'rr-sup-least r8d-set)
(define r8d-ub-forall
  (dk-landed-1 (lambda () (mac-h 'rr-upper-bound
                                 (list 'RR-UPPER-BOUND r8d-set r8d-sup)))))
(dk-split! r8d-ub-forall)
(define r8d-ub
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (let ((cc (r8d-law-core fm)))
                               (and (pair? cc) (eq? (car cc) '<=)
                                    (equal? (caddr cc) r8d-sup)))))
           "SUP is an upper bound"))
(define r8d-least
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (let ((cc (r8d-law-core fm)))
                               (and (pair? cc) (eq? (car cc) '<=)
                                    (equal? (cadr cc) r8d-sup)))))
           "SUP is least"))

;;; the two sup facts, in the shape hbg-core wants
(have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ 's)
                               (list '<= (r8d-lo 'u_) r8d-sup)))
  (lambda ()
    (let ((uu (dk-di-var!)))
      (r8d-types! uu)
      (have! (list 'IN (r8d-lo uu) r8d-set) (lambda () (r8d-member! uu)))
      (dk-apply! r8d-ub (r8d-lo uu))
      (ass))))
(have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ 's)
                               (list '<= r8d-sup (r8d-hi 'u_))))
  (lambda ()
    (let ((uu (dk-di-var!)))
      (r8d-types! uu)
      (have! (list 'RR-UPPER-BOUND r8d-set (r8d-hi uu))
             (lambda () (r8d-upper! uu)))
      (dk-apply! r8d-least (r8d-hi uu))
      (ass))))

(ew r8d-sup)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IN)
       (ass)
       (begin (fact 'hbg-core 'm 's 'f 'v 'c r8d-sup) (ass)))))
(r8d-check! 'hb-gap-bound)

;;; =================================================================
;;; hb-gap -- theorem-library/hahn-banach-proof.scm:24, statement verbatim
;;; =================================================================
(sp `(FORALL m (FORALL s (FORALL f (FORALL v
     (IMPLIES ,(conjuncts->and '((IS-NORMED-VECTOR-SPACE m)
                                 (IS-SUBMODULE m s)
                                 (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f)
                                 (IN v (VEC m))
                                 (NOT (IN v s))))
       (FORSOME a_ (AND (IN a_ RR)
         (FORALL y_ (IMPLIES (IN y_ s)
           (FORALL r_ (IMPLIES (IN r_ RR)
             (<= (abs (+ (f y_) (* r_ a_)))
                 (* (DUAL-NORM-ON m s f)
                    ((VNRM m) ((VADD m) y_ ((ACT m) r_ v)))))))))))))))))
(dk-peel!)
(dk-split-all!)
(define r8d-mm '(DUAL-NORM-ON m s f))

;;; M is a nonnegative real, and M IS A BOUND on s.  Both are guarded
;;; corollaries of the DUAL-NORM-ON spec, PROVEN `modulo 0' in
;;; theorem-library/rake-dual-norm-spec.scm, which loads first.  Their curried
;;; antecedents are (IS-NORMED-VECTOR-SPACE m), (SUBSET s (VEC m)),
;;; (IS-BOUNDED-LINEAR-FUNCTIONAL-ON m s f); the second is what IS-SUBMODULE
;;; supplies, and it must be LANDED FIRST -- `fact' auto-detaches only what the
;;; context already holds, and would otherwise land the implication silently.
(fact 'submodule-subset 'm 's)
(dk-split! (dk-fact! 'dual-norm-on-nonneg-nvs 'm 's 'f))
(have! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ 's)
               (list '<= '(abs (f x_)) (list '* r8d-mm '((VNRM m) x_)))))
  (lambda ()
    (let ((xx (dk-di-var!)))
      (fact 'dual-norm-on-is-bound-nvs 'm 's 'f xx)
      (ass))))

;;; f is a linear functional on s.
(mac-h 'is-bounded-linear-functional-on
       (dk-pick (dk-head? 'IS-BOUNDED-LINEAR-FUNCTIONAL-ON) "the BLF-ON hypothesis"))
(dk-split-all!)
(fact 'hb-gap-bound 'm 's 'f 'v r8d-mm)
(ass)
(r8d-check! 'hb-gap)
