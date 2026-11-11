;;; cc-sums-ptwise.scm -- wave of 2026-11-09/10 (agent TH3-B2), wired 2026-11-10 from scratchpad/th3-1109/b2/tb2-sums.scm.
;;; Library: operator-algebras.

;;; ====================================================================
;;; tb2-sums.scm -- TH3-B2, 2026-11-09.  POINTWISE algebra of unordered sums in CC.
;;;
;;; Each law is stated with FUNCTION VARIABLES and a POINTWISE equation for the result
;;; family, so that no statement carries a lambda: a user names the family it has
;;; (a lambda over its index set), proves the pointwise equation by beta, and cites.
;;;   cc-sums-to-add-ptwise     h z = f z + g z             ==> sum h = r + s
;;;   cc-sums-to-scale-ptwise   h z = c * f z               ==> sum h = c r
;;;   cc-sums-to-cscale-ptwise  h z = c * conj(f z)         ==> sum h = c conj(r)
;;;   cc-sums-to-comb           h z = (c1 f1 z + c2 f2 z) + (c3 conj(f2 z) + c4 f3 z)
;;;                                                         ==> sum h = (c1 r1 + c2 r2) + (c3 conj r2 + c4 r3)
;;; From sums-to-add (any normed abelian group), cc-sums-to-scale and cc-sums-to-conjugate
;;; (BA-ONB3, sums-to-algebra.scm), transported by function extensionality.
;;;
;;; LOAD WINDOW: after BA-ONB3's sums-to-algebra (sums-to-add, cc-sums-to-scale,
;;; cc-sums-to-conjugate) and BA-ONB2's l2-families-vocab (CC-NAG and its read-offs
;;; cc-nag@carr, cc-nag@opr).  Library: analysis.
;;; ====================================================================

(define (tb2-open?) (not (sequent-node-grounded? (proof-state-focus *ps*))))
(define (tb2-and! . ps)
  (let ((f (let build ((l ps)) (if (null? (cdr l)) (car l) (list 'AND (car l) (build (cdr l)))))))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! dk-ass!))))
    f))
(define (tb2-cite! thm . args)
  (let loop ((r (apply dk-cite! thm args)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (if (dk-asm? (caddr r))
            (loop (caddr r))
            (loop (dk-landed-1 (lambda () (detach! r)))))
        r)))
(define (tb2-close!)
  (cond ((not (tb2-open?)) #t)
        ((dk-asm? (dk-goal)) (ass))
        ((dk-head-is? (dk-goal) '==) (qrfl))
        (#t (rfl))))
(define (tb2-ap! f a b x) (if (not (dk-asm? (list 'IN (list f x) b))) (fact 'fun-apply-type-c f a b x)))

;;; f in FUN(dd, cod) in context: land (IN dd SET), (= (DOM f) dd), (IN f (FUN (DOM f) cod))
(define (tb2-dom! f dd cod)
  (if (not (dk-asm? (list 'IN dd 'SET))) (fact 'fun-domain-in-set dd cod f))
  (if (not (dk-asm? (list '= (list 'DOM f) dd)))
      (begin
        (dk-project! (list 'IN f (list 'FUN dd)) 'fun-codomain-iff (list 'IN f (list 'FUN dd cod)))
        (tb2-and! (list 'IN f (list 'FUN dd)) (list 'IN dd 'SET))
        (fact 'dom-of-fun dd f)
        (let ((x (dk-ctx-form (list 'AND (list 'IN (list 'DOM f) 'SET) (list '= (list 'DOM f) dd)))))
          (if x (dk-split-all! (list x))))))
  (if (not (dk-asm? (list 'IN f (list 'FUN (list 'DOM f) cod))))
      (dk-have! (list 'IN f (list 'FUN (list 'DOM f) cod))
        (lambda () (subst (list '= (list 'DOM f) dd)) (ass)))))

;;; a CC term built from + * conjugate (and -), every atom typed in CC in context: type it
(define (tb2-cc! t)
  (cond ((dk-asm? (list 'IN t 'CC)) #t)
        ((and (pair? t) (memq (car t) '(+ *)) (= (length t) 3))
         (tb2-cc! (cadr t)) (tb2-cc! (caddr t))
         (tb2-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC))
         (fact (if (eq? (car t) '+) 'cc-add-closed 'cc-mul-closed) (cadr t) (caddr t)))
        ((and (pair? t) (eq? (car t) 'conjugate))
         (tb2-cc! (cadr t)) (fact 'cc-conjugate-closed (cadr t)))
        ((and (pair? t) (eq? (car t) '-) (= (length t) 2))
         (tb2-cc! (cadr t)) (fact 'cc-neg-closed (cadr t)))
        ((dk-asm? (list 'IN t 'RR)) (fact 'rr-subset-cc t))
        (#t (error "tb2-cc!: cannot type in CC" (expression->string t)))))

;;; the CC-NAG read-offs
(define (tb2-nag!)
  (if (not (dk-asm? '(IS-NORMED-AG CC-NAG))) (fact 'cc-nag-is-normed-ag))
  (if (not (dk-asm? '(== (CARR CC-NAG) CC))) (fact 'cc-nag@carr)))
(define (tb2-opr-eq) (dk-cite! 'cc-nag@opr))
;;; (IN x (CARR CC-NAG)) from (IN x CC) / a FUN typing into (CARR CC-NAG) from one into CC
(define (tb2-carr! form)          ; form mentions CC where CARR CC-NAG is wanted, given as the target
  (if (not (dk-asm? form))
      (dk-have! form (lambda () (subst '(= (CARR CC-NAG) CC)) (tb2-close!)))))

;;; the pointwise universal (FORALL z_ (IMPLIES (IN z_ dd) (= (h z_) BODY(z_))))
(define (tb2-pw dd h body-of)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dd) (list '= (list h 'z_) (body-of 'z_)))))

;;; the qed with a dump of the open leaves on failure
(define (tb2-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; tb2: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l) (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name)
  (topic! name 'analysis))

;;; ====================================================================
;;; cc-sums-to-add-ptwise
;;; ====================================================================
(sp (make-wff (forall-guarded '(dd f g h r s)
  (list '(IN f (FUN dd CC)) '(IN g (FUN dd CC)) '(IN h (FUN dd CC)) '(IN r CC) '(IN s CC)
        '(SUMS-TO CC-NAG f r) '(SUMS-TO CC-NAG g s)
        (tb2-pw 'dd 'h (lambda (z) (list '+ (list 'f z) (list 'g z)))))
  '(SUMS-TO CC-NAG h (+ r s)))))
(dk-peel!)
(tb2-nag!)
(tb2-dom! 'f 'dd 'CC)
(tb2-dom! 'g 'dd 'CC)
(tb2-carr! '(IN f (FUN (DOM f) (CARR CC-NAG))))
(dk-have! '(IN g (FUN (DOM f) (CARR CC-NAG)))
  (lambda () (subst '(= (CARR CC-NAG) CC)) (subst '(= (DOM f) dd)) (tb2-close!)))
(tb2-carr! '(IN r (CARR CC-NAG)))
(tb2-carr! '(IN s (CARR CC-NAG)))
(let* ((opr (tb2-opr-eq))
       (hyp (dk-ctx-form (tb2-pw 'dd 'h (lambda (z) (list '+ (list 'f z) (list 'g z))))))
       (sa (tb2-cite! 'sums-to-add 'CC-NAG 'f 'g 'r 's))
       (sa2 (dk-rewrite-h! sa '(DOM f) 'dd))
       (A (caddr sa2))
       (V (cadddr sa2)))
  (dk-fun-ext! A 'h 'dd 'CC
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((z (dk-di-var!)))
            (tb2-ap! 'f 'dd 'CC z)
            (tb2-ap! 'g 'dd 'CC z)
            (tb2-cc! (list '+ (list 'f z) (list 'g z)))
            (subst opr)
            (dk-lam-b!)
            (tb2-close!)))
        (lambda () (ass))))
    #f
    (lambda (z)
      (tb2-ap! 'f 'dd 'CC z)
      (tb2-ap! 'g 'dd 'CC z)
      (tb2-cc! (list '+ (list 'f z) (list 'g z)))
      (subst (dk-apply! hyp z))
      (subst opr)
      (dk-lam-b!)
      (tb2-close!)))
  (let ((sh (dk-rewrite-h! sa2 A 'h)))
    (dk-have! (list '= V '(+ r s))
      (lambda () (subst opr) (dk-lam-b!) (tb2-close!)))
    (subst (list '= '(+ r s) V))
    (tb2-close!)))
(tb2-done! 'cc-sums-to-add-ptwise)

;;; ====================================================================
;;; cc-sums-to-scale-ptwise
;;; ====================================================================
(sp (make-wff (forall-guarded '(dd c f h r)
  (list '(IN c CC) '(IN f (FUN dd CC)) '(IN h (FUN dd CC)) '(IN r CC)
        '(SUMS-TO CC-NAG f r)
        (tb2-pw 'dd 'h (lambda (z) (list '* 'c (list 'f z)))))
  '(SUMS-TO CC-NAG h (* c r)))))
(dk-peel!)
(tb2-dom! 'f 'dd 'CC)
(let* ((hyp (dk-ctx-form (tb2-pw 'dd 'h (lambda (z) (list '* 'c (list 'f z))))))
       (sc (tb2-cite! 'cc-sums-to-scale 'c 'f 'r))
       (sc2 (dk-rewrite-h! sc '(DOM f) 'dd))
       (A (caddr sc2)))
  (dk-fun-ext! A 'h 'dd 'CC
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((z (dk-di-var!)))
            (tb2-ap! 'f 'dd 'CC z)
            (tb2-cc! (list '* 'c (list 'f z)))
            (tb2-close!)))
        (lambda () (ass))))
    #f
    (lambda (z)
      (tb2-ap! 'f 'dd 'CC z)
      (tb2-cc! (list '* 'c (list 'f z)))
      (subst (dk-apply! hyp z))
      (dk-lam-b!)
      (tb2-close!)))
  (dk-rewrite-h! sc2 A 'h)
  (tb2-close!))
(tb2-done! 'cc-sums-to-scale-ptwise)

;;; ====================================================================
;;; cc-sums-to-cscale-ptwise
;;; ====================================================================
(sp (make-wff (forall-guarded '(dd c f h r)
  (list '(IN c CC) '(IN f (FUN dd CC)) '(IN h (FUN dd CC)) '(IN r CC)
        '(SUMS-TO CC-NAG f r)
        (tb2-pw 'dd 'h (lambda (z) (list '* 'c (list 'conjugate (list 'f z))))))
  '(SUMS-TO CC-NAG h (* c (conjugate r))))))
(dk-peel!)
(tb2-dom! 'f 'dd 'CC)
(let* ((hyp (dk-ctx-form (tb2-pw 'dd 'h (lambda (z) (list '* 'c (list 'conjugate (list 'f z)))))))
       (cj (tb2-cite! 'cc-sums-to-conjugate 'f 'r))
       (cj2 (dk-rewrite-h! cj '(DOM f) 'dd))
       (CJ (caddr cj2)))
  (dk-have! (list 'IN CJ '(FUN dd CC))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((z (dk-di-var!)))
            (tb2-ap! 'f 'dd 'CC z)
            (tb2-cc! (list 'conjugate (list 'f z)))
            (tb2-close!)))
        (lambda () (ass)))))
  (tb2-dom! CJ 'dd 'CC)
  (tb2-cc! '(conjugate r))
  (let* ((sc (tb2-cite! 'cc-sums-to-scale 'c CJ '(conjugate r)))
         (sc2 (dk-rewrite-h! sc (list 'DOM CJ) 'dd))
         (A (caddr sc2)))
    (dk-fun-ext! A 'h 'dd 'CC
      (lambda ()
        (dk-lam-type!
          (lambda ()
            (let ((z (dk-di-var!)))
              (tb2-ap! CJ 'dd 'CC z)
              (tb2-cc! (list '* 'c (list CJ z)))
              (tb2-close!)))
          (lambda () (ass))))
      #f
      (lambda (z)
        (tb2-ap! 'f 'dd 'CC z)
        (tb2-cc! (list '* 'c (list 'conjugate (list 'f z))))
        (subst (dk-apply! hyp z))
        (dk-lam-b!)
        (tb2-close!)))
    (dk-rewrite-h! sc2 A 'h)
    (tb2-close!)))
(tb2-done! 'cc-sums-to-cscale-ptwise)

;;; ====================================================================
;;; cc-sums-to-comb: the four-term combination the polarization needs
;;; ====================================================================
(define (tb2-comb-body z)
  (list '+ (list '+ (list '* 'c1 (list 'f1 z)) (list '* 'c2 (list 'f2 z)))
           (list '+ (list '* 'c3 (list 'conjugate (list 'f2 z))) (list '* 'c4 (list 'f3 z)))))
(sp (make-wff (forall-guarded '(dd f1 f2 f3 h r1 r2 r3 c1 c2 c3 c4)
  (list '(IN f1 (FUN dd CC)) '(IN f2 (FUN dd CC)) '(IN f3 (FUN dd CC)) '(IN h (FUN dd CC))
        '(IN r1 CC) '(IN r2 CC) '(IN r3 CC) '(IN c1 CC) '(IN c2 CC) '(IN c3 CC) '(IN c4 CC)
        '(SUMS-TO CC-NAG f1 r1) '(SUMS-TO CC-NAG f2 r2) '(SUMS-TO CC-NAG f3 r3)
        (tb2-pw 'dd 'h tb2-comb-body))
  '(SUMS-TO CC-NAG h (+ (+ (* c1 r1) (* c2 r2)) (+ (* c3 (conjugate r2)) (* c4 r3)))))))
(dk-peel!)
(fact 'fun-domain-in-set 'dd 'CC 'f1)
(define (tb2-lam body-of) (list 'VNB-LAMBDA 'tbz_ 'dd (body-of 'tbz_)))
;;; a family over dd given by BODY-OF, typed in FUN(dd, CC); TYPES! types the body at z
(define (tb2-fam! body-of types!)
  (let ((L (tb2-lam body-of)))
    (if (not (dk-asm? (list 'IN L '(FUN dd CC))))
        (dk-have! (list 'IN L '(FUN dd CC))
          (lambda ()
            (dk-lam-type!
              (lambda ()
                (let ((z (dk-di-var!)))
                  (types! z)
                  (tb2-cc! (body-of z))
                  (tb2-close!)))
              (lambda () (ass))))))
    L))
;;; the pointwise equation (L z) = BODY(z) for a family L = tb2-lam BODY, by beta
(define (tb2-fam-pw! L body-of types!)
  (let ((pw (tb2-pw 'dd L body-of)))
    (if (not (dk-asm? pw))
        (dk-have! pw
          (lambda ()
            (let ((z (dk-di-var!)))
              (types! z)
              (tb2-cc! (body-of z))
              (dk-lam-b!)
              (tb2-close!)))))
    pw))
(define (tb2-ty-all! z)
  (tb2-ap! 'f1 'dd 'CC z) (tb2-ap! 'f2 'dd 'CC z) (tb2-ap! 'f3 'dd 'CC z))
(let* ((b1 (lambda (z) (list '* 'c1 (list 'f1 z))))
       (b2 (lambda (z) (list '* 'c2 (list 'f2 z))))
       (b3 (lambda (z) (list '* 'c3 (list 'conjugate (list 'f2 z)))))
       (b4 (lambda (z) (list '* 'c4 (list 'f3 z))))
       (G1 (tb2-fam! b1 tb2-ty-all!))
       (G2 (tb2-fam! b2 tb2-ty-all!))
       (G3 (tb2-fam! b3 tb2-ty-all!))
       (G4 (tb2-fam! b4 tb2-ty-all!))
       (v1 '(* c1 r1)) (v2 '(* c2 r2)) (v3 '(* c3 (conjugate r2))) (v4 '(* c4 r3)))
  (for-each tb2-cc! (list v1 v2 v3 v4))
  (tb2-fam-pw! G1 b1 tb2-ty-all!)
  (tb2-fam-pw! G2 b2 tb2-ty-all!)
  (tb2-fam-pw! G3 b3 tb2-ty-all!)
  (tb2-fam-pw! G4 b4 tb2-ty-all!)
  (tb2-cite! 'cc-sums-to-scale-ptwise 'dd 'c1 'f1 G1 'r1)
  (tb2-cite! 'cc-sums-to-scale-ptwise 'dd 'c2 'f2 G2 'r2)
  (tb2-cite! 'cc-sums-to-cscale-ptwise 'dd 'c3 'f2 G3 'r2)
  (tb2-cite! 'cc-sums-to-scale-ptwise 'dd 'c4 'f3 G4 'r3)
  (let* ((a1b (lambda (z) (list '+ (b1 z) (b2 z))))
         (a2b (lambda (z) (list '+ (b3 z) (b4 z))))
         (A1 (tb2-fam! a1b tb2-ty-all!))
         (A2 (tb2-fam! a2b tb2-ty-all!)))
    ;; A1 z = G1 z + G2 z, A2 z = G3 z + G4 z
    (dk-have! (tb2-pw 'dd A1 (lambda (z) (list '+ (list G1 z) (list G2 z))))
      (lambda () (let ((z (dk-di-var!))) (tb2-ty-all! z) (tb2-cc! (a1b z)) (dk-lam-b!) (tb2-close!))))
    (dk-have! (tb2-pw 'dd A2 (lambda (z) (list '+ (list G3 z) (list G4 z))))
      (lambda () (let ((z (dk-di-var!))) (tb2-ty-all! z) (tb2-cc! (a2b z)) (dk-lam-b!) (tb2-close!))))
    (tb2-cite! 'cc-sums-to-add-ptwise 'dd G1 G2 A1 v1 v2)
    (tb2-cite! 'cc-sums-to-add-ptwise 'dd G3 G4 A2 v3 v4)
    (tb2-cc! (list '+ v1 v2))
    (tb2-cc! (list '+ v3 v4))
    ;; h z = A1 z + A2 z
    (let ((hyp (dk-ctx-form (tb2-pw 'dd 'h tb2-comb-body))))
      (dk-have! (tb2-pw 'dd 'h (lambda (z) (list '+ (list A1 z) (list A2 z))))
        (lambda ()
          (let ((z (dk-di-var!)))
            (tb2-ty-all! z)
            (tb2-cc! (tb2-comb-body z))
            (subst (dk-apply! hyp z))
            (dk-lam-b!)
            (tb2-close!)))))
    (tb2-cite! 'cc-sums-to-add-ptwise 'dd A1 A2 'h (list '+ v1 v2) (list '+ v3 v4))
    (tb2-close!)))
(tb2-done! 'cc-sums-to-comb)
