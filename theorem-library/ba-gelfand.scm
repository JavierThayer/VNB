;;; ba-gelfand.scm -- wave of 2026-11-09/10 (agent BA-1B), wired 2026-11-10 from scratchpad/ba1b-1109/ba-gelfand.scm.
;;; Library: operator-algebras.

;;; ba-gelfand.scm -- BANACH ALGEBRAS: the Gelfand transform is a homomorphism (Proposition 1.15,
;;; the pointwise calculation) and the values of G(x) lie in the spectrum (one half of 1.16).
;;; F. J. Thayer, "Banach Algebras and Applications", ch. 1 s. 1.
;;; Agent BA-1B, wave 2026-11-09.  Destination: theorem-library/ba-gelfand.scm.
;;; Library: operator-algebras.  All proofs modulo 0.
;;;
;;; G(x) = GELFAND-TRANSFORM(a)(x) is the function chi |-> chi(x) on CHARACTERS(a) (ba-vocab).  The
;;; laws are stated POINTWISE at a character: G(x y)(chi) = G(x)(chi) G(y)(chi), and so on, and
;;; |G(x)(chi)| <= ||x|| (the norm half of 1.15, from character-bounded).  Not stated: that G(x) is
;;; continuous on GELFAND-SPACE(a), i.e. that G maps into CCONT(GELFAND-SPACE(a)) (see the report).
;;; character-value-in-spectrum: chi(x) in sigma(x), i.e. the range of G(x) is contained in
;;; sigma(x); the reverse inclusion needs 1.11 (maximal ideals are kernels of characters).
;;;
;;; LOAD WINDOW: after ba-spectrum (bas-characters-unfold, character-bounded,
;;; character-nonzero-at-invertible, bas-spectrum-unfold, bas-shift-unfold, bas-shift-type).
;;; Helper prefix: bgt-.

(define (bgt-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'algebra))
      (begin
        (display "\n*** ba-gelfand: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "ba-gelfand: unfinished" name))))

(define (bgt-st body) (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-BANACH-ALGEBRA a) body))))
(define (bgt-m x y) (list '(VMUL a) x y))
(define (bgt-ad x y) (list '(VADD a) x y))
(define (bgt-ng x) (list '(VNEG a) x))
(define (bgt-sb x y) (bgt-ad x (bgt-ng y)))
(define (bgt-ac z x) (list '(ACT a) z x))
(define bgt-one '(VONE a))
(define bgt-zero '(VZERO a))
(define (bgt-g x c) (list (list '(GELFAND-TRANSFORM a) x) c))
(define (bgt-rw! from to) (subst (list '= from to)))

(define (bgt-vt x)
  (let ((want (list 'IN x '(VEC a))))
    (cond ((dk-asm? want) x)
          ((equal? x bgt-one) (dk-cite! 'ring-one-in-uba-as-ring 'a) x)
          ((equal? x bgt-zero) (dk-cite! 'ring-zero-in-uba-as-ring 'a) x)
          ((and (pair? x) (equal? (car x) '(VADD a)))
           (bgt-vt (cadr x)) (bgt-vt (caddr x))
           (dk-cite! 'ring-add-closed-uba-as-ring 'a (cadr x) (caddr x)) x)
          ((and (pair? x) (equal? (car x) '(VMUL a)))
           (bgt-vt (cadr x)) (bgt-vt (caddr x))
           (dk-cite! 'ring-carrier-closed-mul-uba-as-ring 'a (cadr x) (caddr x)) x)
          ((and (pair? x) (equal? (car x) '(VNEG a)))
           (bgt-vt (cadr x))
           (dk-cite! 'ring-neg-in-carr-uba-as-ring 'a (cadr x)) x)
          ((and (pair? x) (equal? (car x) '(ACT a)))
           (bgt-vt (caddr x)) (dk-cite! 'bae-act-type 'a (cadr x) (caddr x)) x)
          ((and (pair? x) (eq? (car x) 'SHIFT-EL))
           (bgt-vt (cadddr x)) (dk-cite! 'bas-shift-type 'a (caddr x) (cadddr x)) x)
          (#t (error "bgt-vt: cannot type" (expression->string x))))))
(define (bgt-cv! c v) (bgt-vt v) (dk-cite! 'fun-apply-type-c c '(VEC a) 'CC v) (list c v))

;;; (bgt-char-open! c) -- c in CHARACTERS(a) in context: land c in FUN(VEC a, CC), and return
;;; (additivity homogeneity multiplicativity c(1)=1), each as the context holds it
(define (bgt-char-open! c)
  (let* ((m0 (list 'IN c '(CHARACTERS a)))
         (body (caddr (dk-cite! 'bas-characters-unfold 'a)))
         (m1 (dk-rewrite-h! m0 '(CHARACTERS a) body))
         (sb (lambda (f) (subst-free 'bac_ c f)))
         (rest (sb (caddr (cadddr body)))))
    (dk-project! (list 'IN c '(FUN (VEC a) CC)) (lambda () (sep-me m1)))
    (dk-project! (list 'IS-CC-LINEAR-ON 'a c) (lambda () (sep-me m1)))
    (dk-project! (cadr rest) (lambda () (sep-me m1)))
    (dk-project! (caddr rest) (lambda () (sep-me m1)))
    (let* ((ld (caddr (dk-cite! 'IS-CC-LINEAR-ON 'a c)))
           (la (dk-project! (cadr (caddr ld)) 'IS-CC-LINEAR-ON (list 'IS-CC-LINEAR-ON 'a c)))
           (lm (dk-project! (caddr (caddr ld)) 'IS-CC-LINEAR-ON (list 'IS-CC-LINEAR-ON 'a c))))
      (list la lm (cadr rest) (caddr rest)))))

;;; ---- the value: G(x)(chi) = chi(x) --------------------------------------------------------------
(sp (bgt-st '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
  (= (((GELFAND-TRANSFORM a) x) c) (c x))))))))
(dk-peel!)
(bgt-char-open! 'c)
(bgt-cv! 'c 'x)
(mac 'GELFAND-TRANSFORM)
(if (not (dk-lam-b!)) (rfl))
(bgt-qed! 'gelfand-transform-value)

;;; ---- the homomorphism laws, pointwise at a character (Proposition 1.15) ------------------------------
(define (bgt-law! name stmt build!)
  (sp (bgt-st stmt))
  (dk-peel!)
  (let ((laws (bgt-char-open! 'c)))
    (build! laws))
  (bgt-qed! name))

(define (bgt-val! x)              ; land G(x)(c) = c(x) and c(x) in CC; rewrite the goal
  (bgt-cv! 'c x)
  (dk-cite! 'gelfand-transform-value 'a x 'c)
  (bgt-rw! (bgt-g x 'c) (list 'c x)))

(bgt-law! 'gelfand-transform-mul
  '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL y (IMPLIES (IN y (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
     (= (((GELFAND-TRANSFORM a) ((VMUL a) x y)) c) (* (((GELFAND-TRANSFORM a) x) c) (((GELFAND-TRANSFORM a) y) c)))))))))
  (lambda (laws)
    (bgt-val! (bgt-m 'x 'y)) (bgt-val! 'x) (bgt-val! 'y)
    (dk-apply! (caddr laws) 'x 'y)
    (dk-ass!)))

(bgt-law! 'gelfand-transform-add
  '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL y (IMPLIES (IN y (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
     (= (((GELFAND-TRANSFORM a) ((VADD a) x y)) c) (+ (((GELFAND-TRANSFORM a) x) c) (((GELFAND-TRANSFORM a) y) c)))))))))
  (lambda (laws)
    (bgt-val! (bgt-ad 'x 'y)) (bgt-val! 'x) (bgt-val! 'y)
    (dk-apply! (car laws) 'x 'y)
    (dk-ass!)))

(bgt-law! 'gelfand-transform-act
  '(FORALL z (IMPLIES (IN z CC) (FORALL x (IMPLIES (IN x (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
     (= (((GELFAND-TRANSFORM a) ((ACT a) z x)) c) (* z (((GELFAND-TRANSFORM a) x) c)))))))))
  (lambda (laws)
    (bgt-val! (bgt-ac 'z 'x)) (bgt-val! 'x)
    (dk-apply! (cadr laws) 'z 'x)
    (dk-ass!)))

(bgt-law! 'gelfand-transform-one
  '(FORALL c (IMPLIES (IN c (CHARACTERS a)) (= (((GELFAND-TRANSFORM a) (VONE a)) c) 1)))
  (lambda (laws)
    (bgt-val! bgt-one)
    (dk-ass!)))

;;; the norm half of 1.15: |G(x)(chi)| <= ||x||
(bgt-law! 'gelfand-transform-bounded
  '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
     (<= (magnitude (((GELFAND-TRANSFORM a) x) c)) ((VNRM a) x))))))
  (lambda (laws)
    (bgt-val! 'x)
    (dk-cite! 'character-bounded 'a 'c 'x)
    (dk-ass!)))

;;; ---- one half of 1.16: chi(x) is in the spectrum of x ------------------------------------------------
(sp (bgt-st '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL c (IMPLIES (IN c (CHARACTERS a))
  (IN (c x) (SPECTRUM a x))))))))
(dk-peel!)
(let* ((laws (bgt-char-open! 'c))
       (cx (list 'c 'x))
       (s (list 'SHIFT-EL 'a cx 'x))
       (z1 (bgt-ac cx bgt-one))
       (body '(SEP baz_ CC (NOT (IS-INVERTIBLE-EL a (SHIFT-EL a baz_ x))))))
  (bgt-cv! 'c 'x)
  (bgt-vt z1) (bgt-vt s)
  (dk-cite! 'bas-spectrum-unfold 'a 'x)
  (subst (list '== '(SPECTRUM a x) body))
  (in-sep!
    (lambda () (dk-ass!))
    (lambda ()
      (di)
      (dk-cite! 'character-nonzero-at-invertible 'a 'c s)
      ;; c(s) = 0:  c(s) + c(x) = c(s + x) = c(z1) = c(x) c(1) = c(x)
      (let* ((cs (list 'c s))
             (sx (bgt-vt (bgt-ad s 'x))))
        (dk-cite! 'bas-shift-unfold 'a cx 'x)
        (bgt-vt (bgt-ng 'x))
        (dk-cite! 'ring-add-assoc-uba-as-ring 'a z1 (bgt-ng 'x) 'x)
        (dk-cite! 'ring-add-left-inv-uba-as-ring 'a 'x)
        (dk-cite! 'ring-add-right-id-uba-as-ring 'a z1)
        (dk-have! (list '= sx z1)
          (lambda ()
            (subst (list '== s (bgt-sb z1 'x)))
            (bgt-rw! (bgt-ad (bgt-sb z1 'x) 'x) (bgt-ad z1 (bgt-ad (bgt-ng 'x) 'x)))
            (bgt-rw! (bgt-ad (bgt-ng 'x) 'x) bgt-zero)
            (bgt-rw! (bgt-ad z1 bgt-zero) z1)
            (rfl)))
        (bgt-cv! 'c s)
        (dk-apply! (car laws) s 'x)                        ; c(s + x) = c(s) + c(x)
        (dk-apply! (cadr laws) cx bgt-one)                 ; c(z1) = c(x) c(1)
        (bgt-cv! 'c bgt-one)
        (bgt-cv! 'c sx)
        (bgt-cv! 'c z1)
        (let* ((e0 (dk-have! (list '= (list '+ cs cx) (list '* cx 1))
                     (lambda ()
                       (bgt-rw! (list '+ cs cx) (list 'c sx))
                       (bgt-rw! sx z1)
                       (bgt-rw! (list 'c z1) (list '* cx (list 'c bgt-one)))
                       (bgt-rw! (list 'c bgt-one) 1)
                       (rfl))))
               (f0 (list '= cs (list '+ (list '+ cs cx) (list '- cx)))))
          (dk-have! f0 (lambda () (crs)))
          (let* ((f1 (dk-rewrite-h! f0 (list '+ cs cx) (list '* cx 1))))
            (dk-have! (list '= (list '+ (list '* cx 1) (list '- cx)) 0) (lambda () (crs)))
            (dk-rewrite-h! f1 (list '+ (list '* cx 1) (list '- cx)) 0)
            (ai (list 'NOT (list '= cs 0)))))))))
(bgt-qed! 'character-value-in-spectrum)

(display "\n;; BGT qed failures: ")  
