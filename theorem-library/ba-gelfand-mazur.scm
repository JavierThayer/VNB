;;; ba-gelfand-mazur.scm -- wave of 2026-11-09/10 (agent BA-1B), wired 2026-11-10 from scratchpad/ba1b-1109/ba-gelfand-mazur.scm.
;;; Library: operator-algebras.

;;; ba-gelfand-mazur.scm -- BANACH ALGEBRAS: Theorem 1.10 (Gelfand-Mazur) from Proposition 1.9.
;;; F. J. Thayer, "Banach Algebras and Applications", ch. 1 s. 1.
;;; Agent BA-1B, wave 2026-11-09.  Destination: theorem-library/ba-gelfand-mazur.scm.
;;; Library: operator-algebras.  All proofs modulo 0.
;;;
;;; THE STATEMENT.  Hypothesis of 1.10 as the brief fixes it: every nonzero element is invertible.
;;; Then (gelfand-mazur-spectrum-point) a point z of sigma(x) gives x = z 1, since z 1 - x is not
;;; invertible, hence zero; z |-> z 1 is injective (scalar-embedding-injective).  1.10 itself
;;; (gelfand-mazur-from-nonempty-spectrum) is stated with 1.9 -- every sigma(x) is nonempty -- as an
;;; antecedent, because 1.9 is not proven here (see BA-1B-REPORT.md, finding on 1.9): once 1.9 is
;;; a theorem, 1.10 is one detachment.  Commutativity is not used (as in the source's proof).
;;;
;;; LOAD WINDOW: after ba-spectrum (bas-spectrum-unfold, bas-shift-unfold, bas-shift-type,
;;; bas-act-sub), ba-neumann (ban-sub-sub).  Helper prefix: bgm-.

(define (bgm-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'algebra))
      (begin
        (display "\n*** ba-gelfand-mazur: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "ba-gelfand-mazur: unfinished" name))))

(define (bgm-st body) (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-BANACH-ALGEBRA a) body))))
(define (bgm-ad x y) (list '(VADD a) x y))
(define (bgm-ng x) (list '(VNEG a) x))
(define (bgm-sb x y) (bgm-ad x (bgm-ng y)))
(define (bgm-nr x) (list '(VNRM a) x))
(define (bgm-ac z x) (list '(ACT a) z x))
(define bgm-one '(VONE a))
(define bgm-zero '(VZERO a))
(define (bgm-rw! from to) (subst (list '= from to)))
(define (bgm-pin!) (dk-cite! 'bal-uba-scal-pin 'a))
(define (bgm-cite2! . args)
  (let ((r (apply dk-cite! args)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (detach-with! r (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
        r)))
(define bgm-hyp '(FORALL y (IMPLIES (IN y (VEC a)) (IMPLIES (NOT (= y (VZERO a))) (IS-INVERTIBLE-EL a y)))))

(define (bgm-vt x)
  (let ((want (list 'IN x '(VEC a))))
    (cond ((dk-asm? want) x)
          ((equal? x bgm-one) (dk-cite! 'ring-one-in-uba-as-ring 'a) x)
          ((equal? x bgm-zero) (dk-cite! 'ring-zero-in-uba-as-ring 'a) x)
          ((and (pair? x) (equal? (car x) '(VADD a)))
           (bgm-vt (cadr x)) (bgm-vt (caddr x))
           (dk-cite! 'ring-add-closed-uba-as-ring 'a (cadr x) (caddr x)) x)
          ((and (pair? x) (equal? (car x) '(VNEG a)))
           (bgm-vt (cadr x))
           (dk-cite! 'ring-neg-in-carr-uba-as-ring 'a (cadr x)) x)
          ((and (pair? x) (equal? (car x) '(ACT a)))
           (bgm-vt (caddr x)) (dk-cite! 'bae-act-type 'a (cadr x) (caddr x)) x)
          ((and (pair? x) (eq? (car x) 'SHIFT-EL))
           (bgm-vt (cadddr x)) (dk-cite! 'bas-shift-type 'a (caddr x) (cadddr x)) x)
          (#t (error "bgm-vt: cannot type" (expression->string x))))))

;;; (IN z (SPECTRUM a x)) in context: land (IN z CC) and (NOT (IS-INVERTIBLE-EL a (SHIFT-EL a z x)))
(define (bgm-spec-open! z x)
  (let ((m0 (list 'IN z (list 'SPECTRUM 'a x))))
    (dk-cite! 'bas-spectrum-unfold 'a x)
    (let ((m1 (dk-rewrite-h! m0 (list 'SPECTRUM 'a x)
                (list 'SEP 'baz_ 'CC (list 'NOT (list 'IS-INVERTIBLE-EL 'a (list 'SHIFT-EL 'a 'baz_ x)))))))
      (dk-project! (list 'IN z 'CC) (lambda () (sep-me m1)))
      (dk-project! (list 'NOT (list 'IS-INVERTIBLE-EL 'a (list 'SHIFT-EL 'a z x))) (lambda () (sep-me m1))))))

;;; ---- a point of the spectrum makes x a scalar ---------------------------------------------------
(sp (bgm-st (list 'IMPLIES bgm-hyp '(FORALL x (IMPLIES (IN x (VEC a)) (FORALL z (IMPLIES (IN z (SPECTRUM a x))
  (= x ((ACT a) z (VONE a))))))))))
(dk-peel!)
(bgm-spec-open! 'z 'x)
(let* ((s (bgm-vt '(SHIFT-EL a z x)))
       (z1 (bgm-vt (bgm-ac 'z bgm-one)))
       (op (bgm-vt (bgm-sb z1 'x))))
  (dk-cite! 'bas-shift-unfold 'a 'z 'x)
  (dk-have! (list '= op s) (lambda () (subst (list '== s op)) (rfl)))
  (use-em (list '= s bgm-zero)
    (lambda ()
      (let* ((e0 (dk-cite! 'ban-sub-sub 'a z1 'x))                    ; z1 - (z1 - x) = x
             (e1 (dk-rewrite-h! e0 op s))
             (e2 (dk-rewrite-h! e1 s bgm-zero)))
        (dk-cite! 'ring-neg-zero-uba-as-ring 'a)
        (let ((e3 (dk-rewrite-h! e2 (bgm-ng bgm-zero) bgm-zero)))
          (dk-cite! 'ring-add-right-id-uba-as-ring 'a z1)
          (dk-rewrite-h! e3 (bgm-ad z1 bgm-zero) z1)                   ; z1 = x
          (bgm-rw! 'x z1)
          (rfl))))
    (lambda ()
      (dk-apply! bgm-hyp s)
      (ai (list 'NOT (list 'IS-INVERTIBLE-EL 'a s))))))
(bgm-qed! 'gelfand-mazur-spectrum-point)

;;; ---- z |-> z 1 is injective --------------------------------------------------------------------
(sp (bgm-st '(FORALL z (IMPLIES (IN z CC) (FORALL w (IMPLIES (IN w CC)
  (IMPLIES (= ((ACT a) z (VONE a)) ((ACT a) w (VONE a))) (= z w))))))))
(dk-peel!)
(let* ((c '(+ z (- w)))
       (z1 (bgm-vt (bgm-ac 'z bgm-one)))
       (w1 (bgm-vt (bgm-ac 'w bgm-one))))
  (dk-cite! 'cc-neg-closed 'w)
  (dk-have! (list 'IN c 'CC) (lambda () (bgm-cite2! 'cc-add-closed 'z '(- w)) (dk-ass!)))
  (let* ((c1 (bgm-vt (bgm-ac c bgm-one)))
         (n (bgm-nr c1)))
    (dk-cite! 'bae-vnrm-type 'a c1)
    (dk-cite! 'bas-act-sub 'a 'z 'w bgm-one)                             ; c 1 = z1 - w1
    (dk-cite! 'ring-add-right-inv-uba-as-ring 'a w1)
    (dk-have! (list '= c1 bgm-zero)
      (lambda ()
        (bgm-rw! c1 (bgm-sb z1 w1))
        (bgm-rw! z1 w1)
        (dk-ass!)))
    (bgm-pin!)
    (dk-cite! 'rb3-c-in-carr-uba-as-module 'a c)
    (dk-cite! 'bal-uba-vnrm-homog 'a c bgm-one)
    (dk-cite! 'bal-uba-vone-norm 'a)
    (dk-cite! 'cc-magnitude-closed c)
    (let ((dfn (dk-cite! 'bal-uba-vnrm-definite 'a c1)))
      (dk-have! (list '= n 0)
        (lambda () (keep (list '= c1 bgm-zero) (iff-for (list '= n 0))) (prop))))
    (let* ((mc (list 'magnitude c))
           (h1 (dk-rewrite-h! (list '= n (list '* mc (bgm-nr bgm-one))) (bgm-nr bgm-one) 1))
           (h2 (dk-rewrite-h! h1 n 0)))
      (dk-real! (list '* mc 1))
      (dk-have! (list '= (list '* mc 1) mc) (lambda () (crs)))
      (dk-rewrite-h! h2 (list '* mc 1) mc)
      (dk-have! (list '= mc 0) (lambda () (bgm-rw! mc 0) (rfl))))
    (mac-h 'cc-magnitude-zero-iff (list '= (list 'magnitude c) 0))
    (dk-have! (list '= 'z (list '+ c 'w)) (lambda () (crs)))
    (let* ((e1 (dk-rewrite-h! (list '= 'z (list '+ c 'w)) c 0)))
      (dk-have! '(= (+ 0 w) w) (lambda () (crs)))
      (dk-rewrite-h! e1 '(+ 0 w) 'w)
      (dk-ass!))))
(bgm-qed! 'scalar-embedding-injective)

;;; ---- Theorem 1.10, with Proposition 1.9 as the antecedent -----------------------------------------
(sp (bgm-st (list 'IMPLIES bgm-hyp
  '(IMPLIES (FORALL x (IMPLIES (IN x (VEC a)) (FORSOME z (IN z (SPECTRUM a x)))))
     (FORALL x (IMPLIES (IN x (VEC a)) (FORSOME z (AND (IN z CC) (= x ((ACT a) z (VONE a)))))))))))
(dk-peel!)
(let* ((ne (or (dk-ctx-form '(FORALL x (IMPLIES (IN x (VEC a)) (FORSOME z (IN z (SPECTRUM a x))))))
               (error "gelfand-mazur: the 1.9 antecedent did not land")))
       (x 'x)
       (z (dk-skolem! (dk-apply! ne x))))
  (bgm-spec-open! z x)
  (dk-cite! 'gelfand-mazur-spectrum-point 'a x z)
  (ew z)
  (dk-conj-close! (lambda () (dk-ass!))))
(bgm-qed! 'gelfand-mazur-from-nonempty-spectrum)

(display "\n;; BGM qed failures: ")  
