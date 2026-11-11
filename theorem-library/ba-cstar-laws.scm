;;; ba-cstar-laws.scm -- wave of 2026-11-09/10 (agent BA-1H), wired 2026-11-10 from scratchpad/ba1h-1109/ba-cstar-laws.scm.
;;; Library: operator-algebras.

;;; ba-cstar-laws.scm -- C*-ALGEBRAS WITH UNIT: the projected laws, the view UIBA-AS-UBA and its
;;; read-offs, the involution at the unit, the bound |chi(x)| <= ||x|| for a character, and the
;;; real-variable lemma of Arens' argument (BanachAlgebras.pdf, 1.22, the first layer).
;;; Agent BA-1H, wave 2026-11-09.  Destination: theorem-library/ba-cstar-laws.scm.
;;; Library: operator-algebras (bcs-linear-bound-zero is general real analysis and may move to
;;; an analysis file).  All proofs modulo 0.
;;;
;;; THE ROUTE.  A unital involutive Banach algebra states its Banach-algebra laws as ONE law,
;;; IS-UNITAL-BANACH-ALGEBRA of the tuple of its first nine slots, which is UIBA-AS-UBA(a).  So
;;;   (1) the laws of IS-COMMUTATIVE-C-STAR-ALGEBRA, IS-UNITAL-C-STAR-ALGEBRA and
;;;       IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA are projected (bcs-ccsa-*, bcs-ucsa-*, bcs-uiba-*);
;;;   (2) the view is unfolded and shown to be a unital Banach algebra (bcs-uiba-is-uba), with its
;;;       nine read-offs ACC(UIBA-AS-UBA(a)) == ACC(a) (bcs-uu-*);
;;;   (3) every theorem about unital Banach algebras applies at UIBA-AS-UBA(a) and is read back
;;;       onto a (bcs-star-one, bcs-characters-view, bcs-character-bound are the first).
;;;
;;; LOAD WINDOW: after BA-1's ba-laws (bal-uba-vone-right) and BA-1B's ba-gelfand
;;; (gelfand-transform-bounded, gelfand-transform-value); after bas-characters-unfold (BA-1's
;;; ba-spectrum).  Kernel facts: fun-apply-type-c, rr-recip-inverse, rr-sq-nonneg, all early.
;;; Helper prefix: bcs-.

(define (bcs-close-owed!)
  (for-each (lambda (l)
              (if (and (not (sequent-node-grounded? l))
                       (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                  (begin (dk-focus! l) (rfl))))
            (dk-open-leaves)))
(define (bcs-qed! name)
  (if (not (proof-done? *ps*)) (bcs-close-owed!))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** ba-cstar-laws: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "ba-cstar-laws: unfinished" name))))
(define (bcs-occurs? x t)
  (or (equal? x t) (and (pair? t) (or (bcs-occurs? x (car t)) (bcs-occurs? x (cdr t))))))

;;; (bcs-project! NAME PRED MACETE CONJ) -- forall a. PRED(a) => CONJ, CONJ a conjunct of PRED's definition
(define (bcs-project! name pred mname conj)
  (sp (make-wff (list 'FORALL 'a (list 'IMPLIES (list pred 'a) conj))))
  (di)
  (di)
  (let ((u (dk-landed-1 (lambda () (mac-h mname (list pred 'a))))))
    (dk-split-all! (list u)))
  (ass)
  (bcs-qed! name))

;;; ---- (1) the projected laws ------------------------------------------------------------------
(bcs-project! 'bcs-ccsa-ucsa 'IS-COMMUTATIVE-C-STAR-ALGEBRA 'is-commutative-c-star-algebra-def
  '(IS-UNITAL-C-STAR-ALGEBRA a))
(bcs-project! 'bcs-ccsa-comm 'IS-COMMUTATIVE-C-STAR-ALGEBRA 'is-commutative-c-star-algebra-def
  '(FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
     (= ((VMUL a) x_ y_) ((VMUL a) y_ x_)))))))
(bcs-project! 'bcs-ucsa-uiba 'IS-UNITAL-C-STAR-ALGEBRA 'is-unital-c-star-algebra-def
  '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a))
(bcs-project! 'bcs-ucsa-cstar 'IS-UNITAL-C-STAR-ALGEBRA 'is-unital-c-star-algebra-def
  '(FORALL x_ (IMPLIES (IN x_ (VEC a))
     (= ((VNRM a) ((VMUL a) ((VSTAR a) x_) x_)) (* ((VNRM a) x_) ((VNRM a) x_))))))
(define bcs-tuple '(LIST (SCAL a) (VEC a) (VADD a) (VZERO a) (VNEG a) (ACT a) (VNRM a) (VMUL a) (VONE a)))
(define bcs-uiba-laws
  (list
    (list 'bcs-uiba-uba-tuple (list 'IS-UNITAL-BANACH-ALGEBRA bcs-tuple))
    '(bcs-uiba-scal-carr (= (CARR (SCAL a)) CC))
    '(bcs-uiba-vstar-fun (IN (VSTAR a) (FUN (VEC a) (VEC a))))
    '(bcs-uiba-star-add (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
       (= ((VSTAR a) ((VADD a) x_ y_)) ((VADD a) ((VSTAR a) x_) ((VSTAR a) y_))))))))
    '(bcs-uiba-star-act (FORALL r_ (IMPLIES (IN r_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC a))
       (= ((VSTAR a) ((ACT a) r_ x_)) ((ACT a) (conjugate r_) ((VSTAR a) x_))))))))
    '(bcs-uiba-star-invol (FORALL x_ (IMPLIES (IN x_ (VEC a)) (= ((VSTAR a) ((VSTAR a) x_)) x_))))
    '(bcs-uiba-star-mul (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
       (= ((VSTAR a) ((VMUL a) x_ y_)) ((VMUL a) ((VSTAR a) y_) ((VSTAR a) x_))))))))
    '(bcs-uiba-star-norm (FORALL x_ (IMPLIES (IN x_ (VEC a)) (= ((VNRM a) ((VSTAR a) x_)) ((VNRM a) x_)))))))
(for-each (lambda (e) (bcs-project! (car e) 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA (cadr e)))
          bcs-uiba-laws)

;;; ---- (2) the view UIBA-AS-UBA ----------------------------------------------------------------
(define bcs-V '(UIBA-AS-UBA a))
(sp (make-wff (list 'FORALL 'a (list '== bcs-V bcs-tuple))))
(di) (mac 'UIBA-AS-UBA) (qrfl)
(bcs-qed! 'bcs-uiba-view-unfold)

(sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a)
  (list 'IS-UNITAL-BANACH-ALGEBRA bcs-V)))))
(dk-peel!)
(dk-cite! 'bcs-uiba-uba-tuple 'a)
(dk-cite! 'bcs-uiba-view-unfold 'a)
(subst (list '= bcs-V bcs-tuple))
(dk-ass!)
(bcs-qed! 'bcs-uiba-is-uba)

(define bcs-uu-accs '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VONE))
(define (bcs-uu-name acc)
  (symbol-append 'bcs-uu- (string->symbol (string-downcase (symbol->string acc)))))
(define (bcs-readoff! name view pred acc)
  (sp (make-wff (list 'FORALL 'a (list 'IMPLIES (list pred 'a)
                  (list '== (list acc (list view 'a)) (list acc 'a))))))
  (dk-peel!)
  (mac view)
  (slot acc)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (quietly (lambda () (nth-r)))
      (if (and (< n 6) (not (equal? g (dk-goal)))) (loop (+ n 1)))))
  (if (not (proof-done? *ps*))
      (begin (quietly (lambda () (slot acc))) (qrfl)))
  (bcs-qed! name))
(for-each (lambda (acc) (bcs-readoff! (bcs-uu-name acc) 'UIBA-AS-UBA 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA acc))
          bcs-uu-accs)

;;; land every read-off ACC(V) == ACC(a) that occurs in F, and rewrite F onto a
(define (bcs-readback! f)
  (let loop ((accs bcs-uu-accs) (g f))
    (if (null? accs) g
        (let ((t (list (car accs) bcs-V)))
          (if (bcs-occurs? t g)
              (begin (dk-cite! (bcs-uu-name (car accs)) 'a)
                     (loop (cdr accs) (dk-rewrite-h! g t (list (car accs) 'a))))
              (loop (cdr accs) g))))))
;;; rewrite the GOAL from accessors of a onto the view (the read-offs, backwards)
(define (bcs-goal-onto-view!)
  (for-each (lambda (acc)
              (let ((t (list acc 'a)))
                (if (bcs-occurs? t (dk-goal))
                    (begin (dk-cite! (bcs-uu-name acc) 'a)
                           (subst (list '= t (list acc bcs-V)))))))
            bcs-uu-accs))

;;; ---- (3) the involution fixes the unit --------------------------------------------------------
(sp (make-wff '(FORALL a (IMPLIES (IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a) (= ((VSTAR a) (VONE a)) (VONE a))))))
(dk-peel!)
(let* ((o '(VONE a)) (s1 (list '(VSTAR a) o)))
  (dk-cite! 'bcs-uiba-is-uba 'a)
  (dk-cite! 'bal-uba-vone-in bcs-V)
  (let ((t1 (bcs-readback! (list 'IN (list 'VONE bcs-V) (list 'VEC bcs-V)))))
    (dk-cite! 'bcs-uiba-vstar-fun 'a)
    (dk-cite! 'fun-apply-type-c '(VSTAR a) '(VEC a) '(VEC a) o)
    (let* ((vr (dk-cite! 'bal-uba-vone-right bcs-V))
           (vr2 (bcs-readback! vr))
           (e3 (dk-apply! vr2 s1))
           (e1 (dk-cite! 'bcs-uiba-star-invol 'a o))
           (e2 (dk-cite! 'bcs-uiba-star-mul 'a s1 o))
           (e2b (dk-rewrite-h! e2 (list '(VMUL a) s1 o) s1))
           (e2c (dk-rewrite-h! e2b (list '(VSTAR a) s1) o))
           (e2d (dk-rewrite-h! e2c (list '(VMUL a) s1 o) s1)))
      (subst (list '= s1 o))
      (rfl))))
(bcs-qed! 'bcs-star-one)

;;; ---- (4) the characters of the view are the characters of a; |chi(x)| <= ||x|| ---------------
(sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a)
  (list '== (list 'CHARACTERS bcs-V) '(CHARACTERS a))))))
(dk-peel!)
(let ((u1 (dk-cite! 'bas-characters-unfold bcs-V)) (u2 (dk-cite! 'bas-characters-unfold 'a)))
  (subst (list '= (cadr u1) (caddr u1)))
  (subst (list '= (cadr u2) (caddr u2))))
(let loop ((n 0))
  (if (and (< n 4) (bcs-occurs? 'IS-CC-LINEAR-ON (dk-goal)))
      (begin (quietly (lambda () (mac 'IS-CC-LINEAR-ON))) (loop (+ n 1)))))
(for-each (lambda (acc)
            (let ((t (list acc bcs-V)))
              (if (bcs-occurs? t (dk-goal))
                  (begin (dk-cite! (bcs-uu-name acc) 'a)
                         (subst (list '= t (list acc 'a)))))))
          bcs-uu-accs)
(qrfl)
(bcs-qed! 'bcs-characters-view)

(sp (make-wff '(FORALL a (IMPLIES (IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a) (FORALL c (IMPLIES (IN c (CHARACTERS a))
  (FORALL x (IMPLIES (IN x (VEC a)) (<= (magnitude (c x)) ((VNRM a) x))))))))))
(dk-peel!)
(dk-cite! 'bcs-uiba-is-uba 'a)
(dk-cite! 'bcs-characters-view 'a)
(dk-cite! 'bcs-uu-vec 'a)
(let* ((cv (dk-rewrite-h! '(IN c (CHARACTERS a)) '(CHARACTERS a) (list 'CHARACTERS bcs-V)))
       (xv (dk-rewrite-h! '(IN x (VEC a)) '(VEC a) (list 'VEC bcs-V)))
       (b0 (dk-cite! 'gelfand-transform-bounded bcs-V 'x 'c))
       (v0 (dk-cite! 'gelfand-transform-value bcs-V 'x 'c))
       (b1 (dk-rewrite-h! b0 (cadr v0) (caddr v0))))
  (bcs-readback! b1)
  (dk-ass!))
(bcs-qed! 'bcs-character-bound)

;;; ---- (5) the real-variable lemma of 1.22: a^2 + (b + t)^2 <= c + t^2 for every real t forces b = 0
(define (bcs-cite2! . args)
  (let loop ((ch (apply dk-cite! args)))
    (if (dk-head-is? ch 'IMPLIES)
        (loop (detach-with! ch (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
        ch)))
(define (bcs-rr! t)
  (cond ((dk-asm? (list 'IN t 'RR)) t)
        ((equal? t 0) (dk-cite! 'rr-zero-in) t)
        ((equal? t 1) (dk-cite! 'rr-one-in) t)
        ((number? t) (dk-have! (list 'IN t 'RR) (lambda () (arith))) t)
        ((and (pair? t) (eq? (car t) '+) (= (length t) 3))
         (bcs-rr! (cadr t)) (bcs-rr! (caddr t)) (dk-cite! 'rr-add-in-rr (cadr t) (caddr t)) t)
        ((and (pair? t) (eq? (car t) '*) (= (length t) 3))
         (bcs-rr! (cadr t)) (bcs-rr! (caddr t)) (dk-cite! 'rr-mul-in-rr (cadr t) (caddr t)) t)
        (#t (error "bcs-rr!: cannot type" (expression->string t)))))
(sp (make-wff '(FORALL bal (IMPLIES (IN bal RR) (FORALL bbe (IMPLIES (IN bbe RR) (FORALL bcc (IMPLIES (IN bcc RR)
  (IMPLIES (FORALL bt (IMPLIES (IN bt RR) (<= (+ (* bal bal) (* (+ bbe bt) (+ bbe bt))) (+ bcc (* bt bt)))))
    (= bbe 0))))))))))
(dk-peel!)
(let ((hall (car (filter (lambda (h) (and (dk-head-is? h 'FORALL) (bcs-occurs? 'bcc h))) (dk-asms)))))
  (use-em '(= bbe 0)
    (lambda () (dk-ass!))
    (lambda ()
      (let ((k '(* 2 bbe)))
        (bcs-rr! k)
        (dk-have! (list 'NOT (list '= k 0))
          (lambda ()
            (di)
            (dk-have! '(= bbe 0) (lambda () (dk-ineq! (list '= k 0) '(IN bbe RR))))
            (ai '(NOT (= bbe 0)))))
        (bcs-cite2! 'rr-recip-closed k)
        (bcs-cite2! 'rr-recip-inverse k)
        (let* ((w (dk-name! (list 'recip k)))
               (kw (dk-rewrite-h! (list '= (list '* k (list 'recip k)) 1) (list 'recip k) w))
               (t0 (list '* '(+ bcc 1) w)))
          (bcs-rr! t0)
          (let* ((h0 (dk-apply! hall t0))
                 (iden (list '= (list '+ '(* bal bal) (list '* (list '+ 'bbe t0) (list '+ 'bbe t0)))
                             (list '+ (list '+ '(* bal bal) '(* bbe bbe)) (list '+ (list '* (list '* k w) '(+ bcc 1)) (list '* t0 t0))))))
            (dk-have! iden (lambda () (crs)))
            (let* ((h1 (dk-rewrite-h! h0 (cadr iden) (caddr iden)))
                   (h2 (dk-rewrite-h! h1 (list '* k w) 1)))
              (bcs-rr! '(* bal bal)) (bcs-rr! '(* bbe bbe)) (bcs-rr! (list '* t0 t0)) (bcs-rr! '(* 1 (+ bcc 1)))
              (dk-cite! 'rr-sq-nonneg 'bal)
              (dk-cite! 'rr-sq-nonneg 'bbe)
              (dk-cite! 'rr-one-mul '(+ bcc 1))
              (dk-absurd! h2 '(<= 0 (* bal bal)) '(<= 0 (* bbe bbe)) '(= (* 1 (+ bcc 1)) (+ bcc 1))
                          (list 'IN '(* bal bal) 'RR) (list 'IN '(* bbe bbe) 'RR) (list 'IN (list '* t0 t0) 'RR)
                          '(IN bcc RR) (list 'IN '(* 1 (+ bcc 1)) 'RR)))))))))
(bcs-qed! 'bcs-linear-bound-zero)

(display "\n;; BCS qed failures: ")  
