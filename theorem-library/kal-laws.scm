;;; kal-laws.scm -- wave of 2026-11-09/10 (agent KIT-ALG), wired 2026-11-10 from scratchpad/kitalg-1109/kal-laws.scm.
;;; Library: operator-algebras.

;;; kal-laws.scm -- the LAW SETS of the algebra normaliser dk-alg-norm! (kit-alg.scm): the laws of a
;;; complex normed algebra, a unital Banach algebra and a unital involutive Banach algebra, each
;;; stated by the template (dk-alg-law-statement ROLE PRED) and named PREFIX-ROLE with the prefixes
;;; kal-cna, kal-uba, kal-uiba.  Agent KIT-ALG, 2026-11-09/10.  Destination: theorem-library/kal-laws.scm.
;;; Library: operator-algebras.  All proofs modulo 0.  Helper prefix kal-.
;;;
;;; THE ROUTE.  (1) kal-cna: each law is one citation of the view companions the vocabulary already
;;; carries at CNA-AS-MODULE (module-*, hbs-*, rb3-c-* with the scalar pin) or of a ba-laws
;;; projection (bal-cna-*), put in the CC form of the template; four are derived (0x = 0, -x = (-1)x,
;;; 0y = 0, y0 = 0: idempotent elements of the additive group are 0) and the product's associativity
;;; is read off IS-ASSOCIATIVE.  (2) kal-uba: every kal-cna law transferred through the view
;;; UBA-AS-CBA (the bal-uba-transfer! device of ba-laws), plus the three unit laws.  (3) kal-uiba:
;;; every kal-uba law transferred through UIBA-AS-UBA (read-offs kal-uu-*), plus the involution's
;;; laws (projections, 0* = 0, 1* = 1).  The transfer is generic: no law is proved three times.
;;;
;;; LOAD WINDOW: after structure-library/ba-vocab and theorem-library/ba-laws (BA-1); the view
;;; companions rb3-c-*-cna-as-module come with ba-vocab (after rake-asm-b3).  Needs kit-alg.scm
;;; (for the statement template and the typing helper) in the driver-kit environment.
;;; DUPLICATES (proven-duplicate-audit, warn-only): kal-uu-* = bcs-uu-* (BA-1H) = bcp-ro-* (BA-2);
;;; kal-uiba-star-* = bcs-uiba-star-* = bcp-star-*; kal-cna-add-zero-* = bun-vadd-zero-* (BA-1C).

(define (kal-qed! name)
  (if (not (proof-done? *ps*))
      (for-each (lambda (l)
                  (if (and (not (sequent-node-grounded? l))
                           (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                      (begin (dk-focus! l) (rfl))))
                (dk-open-leaves)))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** kal-laws: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "kal-laws: unfinished" name))))
(define (kal-name prefix role) (symbol-append prefix '- role))
(define kal-S-cna (list 'a 'kal-cna '() #f))
(define (kal-vt! t) (dk--alg-vt! kal-S-cna t))
;;; close (= P Q) from (= Q P) in context: rewrite the side that does not contain the other
(define (kal-flip-close!)
  (let* ((g (dk-goal)) (p (cadr g)) (q (caddr g)))
    (cond ((dk-asm? g) (ass))
          (#t (kal-vt! p) (kal-vt! q)
              (if (dk--occurs? q p) (subst (list '= p q)) (subst (list '= q p)))
              (rfl)))))
(define (kal-close!) (if (not (dk-ass!)) (kal-flip-close!)))
(define (kal-pin!) (dk-cite! 'bal-cna-scal-pin 'a))
(define (kal-ad x y) (list '(VADD a) x y))
(define (kal-ac c x) (list '(ACT a) c x))
(define (kal-mu x y) (list '(VMUL a) x y))
(define kal-z '(VZERO a))
;;; with p typed and (= p (VADD p p)) in context, land (= p VZERO)
(define (kal-idem! p)
  (kal-vt! p)
  (dk-have! (list '= (kal-ad p p) p) (lambda () (subst (list '= (kal-ad p p) p)) (rfl)))
  (dk-cite! 'abelian-group-idempotent-is-id-module-vector-ag-cna-as-module 'a p))

;;; ---- (1) the complex normed algebra ------------------------------------------------------------
(define (kal-cna! role proof)
  (sp (make-wff (dk-alg-law-statement role 'IS-COMPLEX-NORMED-ALGEBRA)))
  (dk-peel!)
  (proof)
  (if (not (proof-done? *ps*)) (kal-close!))
  (kal-qed! (kal-name 'kal-cna role)))

(kal-cna! 'vadd-in (lambda () (dk-cite! 'module-vadd-type-cna-as-module 'a 'kax_ 'kay_)))
(kal-cna! 'vneg-in (lambda () (dk-cite! 'module-vneg-type-cna-as-module 'a 'kax_)))
(kal-cna! 'act-in (lambda () (kal-pin!) (dk-cite! 'rb3-c-act-in-cna-as-module 'a 'kar_ 'kax_)))
(kal-cna! 'vzero-in (lambda () (dk-cite! 'module-vzero-in-cna-as-module 'a)))
(kal-cna! 'vmul-in
  (lambda ()
    (let ((u 'kax_) (v 'kay_))
      (dk-cite! 'bal-cna-vmul-fun 'a)
      (dk-cite! 'pair-in-cartesian '(VEC a) '(VEC a) u v)
      (dk-cite! 'fun-apply-type-c '(VMUL a) '(CARTESIAN (VEC a) (VEC a)) '(VEC a) (list 'LIST u v))
      (dk-cite! 'apply-tupling-2 '(VMUL a) u v)
      (dk-rewrite-h! (list 'IN (list '(VMUL a) (list 'LIST u v)) '(VEC a)) (list '(VMUL a) (list 'LIST u v))
                     (kal-mu u v)))))
(kal-cna! 'add-assoc (lambda () (dk-cite! 'hbs-vadd-assoc-cna-as-module 'a 'kax_ 'kay_ 'kaz_)))
(kal-cna! 'add-comm (lambda () (dk-cite! 'hbs-vadd-comm-cna-as-module 'a 'kax_ 'kay_)))
(kal-cna! 'add-zero-l (lambda () (dk-cite! 'hbs-vzero-l-cna-as-module 'a 'kax_)))
(kal-cna! 'add-zero-r (lambda () (dk-cite! 'hbs-vzero-r-cna-as-module 'a 'kax_)))
(kal-cna! 'act-vadd (lambda () (kal-pin!) (dk-cite! 'rb3-c-act-vadd-cna-as-module 'a 'kar_ 'kax_ 'kay_)))
(kal-cna! 'act-add (lambda () (kal-pin!) (dk-cite! 'rb3-c-act-add-cna-as-module 'a 'kar_ 'kas_ 'kax_)))
(kal-cna! 'act-mul (lambda () (kal-pin!) (dk-cite! 'rb3-c-act-mul-cna-as-module 'a 'kar_ 'kas_ 'kax_)))
(kal-cna! 'act-one
  (lambda ()
    (kal-pin!)
    (dk-cite! 'rb3-c-one-eq-cna-as-module 'a)
    (dk-rewrite-h! (dk-cite! 'module-act-unital-cna-as-module 'a 'kax_) '(ONE (SCAL a)) 1)))
(kal-cna! 'act-zero                     ; 0x = 0x + 0x, so 0x = 0
  (lambda ()
    (let ((p (kal-ac 0 'kax_)))
      (kal-pin!)
      (dk-have! '(IN 0 CC) (lambda () (arith)))
      (dk-have! '(= (+ 0 0) 0) (lambda () (arith)))
      (dk-rewrite-h! (dk-cite! 'rb3-c-act-add-cna-as-module 'a 0 0 'kax_) '(+ 0 0) 0)
      (kal-idem! p))))
(kal-cna! 'act-vzero
  (lambda ()
    (kal-pin!)
    (dk-cite! 'rb3-c-in-carr-cna-as-module 'a 'kar_)
    (dk-cite! 'module-act-zero-vec-cna-as-module 'a 'kar_)))
(kal-cna! 'vneg-act                     ; x + (-1)x = (1 + -1)x = 0x = 0, so (-1)x = -x
  (lambda ()
    (let ((x 'kax_))
      (kal-pin!)
      (dk-have! '(IN 1 CC) (lambda () (arith)))
      (dk-have! '(IN -1 CC) (lambda () (arith)))
      (dk-have! '(= (+ 1 -1) 0) (lambda () (arith)))
      (let* ((e0 (dk-cite! 'rb3-c-act-add-cna-as-module 'a 1 -1 x))
             (e1 (dk-rewrite-h! e0 '(+ 1 -1) 0))
             (z0 (dk-cite! 'kal-cna-act-zero 'a x))
             (e2 (dk-rewrite-h! e1 (kal-ac 0 x) kal-z))
             (o1 (dk-cite! 'kal-cna-act-one 'a x))
             (e3 (dk-rewrite-h! e2 (kal-ac 1 x) x))
             (s (kal-ad x (kal-ac -1 x))))
        (kal-vt! (kal-ac -1 x)) (kal-vt! s)
        (dk-have! (list '= s kal-z) (lambda () (subst (list '= s kal-z)) (kal-vt! kal-z) (rfl)))
        (dk-cite! 'abelian-group-inverse-unique-module-vector-ag-cna-as-module 'a x (kal-ac -1 x))))))
(kal-cna! 'mul-assoc
  (lambda ()
    (let* ((h (dk-cite! 'bal-cna-vmul-assoc 'a))
           (iff (dk-cite! 'IS-ASSOCIATIVE '(VMUL a) '(VEC a)))
           (univ (dk-project! (caddr iff) 'IS-ASSOCIATIVE h)))
      (dk-apply! univ 'kax_ 'kay_ 'kaz_))))
(kal-cna! 'mul-dist-l (lambda () (dk-cite! 'bal-cna-vmul-dist-left 'a 'kax_ 'kay_ 'kaz_)))
(kal-cna! 'mul-dist-r (lambda () (dk-cite! 'bal-cna-vmul-dist-right 'a 'kax_ 'kay_ 'kaz_)))
(kal-cna! 'mul-act-l
  (lambda () (kal-pin!) (dk-cite! 'rb3-c-in-carr-cna-as-module 'a 'kar_)
             (dk-cite! 'bal-cna-vmul-act-left 'a 'kar_ 'kax_ 'kay_)))
(kal-cna! 'mul-act-r
  (lambda () (kal-pin!) (dk-cite! 'rb3-c-in-carr-cna-as-module 'a 'kar_)
             (dk-cite! 'bal-cna-vmul-act-right 'a 'kar_ 'kax_ 'kay_)))
(kal-cna! 'mul-zero-l                   ; 0y = (0 + 0)y = 0y + 0y
  (lambda ()
    (let ((y 'kax_))
      (kal-vt! kal-z)
      (dk-cite! 'hbs-vzero-l-cna-as-module 'a kal-z)
      (dk-rewrite-h! (dk-cite! 'bal-cna-vmul-dist-right 'a kal-z kal-z y) (kal-ad kal-z kal-z) kal-z)
      (kal-idem! (kal-mu kal-z y)))))
(kal-cna! 'mul-zero-r
  (lambda ()
    (let ((y 'kax_))
      (kal-vt! kal-z)
      (dk-cite! 'hbs-vzero-l-cna-as-module 'a kal-z)
      (dk-rewrite-h! (dk-cite! 'bal-cna-vmul-dist-left 'a y kal-z kal-z) (kal-ad kal-z kal-z) kal-z)
      (kal-idem! (kal-mu y kal-z)))))

(define kal-cna-roles
  '(vadd-in vneg-in act-in vmul-in vzero-in add-assoc add-comm add-zero-l add-zero-r vneg-act act-vadd
    act-add act-mul act-one act-zero act-vzero mul-assoc mul-dist-l mul-dist-r mul-act-l mul-act-r
    mul-zero-l mul-zero-r))

;;; ---- the generic transfer: a law of PRED-FROM at VIEW(a), read back onto a by the read-offs ----
(define (kal-occurs? x t)
  (or (equal? x t) (and (pair? t) (or (kal-occurs? x (car t)) (kal-occurs? x (cdr t))))))
(define (kal-transfer! role from-prefix to-prefix pred view is-view-thm readoff accs)
  (let ((V (list view 'a)))
    (sp (make-wff (dk-alg-law-statement role pred)))
    (di) (di)
    (fact is-view-thm 'a)
    (if (eq? from-prefix 'kal-cna) (fact 'bal-cba-is-cna V))
    (fact (kal-name from-prefix role) V)
    (for-each (lambda (acc)
                (if (kal-occurs? (list acc 'a) (dk-goal))
                    (begin (fact (readoff acc) 'a)
                           (subst (list '= (list acc 'a) (list acc V))))))
              accs)
    (ass)
    (kal-qed! (kal-name to-prefix role))))

;;; ---- (2) the unital Banach algebra ---------------------------------------------------------------
(define (kal-ucba-name acc) (symbol-append 'bal-ucba- (string->symbol (string-downcase (symbol->string acc)))))
(for-each (lambda (role)
            (kal-transfer! role 'kal-cna 'kal-uba 'IS-UNITAL-BANACH-ALGEBRA 'UBA-AS-CBA
                           'uba-as-cba-is-complex-banach-algebra kal-ucba-name
                           '(VEC VADD VZERO VNEG ACT VMUL)))
          kal-cna-roles)
(define (kal-uba-own! role thm . args)
  (sp (make-wff (dk-alg-law-statement role 'IS-UNITAL-BANACH-ALGEBRA)))
  (dk-peel!)
  (apply dk-cite! thm 'a args)
  (dk-ass!)
  (kal-qed! (kal-name 'kal-uba role)))
(kal-uba-own! 'vone-in 'bal-uba-vone-in)
(kal-uba-own! 'mul-one-l 'bal-uba-vone-left 'kax_)
(kal-uba-own! 'mul-one-r 'bal-uba-vone-right 'kax_)
(define kal-uba-roles (append kal-cna-roles '(vone-in mul-one-l mul-one-r)))

;;; ---- (3) the unital involutive Banach algebra ----------------------------------------------------
(define kal-uu-accs '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL VONE))
(define (kal-uu-name acc) (symbol-append 'kal-uu- (string->symbol (string-downcase (symbol->string acc)))))
(for-each
  (lambda (acc)
    (sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a)
                    (list '== (list acc '(UIBA-AS-UBA a)) (list acc 'a))))))
    (dk-peel!)
    (mac 'UIBA-AS-UBA)
    (slot acc)
    (let loop ((n 0))
      (let ((g (dk-goal)))
        (quietly (lambda () (nth-r)))
        (if (and (< n 6) (not (proof-done? *ps*)) (not (equal? g (dk-goal)))) (loop (+ n 1)))))
    (if (not (proof-done? *ps*))
        (begin (quietly (lambda () (slot acc))) (qrfl)))
    (kal-qed! (kal-uu-name acc)))
  kal-uu-accs)
(for-each (lambda (role)
            (kal-transfer! role 'kal-uba 'kal-uiba 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA 'UIBA-AS-UBA
                           'uiba-as-uba-is-unital-banach-algebra kal-uu-name
                           '(VEC VADD VZERO VNEG ACT VMUL VONE)))
          kal-uba-roles)
;;; the involution: projections of IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA
(define (kal-uiba-project! name conj)
  (sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a) conj))))
  (di) (di)
  (let ((u (dk-landed-1 (lambda () (mac-h 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA '(IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA a))))))
    (dk-split-all! (list u)))
  (ass)
  (kal-qed! name))
(define (kal-law-body role)              ; the conjunct: the template without its a-prefix
  (caddr (caddr (dk-alg-law-statement role 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA))))
(kal-uiba-project! 'kal-uiba-vstar-fun '(IN (VSTAR a) (FUN (VEC a) (VEC a))))
(for-each (lambda (role) (kal-uiba-project! (kal-name 'kal-uiba role) (kal-law-body role)))
          '(star-vadd star-act star-star star-mul))
(define (kal-uiba-own! role proof)
  (sp (make-wff (dk-alg-law-statement role 'IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA)))
  (dk-peel!)
  (proof)
  (if (not (proof-done? *ps*)) (kal-close!))
  (kal-qed! (kal-name 'kal-uiba role)))
(kal-uiba-own! 'vstar-in
  (lambda () (dk-cite! 'kal-uiba-vstar-fun 'a)
             (dk-cite! 'fun-apply-type-c '(VSTAR a) '(VEC a) '(VEC a) 'kax_)))
(define kal-S-uiba (list 'a 'kal-uiba '() #f))
(define (kal-st x) (list '(VSTAR a) x))
(define kal-o '(VONE a))
(kal-uiba-own! 'star-zero               ; 0* = (0 0)* = conj(0) 0* = 0 0* = 0
  (lambda ()
    (let ((vt (lambda (t) (dk--alg-vt! kal-S-uiba t))))
      (vt kal-z) (vt (kal-st kal-z))
      (dk-have! '(IN 0 CC) (lambda () (arith)))
      (dk-have! '(IN 0 RR) (lambda () (arith)))
      (dk-cite! 'kal-uiba-act-zero 'a kal-z)
      (dk-cite! 'cc-conjugate-fixes-rr 0)
      (dk-cite! 'kal-uiba-act-zero 'a (kal-st kal-z))
      (let* ((e0 (dk-cite! 'kal-uiba-star-act 'a 0 kal-z))
             (e1 (dk-rewrite-h! e0 (kal-ac 0 kal-z) kal-z))
             (e2 (dk-rewrite-h! e1 '(conjugate 0) 0)))
        (dk-rewrite-h! e2 (kal-ac 0 (kal-st kal-z)) kal-z)))))
(kal-uiba-own! 'star-one                ; 1* = 1* 1, so 1 = (1* 1)* = 1* 1** = 1* 1 = 1*
  (lambda ()
    (let* ((vt (lambda (t) (dk--alg-vt! kal-S-uiba t)))
           (s1 (kal-st kal-o)))
      (vt kal-o) (vt s1)
      (dk-cite! 'kal-uiba-mul-one-r 'a s1)
      (dk-cite! 'kal-uiba-star-star 'a kal-o)
      (let* ((e0 (dk-cite! 'kal-uiba-star-mul 'a s1 kal-o))
             (e1 (dk-rewrite-h! e0 (kal-mu s1 kal-o) s1))
             (e2 (dk-rewrite-h! e1 (kal-st s1) kal-o)))
        (dk-rewrite-h! e2 (kal-mu s1 kal-o) s1)))))

(display "\n;; KAL qed failures: ")  
