;;; ba-laws.scm -- wave of 2026-11-09/10 (agent BA-1), wired 2026-11-10 from scratchpad/ba1-1109/ba-laws.scm.
;;; Library: operator-algebras.

;;; ba-laws.scm -- BANACH ALGEBRAS: the projected laws of the structures of ba-vocab.scm, the
;;; read-offs of the views, and the elementary algebra of a unital Banach algebra.
;;; Agent BA-1, wave 2026-11-09.  Destination: theorem-library/ba-laws.scm.
;;; Library: operator-algebras.  All proofs modulo 0.
;;;
;;; THE ROUTE.  A unital algebra states its non-unital laws as ONE law, IS-COMPLEX-BANACH-ALGEBRA
;;; of the tuple of its first eight slots, which is UBA-AS-CBA(a).  So:
;;;   (1) the laws of IS-COMPLEX-NORMED-ALGEBRA are projected once (bal-cna-*);
;;;   (2) the view's eight read-offs ACC(UBA-AS-CBA(a)) == ACC(a) are proved (bal-ucba-*);
;;;   (3) a UBA law is the CNA law at UBA-AS-CBA(a) with the goal's accessors rewritten
;;;       onto the view (bal-uba-transfer!), so every CNA projection has a UBA twin (bal-uba-*).
;;;
;;; LOAD WINDOW: after structure-library/ba-vocab (and the kernel facts fun-apply-type-c,
;;; apply-tupling-2, pair-in-cartesian, all early).  Helper prefix: bal-.

;;; close the owed `t = t' leaves (the definedness of a literal tuple of accessors) by rfl
(define (bal-close-owed!)
  (for-each (lambda (l)
              (if (and (not (sequent-node-grounded? l))
                       (let ((g (dk-goal-of l))) (and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g)))))
                  (begin (dk-focus! l) (rfl))))
            (dk-open-leaves)))
(define (bal-qed! name)
  (if (not (proof-done? *ps*)) (bal-close-owed!))
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** ba-laws: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "ba-laws: unfinished" name))))

;;; (bal-project! NAME PRED MACETE CONJ) -- forall a. PRED(a) => CONJ, CONJ a conjunct of the
;;; definition of PRED at a.
(define (bal-project! name pred mname conj)
  (sp (make-wff (list 'FORALL 'a (list 'IMPLIES (list pred 'a) conj))))
  (di)
  (di)
  (let ((u (dk-landed-1 (lambda () (mac-h mname (list pred 'a))))))
    (dk-split-all! (list u)))
  (ass)
  (bal-qed! name))

;;; ---- (1) the laws of a complex normed algebra -----------------------------------------
(define bal-cna-laws
  '((bal-cna-scal-pin (= (SCAL a) (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD)))
    (bal-cna-scal-carr (= (CARR (SCAL a)) CC))
    (bal-cna-vec-set (IN (VEC a) SET))
    (bal-cna-vadd-fun (IN (VADD a) (FUN (CARTESIAN (VEC a) (VEC a)) (VEC a))))
    (bal-cna-vzero-in (IN (VZERO a) (VEC a)))
    (bal-cna-vneg-fun (IN (VNEG a) (FUN (VEC a) (VEC a))))
    (bal-cna-act-fun (IN (ACT a) (FUN (CARTESIAN (CARR (SCAL a)) (VEC a)) (VEC a))))
    (bal-cna-vnrm-fun (IN (VNRM a) (FUN (VEC a) RR)))
    (bal-cna-vmul-fun (IN (VMUL a) (FUN (CARTESIAN (VEC a) (VEC a)) (VEC a))))
    (bal-cna-vadd-assoc (IS-ASSOCIATIVE (VADD a) (VEC a)))
    (bal-cna-vadd-comm (IS-COMMUTATIVE (VADD a) (VEC a)))
    (bal-cna-vadd-ident (IS-IDENTITY (VADD a) (VZERO a) (VEC a)))
    (bal-cna-vadd-inv (HAS-INVERSES (VADD a) (VZERO a) (VNEG a) (VEC a)))
    (bal-cna-vmul-assoc (IS-ASSOCIATIVE (VMUL a) (VEC a)))
    (bal-cna-act-vadd
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
        (= ((ACT a) r_ ((VADD a) x_ y_)) ((VADD a) ((ACT a) r_ x_) ((ACT a) r_ y_))))))))))
    (bal-cna-act-add
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a))
        (= ((ACT a) ((ADD (SCAL a)) r_ s_) x_) ((VADD a) ((ACT a) r_ x_) ((ACT a) s_ x_))))))))))
    (bal-cna-act-mul
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL s_ (IMPLIES (IN s_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a))
        (= ((ACT a) ((MUL (SCAL a)) r_ s_) x_) ((ACT a) r_ ((ACT a) s_ x_))))))))))
    (bal-cna-act-one
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (= ((ACT a) (ONE (SCAL a)) x_) x_))))
    (bal-cna-vnrm-nonneg
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (<= 0 ((VNRM a) x_)))))
    (bal-cna-vnrm-definite
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (IFF (= ((VNRM a) x_) 0) (= x_ (VZERO a))))))
    (bal-cna-vnrm-homog
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a))
        (= ((VNRM a) ((ACT a) r_ x_)) (* (magnitude r_) ((VNRM a) x_))))))))
    (bal-cna-vnrm-triangle
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
        (<= ((VNRM a) ((VADD a) x_ y_)) (+ ((VNRM a) x_) ((VNRM a) y_))))))))
    (bal-cna-vmul-dist-left
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a)) (FORALL z_ (IMPLIES (IN z_ (VEC a))
        (= ((VMUL a) x_ ((VADD a) y_ z_)) ((VADD a) ((VMUL a) x_ y_) ((VMUL a) x_ z_))))))))))
    (bal-cna-vmul-dist-right
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a)) (FORALL z_ (IMPLIES (IN z_ (VEC a))
        (= ((VMUL a) ((VADD a) x_ y_) z_) ((VADD a) ((VMUL a) x_ z_) ((VMUL a) y_ z_))))))))))
    (bal-cna-vmul-act-left
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
        (= ((VMUL a) ((ACT a) r_ x_) y_) ((ACT a) r_ ((VMUL a) x_ y_))))))))))
    (bal-cna-vmul-act-right
      (FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
        (= ((VMUL a) x_ ((ACT a) r_ y_)) ((ACT a) r_ ((VMUL a) x_ y_))))))))))
    (bal-cna-vnrm-submult
      (FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
        (<= ((VNRM a) ((VMUL a) x_ y_)) (* ((VNRM a) x_) ((VNRM a) y_))))))))))

(for-each (lambda (e) (bal-project! (car e) 'IS-COMPLEX-NORMED-ALGEBRA 'IS-COMPLEX-NORMED-ALGEBRA (cadr e)))
          bal-cna-laws)

;;; a complex Banach algebra is a complex normed algebra, and is complete
(bal-project! 'bal-cba-is-cna 'IS-COMPLEX-BANACH-ALGEBRA 'is-complex-banach-algebra-def
  '(IS-COMPLEX-NORMED-ALGEBRA a))
(bal-project! 'bal-cba-complete 'IS-COMPLEX-BANACH-ALGEBRA 'is-complex-banach-algebra-def
  '(IS-COMPLETE (NAG-METRIC-SPACE (CNA-AS-NORMED-AG a))))

;;; ---- (2) the read-offs of the view UBA-AS-CBA ------------------------------------------
(define bal-ucba-accs '(SCAL VEC VADD VZERO VNEG ACT VNRM VMUL))
(define (bal-ucba-name acc)
  (symbol-append 'bal-ucba- (string->symbol (string-downcase (symbol->string acc)))))
(define (bal-readoff! name view pred acc)
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
  (bal-qed! name))
(for-each (lambda (acc) (bal-readoff! (bal-ucba-name acc) 'UBA-AS-CBA 'IS-UNITAL-BANACH-ALGEBRA acc))
          bal-ucba-accs)

;;; ---- (3) the transfer: a CNA law at UBA-AS-CBA(a), read back onto a ---------------------
(define (bal-occurs? x t)
  (or (equal? x t) (and (pair? t) (or (bal-occurs? x (car t)) (bal-occurs? x (cdr t))))))
(define bal-V '(UBA-AS-CBA a))
(define (bal-uba-transfer! name cna-thm conj)
  (sp (make-wff (list 'FORALL 'a (list 'IMPLIES '(IS-UNITAL-BANACH-ALGEBRA a) conj))))
  (di)
  (di)
  (fact 'uba-as-cba-is-complex-banach-algebra 'a)
  (fact 'bal-cba-is-cna bal-V)
  (fact cna-thm bal-V)
  (for-each (lambda (acc)
              (if (bal-occurs? (list acc 'a) (dk-goal))
                  (begin
                    (fact (bal-ucba-name acc) 'a)
                    (subst (list '= (list acc 'a) (list acc bal-V))))))
            bal-ucba-accs)
  (ass)
  (bal-qed! name))

(define (bal-uba-name cna-name)
  (let ((s (symbol->string cna-name)))
    (string->symbol (string-append "bal-uba-" (substring s 8 (string-length s))))))
(for-each (lambda (e) (bal-uba-transfer! (bal-uba-name (car e)) (car e) (cadr e)))
          bal-cna-laws)

;;; the UBA's own laws
(define bal-uba-own
  '((bal-uba-vone-in (IN (VONE a) (VEC a)))
    (bal-uba-vone-left (FORALL x_ (IMPLIES (IN x_ (VEC a)) (= ((VMUL a) (VONE a) x_) x_))))
    (bal-uba-vone-right (FORALL x_ (IMPLIES (IN x_ (VEC a)) (= ((VMUL a) x_ (VONE a)) x_))))
    (bal-uba-vone-norm (= ((VNRM a) (VONE a)) 1))))
(for-each (lambda (e) (bal-project! (car e) 'IS-UNITAL-BANACH-ALGEBRA 'IS-UNITAL-BANACH-ALGEBRA (cadr e)))
          bal-uba-own)

;;; completeness of a unital algebra, on its own metric space
(sp (make-wff '(FORALL a (IMPLIES (IS-UNITAL-BANACH-ALGEBRA a)
  (== (UBA-AS-NORMED-AG a) (CNA-AS-NORMED-AG (UBA-AS-CBA a)))))))
(dk-peel!)
(mac 'UBA-AS-NORMED-AG)
(mac 'CNA-AS-NORMED-AG)
(for-each (lambda (acc)
            (fact (bal-ucba-name acc) 'a)
            (subst (list '= (list acc bal-V) (list acc 'a))))
          '(VEC VADD VZERO VNEG VNRM))
(qrfl)
(bal-qed! 'bal-uba-nag-view)

(sp (make-wff '(FORALL a (IMPLIES (IS-UNITAL-BANACH-ALGEBRA a) (IS-COMPLETE (BA-METRIC-SPACE a))))))
(di) (di)
(fact 'uba-as-cba-is-complex-banach-algebra 'a)
(fact 'bal-cba-complete bal-V)
(fact 'bal-uba-nag-view 'a)
(mac 'BA-METRIC-SPACE)
(subst (list '= '(UBA-AS-NORMED-AG a) (list 'CNA-AS-NORMED-AG bal-V)))
(ass)
(bal-qed! 'bal-uba-complete)

(display "\n;; BAL qed failures: ")  
