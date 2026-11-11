;;; cnvs-ba.scm -- wave of 2026-11-09/10 (agent CNVS), wired 2026-11-10 from scratchpad/cnvs-1109/cnvs-ba.scm.
;;; Library: operator-algebras.

;;; cnvs-ba.scm -- A COMPLEX NORMED ALGEBRA IS A COMPLEX NORMED VECTOR SPACE, and a complex
;;; Banach algebra a complex Banach space (CNVS, 2026-11-09).  All PROVEN modulo 0.
;;; Destination: theorem-library/cnvs-ba.scm.  Vocabulary: structure-library/cnvs-ba-vocab.scm.
;;;
;;; CNA-CNVS(a) = CMOD-CNVS(CNA-AS-MODULE(a), VNRM(a)); the module view is a module with complex
;;; scalars (the def-functor typing of CNA-AS-MODULE and the scalar law of the structure), the
;;; four norm laws of IS-CMOD-NORM are four laws of IS-COMPLEX-NORMED-ALGEBRA read through the
;;; view, and cmod-cnvs-is-cnvs (cnvs-b.scm) does the rest.  The two metric spaces are the same
;;; term: CNVS-AS-NORMED-AG(CNA-CNVS(a)) and CNA-AS-NORMED-AG(a) are the same 5-tuple.
;;;
;;; Helper prefix: cnvba-.
;;; LOAD WINDOW: after theorem-library/cnvs-b, structure-library/ba-vocab and
;;; structure-library/cnvs-ba-vocab.  Library: operator-algebras.

(define (cnvba-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** cnvs-ba: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "cnvs-ba: unfinished" name))))

(define cnvba-ccr '(NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD))
(define cnvba-is '(IS-COMPLEX-NORMED-ALGEBRA a))
(define cnvba-mv '(CNA-AS-MODULE a))
(define cnvba-nf '(VNRM a))
(define (cnvba-stmt body) (list 'FORALL 'a (list 'IMPLIES cnvba-is body)))
(define (cnvba-has-head? h e)
  (and (pair? e) (or (equal? (car e) h) (cnvba-has-head? h (car e)) (cnvba-has-head? h (cdr e)))))

;;; the laws of a complex normed algebra this file reads
(define (cnvba-proj! name conj)
  (sp (make-wff (cnvba-stmt conj)))
  (di) (di)
  (dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'is-complex-normed-algebra cnvba-is)))))
  (ass)
  (cnvba-qed! name))
(cnvba-proj! 'cna-vnrm-fun '(IN (VNRM a) (FUN (VEC a) RR)))
(cnvba-proj! 'cna-scal-pin (list '= '(SCAL a) cnvba-ccr))
(cnvba-proj! 'cna-scal-carr '(= (CARR (SCAL a)) CC))
(cnvba-proj! 'cna-vnrm-nonneg '(FORALL x_ (IMPLIES (IN x_ (VEC a)) (<= 0 ((VNRM a) x_)))))
(cnvba-proj! 'cna-vnrm-definite '(FORALL x_ (IMPLIES (IN x_ (VEC a)) (IFF (= ((VNRM a) x_) 0) (= x_ (VZERO a))))))
(cnvba-proj! 'cna-vnrm-homog-scal
  '(FORALL r_ (IMPLIES (IN r_ (CARR (SCAL a))) (FORALL x_ (IMPLIES (IN x_ (VEC a))
     (= ((VNRM a) ((ACT a) r_ x_)) (* (magnitude r_) ((VNRM a) x_))))))))
(cnvba-proj! 'cna-vnrm-triangle
  '(FORALL x_ (IMPLIES (IN x_ (VEC a)) (FORALL y_ (IMPLIES (IN y_ (VEC a))
     (<= ((VNRM a) ((VADD a) x_ y_)) (+ ((VNRM a) x_) ((VNRM a) y_))))))))

;;; ... the homogeneity over CC
(sp (make-wff (cnvba-stmt '(FORALL c_ (IMPLIES (IN c_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC a))
  (= ((VNRM a) ((ACT a) c_ x_)) (* (magnitude c_) ((VNRM a) x_))))))))))
(dk-peel!)
(fact 'cna-scal-carr 'a)
(dk-have! '(IN c_ (CARR (SCAL a))) (lambda () (subst '(= (CARR (SCAL a)) CC)) (ass)))
(fact 'cna-vnrm-homog-scal 'a 'c_ 'x_)
(ass)
(cnvba-qed! 'cna-vnrm-homog)

;;; the read-offs of the module view
(define (cnvba-mv-read-off! name acc)
  (sp (make-wff (cnvba-stmt (list '== (list acc cnvba-mv) (list acc 'a)))))
  (di) (di)
  (slot acc)
  (mac 'CNA-AS-MODULE)
  (nth-r)
  (if (and (not (proof-done? *ps*)) (cnvba-has-head? acc (dk-goal))) (slot acc))
  (if (not (proof-done? *ps*)) (qrfl))
  (cnvba-qed! name))
(for-each (lambda (acc) (cnvba-mv-read-off! (symbol-append 'cna-module-view- acc) acc))
          '(SCAL VEC VADD VZERO VNEG ACT))

;;; ==========================================================================================
;;; THE BRIDGE
;;; ==========================================================================================
(sp (make-wff (cnvba-stmt (list 'IS-CMOD-NORM cnvba-mv cnvba-nf))))
(dk-peel!)
(for-each (lambda (n) (fact n 'a))
          '(cna-module-view-vec cna-module-view-vadd cna-module-view-vzero cna-module-view-act cna-vnrm-fun
            cna-vnrm-nonneg cna-vnrm-definite cna-vnrm-homog cna-vnrm-triangle))
(mac 'IS-CMOD-NORM)
(for-each (lambda (acc) (if (cnvba-has-head? (list acc cnvba-mv) (dk-goal)) (subst (list '= (list acc cnvba-mv) (list acc 'a)))))
          '(VEC VADD VZERO ACT))
(dk-conj-close! (lambda () (ass)))
(cnvba-qed! 'cna-cmod-norm)

(define (cnvba-setup!)                  ; after the peel: the three hypotheses of cmod-cnvs-is-cnvs
  (fact 'cna-as-module-is-module 'a)
  (fact 'cna-module-view-scal 'a)
  (fact 'cna-scal-pin 'a)
  (dk-have! (list '= (list 'SCAL cnvba-mv) cnvba-ccr)
    (lambda () (subst (list '= (list 'SCAL cnvba-mv) '(SCAL a))) (ass)))
  (fact 'cna-cmod-norm 'a)
  (fact 'cna-vnrm-fun 'a))

(sp (make-wff (cnvba-stmt '(IS-COMPLEX-NORMED-VECTOR-SPACE (CNA-CNVS a)))))
(dk-peel!)
(cnvba-setup!)
(mac 'CNA-CNVS)
(fact 'cmod-cnvs-is-cnvs cnvba-mv cnvba-nf)
(ass)
(cnvba-qed! 'cna-cnvs-is-cnvs)

(define (cnvba-ro! name acc val via-view?)
  (sp (make-wff (cnvba-stmt (list '== (list acc '(CNA-CNVS a)) val))))
  (dk-peel!)
  (cnvba-setup!)
  (mac 'CNA-CNVS)
  (subst (dk-cite! (symbol-append 'cmod-cnvs- acc) cnvba-mv cnvba-nf))
  (if via-view? (subst (dk-cite! (symbol-append 'cna-module-view- acc) 'a)))
  (if (not (proof-done? *ps*)) (qrfl))
  (cnvba-qed! name))
(cnvba-ro! 'cna-cnvs-vec 'VEC '(VEC a) #t)
(cnvba-ro! 'cna-cnvs-vadd 'VADD '(VADD a) #t)
(cnvba-ro! 'cna-cnvs-vzero 'VZERO '(VZERO a) #t)
(cnvba-ro! 'cna-cnvs-vneg 'VNEG '(VNEG a) #t)
(cnvba-ro! 'cna-cnvs-vnrm 'VNRM '(VNRM a) #f)

;;; the CNVS complex action of CNA-CNVS(a) is the algebra's scalar action
(sp (make-wff (cnvba-stmt '(FORALL c_ (IMPLIES (IN c_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC a))
  (= ((CACT (CNA-CNVS a)) c_ x_) ((ACT a) c_ x_)))))))))
(dk-peel!)
(cnvba-setup!)
(fact 'cna-module-view-vec 'a) (fact 'cna-module-view-act 'a)
(dk-have! (list 'IN 'x_ (list 'VEC cnvba-mv)) (lambda () (subst (list '= (list 'VEC cnvba-mv) '(VEC a))) (ass)))
(fact 'cna-scal-carr 'a)
(dk-have! '(IN c_ (CARR (SCAL a))) (lambda () (subst '(= (CARR (SCAL a)) CC)) (ass)))
(dk-cite! 'module-act-type-cna-as-module 'a 'c_ 'x_)
(mac 'CNA-CNVS)
(subst (dk-cite! 'cmod-cact-value cnvba-mv cnvba-nf 'c_ 'x_))
(subst (list '= (list 'ACT cnvba-mv) '(ACT a)))
(if (not (proof-done? *ps*)) (rfl))
(cnvba-qed! 'cna-cnvs-cact)

;;; the two normed groups, hence the two metric spaces, are the same
(sp (make-wff (cnvba-stmt '(== (CNVS-AS-NORMED-AG (CNA-CNVS a)) (CNA-AS-NORMED-AG a)))))
(dk-peel!)
(fact 'cna-cnvs-is-cnvs 'a)
(for-each (lambda (n) (fact n 'a)) '(cna-cnvs-vec cna-cnvs-vadd cna-cnvs-vzero cna-cnvs-vneg cna-cnvs-vnrm))
(mac 'CNVS-AS-NORMED-AG)
(mac 'CNA-AS-NORMED-AG)
(for-each (lambda (acc) (if (cnvba-has-head? (list acc '(CNA-CNVS a)) (dk-goal))
                            (subst (list '= (list acc '(CNA-CNVS a)) (list acc 'a)))))
          '(VEC VADD VZERO VNEG VNRM))
(if (not (proof-done? *ps*)) (qrfl))
(cnvba-qed! 'cna-cnvs-normed-ag)

(sp (make-wff (cnvba-stmt '(== (CNVS-METRIC-SPACE (CNA-CNVS a)) (CNA-METRIC-SPACE a)))))
(dk-peel!)
(fact 'cna-cnvs-normed-ag 'a)
(mac 'CNVS-METRIC-SPACE)
(mac 'CNA-METRIC-SPACE)
(subst '(= (CNVS-AS-NORMED-AG (CNA-CNVS a)) (CNA-AS-NORMED-AG a)))
(if (not (proof-done? *ps*)) (qrfl))
(cnvba-qed! 'cna-cnvs-metric-space)

;;; a complex Banach algebra is a complex Banach space
(sp (make-wff '(FORALL a (IMPLIES (IS-COMPLEX-BANACH-ALGEBRA a) (IS-COMPLEX-BANACH-SPACE (CNA-CNVS a))))))
(di) (di)
(dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'is-complex-banach-algebra-def '(IS-COMPLEX-BANACH-ALGEBRA a))))))
(fact 'cna-cnvs-is-cnvs 'a)
(fact 'cna-cnvs-normed-ag 'a)
(mac 'is-complex-banach-space-def)
(dk-conj-close!
  (lambda ()
    (if (not (dk-asm? (dk-goal)))
        (begin
          (if (cnvba-has-head? 'CNVS-METRIC-SPACE (dk-goal)) (mac 'CNVS-METRIC-SPACE))
          (if (cnvba-has-head? 'CNVS-AS-NORMED-AG (dk-goal))
              (subst '(= (CNVS-AS-NORMED-AG (CNA-CNVS a)) (CNA-AS-NORMED-AG a))))))
    (if (not (proof-done? *ps*)) (vnb-guard (lambda () (ass))))))
(cnvba-qed! 'cba-cnvs-is-cbs)
