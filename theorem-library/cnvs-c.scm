;;; cnvs-c.scm -- wave of 2026-11-09/10 (agent CNVS), wired 2026-11-10 from scratchpad/cnvs-1109/cnvs-c.scm.
;;; Library: analysis.

;;; cnvs-c.scm -- THE INNER-PRODUCT BRIDGES: a complex inner-product space, and a complex
;;; pre-Hilbert space through CSIP-CIPS, is a COMPLEX-NORMED-VECTOR-SPACE (CNVS, 2026-11-09).
;;; All PROVEN modulo 0.  Destination: theorem-library/cnvs-c.scm.
;;;
;;; CIPS-CNVS(w) is the realification CMOD-CNVS of the module view of w with the norm
;;; x |-> IP-NORM(w, x); the four norm laws of IS-CMOD-NORM are proven here for IP-NORM
;;; (the homogeneity ||c x|| = |c| ||x|| by sqrt-char from <cx, cx> = c conj(c) <x, x>), and
;;; cmod-cnvs-is-cnvs (cnvs-b.scm) does the rest.  CSIP-CNVS(v) = CIPS-CNVS(CSIP-CIPS(v)), so the
;;; pre-Hilbert bridge is cphs-is-complex-inner-product-space plus one citation, and its
;;; compatibility with CSIP-CIPS is a set of read-offs: same vectors, same addition, zero and
;;; negation, the CNVS complex action is the CSIP's CACT, the CNVS norm is the norm of CSIP-CIPS.
;;;
;;; The IP-NORM lemmas (cips-ipn-*) are stated as BA-BH's ip-norm-* (scratchpad/babh-1109/
;;; ba-bh.scm, library operator-algebras) under other names: an analysis file cannot cite an
;;; operator-algebras one.  When both are wired, ba-bh should cite these and drop its own.
;;;
;;; Helper prefix: cnvc-.
;;; LOAD WINDOW: after theorem-library/cnvs-b and theorem-library/sip-b (cips-module-view-*,
;;; csip-cips-*, cphs-is-complex-inner-product-space).  Library: analysis.

(define (cnvc-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** cnvs-c: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "cnvs-c: unfinished" name))))

(define cnvc-ccr '(NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD))
(define cnvc-mv '(COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE w))
(define cnvc-nf '(CIPS-VNRM w))
(define (cnvc-wstmt body) (list 'FORALL 'w (list 'IMPLIES '(IS-COMPLEX-INNER-PRODUCT-SPACE w) body)))
(define (cnvc-q x) (list '(IP w) x x))
(define (cnvc-n x) (list 'IP-NORM 'w x))
(define (cnvc-has-head? h e)
  (and (pair? e) (or (equal? (car e) h) (cnvc-has-head? h (car e)) (cnvc-has-head? h (cdr e)))))
(define (cnvc-conj-ass!) (dk-conj-close! (lambda () (ass))))

;;; q = <x, x> in RR, 0 <= q, and the same for sqrt(q)
(define (cnvc-sqrt-facts! x)
  (let ((q (cnvc-q x)))
    (dk-cite! 'cips-ip-self-real 'w x)
    (dk-cite! 'cips-ip-self-nonneg 'w x)
    (if (not (dk-asm? (list 'IN (list 'SQRT q) 'RR)))
        (begin
          (dk-have! (list 'AND (list 'IN q 'RR) (list '<= 0 q)) cnvc-conj-ass!)
          (dk-split-all! (list (dk-cite! 'sqrt-nonneg q)))))))

;;; ==========================================================================================
;;; THE NORM of an inner-product space
;;; ==========================================================================================
(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (IN (IP-NORM w x_) RR))))))
(dk-peel!)
(cnvc-sqrt-facts! 'x_)
(subst (dk-cite! 'ip-norm-unfold 'w 'x_))
(ass)
(cnvc-qed! 'cips-ipn-in-rr)

(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (<= 0 (IP-NORM w x_)))))))
(dk-peel!)
(cnvc-sqrt-facts! 'x_)
(subst (dk-cite! 'ip-norm-unfold 'w 'x_))
(ass)
(cnvc-qed! 'cips-ipn-nonneg)

(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (= (* (IP-NORM w x_) (IP-NORM w x_)) ((IP w) x_ x_)))))))
(dk-peel!)
(cnvc-sqrt-facts! 'x_)
(dk-have! (list 'AND (list 'IN (cnvc-q 'x_) 'RR) (list '<= 0 (cnvc-q 'x_))) cnvc-conj-ass!)
(dk-cite! 'sqrt-sq (cnvc-q 'x_))
(subst (dk-cite! 'ip-norm-unfold 'w 'x_))
(ass)
(cnvc-qed! 'cips-ipn-sq)

(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (IFF (= (IP-NORM w x_) 0) (= x_ (VZERO w))))))))
(dk-peel!)
(cnvc-sqrt-facts! 'x_)
(dk-cite! 'cips-ipn-sq 'w 'x_)
(dk-iff! (lambda (g) (equal? (caddr g) '(VZERO w)))
  (lambda ()
    (dk-have! (list '= (cnvc-q 'x_) 0)
      (lambda ()
        (subst (list '= (cnvc-q 'x_) (list '* (cnvc-n 'x_) (cnvc-n 'x_))))
        (subst (list '= (cnvc-n 'x_) 0))
        (arith)))
    (dk-cite! 'cips-ip-zero-vector 'w 'x_)
    (ass))
  (lambda ()
    (fact 'cips-vzero-in 'w)
    (subst '(= x_ (VZERO w)))
    (subst (dk-cite! 'ip-norm-unfold 'w '(VZERO w)))
    (subst (dk-cite! 'cips-ip-zero-left 'w '(VZERO w)))
    (subst (dk-cite! 'sqrt-zero))
    (if (not (proof-done? *ps*)) (vnb-guard (lambda () (rfl))))))
(cnvc-qed! 'cips-ipn-zero-iff)

;;; ||c x|| = |c| ||x||
(sp (make-wff (cnvc-wstmt '(FORALL c_ (IMPLIES (IN c_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC w))
  (= (IP-NORM w ((ACT w) c_ x_)) (* (magnitude c_) (IP-NORM w x_))))))))))
(dk-peel!)
(let* ((cx '((ACT w) c_ x_)) (m '(magnitude c_)) (n (cnvc-n 'x_)) (q (cnvc-q 'x_)) (qc (cnvc-q cx))
       (mn (list '* m n)))
  (dk-cite! 'cips-act-type 'w 'c_ 'x_)
  (cnvc-sqrt-facts! cx) (cnvc-sqrt-facts! 'x_)
  (dk-cite! 'cips-ipn-in-rr 'w 'x_) (dk-cite! 'cips-ipn-nonneg 'w 'x_)
  (dk-cite! 'cc-magnitude-closed 'c_) (dk-cite! 'cc-magnitude-nonneg 'c_)
  (dk-cite! 'cips-ip-type 'w 'x_ 'x_) (dk-cite! 'cips-ip-type 'w 'x_ cx)
  (dk-have! (list 'AND (list 'IN m 'RR) (list 'IN n 'RR)) cnvc-conj-ass!)
  (dk-cite! 'rr-mul-closed m n)
  (dk-have! (list 'AND (list '<= 0 m) (list '<= 0 n)) cnvc-conj-ass!)
  (dk-cite! 'rr-leq-mul-nonneg m n)
  (dk-have! (list '= (list '* mn mn) qc)
    (dk-lane (lambda ()
      (dk-have! (list '= (list '* mn mn) (list '* (list '* m m) (list '* n n))) (lambda () (crs)))
      (subst (list '= (list '* mn mn) (list '* (list '* m m) (list '* n n))))
      (subst (dk-cite! 'cips-ipn-sq 'w 'x_))
      (subst (dk-cite! 'cc-magnitude-sq-conjugate 'c_))
      (subst (dk-cite! 'cips-ip-homog-left 'w 'c_ 'x_ cx))
      (subst (dk-cite! 'cips-ip-conj-homog-right 'w 'c_ 'x_ 'x_))
      (dk-cite! 'cc-conjugate-closed 'c_)
      (dk-lane-if! crs))))
  (dk-have! (list 'AND (list 'IN qc 'RR) (list '<= 0 qc)) cnvc-conj-ass!)
  (dk-have! (list 'AND (list 'IN mn 'RR) (list '<= 0 mn)) cnvc-conj-ass!)
  (dk-cite! 'sqrt-char qc mn)
  (subst (dk-cite! 'ip-norm-unfold 'w cx))
  (ass))
(cnvc-qed! 'cips-ipn-homog)

;;; the norm as a function
(sp (make-wff (cnvc-wstmt (list 'IN cnvc-nf '(FUN (VEC w) RR)))))
(dk-peel!)
(fact 'cips-vec-set 'w)
(mac 'CIPS-VNRM)
(dk-lam-type!
  (lambda ()
    (dk-peel!)
    (dk-cite! 'cips-ipn-in-rr 'w (caddr (cadr (dk-goal))))
    (ass)))
(cnvc-qed! 'cips-vnrm-fun)

(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (= ((CIPS-VNRM w) x_) (IP-NORM w x_)))))))
(dk-peel!)
(dk-cite! 'cips-ipn-in-rr 'w 'x_)
(mac 'CIPS-VNRM)
(dk-lam-b!)
(if (not (proof-done? *ps*)) (rfl))
(cnvc-qed! 'cips-vnrm-value)

;;; the two read-offs of the module view sip-b does not state
(define (cnvc-mv-read-off! name acc)
  (sp (make-wff (cnvc-wstmt (list '== (list acc cnvc-mv) (list acc 'w)))))
  (di) (di)
  (slot acc)
  (mac 'COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE)
  (nth-r)
  (if (and (not (proof-done? *ps*)) (cnvc-has-head? acc (dk-goal))) (slot acc))
  (if (not (proof-done? *ps*)) (qrfl))
  (cnvc-qed! name))
(cnvc-mv-read-off! 'cips-module-view-vadd 'VADD)
(cnvc-mv-read-off! 'cips-module-view-vzero 'VZERO)

;;; ==========================================================================================
;;; THE BRIDGE
;;; ==========================================================================================
(sp (make-wff (cnvc-wstmt (list 'IS-CMOD-NORM cnvc-mv cnvc-nf))))
(dk-peel!)
(for-each (lambda (n) (fact n 'w))
          '(cips-module-view-vec cips-module-view-vadd cips-module-view-vzero cips-module-view-act cips-vec-set cips-vnrm-fun))
(mac 'IS-CMOD-NORM)
(for-each (lambda (acc) (if (cnvc-has-head? (list acc cnvc-mv) (dk-goal)) (subst (list '= (list acc cnvc-mv) (list acc 'w)))))
          '(VEC VADD VZERO ACT))
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal))
        (ass)
        (begin
          (dk-peel!)
          ;; type the arguments of the norm, then read its values
          (let walk ((e (dk-goal)))
            (if (pair? e)
                (begin
                  (if (and (equal? (car e) cnvc-nf) (= (length e) 2))
                      (let ((t (cadr e)))
                        (cond ((and (pair? t) (equal? (car t) '(ACT w))) (dk-cite! 'cips-act-type 'w (cadr t) (caddr t)))
                              ((and (pair? t) (equal? (car t) '(VADD w))) (dk-cite! 'cips-vadd-type 'w (cadr t) (caddr t))))))
                  (for-each walk e))))
          (let loop ((fuel 4))
            (let ((app (let find ((e (dk-goal)))
                         (and (pair? e) (list? e)
                              (or (and (equal? (car e) cnvc-nf) (= (length e) 2) e)
                                  (let inner ((xs e)) (cond ((null? xs) #f) ((find (car xs))) (#t (inner (cdr xs))))))))))
              (if (and app (> fuel 0))
                  (begin (subst (dk-cite! 'cips-vnrm-value 'w (cadr app))) (loop (- fuel 1))))))
          (let* ((g (dk-goal)))
            (cond ((dk-head-is? g 'IFF) (dk-cite! 'cips-ipn-zero-iff 'w (caddr (cadr (cadr g)))))
                  ((and (dk-head-is? g '<=) (equal? (cadr g) 0)) (dk-cite! 'cips-ipn-nonneg 'w (caddr (caddr g))))
                  ((dk-head-is? g '=)
                   (let ((t (caddr (cadr g)))) (dk-cite! 'cips-ipn-homog 'w (cadr t) (caddr t))))
                  ((dk-head-is? g '<=)
                   (let ((t (caddr (cadr g)))) (dk-cite! 'cips-minkowski 'w (cadr t) (caddr t))))))
          (if (not (proof-done? *ps*)) (vnb-guard (lambda () (ass))))))))
(cnvc-qed! 'cips-cmod-norm)

(define (cnvc-setup!)                   ; after the peel: the three hypotheses of cmod-cnvs-is-cnvs
  (fact 'complex-inner-product-space-as-module-is-module 'w)
  (fact 'cips-module-view-scal 'w)
  (fact 'cips-scal-pin 'w)
  (dk-have! (list '= (list 'SCAL cnvc-mv) cnvc-ccr)
    (lambda () (subst (list '= (list 'SCAL cnvc-mv) '(SCAL w))) (ass)))
  (fact 'cips-cmod-norm 'w)
  (fact 'cips-vnrm-fun 'w))

(sp (make-wff (cnvc-wstmt '(IS-COMPLEX-NORMED-VECTOR-SPACE (CIPS-CNVS w)))))
(dk-peel!)
(cnvc-setup!)
(mac 'CIPS-CNVS)
(fact 'cmod-cnvs-is-cnvs cnvc-mv cnvc-nf)
(ass)
(cnvc-qed! 'cips-cnvs-is-cnvs)

;;; the read-offs of CIPS-CNVS(w)
(define (cnvc-ro! name acc val via-view?)
  (sp (make-wff (cnvc-wstmt (list '== (list acc '(CIPS-CNVS w)) val))))
  (dk-peel!)
  (cnvc-setup!)
  (mac 'CIPS-CNVS)
  (subst (dk-cite! (symbol-append 'cmod-cnvs- acc) cnvc-mv cnvc-nf))
  (if via-view? (subst (dk-cite! (symbol-append 'cips-module-view- acc) 'w)))
  (if (not (proof-done? *ps*)) (qrfl))
  (cnvc-qed! name))
(cnvc-ro! 'cips-cnvs-scal 'SCAL '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) #f)
(cnvc-ro! 'cips-cnvs-vec 'VEC '(VEC w) #t)
(cnvc-ro! 'cips-cnvs-vadd 'VADD '(VADD w) #t)
(cnvc-ro! 'cips-cnvs-vzero 'VZERO '(VZERO w) #t)
(cnvc-ro! 'cips-cnvs-vneg 'VNEG '(VNEG w) #t)
(cnvc-ro! 'cips-cnvs-vnrm 'VNRM cnvc-nf #f)

;;; the norm, the complex action and J of CIPS-CNVS(w), pointwise
(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w)) (= ((VNRM (CIPS-CNVS w)) x_) (IP-NORM w x_)))))))
(dk-peel!)
(fact 'cips-vnrm-fun 'w)
(subst (dk-cite! 'cips-cnvs-vnrm 'w))
(subst (dk-cite! 'cips-vnrm-value 'w 'x_))
(dk-cite! 'cips-ipn-in-rr 'w 'x_)
(if (not (proof-done? *ps*)) (rfl))
(cnvc-qed! 'cips-cnvs-vnrm-value)

(sp (make-wff (cnvc-wstmt '(FORALL c_ (IMPLIES (IN c_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC w))
  (= ((CACT (CIPS-CNVS w)) c_ x_) ((ACT w) c_ x_)))))))))
(dk-peel!)
(cnvc-setup!)
(fact 'cips-module-view-vec 'w) (fact 'cips-module-view-act 'w)
(dk-have! (list 'IN 'x_ (list 'VEC cnvc-mv)) (lambda () (subst (list '= (list 'VEC cnvc-mv) '(VEC w))) (ass)))
(dk-cite! 'cips-act-type 'w 'c_ 'x_)
(mac 'CIPS-CNVS)
(subst (dk-cite! 'cmod-cact-value cnvc-mv cnvc-nf 'c_ 'x_))
(subst (list '= (list 'ACT cnvc-mv) '(ACT w)))
(if (not (proof-done? *ps*)) (rfl))
(cnvc-qed! 'cips-cnvs-cact)

(sp (make-wff (cnvc-wstmt '(FORALL x_ (IMPLIES (IN x_ (VEC w))
  (= ((JOP (CIPS-CNVS w)) x_) ((ACT w) +i x_)))))))
(dk-peel!)
(cnvc-setup!)
(fact 'cips-cnvs-is-cnvs 'w)
(fact 'cc-i-in)
(fact 'cips-cnvs-vec 'w)
(dk-have! '(IN x_ (VEC (CIPS-CNVS w))) (lambda () (subst '(= (VEC (CIPS-CNVS w)) (VEC w))) (ass)))
(let ((e (dk-cite! 'cnvs-cact-i '(CIPS-CNVS w) 'x_))) (subst (list '= (caddr e) (cadr e))))
(dk-cite! 'cips-act-type 'w '+i 'x_)
(subst (dk-cite! 'cips-cnvs-cact 'w '+i 'x_))
(if (not (proof-done? *ps*)) (rfl))
(cnvc-qed! 'cips-cnvs-jop-value)

;;; ==========================================================================================
;;; THE PRE-HILBERT BRIDGE, compatible with CSIP-CIPS
;;; ==========================================================================================
(define (cnvc-vstmt body) (list 'FORALL 'v (list 'IMPLIES '(IS-COMPLEX-PRE-HILBERT-SPACE v) body)))
(define cnvc-cv '(CSIP-CIPS v))

(sp (make-wff (cnvc-vstmt '(IS-COMPLEX-NORMED-VECTOR-SPACE (CSIP-CNVS v)))))
(dk-peel!)
(fact 'cphs-is-complex-inner-product-space 'v)
(mac 'CSIP-CNVS)
(fact 'cips-cnvs-is-cnvs cnvc-cv)
(ass)
(cnvc-qed! 'cphs-cnvs-is-cnvs)

(sp (make-wff (cnvc-vstmt '(== (CSIP-CNVS v) (CIPS-CNVS (CSIP-CIPS v))))))
(dk-peel!)
(mac 'CSIP-CNVS)
(if (not (proof-done? *ps*)) (qrfl))
(cnvc-qed! 'csip-cnvs-unfold)

(define (cnvc-csip-ro! name acc)
  (sp (make-wff (cnvc-vstmt (list '== (list acc '(CSIP-CNVS v)) (list acc 'v)))))
  (dk-peel!)
  (fact 'cphs-is-complex-inner-product-space 'v)
  (fact 'cphs-is-csip 'v)
  (mac 'CSIP-CNVS)
  (subst (dk-cite! (symbol-append 'cips-cnvs- acc) cnvc-cv))
  (subst (dk-cite! (symbol-append 'csip-cips- acc) 'v))
  (if (not (proof-done? *ps*)) (qrfl))
  (cnvc-qed! name))
(cnvc-csip-ro! 'csip-cnvs-vec 'VEC)
(cnvc-csip-ro! 'csip-cnvs-vadd 'VADD)
(cnvc-csip-ro! 'csip-cnvs-vzero 'VZERO)
(cnvc-csip-ro! 'csip-cnvs-vneg 'VNEG)

;;; the CNVS complex action of CSIP-CNVS(v) is the CSIP's own CACT
(sp (make-wff (cnvc-vstmt '(FORALL c_ (IMPLIES (IN c_ CC) (FORALL x_ (IMPLIES (IN x_ (VEC v))
  (= ((CACT (CSIP-CNVS v)) c_ x_) ((CACT v) c_ x_)))))))))
(dk-peel!)
(fact 'cphs-is-complex-inner-product-space 'v)
(fact 'cphs-is-csip 'v)
(fact 'csip-cips-vec 'v) (fact 'csip-cips-act 'v)
(dk-have! (list 'IN 'x_ (list 'VEC cnvc-cv)) (lambda () (subst (list '= (list 'VEC cnvc-cv) '(VEC v))) (ass)))
(dk-rewrite-h! (dk-cite! 'cips-act-type cnvc-cv 'c_ 'x_) (list 'ACT cnvc-cv) '(CACT v))
(mac 'CSIP-CNVS)
(subst (dk-cite! 'cips-cnvs-cact cnvc-cv 'c_ 'x_))
(subst (list '= (list 'ACT cnvc-cv) '(CACT v)))
(if (not (proof-done? *ps*)) (rfl))
(cnvc-qed! 'csip-cnvs-cact)

;;; its norm is the norm of the inner-product space CSIP-CIPS(v)
(sp (make-wff (cnvc-vstmt '(FORALL x_ (IMPLIES (IN x_ (VEC v))
  (= ((VNRM (CSIP-CNVS v)) x_) (IP-NORM (CSIP-CIPS v) x_)))))))
(dk-peel!)
(fact 'cphs-is-complex-inner-product-space 'v)
(fact 'cphs-is-csip 'v)
(fact 'csip-cips-vec 'v)
(dk-have! (list 'IN 'x_ (list 'VEC cnvc-cv)) (lambda () (subst (list '= (list 'VEC cnvc-cv) '(VEC v))) (ass)))
(mac 'CSIP-CNVS)
(fact 'cips-cnvs-vnrm-value cnvc-cv 'x_)
(ass)
(cnvc-qed! 'csip-cnvs-vnrm-value)

;;; ==========================================================================================
;;; THE METRIC: the normed group of CIPS-CNVS(w) is IP-NORMED-AG(w), so a Hilbert space is a
;;; complex Banach space
;;; ==========================================================================================
(sp (make-wff (cnvc-wstmt '(== (CNVS-AS-NORMED-AG (CIPS-CNVS w)) (IP-NORMED-AG w)))))
(dk-peel!)
(fact 'cips-cnvs-is-cnvs 'w)
(for-each (lambda (n) (fact n 'w)) '(cips-cnvs-vec cips-cnvs-vadd cips-cnvs-vzero cips-cnvs-vneg cips-cnvs-vnrm))
(mac 'CNVS-AS-NORMED-AG)
(for-each (lambda (acc) (if (cnvc-has-head? (list acc '(CIPS-CNVS w)) (dk-goal))
                            (subst (list '= (list acc '(CIPS-CNVS w)) (if (eq? acc 'VNRM) cnvc-nf (list acc 'w))))))
          '(VEC VADD VZERO VNEG VNRM))
(mac 'CIPS-VNRM)
(mac 'IP-NORMED-AG)
(if (not (proof-done? *ps*)) (qrfl))
(cnvc-qed! 'cips-cnvs-normed-ag)

(sp (make-wff (cnvc-wstmt '(== (CNVS-METRIC-SPACE (CIPS-CNVS w)) (IP-METRIC-SPACE w)))))
(dk-peel!)
(fact 'cips-cnvs-normed-ag 'w)
(mac 'CNVS-METRIC-SPACE)
(mac 'IP-METRIC-SPACE)
(subst '(= (CNVS-AS-NORMED-AG (CIPS-CNVS w)) (IP-NORMED-AG w)))
(if (not (proof-done? *ps*)) (qrfl))
(cnvc-qed! 'cips-cnvs-metric-space)

(sp (make-wff '(FORALL w (IMPLIES (IS-HILBERT-SPACE w) (IS-COMPLEX-BANACH-SPACE (CIPS-CNVS w))))))
(di) (di)
(dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'IS-HILBERT-SPACE '(IS-HILBERT-SPACE w))))))
(fact 'cips-cnvs-is-cnvs 'w)
(fact 'cips-cnvs-metric-space 'w)
(mac 'is-complex-banach-space-def)
(dk-conj-close!
  (lambda ()
    (if (not (dk-asm? (dk-goal)))
        (subst '(= (CNVS-METRIC-SPACE (CIPS-CNVS w)) (IP-METRIC-SPACE w))))
    (if (not (proof-done? *ps*)) (vnb-guard (lambda () (ass))))))
(cnvc-qed! 'hilbert-cnvs-is-cbs)
