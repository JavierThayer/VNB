;;; ca1-alg-closed.scm -- C IS ALGEBRAICALLY CLOSED, IN THE NOTES' FORM, AND THE GROWTH
;;; ESTIMATE (6)-(7) OF ITS PROOF (complex-analysis.pdf, Theorem 1.15).  Agent CA-1,
;;; 2026-10-19.
;;;
;;; THEOREM 1.15 (the notes).  C is algebraically closed: every equation
;;; a_n z^n + ... + a_0 = 0 with n in N (the notes' N starts at 1) and a_n /= 0 has a
;;; solution in C.
;;;
;;; WHAT WAS ALREADY THERE.  theorem-library/cauchy-estimates.scm (CA-3, 2026-10-04) proves
;;; `fundamental-theorem-of-algebra' for a coefficient FUNCTION p in FUN(NN, CC) and a degree
;;; written succ(m): p(succ m) /= 0 implies sum_{k <= succ m} p(k) z^k = 0 for some z.  Its
;;; route is the centre bound of Cauchy's estimates applied to 1/p (one step shorter than
;;; Liouville, Corollary 3.50 of the notes).  The polynomial is the partial sum
;;; CC-SERIES-PARTIAL-SUM(k |-> p(k) z^k, n + 1); the tree has no evaluation map from
;;; POLY(CC) to functions on CC (that file's header).
;;;
;;; WHAT IS ADDED HERE.
;;;  cc-algebraically-closed     the notes' form: n in NN, 1 <= n, a_n /= 0 (one citation of
;;;                              fundamental-theorem-of-algebra after n = succ(m),
;;;                              nn-pos-is-succ).
;;;  cc-polynomial-lower-growth  the notes' main estimate (6)-(7), as a citable lemma:
;;;                              |z| >= 1 and 2 (|a_0| + ... + |a_(n-1)|) <= |a_n| |z|
;;;                              imply |a_n| |z|^n <= 2 |P(z)|.  The notes' threshold
;;;                              L = max{1, 2 (|a_(n-1)| + ... + |a_0|) / |a_n|} is stated
;;;                              without the division; |z| >= L is the hypothesis (the notes
;;;                              ask |z| > L), and no hypothesis a_n /= 0 is needed.  It is
;;;                              the estimate the proof of fundamental-theorem-of-algebra
;;;                              carries out inline, at the end of a circle-bound lemma; here
;;;                              it stands alone, the input of (6), lim |P(z)| = +infinity,
;;;                              and of Corollary 3.50.
;;; The notes' own proof of 1.15 (the minimum of |P| on a disc, then n-th roots of
;;; -a_0 / a_r to push |P| below its minimum) is NOT formalised: the tree has no n-th roots
;;; of a complex number (the polar form r (cos t + i sin t) with r^(1/n)); see the report.
;;;
;;; NOTHING asserted, no definition.  LOAD WINDOW: lo = theorem-library/cauchy-estimates
;;; (load.scm 3683: fundamental-theorem-of-algebra, polynomial-growth-bound), the latest
;;; citation; the next are cc-power-series-laws (3608: cc-magnitude-power) and limsup-tests
;;; (3435: rr-power-mono-base).  hi: none.  Library: complex-analysis.  Tactics: the early
;;; kit (dk-*, crs, ineq, prop).  Helper prefix cag-.

;;; =====================================================================
;;; File-local driver helpers (prefix cag-).  Copied from the cie- helpers of
;;; theorem-library/cauchy-estimates.scm (a helper is local to its file); the
;;; coefficient function is ciep_ and the lambda binder k, as there, so that the
;;; polynomial terms built here are the terms polynomial-growth-bound states.
;;; =====================================================================
(define cag-nfm '(NF-METRIC-SPACE CC-NORMED-FIELD))
(define (cag-op? t op n) (and (pair? t) (eq? (car t) op) (= (length t) n)))
(define (cag-imps hyps body)
  (if (null? hyps) body (list 'IMPLIES (car hyps) (cag-imps (cdr hyps) body))))
(define (cag-all vars body)
  (if (null? vars) body (list 'FORALL (car vars) (cag-all (cdr vars) body))))
(define (cag-and! a b)
  (let* ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! dk-ass!))))
    f))
(define (cag-pz z) (list 'DIFFERENCE 'CC (list 'SINGLETON z)))
(define (cag-rr! t)
  (let* ((typ (list 'IN t 'RR)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'rr-zero-in) typ)
          ((eqv? t 1) (fact 'rr-one-in) typ)
          ((eq? t 'PI) (dk-split-all! (list (dk-cite! 'pi-pos))) typ)
          ((number? t) (dk-have! typ (lambda () (arith))) typ)
          ((dk-asm? (list 'IN t 'NN)) (fact 'nn-in-rr t) typ)
          ((cag-op? t 'succ 2) (cag-nn! t) (fact 'nn-in-rr t) typ)
          ((cag-op? t '* 3) (cag-rr! (cadr t)) (cag-rr! (caddr t)) (fact 'rr-mul-in-rr (cadr t) (caddr t)) typ)
          ((cag-op? t '+ 3) (cag-rr! (cadr t)) (cag-rr! (caddr t)) (fact 'rr-add-in-rr (cadr t) (caddr t)) typ)
          ((cag-op? t '- 3) (cag-rr! (cadr t)) (cag-rr! (caddr t)) (fact 'rr-sub-in-rr (cadr t) (caddr t)) typ)
          ((cag-op? t '- 2) (cag-rr! (cadr t)) (fact 'rr-neg-closed (cadr t)) typ)
          ((cag-op? t 'magnitude 2) (cag-cc! (cadr t)) (fact 'cc-magnitude-closed (cadr t)) typ)
          ((cag-op? t 'real-part 2) (cag-cc! (cadr t)) (fact 'real-part-in-rr (cadr t)) typ)
          ((cag-op? t 'imag-part 2) (cag-cc! (cadr t)) (fact 'imag-part-in-rr (cadr t)) typ)
          ((cag-op? t 'abs 2) (cag-rr! (cadr t)) (fact 'rr-abs-closed (cadr t)) typ)
          ((cag-op? t 'recip 2)
           (cag-rr! (cadr t))
           (if (not (dk-asm? (list 'NOT (list '= (cadr t) 0))))
               (if (dk-asm? (list '< 0 (cadr t)))
                   (fact 'rr-pos-ne-zero (cadr t))
                   (error "cag-rr!: land the non-vanishing first" (expression->string (cadr t)))))
           (cag-and! (list 'IN (cadr t) 'RR) (list 'NOT (list '= (cadr t) 0)))
           (fact 'rr-recip-closed (cadr t))
           typ)
          (#t (dk-real! t) typ))))
(define (cag-nn! t)
  (let* ((typ (list 'IN t 'NN)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'nn-zero-in) typ)
          ((cag-op? t 'succ 2) (cag-nn! (cadr t)) (fact 'nn-succ-closed (cadr t)) typ)
          (#t (dk-type! t 'NN)))))
(define (cag-cc! t)
  (let* ((typ (list 'IN t 'CC)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'cc-zero-in) typ)
          ((eqv? t +i) (fact 'cc-i-in) typ)
          ((or (and (number? t) (real? t)) (eq? t 'PI) (dk-asm? (list 'IN t 'RR)) (dk-asm? (list 'IN t 'NN))
               (cag-op? t 'succ 2)
               (cag-op? t 'magnitude 2) (cag-op? t 'real-part 2) (cag-op? t 'imag-part 2))
           (cag-rr! t) (fact 'rr-subset-cc t) typ)
          ((cag-op? t '- 3) (cag-cc! (cadr t)) (cag-cc! (caddr t)) (fact 'cc-sub-in-cc (cadr t) (caddr t)) typ)
          ((cag-op? t '- 2) (cag-cc! (cadr t)) (fact 'cc-neg-closed (cadr t)) typ)
          ((cag-op? t '+ 3) (cag-cc! (cadr t)) (cag-cc! (caddr t))
           (cag-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC)) (fact 'cc-add-closed (cadr t) (caddr t)) typ)
          ((cag-op? t '* 3) (cag-cc! (cadr t)) (cag-cc! (caddr t))
           (cag-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC)) (fact 'cc-mul-closed (cadr t) (caddr t)) typ)
          ((cag-op? t 'power 3) (cag-cc! (cadr t)) (cag-nn! (caddr t))
           (cag-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'NN)) (fact 'power-typing-nonneg (cadr t) (caddr t)) typ)
          ((cag-op? t 'CC-EXP 2) (cag-cc! (cadr t))
           (dk-split-all! (list (dk-cite! 'cc-exp-converges (cadr t)))) typ)
          ((cag-op? t 'recip 2) (cag-cc! (cadr t))
           (if (not (dk-asm? (list 'NOT (list '= (cadr t) 0))))
               (error "cag-cc!: land the non-vanishing first" (expression->string (cadr t))))
           (cag-and! (list 'IN (cadr t) 'CC) (list 'NOT (list '= (cadr t) 0)))
           (fact 'cc-recip-closed (cadr t)) typ)
          (#t (dk-type! t 'CC)))))
(define (cag-steps . thunks)
  ;; run THUNKS in order while the leaf focused at the start stays open
  (let* ((leaf (proof-state-focus *ps*)))
    (let loop ((ts thunks))
      (if (and (pair? ts) (not (sequent-node-grounded? leaf)))
          (begin ((car ts)) (loop (cdr ts)))))))
;;; (cag-lam-typ! LAM DOM TYPER) -- LAM in FUN(DOM, CC); TYPER of the eigenvariable
(define (cag-lam-typ! lam dom pre)
  (dk-have! (list 'IN lam (list 'FUN dom 'CC))
    (lambda ()
      (dk-lam-type! (lambda ()
                      (let* ((v (dk-di-var!)) (leaf (proof-state-focus *ps*)))
                        (cag-steps
                          (lambda () (pre v))
                          (lambda () (if (dk--redex? (dk-goal)) (dk-lam-b!)))
                          (lambda () (if (not (dk-asm? (dk-goal))) (cag-cc! (cadr (dk-goal)))))
                          (lambda () (ass)))))))))
(define (cag-only-prop! . fs) (if (apply dk-only! fs) (prop)))
(define (cag-lam-b-if!) (if (dk--redex? (dk-goal)) (dk-lam-b!)))
(define (cag-pow-succ! a n)
  (cag-cc! a) (cag-nn! n)
  (cag-and! (list 'IN a 'CC) (list 'IN n 'NN))
  (dk-cite! 'power-succ a n))
(define (cag-pterm w) (list 'VNB-LAMBDA 'k 'NN (list '* '(ciep_ k) (list 'power w 'k))))
(define (cag-poly w n) (list 'CC-SERIES-PARTIAL-SUM (cag-pterm w) n))
(define cag-A '(VNB-LAMBDA k NN (magnitude (ciep_ k))))
;;; w in CC, j in NN, p in FUN(NN, CC): T_w typed, T_w(j) and the partial sums typed
(define (cag-pterm-typ! w)
  (cag-lam-typ! (cag-pterm w) 'NN (lambda (k) (fact 'fun-apply-type-c 'ciep_ 'NN 'CC k))))
(define (cag-ps-typ! w n)
  (cag-pterm-typ! w)
  (cag-nn! n)
  (dk-cite! 'cc-series-partial-sum-in-cc n (cag-pterm w)))
;;; (cag-ps-succ! w n): PS(T_w, succ n) == PS(T_w, n) + p(n) w^n, landed
(define (cag-ps-succ! w n)
  (let* ((tn (list (cag-pterm w) n)) (v (list '* (list 'ciep_ n) (list 'power w n))))
    (cag-ps-typ! w n)
    (fact 'fun-apply-type-c 'ciep_ 'NN 'CC n)
    (cag-cc! v)
    (dk-have! (list 'IN tn 'CC) (lambda () (cag-steps cag-lam-b-if! ass)))
    (let* ((e (dk-cite! 'cc-series-partial-sum-succ (cag-pterm w) n)))
      (dk-have! (list '== (list 'CC-SERIES-PARTIAL-SUM (cag-pterm w) (list 'succ n)) (list '+ (cag-poly w n) v))
        (lambda () (subst e) (dk-lam-b!) (qrfl))))))
(define (cag-SA n) (list 'CC-SERIES-PARTIAL-SUM cag-A n))
(define (cag-A-typ!)
  (dk-have! (list 'IN cag-A '(FUN NN RR))
    (lambda () (dk-lam-type! (lambda () (let* ((k (dk-di-var!)) (leaf (proof-state-focus *ps*)))
                                          (fact 'fun-apply-type-c 'ciep_ 'NN 'CC k)
                                          (cag-lam-b-if!)
                                          (cag-rr! (cadr (dk-goal)))
                                          (if (not (sequent-node-grounded? leaf)) (ass)))))))
  (dk-have! (list 'IN cag-A '(FUN NN CC))
    (lambda () (dk-lam-type! (lambda () (let* ((k (dk-di-var!)) (leaf (proof-state-focus *ps*)))
                                          (fact 'fun-apply-type-c 'ciep_ 'NN 'CC k)
                                          (cag-lam-b-if!)
                                          (cag-cc! (cadr (dk-goal)))
                                          (if (not (sequent-node-grounded? leaf)) (ass))))))))

;;; =====================================================================
;;; 1.  THEOREM 1.15 IN THE NOTES' FORM.
;;; Every polynomial a_n z^n + ... + a_0 with n >= 1 and a_n /= 0 has a root in C.
;;; =====================================================================

(sp (make-wff '(FORALL ciep_ (IMPLIES (IN ciep_ (FUN NN CC))
      (FORALL ca1n_ (IMPLIES (IN ca1n_ NN)
        (IMPLIES (<= 1 ca1n_)
          (IMPLIES (NOT (= (ciep_ ca1n_) 0))
            (FORSOME z (AND (IN z CC)
              (= (CC-SERIES-PARTIAL-SUM (VNB-LAMBDA k NN (* (ciep_ k) (power z k))) (succ ca1n_))
                 0)))))))))))
(dk-peel!)
(define cag-q (dk-skolem! (dk-cite! 'nn-pos-is-succ 'ca1n_)))
(subst (list '= 'ca1n_ (list 'succ cag-q)))
(dk-rewrite-h! '(NOT (= (ciep_ ca1n_) 0)) 'ca1n_ (list 'succ cag-q))
(dk-cite! 'fundamental-theorem-of-algebra 'ciep_ cag-q)
(from-context!)
(qed 'cc-algebraically-closed)

;;; =====================================================================
;;; 2.  THE GROWTH ESTIMATE OF THE NOTES' PROOF, (6)-(7).
;;; For P(z) = a_n z^n + ... + a_0 (n = succ m) and |z| at least
;;; L = max{1, 2 (|a_(n-1)| + ... + |a_0|) / |a_n|}:  |a_n| |z|^n <= 2 |P(z)|.
;;; Stated without the division: |z| >= 1 and 2 (|a_0| + ... + |a_m|) <= |a_n| |z|.
;;; No hypothesis a_n /= 0 is needed (when a_n = 0 the conclusion is 0 <= 2 |P(z)|).
;;; =====================================================================

(define cag-S (cag-SA '(succ ciem_)))
(define cag-an '(ciep_ (succ ciem_)))
(define cag-al (list 'magnitude cag-an))
(sp (make-wff (list 'FORALL 'ciep_ (list 'IMPLIES '(IN ciep_ (FUN NN CC))
  (list 'FORALL 'ciem_ (list 'IMPLIES '(IN ciem_ NN)
    (list 'FORALL 'z (list 'IMPLIES '(IN z CC)
      (list 'IMPLIES '(<= 1 (magnitude z))
        (list 'IMPLIES (list '<= (list '* 2 cag-S) (list '* cag-al '(magnitude z)))
          (list '<= (list '* cag-al (list 'power '(magnitude z) '(succ ciem_)))
                    (list '* 2 (list 'magnitude (cag-poly 'z '(succ (succ ciem_))))))))))))))))
(define cag-lk (dk-peel!))
(define cag-y (cadr (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'CC))) cag-lk)))
(define cag-n '(succ ciem_))
(define cag-rho (list 'magnitude cag-y))
(fact 'nn-succ-closed 'ciem_)
(fact 'fun-apply-type-c 'ciep_ 'NN 'CC cag-n)
(cag-rr! cag-al)
(cag-rr! cag-rho)
(dk-cite! 'cc-magnitude-nonneg cag-an)
(cag-A-typ!)
(dk-split-all! (list (dk-cite! 'polynomial-growth-bound 'ciem_ 'ciep_)))
(define cag-gb (dk-pick (lambda (fm) (and (dk-head-is? fm 'FORALL) (dk-contains? fm 'ciew_))) "the growth bound"))
(dk-apply! cag-gb cag-y)
;; P = Q + top
(cag-ps-succ! cag-y cag-n)
(define cag-qq (cag-poly cag-y cag-n))
(define cag-top (list '* cag-an (list 'power cag-y cag-n)))
(define cag-pp (cag-poly cag-y (list 'succ cag-n)))
(cag-ps-typ! cag-y (list 'succ cag-n))
(cag-cc! cag-qq) (cag-cc! cag-top) (cag-cc! cag-pp)
(cag-cc! (list '- cag-qq))
(dk-have! (list '= cag-top (list '+ cag-pp (list '- cag-qq)))
  (lambda () (subst (list '== cag-pp (list '+ cag-qq cag-top))) (crs)))
(cag-and! (list 'IN cag-pp 'CC) (list 'IN (list '- cag-qq) 'CC))
(dk-cite! 'cc-magnitude-triangle cag-pp (list '- cag-qq))
(dk-cite! 'cc-magnitude-neg cag-qq)
(cag-and! (list 'IN cag-an 'CC) (list 'IN (list 'power cag-y cag-n) 'CC))
(dk-cite! 'cc-magnitude-mul cag-an (list 'power cag-y cag-n))
(dk-cite! 'cc-magnitude-power cag-n cag-y)
(fact 'power-real-closed cag-rho 'ciem_)
(fact 'rr-subset-cc cag-rho)
(cag-pow-succ! cag-rho 'ciem_)
(define cag-x (list 'power cag-rho 'ciem_))
(define cag-mp (list 'magnitude cag-pp))
(define cag-mq (list 'magnitude cag-qq))
(define cag-mt (list 'magnitude cag-top))
(cag-rr! cag-mp) (cag-rr! cag-mq) (cag-rr! cag-mt) (cag-rr! (list 'magnitude (list '- cag-qq)))
(cag-rr! (list 'magnitude (list '+ cag-pp (list '- cag-qq))))
(define cag-xv (dk-name! cag-x))
;; X >= 1 >= 0
(fact 'rr-one-in)
(dk-have! '(<= 0 1) (lambda () (dk-ineq!)))
(dk-cite! 'rr-power-mono-base 'ciem_ 1 cag-rho)
(dk-cite! 'rr-power-one 'ciem_)
(dk-have! (list '<= 1 cag-xv) (lambda () (subst (list '= cag-xv cag-x)) (subst (list '= 1 (list 'power 1 'ciem_))) (ass)))
(dk-have! (list '<= 0 cag-xv) (lambda () (dk-ineq! (list '<= 1 cag-xv))))
(define cag-u (begin (cag-rr! (list '* cag-al cag-rho)) (dk-name! (list '* cag-al cag-rho))))
(define cag-ux (begin (cag-rr! (list '* cag-u cag-xv)) (dk-name! (list '* cag-u cag-xv))))
(define cag-sx (begin (cag-rr! (list '* cag-S cag-xv)) (dk-name! (list '* cag-S cag-xv))))
;; |top| = U X
(dk-have! (list '= cag-mt cag-ux)
  (lambda ()
    (subst (list '= cag-mt (list '* cag-al (list 'magnitude (list 'power cag-y cag-n)))))
    (subst (list '= (list 'magnitude (list 'power cag-y cag-n)) (list 'power cag-rho cag-n)))
    (subst (list '= (list 'power cag-rho cag-n) (list '* cag-rho cag-x)))
    (subst (list '= cag-x cag-xv))
    (subst (list '= cag-ux (list '* cag-u cag-xv)))
    (subst (list '= cag-u (list '* cag-al cag-rho)))
    (crs)))
;; |Q| <= S X
(dk-have! (list '<= cag-mq cag-sx)
  (lambda () (subst (list '= cag-sx (list '* cag-S cag-xv))) (subst (list '= cag-xv cag-x)) (ass)))
;; 2 S <= U, hence 2 S X <= U X
(dk-have! (list '<= (list '* 2 cag-S) cag-u)
  (lambda () (subst (list '= cag-u (list '* cag-al cag-rho))) (from-context!)))
(cag-rr! (list '* 2 cag-S))
(cag-and! (list '<= 0 cag-xv) (list '<= (list '* 2 cag-S) cag-u))
(dk-cite! 'rr-le-scale-nonneg cag-xv (list '* 2 cag-S) cag-u)
(cag-rr! (list '* cag-xv (list '* 2 cag-S)))
(cag-rr! (list '* cag-xv cag-u))
(dk-have! (list '= (list '* cag-xv (list '* 2 cag-S)) (list '* 2 cag-sx))
  (lambda () (subst (list '= cag-sx (list '* cag-S cag-xv))) (crs)))
(dk-have! (list '= (list '* cag-xv cag-u) cag-ux)
  (lambda () (subst (list '= cag-ux (list '* cag-u cag-xv))) (crs)))
;; |top| <= |P| + |-Q|
(dk-have! (list '<= cag-mt (list '+ cag-mp (list 'magnitude (list '- cag-qq))))
  (lambda () (subst (list '= cag-top (list '+ cag-pp (list '- cag-qq)))) (ass)))
;; the goal's left side is U X
(dk-have! (list '= (list '* cag-al (list 'power cag-rho cag-n)) cag-ux)
  (lambda ()
    (subst (list '= (list 'power cag-rho cag-n) (list '* cag-rho cag-x)))
    (subst (list '= cag-x cag-xv))
    (subst (list '= cag-ux (list '* cag-u cag-xv)))
    (subst (list '= cag-u (list '* cag-al cag-rho)))
    (crs)))
(cag-rr! (list '* cag-al (list 'power cag-rho cag-n)))
(dk-ineq! (list '= (list '* cag-al (list 'power cag-rho cag-n)) cag-ux)
          (list '= cag-mt cag-ux)
          (list '<= cag-mt (list '+ cag-mp (list 'magnitude (list '- cag-qq))))
          (list '= (list 'magnitude (list '- cag-qq)) cag-mq)
          (list '<= cag-mq cag-sx)
          (list '<= (list '* cag-xv (list '* 2 cag-S)) (list '* cag-xv cag-u))
          (list '= (list '* cag-xv (list '* 2 cag-S)) (list '* 2 cag-sx))
          (list '= (list '* cag-xv cag-u) cag-ux))
(qed 'cc-polynomial-lower-growth)

(topic! 'cc-algebraically-closed 'analysis)
(topic! 'cc-polynomial-lower-growth 'analysis)
(alias! 'cc-algebraically-closed "C is algebraically closed: a polynomial of degree n >= 1 has a root (Theorem 1.15)")
