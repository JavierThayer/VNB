;;; cps-taylor-coefficients.scm -- COROLLARY 2.14: THE TAYLOR COEFFICIENTS OF
;;; A COMPLEX POWER SERIES.  f^(k)(0) = k! a_k.
;;; Batch 27-A, 2026-09-24.
;;;
;;; THE SOURCE.  ~/docs/complex-analysis.pdf, 2.14 (p. 28): "If f is analytic at
;;; 0, f(z) = sum_k a_k z^k on a ball, then by 2.10 and induction f^(k)(0) =
;;; k! a_k, so that f(z) = sum_k f^(k)(0)/k! z^k."
;;;
;;; NO ITERATED DERIVATIVE.  The tree has no k-th derivative over CC (NTH-DERIV
;;; is RR -> RR; defining one over a normed field is the user's decision,
;;; pending), and this file defines nothing.  f^(k) is read as F_k, the sum
;;; function of the k-th DERIVED SERIES, whose coefficients are
;;;     g(n) = (n+k)!/n! * a_(n+k)          [the notes' k-fold termwise derivative]
;;; GIVEN BY THEIR VALUES (as cps-radius-derived does), never by a new functoid.
;;; With the convention of cc-power-series-deriv.scm for B(0, R) (every real r,
;;; 0 < r < R, on B(0, r)):
;;;   cps-kth-derived-step     the (k+1)-th sequence is the DERIVED sequence of
;;;                            the k-th in the sense of 2.10: h(n) = (n+1) g(n+1)
;;;   cps-kth-derived-radius   the k-th derived series has the radius of cf
;;;   cps-sum-at-zero          sum_n g(n) 0^n converges, to g(0)
;;;   cps-taylor-coefficients  (THE HEADLINE) F_k is holomorphic on B(0, r),
;;;                            F_k(0) = k! a_k, and DERIV-ON(F_k)(u) = F_(k+1)(u)
;;;                            at every u of B(0, r) -- so F_k IS the k-th
;;;                            derivative of F_0 = f, one DERIV-ON at a time
;;;   cps-coefficient-formula  a_k = F_k(0)/k!, the notes' "f(z) = sum_k
;;;                            f^(k)(0)/k! z^k" read coefficientwise
;;; The index arithmetic is NN: (n+1)+k is n+(k+1) by nn-add-succ / nn-add-comm,
;;; and the one factorial identity is tgd-recip-factorial-succ
;;; (1/n! = (n+1)/(n+1)!, theorem-library/taylor-proof.scm).
;;;
;;; NOTHING asserted: no support, stamp, axiom or definition.
;;; Helper prefix: ctc-.  Theorem binders ctc..._, and the binders of
;;; cc-power-series-deriv.scm (cpdr_, cpda_, cpdz_, cpsk_, cpdj_) where a
;;; conclusion must match one of its theorems literally.
;;; LOAD WINDOW: lo = theorem-library/cc-power-series-deriv (cps-radius-derived,
;;; cps-holomorphic-ball, cps-diff-on-ball, cpd-cc-squeeze); hi: none.

(define (ctc-head g) (and (pair? g) (car g)))
(define (ctc-op? t op n) (and (pair? t) (eq? (car t) op) (= (length t) n)))

;;; ---- typing of the coefficient terms ----------------------------------
(define (ctc-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! (lambda () (ass))))))
    f))
(define (ctc-nn-typ! t)
  (let ((typ (list 'IN t 'NN)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'nn-zero-in) typ)
          ((ctc-op? t 'succ 2) (ctc-nn-typ! (cadr t)) (fact 'nn-succ-closed (cadr t)) typ)
          ((ctc-op? t '+ 3) (ctc-nn-typ! (cadr t)) (ctc-nn-typ! (caddr t))
           (ctc-and! (list 'IN (cadr t) 'NN) (list 'IN (caddr t) 'NN))
           (fact 'nn-add-closed (cadr t) (caddr t)) typ)
          (#t (error "ctc-nn-typ!: cannot type" (expression->string t))))))
(define (ctc-real? t)
  (or (eqv? t 0) (eqv? t 1)
      (dk-asm? (list 'IN t 'RR)) (dk-asm? (list 'IN t 'NN))
      (ctc-op? t 'succ 2) (ctc-op? t 'FACTORIAL 2)
      (and (ctc-op? t 'recip 2) (ctc-op? (cadr t) 'FACTORIAL 2))
      (and (ctc-op? t '* 3) (ctc-real? (cadr t)) (ctc-real? (caddr t)))))
(define (ctc-rr-typ! t)
  (let ((typ (list 'IN t 'RR)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'rr-zero-in) typ)
          ((eqv? t 1) (fact 'rr-one-in) typ)
          ((ctc-op? t 'FACTORIAL 2)
           (ctc-nn-typ! (cadr t))
           (dk-split-all! (list (dk-fact! 'factorial-real-pos (cadr t)))) typ)
          ((or (dk-asm? (list 'IN t 'NN)) (ctc-op? t 'succ 2))
           (ctc-nn-typ! t) (fact 'nn-in-rr t) typ)
          ((and (ctc-op? t 'recip 2) (ctc-op? (cadr t) 'FACTORIAL 2))
           (ctc-nn-typ! (cadr (cadr t))) (fact 'recip-factorial-in-rr (cadr (cadr t))) typ)
          ((ctc-op? t '* 3) (ctc-rr-typ! (cadr t)) (ctc-rr-typ! (caddr t)) (fact 'rr-mul-in-rr (cadr t) (caddr t)) typ)
          (#t (error "ctc-rr-typ!: cannot type" (expression->string t))))))
(define (ctc-cc-typ! t)
  (let ((typ (list 'IN t 'CC)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'cc-zero-in) typ)
          ((ctc-real? t) (ctc-rr-typ! t) (fact 'rr-subset-cc t) typ)
          ((and (ctc-op? t 'cf 2)) (ctc-nn-typ! (cadr t)) (fact 'fun-apply-type-c 'cf 'NN 'CC (cadr t)) typ)
          ((and (pair? t) (= (length t) 2) (symbol? (car t)) (dk-asm? (list 'IN (car t) '(FUN NN CC))))
           (ctc-nn-typ! (cadr t)) (fact 'fun-apply-type-c (car t) 'NN 'CC (cadr t)) typ)
          ((ctc-op? t '* 3) (ctc-cc-typ! (cadr t)) (ctc-cc-typ! (caddr t))
           (ctc-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC)) (fact 'cc-mul-closed (cadr t) (caddr t)) typ)
          ((ctc-op? t '+ 3) (ctc-cc-typ! (cadr t)) (ctc-cc-typ! (caddr t))
           (ctc-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC)) (fact 'cc-add-closed (cadr t) (caddr t)) typ)
          ((ctc-op? t '- 3) (ctc-cc-typ! (cadr t)) (ctc-cc-typ! (caddr t)) (fact 'cc-sub-in-cc (cadr t) (caddr t)) typ)
          ((ctc-op? t 'power 3) (ctc-cc-typ! (cadr t)) (ctc-nn-typ! (caddr t))
           (ctc-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'NN)) (fact 'power-typing-nonneg (cadr t) (caddr t)) typ)
          (#t (error "ctc-cc-typ!: cannot type" (expression->string t))))))

;;; (IN LAM (FUN NN COD)) for LAM = (VNB-LAMBDA v NN body): TYPER gets the
;;; eigenvariable and must land the body's typing.
(define (ctc-lam-typ! lam cod typer)
  (let ((typ (list 'IN lam (list 'FUN 'NN cod))))
    (if (not (dk-asm? typ))
        (dk-have! typ
          (lambda ()
            (dk-lam-t!)
            (let ((j (dk-di-var!))) (typer j) (ass)))))
    typ))

;;; beta-reduce the focus goal; the reduct is a NEW node that becomes the focus
;;; while the worked leaf stays open, unless beta grounded it: run CLOSER then.
(define (ctc-beta! closer)
  (let ((leaf (proof-state-focus *ps*)))
    (dk-lam-b!)
    (if (not (sequent-node-grounded? leaf)) (closer))))

;;; A commutative-ring identity with opaque (recip-bearing) atoms: prove the
;;; identity BODY over fresh universally quantified complex variables VARS by
;;; crs on a lane, then instantiate it at TERMS (typed in CC first); returns the
;;; landed instance.
(define (ctc-ring-id! vars body terms)
  (let ((gen (let build ((vs vars))
               (if (null? vs) body
                   (list 'FORALL (car vs) (list 'IMPLIES (list 'IN (car vs) 'CC) (build (cdr vs))))))))
    (dk-have! gen (lambda () (dk-peel!) (crs)))
    (for-each ctc-cc-typ! terms)
    (apply dk-apply! gen terms)))

;;; the k-th derived coefficient: (n+k)!/n! * cf(n+k)
(define (ctc-coef n k)
  (list '* (list '* (list 'FACTORIAL (list '+ n k)) (list 'recip (list 'FACTORIAL n))) (list 'cf (list '+ n k))))
;;; "G is the k-th derived sequence of cf, given by its values"
(define (ctc-val g k)
  (list 'FORALL 'ctcn_ (list 'IMPLIES '(IN ctcn_ NN) (list '= (list g 'ctcn_) (ctc-coef 'ctcn_ k)))))
;;; the hypothesis of cps-radius-derived / cps-diff-on-ball: H is the derived sequence of G
(define (ctc-derived h g)
  (list 'FORALL 'cpdj_ (list 'IMPLIES '(IN cpdj_ NN)
    (list '= (list h 'cpdj_) (list '* '(succ cpdj_) (list g '(succ cpdj_)))))))

;;; ======================================================================
;;; (1) THE STEP.  If g, h are the k-th and (k+1)-th derived sequences of cf,
;;; then h(n) = (n+1) g(n+1): h is the derived sequence of g in the sense of 2.10.
;;;   (n+k+1)!/n! cf(n+k+1) = (n+1) . (n+1+k)!/(n+1)! cf(n+1+k)
;;; by n+(k+1) = succ(n+k) = (n+1)+k and 1/n! = (n+1)/(n+1)!.
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'ctck_ (list 'IMPLIES '(IN ctck_ NN)
      (list 'FORALL 'ctcg_ (list 'IMPLIES '(IN ctcg_ (FUN NN CC))
        (list 'FORALL 'ctch_ (list 'IMPLIES '(IN ctch_ (FUN NN CC))
          (list 'IMPLIES (ctc-val 'ctcg_ 'ctck_)
            (list 'IMPLIES (ctc-val 'ctch_ '(succ ctck_))
              (ctc-derived 'ctch_ 'ctcg_)))))))))))))
(dk-peel!)
(define ctc-st-j (cadr (cadr (dk-goal))))
(define ctc-st-sj (list 'succ ctc-st-j))
(define ctc-st-m (list '+ ctc-st-j 'ctck_))
(define ctc-st-sm (list 'succ ctc-st-m))
(ctc-nn-typ! ctc-st-sj)
(ctc-nn-typ! '(succ ctck_))
(define ctc-st-vg (dk-pick (lambda (f) (alpha-equiv? f (ctc-val 'ctcg_ 'ctck_))) "the values of g"))
(define ctc-st-vh (dk-pick (lambda (f) (alpha-equiv? f (ctc-val 'ctch_ '(succ ctck_)))) "the values of h"))
(define ctc-st-eh (dk-deepest (lambda () (inst+ ctc-st-vh ctc-st-j))))
(define ctc-st-eg (dk-deepest (lambda () (inst+ ctc-st-vg ctc-st-sj))))
(subst ctc-st-eh)
(subst ctc-st-eg)
;; the indices: j + succ(k) = succ(j + k) = succ(j) + k
(subst (dk-fact! 'nn-add-succ ctc-st-j 'ctck_))
(ctc-and! (list 'IN ctc-st-sj 'NN) '(IN ctck_ NN))
(subst (dk-fact! 'nn-add-comm ctc-st-sj 'ctck_))
(subst (dk-fact! 'nn-add-succ 'ctck_ ctc-st-j))
(ctc-and! '(IN ctck_ NN) (list 'IN ctc-st-j 'NN))
(subst (dk-fact! 'nn-add-comm 'ctck_ ctc-st-j))
;; 1/j! = (j+1) . 1/(j+1)!
(subst (dk-fact! 'tgd-recip-factorial-succ ctc-st-j))
(ctc-nn-typ! ctc-st-sm)
(define ctc-st-id
  (ctc-ring-id! '(ctca_ ctcb_ ctcc_ ctcd_)
    '(= (* (* ctca_ (* ctcb_ ctcc_)) ctcd_) (* ctcb_ (* (* ctca_ ctcc_) ctcd_)))
    (list (list 'FACTORIAL ctc-st-sm) ctc-st-sj (list 'recip (list 'FACTORIAL ctc-st-sj)) (list 'cf ctc-st-sm))))
(ass)
(qed 'cps-kth-derived-step)

;;; ======================================================================
;;; (2) THE RADIUS.  The k-th derived series has the radius of cf: induction on
;;; k through cps-radius-derived; k = 0 is g = cf pointwise, hence g = cf by
;;; function extensionality.
;;; ======================================================================
(define (ctc-fun-dom! f)
  (dk-have! (list 'IN f '(FUN NN))
    (lambda ()
      (mac-h 'fun-codomain-iff (list 'IN f '(FUN NN CC)))
      (dk-split-all!)
      (ass))))
(define ctc-rd-claim
  (list 'FORALL 'ctcm_ (list 'IMPLIES '(IN ctcm_ NN)
    (list 'FORALL 'ctcq_ (list 'IMPLIES '(IN ctcq_ (FUN NN CC))
      (list 'IMPLIES (ctc-val 'ctcq_ 'ctcm_) '(= (CPS-RADIUS ctcq_) (CPS-RADIUS cf))))))))
(sp (make-wff
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'ctck_ (list 'IMPLIES '(IN ctck_ NN)
      (list 'FORALL 'ctcg_ (list 'IMPLIES '(IN ctcg_ (FUN NN CC))
        (list 'IMPLIES (ctc-val 'ctcg_ 'ctck_) '(= (CPS-RADIUS ctcg_) (CPS-RADIUS cf)))))))))))
(dk-peel!)
(fact 'cps-radius-in 'cf)
(dk-have! ctc-rd-claim
  (lambda ()
    (let* ((br (use-induction))
           (m (cdr (assq 'var br)))
           (ih (cdr (assq 'ih br)))
           (step (cdr (assq 'step br))))
      ;; k = 0: q = cf
      (dk-focus! (cdr (assq 'base br)))
      (dk-peel!)
      (let* ((q (cadr (cadr (dk-goal))))
             (vq (dk-pick (lambda (f) (alpha-equiv? f (ctc-val q 0))) "the values of q"))
             (eqn (list '= q 'cf)))
        (ctc-fun-dom! q)
        (ctc-fun-dom! 'cf)
        (dk-have! eqn
          (lambda ()
            (let ((ch (dk-fact! 'fun-domain-extensionality 'NN q 'cf))
                  (fa (list 'FORALL 'ctcz_ (list 'IMPLIES '(IN ctcz_ NN) (list '= (list q 'ctcz_) '(cf ctcz_))))))
              (dk-have! fa
                (lambda ()
                  (let ((v (dk-di-var!)))
                    (subst (dk-deepest (lambda () (inst+ vq v))))
                    (subst (dk-fact! 'nn-add-zero v))
                    (subst (dk-fact! 'rr-recip-factorial v))
                    (ctc-cc-typ! (list 'cf v))
                    (crs))))
              (detach! ch)
              (ass))))
        (subst eqn)
        (rfl))
      ;; k -> k + 1: g0, the k-th sequence, as a lambda; its successor is q
      (dk-focus! step)
      (dk-peel!)
      (let* ((q (cadr (cadr (dk-goal))))
             (g0 (list 'VNB-LAMBDA 'ctcv_ 'NN (ctc-coef 'ctcv_ m))))
        (ctc-lam-typ! g0 'CC (lambda (v) (ctc-cc-typ! (ctc-coef v m))))
        (dk-have! (ctc-val g0 m)
          (lambda ()
            (let ((v (dk-di-var!)))
              (ctc-cc-typ! (ctc-coef v m))
              (ctc-beta! (lambda () (rfl))))))
        (let ((rg0 (dk-apply! ih g0)))
          (dk-fact! 'cps-kth-derived-step 'cf m g0 q)
          (let ((rq (dk-fact! 'cps-radius-derived g0 q)))
            (subst rq)
            (subst rg0)
            (rfl)))))))
(dk-apply! ctc-rd-claim 'ctck_ 'ctcg_)
(ass)
(qed 'cps-kth-derived-radius)

;;; ======================================================================
;;; (3) THE SUM AT 0.  sum_n g(n) 0^n is g(0), 0, 0, ...: its partial sums are
;;; g(0) from index 1 on, so they are within |g(0)| 0^n of g(0), which tends
;;; to 0 (cpd-cc-squeeze).
;;; ======================================================================
(define (ctc-t0 g) (list 'VNB-LAMBDA 'cpsk_ 'NN (list '* (list g 'cpsk_) '(power 0 cpsk_))))
(sp (make-wff
  (list 'FORALL 'ctcg_ (list 'IMPLIES '(IN ctcg_ (FUN NN CC))
    (list 'AND (list 'CC-SERIES-CONVERGES (ctc-t0 'ctcg_))
               (list '= (list 'CC-SERIES-LIMIT (ctc-t0 'ctcg_)) '(ctcg_ 0)))))))
(dk-peel!)
(define ctc-sz-t (cadr (cadr (dk-goal))))
(define ctc-sz-g0 (caddr (caddr (dk-goal))))
(define ctc-sz-g (car ctc-sz-g0))
(fact 'cc-zero-in)
(fact 'nn-zero-in)
(ctc-cc-typ! ctc-sz-g0)
(ctc-lam-typ! ctc-sz-t 'CC (lambda (v) (ctc-cc-typ! (list '* (list ctc-sz-g v) (list 'power 0 v)))))
(define (ctc-sz-ps! k)          ; S(T, k) and T(k) typed in CC
  (ctc-nn-typ! k)
  (fact 'cc-series-partial-sum-in-cc k ctc-sz-t)
  (fact 'fun-apply-type-c ctc-sz-t 'NN 'CC k))
;; the partial sums are g(0) from index 1 on
(define ctc-sz-claim
  (list 'FORALL 'ctcm_ (list 'IMPLIES '(IN ctcm_ NN)
    (list '= (list 'CC-SERIES-PARTIAL-SUM ctc-sz-t '(succ ctcm_)) ctc-sz-g0))))
(dk-have! ctc-sz-claim
  (lambda ()
    (let* ((br (use-induction))
           (v (cdr (assq 'var br)))
           (ih (cdr (assq 'ih br)))
           (step (cdr (assq 'step br))))
      (dk-focus! (cdr (assq 'base br)))
      (ctc-sz-ps! 0)
      (subst (dk-fact! 'cc-series-partial-sum-succ ctc-sz-t 0))
      (subst (dk-fact! 'cc-series-partial-sum-zero ctc-sz-t))
      (ctc-beta!
        (lambda ()
          (subst (dk-fact! 'power-zero 0))
          (crs)))
      (dk-focus! step)
      (let ((sv (list 'succ v)))
        (ctc-sz-ps! sv)
        (ctc-cc-typ! (list ctc-sz-g sv))
        (subst (dk-fact! 'cc-series-partial-sum-succ ctc-sz-t sv))
        (subst ih)
        (ctc-beta!
          (lambda ()
            (subst (dk-fact! 'power-zero-base v))
            (crs)))))))
;; the partial-sum sequence P, read off the definition's instance
(define ctc-sz-iff (dk-fact! 'cc-series-converges-to ctc-sz-t ctc-sz-g0))
(define ctc-sz-p (caddr (caddr ctc-sz-iff)))
(ctc-lam-typ! ctc-sz-p 'CC (lambda (v) (fact 'cc-series-partial-sum-in-cc v ctc-sz-t)))
;; the bound M(j) = 0^j |g(0)| tends to 0
(define ctc-sz-b (list 'magnitude ctc-sz-g0))
(define ctc-sz-mm (list 'VNB-LAMBDA 'ctcj_ 'NN (list '* '(power 0 ctcj_) ctc-sz-b)))
(fact 'rr-zero-in)
(fact 'cc-magnitude-closed ctc-sz-g0)
(fact 'cc-magnitude-nonneg ctc-sz-g0)
(ctc-lam-typ! ctc-sz-mm 'RR
  (lambda (v) (fact 'power-real-closed 0 v) (fact 'rr-mul-in-rr (list 'power 0 v) ctc-sz-b)))
(dk-have! '(AND (IN 0 RR) (< (abs 0) 1))
  (lambda ()
    (dk-conj-close!
      (lambda ()
        (if (dk-head-is? (dk-goal) 'IN)
            (ass)
            (begin (subst (dk-fact! 'rr-abs-zero-value)) (dk-ineq!)))))))
(define ctc-sz-gz (dk-fact! 'power-tends-to-zero 0))
(define ctc-sz-geo (caddr ctc-sz-gz))
(ctc-lam-typ! ctc-sz-geo 'RR (lambda (v) (fact 'power-real-closed 0 v)))
(dk-have! (list 'FORALL 'ctcj_ (list 'IMPLIES '(IN ctcj_ NN)
            (list '= (list ctc-sz-mm 'ctcj_) (list '* (list ctc-sz-geo 'ctcj_) ctc-sz-b))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (fact 'power-real-closed 0 v)
      (ctc-beta! (lambda () (fact 'rr-mul-in-rr (list 'power 0 v) ctc-sz-b) (rfl))))))
(define ctc-sz-lim0 (dk-fact! 'rr-limit-scale ctc-sz-b ctc-sz-geo ctc-sz-mm 0))
(define ctc-sz-zero
  '(FORALL ctcw_ (IMPLIES (IN ctcw_ (FUN NN RR)) (FORALL ctcb_ (IMPLIES (IN ctcb_ RR)
     (IMPLIES (CONVERGES-TO RR-MS ctcw_ (* 0 ctcb_)) (CONVERGES-TO RR-MS ctcw_ 0)))))))
(dk-have! ctc-sz-zero
  (lambda ()
    (dk-peel!)
    (dk-have! '(= (* 0 ctcb_) 0) (lambda () (dk-ineq!)))
    (subst '(= 0 (* 0 ctcb_)))
    (ass)))
(dk-apply! ctc-sz-zero ctc-sz-mm ctc-sz-b)
;; |P(j) - g(0)| <= M(j)
(dk-have! (list 'FORALL 'cpdj_ (list 'IMPLIES '(IN cpdj_ NN)
            (list '<= (list 'magnitude (list '- (list ctc-sz-p 'cpdj_) ctc-sz-g0)) (list ctc-sz-mm 'cpdj_))))
  (lambda ()
    (let ((j (dk-di-var!)))
      (fact 'power-real-closed 0 j)
      (ctc-beta!
        (lambda ()
          (let ((cases (dk-fact! 'nn-zero-or-succ j)))
            (use-cases cases
              (lambda ()
                (subst (list '= j 0))
                (subst (dk-fact! 'cc-series-partial-sum-zero ctc-sz-t))
                (subst (dk-fact! 'power-zero 0))
                (fact 'cc-neg-closed ctc-sz-g0)
                (dk-have! (list '= (list '- 0 ctc-sz-g0) (list '- ctc-sz-g0)) (lambda () (crs)))
                (subst (list '= (list '- 0 ctc-sz-g0) (list '- ctc-sz-g0)))
                (subst (dk-fact! 'cc-magnitude-neg ctc-sz-g0))
                (dk-ineq!))
              (lambda ()
                (let ((q (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the predecessor"))))
                  (subst (list '= j (list 'succ q)))
                  (subst (dk-deepest (lambda () (inst+ ctc-sz-claim q))))
                  (dk-have! (list '= (list '- ctc-sz-g0 ctc-sz-g0) 0) (lambda () (crs)))
                  (subst (list '= (list '- ctc-sz-g0 ctc-sz-g0) 0))
                  (subst (dk-fact! 'cc-magnitude-zero))
                  (subst (dk-fact! 'power-zero-base q))
                  (dk-ineq!))))))))))
(define ctc-sz-cv (dk-fact! 'cpd-cc-squeeze ctc-sz-p ctc-sz-g0 ctc-sz-mm))
(dk-have! (list 'CC-SERIES-CONVERGES-TO ctc-sz-t ctc-sz-g0)
  (lambda () (mac 'cc-series-converges-to) (ass)))
(dk-have! (list 'CC-SERIES-CONVERGES ctc-sz-t)
  (lambda () (mac 'cc-series-converges) (mac 'converges) (ew ctc-sz-g0) (ass)))
(define ctc-sz-l (list 'CC-SERIES-LIMIT ctc-sz-t))
(fact 'cc-series-limit-converges-to ctc-sz-t)
(fact 'cc-series-limit-in-cc ctc-sz-t)
(dk-have! (list 'CONVERGES-TO 'CC-MS ctc-sz-p ctc-sz-l)
  (lambda () (mac-h 'cc-series-converges-to (list 'CC-SERIES-CONVERGES-TO ctc-sz-t ctc-sz-l)) (ass)))
(fact 'cc-limit-unique ctc-sz-p ctc-sz-l ctc-sz-g0)
(dk-conj-close! (lambda () (ass)))
(qed 'cps-sum-at-zero)

;;; ======================================================================
;;; (4) COROLLARY 2.14.  F_k = z |-> sum_n g(n) z^n, g the k-th derived
;;; sequence of cf, is holomorphic on B(0, r) for 0 < r < R, F_k(0) = k! a_k,
;;; and its derivative on B(0, r) is F_(k+1).  The derivative is DERIV-ON, the
;;; IOTA of IS-DIFF-ON, read off by iota-d and diff-on-unique.
;;; ======================================================================
(define ctc-B '(BALL CC-MS 0 cpdr_))
(define (ctc-F g)
  (list 'VNB-LAMBDA 'cpdz_ ctc-B
    (list 'CC-SERIES-LIMIT (list 'VNB-LAMBDA 'cpsk_ 'NN (list '* (list g 'cpsk_) '(power cpdz_ cpsk_))))))
(define (ctc-detach-all! ch)
  (let loop ((c ch))
    (if (eq? (ctc-head c) 'IMPLIES)
        (loop (detach-with! c (lambda () (dk-conj-close! (lambda () (ass))))))
        c)))
;;; 0 < cpdr_ in context: the ball B(0, r) is a set and contains 0
(define (ctc-ball-setup!)
  (fact 'cc-is-metric-space)
  (if (not (dk-asm? '(== (PTS CC-MS) CC)))
      (dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl))))
  (fact 'cc-zero-in)
  (fact 'nn-zero-in)
  (fact 'rr-zero-in)
  (dk-have! '(IN 0 (PTS CC-MS)) (lambda () (subst '(== (PTS CC-MS) CC)) (ass)))
  (fact 'rr-lt-implies-le 0 'cpdr_)
  (fact 'rr-pos-ne-zero 'cpdr_)
  (fact 'neq-sym 'cpdr_ 0)
  (fact 'ball-is-set 'CC-MS 0 'cpdr_)
  (if (not (dk-asm? (list 'IN 0 ctc-B)))
      (ctc-detach-all! (dk-fact! 'ball-center-in 'CC-MS 0 'cpdr_))))
;;; rewrite g(0) in the goal to k! cf(k), from the values of g (k = ctck_)
(define (ctc-g0-value! g)
  (let ((vg (dk-pick (lambda (f) (alpha-equiv? f (ctc-val g 'ctck_))) "the values of g")))
    (subst (dk-deepest (lambda () (inst+ vg 0))))
    (ctc-and! '(IN 0 NN) '(IN ctck_ NN))
    (subst (dk-fact! 'nn-add-comm 0 'ctck_))
    (subst (dk-fact! 'nn-add-zero 'ctck_))
    (subst (dk-fact! 'factorial-zero))
    (fact 'nn-one-is-succ-zero)
    (subst '(= (succ 0) 1))
    (subst (dk-fact! 'rr-recip-one))
    (ctc-cc-typ! '(FACTORIAL ctck_))
    (ctc-cc-typ! '(cf ctck_))))

(sp (make-wff
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'ctck_ (list 'IMPLIES '(IN ctck_ NN)
      (list 'FORALL 'ctcg_ (list 'IMPLIES '(IN ctcg_ (FUN NN CC))
        (list 'FORALL 'ctch_ (list 'IMPLIES '(IN ctch_ (FUN NN CC))
          (list 'IMPLIES (ctc-val 'ctcg_ 'ctck_)
            (list 'IMPLIES (ctc-val 'ctch_ '(succ ctck_))
              (list 'FORALL 'cpdr_ (list 'IMPLIES '(IN cpdr_ RR) (list 'IMPLIES '(< 0 cpdr_)
                (list 'IMPLIES '(< cpdr_ (CPS-RADIUS cf))
                  (list 'AND (list 'HOLOMORPHIC-ON ctc-B (ctc-F 'ctcg_))
                    (list 'AND (list '= (list (ctc-F 'ctcg_) 0) '(* (FACTORIAL ctck_) (cf ctck_)))
                      (list 'FORALL 'cpda_ (list 'IMPLIES (list 'IN 'cpda_ ctc-B)
                        (list '= (list 'DERIV-ON 'CC-NORMED-FIELD ctc-B (ctc-F 'ctcg_) 'cpda_)
                                 (list (ctc-F 'ctch_) 'cpda_))))))))))))))))))))))
(dk-peel!)
(define ctc-tc-fg (ctc-F 'ctcg_))
(ctc-ball-setup!)
(dk-fact! 'cps-kth-derived-radius 'cf 'ctck_ 'ctcg_)
(dk-have! '(< cpdr_ (CPS-RADIUS ctcg_)) (lambda () (subst '(= (CPS-RADIUS ctcg_) (CPS-RADIUS cf))) (ass)))
(dk-split-all! (list (dk-fact! 'cps-holomorphic-ball 'ctcg_ 'cpdr_)))
(dk-fact! 'cps-kth-derived-step 'cf 'ctck_ 'ctcg_ 'ctch_)
(define ctc-tc-dd (dk-fact! 'cps-diff-on-ball 'ctcg_ 'ctch_ 'cpdr_))
(fact 'cc-is-normed-field)
(fact 'cc-nf-small-elements)
(define ctc-tc-uq
  (let ((c (dk-fact! 'diff-on-unique 'CC-NORMED-FIELD)))
    (if (eq? (ctc-head c) 'IMPLIES) (dk-landed-1 (lambda () (detach! c))) c)))
;;; (IN T (CARR CC-NORMED-FIELD)) from the IS-DIFF-ON at T in context, on a lane
(define (ctc-diff-typ! u t)
  (let ((pd (list 'IS-DIFF-ON 'CC-NORMED-FIELD ctc-B ctc-tc-fg u t)))
    (dk-have! (list 'IN t '(CARR CC-NORMED-FIELD))
      (lambda () (mac-h 'IS-DIFF-ON (dk-ctx-form pd)) (dk-split-all!) (ass)))))
(dk-conj-close!
  (lambda ()
    (let ((gl (dk-goal)))
      (cond
        ((dk-head-is? gl 'HOLOMORPHIC-ON) (ass))
        ((dk-head-is? gl '=)
         (ctc-beta!
           (lambda ()
             (dk-split-all! (list (dk-fact! 'cps-sum-at-zero 'ctcg_)))
             (subst (list '= (list 'CC-SERIES-LIMIT (ctc-t0 'ctcg_)) '(ctcg_ 0)))
             (ctc-g0-value! 'ctcg_)
             (crs))))
        (#t
         (let* ((u (dk-di-var!))
                (pd (dk-deepest (lambda () (inst+ ctc-tc-dd u))))
                (lv (list-ref pd 5)))
           (ctc-diff-typ! u lv)
           (ctc-beta!
             (lambda ()
               (mac 'DERIV-ON)
               (let ((iot (cadr (dk-goal))))
                 (for-each
                   (lambda (leaf)
                     (dk-focus! leaf)
                     (if (dk-head-is? (dk-goal) 'FORSOME)
                         (begin
                           (ew lv)
                           (dk-conj-close!
                             (lambda ()
                               (if (dk-head-is? (dk-goal) 'FORALL)
                                   (begin
                                     (dk-peel!)
                                     (let ((y (caddr (dk-goal))))
                                       (ctc-diff-typ! u y)
                                       (dk-apply! ctc-tc-uq ctc-B ctc-tc-fg u lv y)
                                       (ass)))
                                   (ass)))))
                         (begin
                           (ctc-diff-typ! u iot)
                           (dk-apply! ctc-tc-uq ctc-B ctc-tc-fg u iot lv)
                           (ass))))
                   (dk-opened (lambda () (iota-d iot)))))))))))))
(qed 'cps-taylor-coefficients)

;;; ======================================================================
;;; (5) THE COEFFICIENT FORMULA: a_k = F_k(0)/k!, the notes' "f(z) = sum_k
;;; f^(k)(0)/k! z^k" read coefficientwise.  Only 0 < r is needed (0 in B(0, r)).
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'ctck_ (list 'IMPLIES '(IN ctck_ NN)
      (list 'FORALL 'ctcg_ (list 'IMPLIES '(IN ctcg_ (FUN NN CC))
        (list 'IMPLIES (ctc-val 'ctcg_ 'ctck_)
          (list 'FORALL 'cpdr_ (list 'IMPLIES '(IN cpdr_ RR) (list 'IMPLIES '(< 0 cpdr_)
            (list '= '(cf ctck_) (list '* (list (ctc-F 'ctcg_) 0) '(recip (FACTORIAL ctck_))))))))))))))))
(dk-peel!)
(ctc-ball-setup!)
(ctc-beta!
  (lambda ()
    (dk-split-all! (list (dk-fact! 'cps-sum-at-zero 'ctcg_)))
    (subst (list '= (list 'CC-SERIES-LIMIT (ctc-t0 'ctcg_)) '(ctcg_ 0)))
    (ctc-g0-value! 'ctcg_)
    (subst (ctc-ring-id! '(ctca_ ctcc_ ctcd_)
             '(= (* (* (* ctca_ 1) ctcc_) ctcd_) (* ctcc_ (* ctca_ ctcd_)))
             (list '(FACTORIAL ctck_) '(cf ctck_) '(recip (FACTORIAL ctck_)))))
    (subst (dk-fact! 'rr-recip-factorial 'ctck_))
    (crs)))
(qed 'cps-coefficient-formula)
