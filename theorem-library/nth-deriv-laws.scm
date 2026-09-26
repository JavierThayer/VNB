;;; nth-deriv-laws.scm -- THE LAWS OF NTH-DERIV-ON, AND COROLLARY 2.14 RESTATED
;;; LITERALLY: f^(k)(0) = k! a_k.
;;; Batch 36, 2026-09-26.
;;;
;;; NTH-DERIV-ON(K, U, f, k) is defined in structure-library/nth-deriv.scm by
;;; def-by-nn-recursion; its two recursion equations nth-deriv-on-zero and
;;; nth-deriv-on-succ are installed THERE, as definitional theorems (so `mac-h'
;;; and `fact' reach them by name, which a def-functoid's macete does not).
;;;
;;; GENERAL LAWS (any normed field K whose norm has nonzero elements of
;;; arbitrarily small norm -- the antecedent exactly as diff-on-unique and
;;; deriv-on-of-is-diff-on state it, binders d2e_ / d2h_, so it detaches
;;; literally; RR and CC have it: rr-nf-small-elements, cc-nf-small-elements):
;;;   nth-deriv-on-succ-apply       NTH-DERIV-ON(K,U,f,succ j)(z) == DERIV-ON(K,U,NTH-DERIV-ON(K,U,f,j),z)
;;;                                 for z in U (no hypothesis on K: `==')
;;;   nth-deriv-on-of-is-diff-on    if IS-DIFF-ON(K,U,NTH-DERIV-ON(K,U,f,j),z,g(z)) at every z of U,
;;;                                 then NTH-DERIV-ON(K,U,f,succ j)(z) = g(z) on U
;;;   nth-deriv-on-succ-eq          the same, as functions, when g in FUN(U, CARR K)
;;;   nth-deriv-on-in-fun           f in FUN(U, CARR K) and every NTH-DERIV-ON(K,U,f,i), i < j,
;;;                                 differentiable at every point of U => NTH-DERIV-ON(K,U,f,j) in FUN(U, CARR K)
;;;
;;; OVER CC, THE POWER SERIES (27-A's reading, cps-taylor-coefficients.scm):
;;; V(g, k) = "g is the k-th derived sequence of cf, given by its values",
;;;   forall n in NN. g(n) = ((n+k)! * recip(n!)) * cf(n+k),
;;; and F_g = vnb-lambda(cpdz_, B(0, r), cc-series-limit(vnb-lambda(cpsk_, nn, g(cpsk_) * cpdz_^cpsk_))),
;;; spelled EXACTLY as 27-A spells it (ball binder cpdr_):
;;;   cps-nth-deriv                 0 < r < R(cf), V(g, k) => NTH-DERIV-ON(CC-NF, B(0,r), F_cf, k) = F_g
;;;                                 (induction on k; the step is cps-taylor-coefficients' third conjunct)
;;;   taylor-coefficients           THE NOTES' 2.14, LITERALLY: 0 < r < R(cf) =>
;;;                                 forall k in NN. NTH-DERIV-ON(CC-NF, B(0,r), F_cf, k)(0) = k! * cf(k)
;;;   taylor-coefficient-formula    ... cf(k) = NTH-DERIV-ON(CC-NF, B(0,r), F_cf, k)(0) * recip(k!)
;;;   nth-deriv-on-holomorphic-ball ... each NTH-DERIV-ON(CC-NF, B(0,r), F_cf, k) is holomorphic on B(0,r)
;;;
;;; NOTHING asserted: no support, stamp, axiom or definition (the one definition
;;; is in structure-library/nth-deriv.scm).  Helper prefix: ndl-.  Theorem
;;; binders ndl..._; the binders of cps-taylor-coefficients.scm / cc-power-series-
;;; deriv.scm (ctcn_, cpdr_, cpdz_, cpsk_, cpda_) where a term must match 27-A's.
;;; LOAD WINDOW: lo = theorem-library/cps-taylor-coefficients (cps-taylor-coefficients,
;;; cps-coefficient-formula, cps-kth-derived-radius); the general laws alone need only
;;; theorem-library/deriv-on-read-off (deriv-on-of-is-diff-on).  hi: none.

(define (ndl-head g) (and (pair? g) (car g)))
(define (ndl-op? t op n) (and (pair? t) (eq? (car t) op) (= (length t) n)))

;;; the non-triviality of K's norm, exactly as diff-on-unique states it
(define (ndl-small k)
  (list 'FORALL 'd2e_
    (list 'IMPLIES '(POS-RR d2e_)
      (list 'FORSOME 'd2h_
        (list 'AND (list 'IN 'd2h_ (list 'CARR k))
          (list 'AND (list 'NOT (list '= 'd2h_ (list 'ZERO k)))
                     (list '< (list (list 'FNRM k) 'd2h_) 'd2e_)))))))
(define (ndl-nd k u f j) (list 'NTH-DERIV-ON k u f j))

;;; deriv-on-of-is-diff-on detached at K (normed field, small elements in context):
;;; forall U f a L. IS-DIFF-ON(K,U,f,a,L) => DERIV-ON(K,U,f,a) = L
(define (ndl-dro! k)
  (let loop ((c (dk-fact! 'deriv-on-of-is-diff-on k)))
    (if (dk-head-is? c 'IMPLIES) (loop (dk-landed-1 (lambda () (detach! c)))) c)))
;;; (IN T (CARR K)) off the IS-DIFF-ON(K, U, F, A, T) in context, on a lane
(define (ndl-diff-typ! pd)
  (let ((k (list-ref pd 1)) (t (list-ref pd 5)))
    (dk-have! (list 'IN t (list 'CARR k))
      (lambda ()
        (mac-h 'IS-DIFF-ON (dk-ctx-form pd))
        (dk-split-all!)
        (ass)))))

;;; ======================================================================
;;; (1) THE SUCCESSOR, APPLIED.  NTH-DERIV-ON(K,U,f,succ j)(z) == DERIV-ON(K,U,
;;; NTH-DERIV-ON(K,U,f,j),z) at z in U: the unfold, then beta.
;;; ======================================================================
(sp (make-wff
  '(FORALL ndlkf_ (FORALL ndlu_ (FORALL ndlf_
     (FORALL ndlj_ (IMPLIES (IN ndlj_ NN)
       (FORALL ndlz_ (IMPLIES (IN ndlz_ ndlu_)
         (== ((NTH-DERIV-ON ndlkf_ ndlu_ ndlf_ (succ ndlj_)) ndlz_)
             (DERIV-ON ndlkf_ ndlu_ (NTH-DERIV-ON ndlkf_ ndlu_ ndlf_ ndlj_) ndlz_)))))))))))
(dk-peel!)
(mac 'nth-deriv-on-succ)
(let ((leaf (proof-state-focus *ps*)))
  (dk-lam-b!)
  (if (not (sequent-node-grounded? leaf)) (qrfl)))
(qed 'nth-deriv-on-succ-apply)

;;; ======================================================================
;;; (2) THE SUCCESSOR READ OFF A DERIVATIVE.  If the j-th derivative has
;;; derivative g(z) at every z of U, the (j+1)-th derivative is g on U.
;;; ======================================================================
(define (ndl-diff-hyp k u f j g)
  (list 'FORALL 'ndlz_ (list 'IMPLIES (list 'IN 'ndlz_ u)
    (list 'IS-DIFF-ON k u (ndl-nd k u f j) 'ndlz_ (list g 'ndlz_)))))
(sp (make-wff
  (list 'FORALL 'ndlkf_ (list 'IMPLIES '(IS-NORMED-FIELD ndlkf_)
    (list 'IMPLIES (ndl-small 'ndlkf_)
      (list 'FORALL 'ndlu_ (list 'FORALL 'ndlf_
        (list 'FORALL 'ndlj_ (list 'IMPLIES '(IN ndlj_ NN)
          (list 'FORALL 'ndlg_
            (list 'IMPLIES (ndl-diff-hyp 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ 'ndlg_)
              (list 'FORALL 'ndlw_ (list 'IMPLIES '(IN ndlw_ ndlu_)
                (list '= (list (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ '(succ ndlj_)) 'ndlw_) '(ndlg_ ndlw_)))))))))))))))
(dk-peel!)
(define ndl-dh-w (cadr (caddr (dk-goal))))
(define ndl-dh-hyp (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (alpha-equiv? f (ndl-diff-hyp 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ 'ndlg_)))) "the derivative hypothesis"))
(define ndl-dh-pd (dk-deepest (lambda () (inst+ ndl-dh-hyp ndl-dh-w))))
(define ndl-dh-d (ndl-dro! 'ndlkf_))
(dk-apply! ndl-dh-d 'ndlu_ (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_) ndl-dh-w (list 'ndlg_ ndl-dh-w))
(subst (dk-cite! 'nth-deriv-on-succ-apply 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ ndl-dh-w))
(ass)
(qed 'nth-deriv-on-of-is-diff-on)

;;; ======================================================================
;;; (3) THE SAME AS FUNCTIONS, when g is a function on U: function
;;; extensionality (dk-fun-ext!), the (j+1)-th derivative typed by lam-t
;;; through the derivative's read-off.
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'ndlkf_ (list 'IMPLIES '(IS-NORMED-FIELD ndlkf_)
    (list 'IMPLIES (ndl-small 'ndlkf_)
      (list 'FORALL 'ndlu_ (list 'FORALL 'ndlf_
        (list 'FORALL 'ndlj_ (list 'IMPLIES '(IN ndlj_ NN)
          (list 'FORALL 'ndlg_ (list 'IMPLIES '(IN ndlg_ (FUN ndlu_ (CARR ndlkf_)))
            (list 'IMPLIES (ndl-diff-hyp 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ 'ndlg_)
              (list '= (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ '(succ ndlj_)) 'ndlg_)))))))))))))
(dk-peel!)
(define ndl-se-lhs (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ '(succ ndlj_)))
(define ndl-se-hyp (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (alpha-equiv? f (ndl-diff-hyp 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ 'ndlg_)))) "the derivative hypothesis"))
(define ndl-se-d (ndl-dro! 'ndlkf_))
(fact 'fun-domain-in-set 'ndlu_ '(CARR ndlkf_) 'ndlg_)
(dk-fun-ext! ndl-se-lhs 'ndlg_ 'ndlu_ '(CARR ndlkf_)
  (lambda ()
    (mac 'nth-deriv-on-succ)
    (dk-lam-type!
      (lambda ()
        (let* ((v (dk-di-var!))
               (pd (dk-deepest (lambda () (inst+ ndl-se-hyp v)))))
          (subst (dk-apply! ndl-se-d 'ndlu_ (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_) v (list 'ndlg_ v)))
          (fact 'fun-apply-type-c 'ndlg_ 'ndlu_ '(CARR ndlkf_) v)
          (ass)))
      (lambda () (ass))))
  #f
  (lambda (v)
    (dk-cite! 'nth-deriv-on-of-is-diff-on 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_ 'ndlg_ v)
    (ass)))
(qed 'nth-deriv-on-succ-eq)

;;; ======================================================================
;;; (4) THE k-TH DERIVATIVE IS A FUNCTION ON U, provided f is one and every
;;; lower derivative is differentiable at every point of U.  k = 0 is f; k =
;;; succ q is a lambda over U whose values are the derivatives of the q-th.
;;; ======================================================================
(sp (make-wff
  (list 'FORALL 'ndlkf_ (list 'IMPLIES '(IS-NORMED-FIELD ndlkf_)
    (list 'IMPLIES (ndl-small 'ndlkf_)
      (list 'FORALL 'ndlu_ (list 'FORALL 'ndlf_ (list 'IMPLIES '(IN ndlf_ (FUN ndlu_ (CARR ndlkf_)))
        (list 'FORALL 'ndlj_ (list 'IMPLIES '(IN ndlj_ NN)
          (list 'IMPLIES
            (list 'FORALL 'ndli_ (list 'IMPLIES '(IN ndli_ NN) (list 'IMPLIES '(< ndli_ ndlj_)
              (list 'FORALL 'ndlz_ (list 'IMPLIES '(IN ndlz_ ndlu_)
                (list 'FORSOME 'ndll_ (list 'IS-DIFF-ON 'ndlkf_ 'ndlu_ (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ 'ndli_) 'ndlz_ 'ndll_)))))))
            (list 'IN (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ 'ndlj_) '(FUN ndlu_ (CARR ndlkf_))))))))))))))
(dk-peel!)
(define ndl-if-j (list-ref (cadr (dk-goal)) 4))
(define ndl-if-hyp (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL) (eq? (cadr f) 'ndli_))) "the lower derivatives"))
(define ndl-if-d (ndl-dro! 'ndlkf_))
(fact 'fun-domain-in-set 'ndlu_ '(CARR ndlkf_) 'ndlf_)
(use-cases (dk-fact! 'nn-zero-or-succ ndl-if-j)
  (lambda ()
    (subst (list '= ndl-if-j 0))
    (mac 'nth-deriv-on-zero)
    (ass))
  (lambda ()
    (let ((q (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the predecessor"))))
      (dk-have! (list '< q ndl-if-j)
        (lambda () (subst (list '= ndl-if-j (list 'succ q))) (dk-nn!)))
      (let ((hq (dk-deepest (lambda () (inst+ ndl-if-hyp q)))))
        (subst (list '= ndl-if-j (list 'succ q)))
        (mac 'nth-deriv-on-succ)
        (dk-lam-type!
          (lambda ()
            (let* ((v (dk-di-var!))
                   (ex (dk-deepest (lambda () (inst+ hq v))))
                   (l (dk-skolem! ex))
                   (pd (list 'IS-DIFF-ON 'ndlkf_ 'ndlu_ (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ q) v l)))
              (ndl-diff-typ! pd)
              (subst (dk-apply! ndl-if-d 'ndlu_ (ndl-nd 'ndlkf_ 'ndlu_ 'ndlf_ q) v l))
              (ass)))
          (lambda () (ass)))))))
(qed 'nth-deriv-on-in-fun)

;;; ======================================================================
;;; OVER CC: THE POWER SERIES.  Typing helpers for the coefficient terms
;;; (copies of 27-A's ctc- typers: they are local to cps-taylor-coefficients.scm).
;;; ======================================================================
(define (ndl-and! a b)
  (let ((f (list 'AND a b)))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! (lambda () (ass))))))
    f))
(define (ndl-nn-typ! t)
  (let ((typ (list 'IN t 'NN)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'nn-zero-in) typ)
          ((ndl-op? t 'succ 2) (ndl-nn-typ! (cadr t)) (fact 'nn-succ-closed (cadr t)) typ)
          ((ndl-op? t '+ 3) (ndl-nn-typ! (cadr t)) (ndl-nn-typ! (caddr t))
           (ndl-and! (list 'IN (cadr t) 'NN) (list 'IN (caddr t) 'NN))
           (fact 'nn-add-closed (cadr t) (caddr t)) typ)
          (#t (error "ndl-nn-typ!: cannot type" (expression->string t))))))
(define (ndl-real? t)
  (or (eqv? t 0) (eqv? t 1)
      (dk-asm? (list 'IN t 'RR)) (dk-asm? (list 'IN t 'NN))
      (ndl-op? t 'succ 2) (ndl-op? t 'FACTORIAL 2)
      (and (ndl-op? t 'recip 2) (ndl-op? (cadr t) 'FACTORIAL 2))
      (and (ndl-op? t '* 3) (ndl-real? (cadr t)) (ndl-real? (caddr t)))))
(define (ndl-rr-typ! t)
  (let ((typ (list 'IN t 'RR)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'rr-zero-in) typ)
          ((eqv? t 1) (fact 'rr-one-in) typ)
          ((ndl-op? t 'FACTORIAL 2)
           (ndl-nn-typ! (cadr t))
           (dk-split-all! (list (dk-fact! 'factorial-real-pos (cadr t)))) typ)
          ((or (dk-asm? (list 'IN t 'NN)) (ndl-op? t 'succ 2))
           (ndl-nn-typ! t) (fact 'nn-in-rr t) typ)
          ((and (ndl-op? t 'recip 2) (ndl-op? (cadr t) 'FACTORIAL 2))
           (ndl-nn-typ! (cadr (cadr t))) (fact 'recip-factorial-in-rr (cadr (cadr t))) typ)
          ((ndl-op? t '* 3) (ndl-rr-typ! (cadr t)) (ndl-rr-typ! (caddr t)) (fact 'rr-mul-in-rr (cadr t) (caddr t)) typ)
          (#t (error "ndl-rr-typ!: cannot type" (expression->string t))))))
(define (ndl-cc-typ! t)
  (let ((typ (list 'IN t 'CC)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'cc-zero-in) typ)
          ((ndl-real? t) (ndl-rr-typ! t) (fact 'rr-subset-cc t) typ)
          ((ndl-op? t 'cf 2) (ndl-nn-typ! (cadr t)) (fact 'fun-apply-type-c 'cf 'NN 'CC (cadr t)) typ)
          ((ndl-op? t '* 3) (ndl-cc-typ! (cadr t)) (ndl-cc-typ! (caddr t))
           (ndl-and! (list 'IN (cadr t) 'CC) (list 'IN (caddr t) 'CC)) (fact 'cc-mul-closed (cadr t) (caddr t)) typ)
          (#t (error "ndl-cc-typ!: cannot type" (expression->string t))))))

;;; the k-th derived coefficient (n+k)!/n! * cf(n+k), and V(g, k) -- 27-A's terms
(define (ndl-coef n k)
  (list '* (list '* (list 'FACTORIAL (list '+ n k)) (list 'recip (list 'FACTORIAL n))) (list 'cf (list '+ n k))))
(define (ndl-val g k)
  (list 'FORALL 'ctcn_ (list 'IMPLIES '(IN ctcn_ NN) (list '= (list g 'ctcn_) (ndl-coef 'ctcn_ k)))))
;;; B(0, r) and F_g, spelled as 27-A spells them
(define ndl-B '(BALL CC-MS 0 cpdr_))
(define (ndl-F g)
  (list 'VNB-LAMBDA 'cpdz_ ndl-B
    (list 'CC-SERIES-LIMIT (list 'VNB-LAMBDA 'cpsk_ 'NN (list '* (list g 'cpsk_) '(power cpdz_ cpsk_))))))
(define (ndl-nd-cc k) (ndl-nd 'CC-NORMED-FIELD ndl-B (ndl-F 'cf) k))
;;; the sequence g of F_g
(define (ndl-F-seq fg) (car (cadr (cadddr (cadr (cadddr fg))))))

;;; 0 < cpdr_ in context: the ball is a set and contains 0 (27-A's ctc-ball-setup!)
(define (ndl-ball-setup!)
  (fact 'cc-is-metric-space)
  (if (not (dk-asm? '(== (PTS CC-MS) CC)))
      (dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl))))
  (fact 'cc-zero-in)
  (fact 'nn-zero-in)
  (fact 'rr-zero-in)
  (dk-have! '(IN 0 (PTS CC-MS)) (lambda () (subst '(== (PTS CC-MS) CC)) (ass)))
  (fact 'ball-is-set 'CC-MS 0 'cpdr_))

;;; A FRESH SYMBOL G with V(G, K) in context (dk-abstract! of the k-th derived
;;; sequence, its value equation read back as V's strict equation); returns G.
(define (ndl-seq! k)
  (ndl-nn-typ! k)
  (let* ((ab (dk-abstract! 'NN 'CC (lambda (v) (ndl-coef v k)) (lambda (v) (ndl-cc-typ! (ndl-coef v k)) (ass))))
         (g (car ab))
         (veq (cdr ab)))
    (dk-have! (ndl-val g k)
      (lambda ()
        (let ((v (dk-di-var!)))
          (ndl-cc-typ! (ndl-coef v k))
          (subst (dk-apply! veq v))
          (rfl))))
    g))

;;; ======================================================================
;;; (5) THE k-TH DERIVATIVE OF THE SUM IS THE SUM OF THE k-TH DERIVED SERIES:
;;; 0 < r < R(cf) and V(g, k) => NTH-DERIV-ON(CC-NF, B(0,r), F_cf, k) = F_g.
;;; Induction on k.  k = 0: V(g, 0) makes g = cf (function extensionality, as
;;; in cps-kth-derived-radius).  k -> k+1: F_(k+1) is the derivative of F_k at
;;; every point of the ball (cps-taylor-coefficients, third conjunct), and the
;;; two lambdas over the ball agree pointwise.
;;; ======================================================================
(define ndl-cn-claim
  (list 'FORALL 'ndlm_ (list 'IMPLIES '(IN ndlm_ NN)
    (list 'FORALL 'ndlq_ (list 'IMPLIES '(IN ndlq_ (FUN NN CC))
      (list 'IMPLIES (ndl-val 'ndlq_ 'ndlm_) (list '= (ndl-nd-cc 'ndlm_) (ndl-F 'ndlq_))))))))
(sp (make-wff
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'cpdr_ (list 'IMPLIES '(IN cpdr_ RR) (list 'IMPLIES '(< 0 cpdr_)
      (list 'IMPLIES '(< cpdr_ (CPS-RADIUS cf))
        (list 'FORALL 'ndlk_ (list 'IMPLIES '(IN ndlk_ NN)
          (list 'FORALL 'ndlg_ (list 'IMPLIES '(IN ndlg_ (FUN NN CC))
            (list 'IMPLIES (ndl-val 'ndlg_ 'ndlk_)
              (list '= (ndl-nd-cc 'ndlk_) (ndl-F 'ndlg_)))))))))))))))
(dk-peel!)
(ndl-ball-setup!)
(define (ndl-fun-dom! f)
  (dk-have! (list 'IN f '(FUN NN))
    (lambda ()
      (mac-h 'fun-codomain-iff (list 'IN f '(FUN NN CC)))
      (dk-split-all!)
      (ass))))
(dk-have! ndl-cn-claim
  (lambda ()
    (let* ((br (use-induction))
           (m (cdr (assq 'var br)))
           (ih (cdr (assq 'ih br)))
           (step (cdr (assq 'step br))))
      ;; k = 0: q = cf
      (dk-focus! (cdr (assq 'base br)))
      (dk-peel!)
      (let* ((q (ndl-F-seq (caddr (dk-goal))))
             (vq (dk-pick (lambda (f) (alpha-equiv? f (ndl-val q 0))) "the values of q"))
             (eqn (list '= q 'cf)))
        (ndl-fun-dom! q)
        (ndl-fun-dom! 'cf)
        (dk-have! eqn
          (lambda ()
            (let ((ch (dk-fact! 'fun-domain-extensionality 'NN q 'cf))
                  (fa (list 'FORALL 'ndlx_ (list 'IMPLIES '(IN ndlx_ NN) (list '= (list q 'ndlx_) '(cf ndlx_))))))
              (dk-have! fa
                (lambda ()
                  (let ((v (dk-di-var!)))
                    (subst (dk-deepest (lambda () (inst+ vq v))))
                    (subst (dk-fact! 'nn-add-zero v))
                    (subst (dk-fact! 'rr-recip-factorial v))
                    (ndl-cc-typ! (list 'cf v))
                    (crs))))
              (detach! ch)
              (ass))))
        (mac 'nth-deriv-on-zero)
        (subst eqn)
        (rfl))
      ;; k -> k + 1
      (dk-focus! step)
      (dk-peel!)
      (let* ((fq (caddr (dk-goal)))
             (q (ndl-F-seq fq))
             (sm (list 'succ m)))
        (ndl-nn-typ! sm)
        (let* ((g0 (ndl-seq! m))
               (fg0 (ndl-F g0)))
          (mac 'nth-deriv-on-succ)
          (subst (dk-apply! ih g0))
          ;; F_q is a function on the ball: its radius is R(cf)
          (dk-fact! 'cps-kth-derived-radius 'cf sm q)
          (dk-have! (list '< 'cpdr_ (list 'CPS-RADIUS q))
            (lambda () (subst (list '= (list 'CPS-RADIUS q) '(CPS-RADIUS cf))) (ass)))
          (dk-split-all! (list (dk-fact! 'cps-holomorphic-ball q 'cpdr_)))
          (fact 'holomorphic-on-in-fun ndl-B fq)
          ;; DERIV-ON(F_g0) = F_q on the ball
          (dk-split-all! (list (dk-fact! 'cps-taylor-coefficients 'cf m g0 q 'cpdr_)))
          (let ((c3 (or (dk-ctx-form
                          (list 'FORALL 'cpda_ (list 'IMPLIES (list 'IN 'cpda_ ndl-B)
                            (list '= (list 'DERIV-ON 'CC-NORMED-FIELD ndl-B fg0 'cpda_) (list fq 'cpda_)))))
                        (error "ndl: the derivative conjunct did not land")))
                (lhs (cadr (dk-goal))))
            (dk-fun-ext! lhs fq ndl-B 'CC
              (lambda ()
                (dk-lam-type!
                  (lambda ()
                    (let ((v (dk-di-var!)))
                      (subst (dk-deepest (lambda () (inst+ c3 v))))
                      (fact 'fun-apply-type-c fq ndl-B 'CC v)
                      (ass)))
                  (lambda () (ass))))
              #f
              (lambda (v)
                (let ((e (dk-deepest (lambda () (inst+ c3 v)))))
                  (subst (list '= (list fq v) (list 'DERIV-ON 'CC-NORMED-FIELD ndl-B fg0 v)))
                  (let ((leaf (proof-state-focus *ps*)))
                    (dk-lam-b!)
                    (if (not (sequent-node-grounded? leaf)) (rfl))))))))))))
(dk-apply! ndl-cn-claim 'ndlk_ 'ndlg_)
(ass)
(qed 'cps-nth-deriv)

;;; the common hypotheses of the three corollaries: cf, 0 < r < R(cf), k in NN
(define (ndl-cor concl)
  (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN CC))
    (list 'FORALL 'cpdr_ (list 'IMPLIES '(IN cpdr_ RR) (list 'IMPLIES '(< 0 cpdr_)
      (list 'IMPLIES '(< cpdr_ (CPS-RADIUS cf))
        (list 'FORALL 'ndlk_ (list 'IMPLIES '(IN ndlk_ NN) concl)))))))))
;;; after the peel: G with V(G, ndlk_), and NTH-DERIV-ON(..., ndlk_) rewritten to F_G
(define (ndl-cor-setup!)
  (dk-peel!)
  (ndl-ball-setup!)
  (let ((g (ndl-seq! 'ndlk_)))
    (subst (dk-fact! 'cps-nth-deriv 'cf 'cpdr_ 'ndlk_ g))
    g))

;;; ======================================================================
;;; (6) COROLLARY 2.14, LITERALLY.  The notes (p. 28): "If f is analytic at 0,
;;; f(z) = sum_k a_k z^k on a ball, then by 2.10 and induction f^(k)(0) = k! a_k."
;;; f = F_cf on B(0, r), every 0 < r < R(cf).
;;; ======================================================================
(sp (make-wff
  (ndl-cor (list '= (list (ndl-nd-cc 'ndlk_) 0) '(* (FACTORIAL ndlk_) (cf ndlk_))))))
(define ndl-tc-g (ndl-cor-setup!))
(define ndl-tc-h (ndl-seq! '(succ ndlk_)))
(dk-split-all! (list (dk-fact! 'cps-taylor-coefficients 'cf 'ndlk_ ndl-tc-g ndl-tc-h 'cpdr_)))
(ass)
(qed 'taylor-coefficients)

;;; ======================================================================
;;; (7) "so that f(z) = sum_k f^(k)(0)/k! z^k", coefficientwise:
;;; a_k = f^(k)(0) / k!.
;;; ======================================================================
(sp (make-wff
  (ndl-cor (list '= '(cf ndlk_) (list '* (list (ndl-nd-cc 'ndlk_) 0) '(recip (FACTORIAL ndlk_)))))))
(define ndl-cf-g (ndl-cor-setup!))
(dk-fact! 'cps-coefficient-formula 'cf 'ndlk_ ndl-cf-g 'cpdr_)
(ass)
(qed 'taylor-coefficient-formula)

;;; ======================================================================
;;; (8) EVERY DERIVATIVE OF THE SUM IS HOLOMORPHIC ON THE BALL.
;;; ======================================================================
(sp (make-wff
  (ndl-cor (list 'HOLOMORPHIC-ON ndl-B (ndl-nd-cc 'ndlk_)))))
(define ndl-hb-g (ndl-cor-setup!))
(dk-fact! 'cps-kth-derived-radius 'cf 'ndlk_ ndl-hb-g)
(dk-have! (list '< 'cpdr_ (list 'CPS-RADIUS ndl-hb-g))
  (lambda () (subst (list '= (list 'CPS-RADIUS ndl-hb-g) '(CPS-RADIUS cf))) (ass)))
(dk-split-all! (list (dk-fact! 'cps-holomorphic-ball ndl-hb-g 'cpdr_)))
(ass)
(qed 'nth-deriv-on-holomorphic-ball)
