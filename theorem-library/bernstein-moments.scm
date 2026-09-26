;;; bernstein-moments.scm -- the moments of the Bernstein basis, and identity
;;; (76) of docs/calculus.pdf Proposition 5.4.
;;;
;;;     (1/n) sum_{l=0}^{n} (l - n x)^2 B_{l,n}(x)  <=  1     on [0,1]
;;;
;;; RUNG 2 of the integration arc, second half.  Identity (75) -- the partition
;;; of unity -- is bernstein-basis.scm; this is the half with content.
;;;
;;; THE MECHANISM is `series-partial-sum-weighted-expansion' (series-linearity.
;;; scm), the WEIGHTED multiply-and-shift.  With g := B_{.,n}(x) and y := 1-x it
;;; collapses to `bernstein-weighted-step' below,
;;;
;;;     sum_k w(k) B_{k,n+1}(x)  =  x sum_j w(j+1) B_{j,n}(x)
;;;                              +  (1-x) sum_k w(k) B_{k,n}(x),
;;;
;;; and the three moments are three weights: w = 1 (identity (75), already
;;; proven), w = k (identity (78)) and w = k(k-1) (identity (79)).  Nothing here
;;; splits on the index k, which is what keeps the whole development clear of
;;; the ZZ-discreteness gap; see the long note at the expansion.
;;;
;;; DELIBERATELY NOT the differentiation route of the notes' Lemma 5.5.
;;; Differentiating the binomial identity (81) twice in x would state these
;;; identities in whatever polynomial-FUNCTION representation rung 1
;;; (deriv-polynomial.scm) uses and couple this rung to that one; the
;;; combinatorial route stays inside the SUM/COMB-KK algebra that already exists
;;; and never mentions a polynomial function at all.
;;;
;;; WHAT IT COSTS.  Every bill here is `trust: well-known', and every leaf in it
;;; is one of two families that were already in the tree: `rr-is-normed-field'
;;; (numeric-instances.scm -- the sole door to IS-COMMUTATIVE-RING at the reals,
;;; so every RR-as-a-ring statement inherits it; WARRANTED 2026-08-24, with the
;;; derivation and the two things blocking its mechanization written out at the
;;; axiom) and the COMB-KK vocabulary of binomial.scm (comb-kk-in-fun / -null /
;;; -above / -0-0 and the bt-* index shims), each already `well-known'.  Nothing
;;; here adds a leaf of its own: no `support', no `add-axiom!'.
;;;
;;; Loads after bernstein-basis (the basis, its unfold, bernstein-partition) and
;;; series-linearity (the three linearity laws and the weighted expansion).

;;; ---- file-local driver (the `bmo-' prefix) ---------------------------

;;; RR as a commutative ring: the 6-tuple projection of RR-NORMED-FIELD, as in
;;; bernstein-basis.scm.
(define bmo-r '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))

(define (bmo-pw-real f)           ; forall k in NN. f(k) in RR
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (list f 'k_) 'RR))))
(define (bmo-pw-real-zz f)        ; forall k in ZZ. f(k) in RR
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ ZZ) (list 'IN (list f 'k_) 'RR))))
(define (bmo-pw-eq h rhs)         ; forall k in NN. h(k) = rhs(k)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list '= (list h 'k_) (rhs 'k_)))))

(define (bmo-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 18))
          (begin (di) (loop (+ n 1))) #t))))

(define (bmo-check name)
  (if (not (proof-done? *ps*))
      (error "bernstein-moments: proof did not close" name
             (expression->string (dk-goal)))))

;;; The typing context every COMB-KK citation wants: RR is a normed field, its
;;; ring view is a commutative ring, and x and 1-x are in that ring's carrier.
;;; (Assumes the eigenvariable is spelled x_ -- every statement below binds it
;;; that way.)
(define (bmo-ring-context!)
  (fact 'rr-is-normed-field)
  (fact 'NORMED-FIELD-AS-COMMUTATIVE-RING-is-COMMUTATIVE-RING 'RR-NORMED-FIELD)
  (fact 'rr-one-in)
  (have! '(AND (IN 1 RR) (IN x_ RR)))
  (fact 'rr-sub-in-rr 1 'x_)
  (have! (list 'IN 'x_ (list 'CARR bmo-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass)))
  (have! (list 'IN '(- 1 x_) (list 'CARR bmo-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass))))

;;; =====================================================================
;;; 1.  THE BASIS IS POINTWISE REAL.
;;;
;;; `bernstein-basis-in-fun' says the family is in FUN(ZZ,RR); this reads one
;;; value out of it.  The pointwise form is what series-linearity's laws take,
;;; and it is the form that survives at a SHIFTED index k-1, where an
;;; NN-indexed typing would not reach.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ k_)
        (list '(IN n_ NN) '(IN x_ RR) '(IN k_ ZZ))
        '(IN ((BERNSTEIN-BASIS n_ x_) k_) RR))))
  (bmo-peel!)
  (fact 'bernstein-basis-in-fun 'n_ 'x_)
  (fact 'fun-apply-type-c '(BERNSTEIN-BASIS n_ x_) 'ZZ 'RR 'k_)
  (ass)))
(bmo-check 'bernstein-basis-ptwise-in-rr)
(qed 'bernstein-basis-ptwise-in-rr)
(topic! 'bernstein-basis-ptwise-in-rr 'analysis)
(alias! 'bernstein-basis-ptwise-in-rr "each Bernstein basis value is real")

;;; =====================================================================
;;; 2.  THE PASCAL RECURRENCE, ON THE RR SURFACE.
;;;
;;;   B_{k,n+1}(x)  =  x B_{k-1,n}(x)  +  (1-x) B_{k,n}(x)
;;;
;;; `comb-kk-succ' read through the ring view.  The two atoms are TYPED before
;;; the closing `crs': the goal ends as a syntactic X = X, and neither `rfl' nor
;;; an untyped `crs' closes it -- `=' is partial in VNB, so X = X is a
;;; definedness claim and wants the generators certified in RR.  The typings are
;;; landed in BERNSTEIN-BASIS form and brought to COMB-KK form with `mac-h' on
;;; `bernstein-basis-unfold', because `mac' rewrites only the goal.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ k_)
        (list '(IN n_ NN) '(IN x_ RR) '(IN k_ NN))
        '(= ((BERNSTEIN-BASIS (succ n_) x_) k_)
            (+ (* x_ ((BERNSTEIN-BASIS n_ x_) (- k_ 1)))
               (* (- 1 x_) ((BERNSTEIN-BASIS n_ x_) k_)))))))
  (bmo-peel!) (bmo-ring-context!)
  (fact 'nn-subset-zz 'k_) (fact 'zz-one-in)
  (fact 'zz-sub-in-zz 'k_ 1)
  (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ '(- k_ 1))
  (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_)
  (mac-h 'bernstein-basis-unfold '(IN ((BERNSTEIN-BASIS n_ x_) (- k_ 1)) RR))
  (mac-h 'bernstein-basis-unfold '(IN ((BERNSTEIN-BASIS n_ x_) k_) RR))
  (mac 'BERNSTEIN-BASIS) (mac 'comb-kk-succ) (lam-b)
  (mac 'rr-scalar-ring-add) (mac 'rr-scalar-ring-mul)
  ;; the ADD/MUL slots hold tupled VNB-LAMBDAs since 2026-08-29, so the surface
  ;; step is the guarded slot read-off rather than binplus-apply / bintimes-apply.
  ;; The two atoms are already typed above -- which is exactly the guard.
  (dk-saturate-slot-ops! 'RR '((+ . rr-add-closed)
                               (* . rr-mul-closed)
                               (- . rr-neg-closed)))
  (crs)))
(bmo-check 'bernstein-basis-succ)
(qed 'bernstein-basis-succ)
(topic! 'bernstein-basis-succ 'analysis)
(alias! 'bernstein-basis-succ "the Pascal recurrence for the Bernstein basis")

;;; =====================================================================
;;; 3.  THE TWO VANISHING LAWS, ON THE RR SURFACE.
;;;
;;; B_{k,n}(x) = 0 outside 0 <= k <= n.  These are what kill the two boundary
;;; terms of the weighted expansion; they are `comb-kk-null' / `comb-kk-above'
;;; with (ZERO of the ring view) read off as the real 0.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ k_)
        (list '(IN n_ NN) '(IN x_ RR) '(IN k_ ZZ) '(< k_ 0))
        '(= ((BERNSTEIN-BASIS n_ x_) k_) 0))))
  (bmo-peel!) (bmo-ring-context!) (mac 'BERNSTEIN-BASIS)
  (let ((a (dk-fact! 'comb-kk-null bmo-r 'x_ '(- 1 x_) 'n_ 'k_)))
    (mac-h 'rr-scalar-ring-zero a)
    (ass))))
(bmo-check 'bernstein-basis-null)
(qed 'bernstein-basis-null)
(topic! 'bernstein-basis-null 'analysis)
(alias! 'bernstein-basis-null "the Bernstein basis vanishes below the range")

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ k_)
        (list '(IN n_ NN) '(IN x_ RR) '(IN k_ ZZ) '(< n_ k_))
        '(= ((BERNSTEIN-BASIS n_ x_) k_) 0))))
  (bmo-peel!) (bmo-ring-context!) (mac 'BERNSTEIN-BASIS)
  (let ((a (dk-fact! 'comb-kk-above bmo-r 'x_ '(- 1 x_) 'n_ 'k_)))
    (mac-h 'rr-scalar-ring-zero a)
    (ass))))
(bmo-check 'bernstein-basis-above)
(qed 'bernstein-basis-above)
(topic! 'bernstein-basis-above 'analysis)
(alias! 'bernstein-basis-above "the Bernstein basis vanishes above the range")

;;; =====================================================================
;;; 4.  THE MECHANISM: ONE STEP OF THE WEIGHTED EXPANSION AT THE BASIS.
;;;
;;;   sum_{k=0}^{n+1} w(k) B_{k,n+1}(x)
;;;      =  x sum_{j=0}^{n} w(j+1) B_{j,n}(x)
;;;      +  (1-x) sum_{k=0}^{n} w(k) B_{k,n}(x)
;;;
;;; `series-partial-sum-weighted-expansion' with g := B_{.,n}(x) and y := 1-x.
;;; The two boundary terms of the expansion die here: B_{-1,n}(x) = 0 by
;;; bernstein-basis-null and B_{n+1,n}(x) = 0 by bernstein-basis-above, which is
;;; the only place the range of the basis is used.  The three families p, q, s
;;; are given by pointwise EQUATIONS rather than as literal lambdas, so each
;;; moment supplies its own and nothing here mentions a weight.
;;;
;;; This is the whole content of the rung.  Each moment below is this lemma at
;;; one weight, plus the partial-sum linearity of series-linearity.scm.
;;; =====================================================================

(define bmo-g  '(BERNSTEIN-BASIS n_ x_))
(define bmo-gs '(BERNSTEIN-BASIS (succ n_) x_))

(define bmo-p-eq
  (bmo-pw-eq 'p_ (lambda (k) (list '* (list 'w_ k) (list bmo-gs k)))))
(define bmo-q-eq
  (bmo-pw-eq 'q_ (lambda (k) (list '* (list 'w_ (list 'succ k)) (list bmo-g k)))))
(define bmo-s-eq
  (bmo-pw-eq 's_ (lambda (k) (list '* (list 'w_ k) (list bmo-g k)))))

;;; the same p-transfer written the way the general expansion states it
(define bmo-p-exp
  (bmo-pw-eq 'p_ (lambda (k) (list '* (list 'w_ k)
                   (list '+ (list '* 'x_ (list bmo-g (list '- k 1)))
                            (list '* '(- 1 x_) (list bmo-g k)))))))

(quietly (lambda ()
  (sp (make-wff
       (forall-guarded '(n_ x_ w_ p_ q_ s_)
         (list '(IN n_ NN) '(IN x_ RR)
               (bmo-pw-real-zz 'w_) (bmo-pw-real 'q_) (bmo-pw-real 's_)
               bmo-p-eq bmo-q-eq bmo-s-eq)
         (list '= (list 'SERIES-PARTIAL-SUM 'p_ '(succ (succ n_)))
                  (list '+ (list '* 'x_ '(SERIES-PARTIAL-SUM q_ (succ n_)))
                           (list '* '(- 1 x_)
                                 '(SERIES-PARTIAL-SUM s_ (succ n_))))))))
  (bmo-peel!)
  (fact 'bt-succ-in-nn 'n_) (fact 'nn-subset-zz 'n_)
  (fact 'nn-subset-zz '(succ n_)) (fact 'zz-zero-in)
  (fact 'bt-neg1-in-zz) (fact 'bt-neg1-neg) (fact 'bt-lt-succ 'n_)
  (fact 'rr-one-in) (have! '(AND (IN 1 RR) (IN x_ RR))) (fact 'rr-sub-in-rr 1 'x_)
  (have! (bmo-pw-real-zz bmo-g)
         (lambda () (di) (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_) (ass)))
  ;; the p-transfer, rewritten by the Pascal recurrence into the shape the
  ;; general expansion asks for
  (have! bmo-p-exp
    (lambda ()
      (di)
      (fact 'nn-subset-zz 'k_) (fact 'zz-one-in) (fact 'zz-sub-in-zz 'k_ 1)
      (dk-deepest (lambda () (inst+ bmo-p-eq 'k_)))
      (subst (list '= '(p_ k_) (list '* '(w_ k_) (list bmo-gs 'k_))))
      (fact 'bernstein-basis-succ 'n_ 'x_ 'k_)
      (subst (list '= (list bmo-gs 'k_)
                   (list '+ (list '* 'x_ (list bmo-g '(- k_ 1)))
                            (list '* '(- 1 x_) (list bmo-g 'k_)))))
      (dk-deepest (lambda () (inst+ (bmo-pw-real-zz 'w_) 'k_)))
      (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ '(- k_ 1))
      (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_)
      (crs)))
  ;; LUTINS instantiation (2026-09-18): the expansion is instantiated AT the
  ;; basis family, and BERNSTEIN-BASIS is a COMB-KK functoid, not a class term,
  ;; so the certificate wants it typed.  bernstein-basis-in-fun is that typing.
  (fact 'bernstein-basis-in-fun 'n_ 'x_)
  (subst (dk-fact! 'series-partial-sum-weighted-expansion
                   '(succ n_) 'x_ '(- 1 x_) bmo-g 'w_ 'p_ 'q_ 's_))
  (fact 'bernstein-basis-null 'n_ 'x_ '(- 0 1))
  (subst (list '= (list bmo-g '(- 0 1)) 0))
  (fact 'bernstein-basis-above 'n_ 'x_ '(succ n_))
  (subst (list '= (list bmo-g '(succ n_)) 0))
  (dk-deepest (lambda () (inst+ (bmo-pw-real-zz 'w_) 0)))
  (dk-deepest (lambda () (inst+ (bmo-pw-real-zz 'w_) '(succ n_))))
  (fact 'series-partial-sum-in-rr-ptwise '(succ n_) 'q_)
  (fact 'series-partial-sum-in-rr-ptwise '(succ n_) 's_)
  (crs)))
(bmo-check 'bernstein-weighted-step)
(qed 'bernstein-weighted-step)
(topic! 'bernstein-weighted-step 'analysis)
(alias! 'bernstein-weighted-step
        "one degree step of a weighted Bernstein sum")

;;; =====================================================================
;;; 5.  IDENTITY (78) -- the FIRST MOMENT.
;;;
;;;   sum_{l=0}^{n} l B_{l,n}(x)  =  n x
;;;
;;; The weight w(k) = k.  At degree n+1 the step gives
;;;   M_1(n+1) = x sum_j (j+1) B_{j,n}(x)  +  (1-x) M_1(n),
;;; and the shifted sum splits as M_1(n) + M_0(n) by partial-sum additivity,
;;; where M_0(n) = 1 is `bernstein-partition' (identity (75)) -- the second
;;; moment identity is thus the FIRST one plus the partition, with no new
;;; combinatorics.  Then x(nx + 1) + (1-x)nx = (n+1)x, which is `crs'.
;;;
;;; The weight is a VNB-LAMBDA over ZZ, and it is used ONLY through `lam-b':
;;; nothing claims it is a member of FUN(ZZ,RR), so no `lam-t' and no sethood
;;; obligation arises.  Its binder is j_, never the driver's k_.
;;; =====================================================================

(define bmo-w-id '(VNB-LAMBDA j_ ZZ j_))
(define (bmo-basis n) (list 'BERNSTEIN-BASIS n 'x_))
(define (bmo-lam-succ n)                ; j |-> succ(j) B_{j,n}(x)
  (list 'VNB-LAMBDA 'j_ 'NN (list '* '(succ j_) (list (bmo-basis n) 'j_))))
(define (bmo-lam-id n)                  ; j |-> j B_{j,n}(x)
  (list 'VNB-LAMBDA 'j_ 'NN (list '* 'j_ (list (bmo-basis n) 'j_))))

;;; `lam-b' reduces one redex; a lane with several wants several calls, and a
;;; call that changes nothing is a no-op that warns and is not recorded.
(define (bmo-lam-b* k) (let loop ((i 0)) (if (< i k) (begin (lam-b) (loop (+ i 1))))))

(define (bmo-nn-ind inner) (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) inner)))

(define bmo-m1-stmt
  (bmo-nn-ind
    (forall-guarded '(x_ h_)
      (list '(IN x_ RR)
            (bmo-pw-eq 'h_ (lambda (k) (list '* k (list (bmo-basis 'n_) k)))))
      '(= (SERIES-PARTIAL-SUM h_ (succ n_)) (* n_ x_)))))

(quietly (lambda ()
  (sp (make-wff bmo-m1-stmt))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br)))
         (bb (bmo-basis n)) (qq (bmo-lam-succ n)) (ss (bmo-lam-id n))
         (type-k! (lambda ()
                    (fact 'nn-subset-zz 'k_) (fact 'nn-in-rr 'k_)
                    (fact 'bt-succ-in-nn 'k_) (fact 'nn-subset-zz '(succ k_))
                    (fact 'nn-in-rr '(succ k_))
                    (fact 'bernstein-basis-ptwise-in-rr n 'x_ 'k_))))

    ;; ---- BASE: the one-term sum is 0 * B_{0,0}(x).
    (dk-focus! (cdr (assq 'base br)))
    (bmo-peel!)
    (fact 'nn-zero-in) (fact 'zz-zero-in)
    ;; series-partial-sum-succ is guarded on its two arguments being real since
    ;; 2026-08-29.  h_ is a TRANSFER sequence -- constrained by a pointwise
    ;; equation, with no realness hypothesis -- so both facts are landed here and
    ;; dk-sps-succ! then finds them in context and simply fires the recurrence.
    (dk-deepest (lambda () (inst+ (bmo-pw-eq 'h_ (lambda (k)
                                    (list '* k (list (bmo-basis 0) k)))) 0)))
    (fact 'rr-zero-in)
    (fact 'bernstein-basis-ptwise-in-rr 0 'x_ 0)
    (dk-have! '(IN (SERIES-PARTIAL-SUM h_ 0) RR)
      (lambda () (mac 'series-partial-sum-zero) (ass)))
    (dk-have! '(IN (h_ 0) RR)
      (lambda () (subst (list '= '(h_ 0) (list '* 0 (list (bmo-basis 0) 0))))
                 (in-rr)))
    (dk-sps-succ! 'h_ 0)
    (mac 'series-partial-sum-zero)
    (subst (list '= '(h_ 0) (list '* 0 (list (bmo-basis 0) 0))))
    (crs)

    ;; ---- STEP.
    (dk-focus! (cdr (assq 'step br)))
    (bmo-peel!)
    (let ((hyp (bmo-pw-eq 'h_ (lambda (k)
                 (list '* k (list (bmo-basis (list 'succ n)) k))))))
      (fact 'bt-succ-in-nn n) (fact 'nn-subset-zz n) (fact 'zz-zero-in)
      (fact 'rr-one-in) (have! '(AND (IN 1 RR) (IN x_ RR)))
      (fact 'rr-sub-in-rr 1 'x_) (fact 'nn-in-rr n)
      ;; pointwise realness of the weight and of the three families
      (have! (bmo-pw-real-zz bmo-w-id)
             (lambda () (di) (bmo-lam-b* 2) (fact 'zz-in-rr 'k_) (ass)))
      (have! (bmo-pw-real bb)
             (lambda () (di) (fact 'nn-subset-zz 'k_)
                        (fact 'bernstein-basis-ptwise-in-rr n 'x_ 'k_) (ass)))
      (have! (bmo-pw-real ss)
        (lambda () (di) (bmo-lam-b* 2) (type-k!)
           (have! (list 'AND '(IN k_ RR) (list 'IN (list bb 'k_) 'RR)))
           (fact 'rr-mul-closed 'k_ (list bb 'k_)) (ass)))
      (have! (bmo-pw-real qq)
        (lambda () (di) (bmo-lam-b* 2) (type-k!)
           (have! (list 'AND '(IN (succ k_) RR) (list 'IN (list bb 'k_) 'RR)))
           (fact 'rr-mul-closed '(succ k_) (list bb 'k_)) (ass)))
      ;; the three transfer equations, each a lam-b and a typed crs
      (have! (bmo-pw-eq 'h_ (lambda (k) (list '* (list bmo-w-id k)
                              (list (bmo-basis (list 'succ n)) k))))
        (lambda () (di) (type-k!)
           (fact 'bernstein-basis-ptwise-in-rr (list 'succ n) 'x_ 'k_)
           (dk-deepest (lambda () (inst+ hyp 'k_)))
           (subst (list '= '(h_ k_)
                        (list '* 'k_ (list (bmo-basis (list 'succ n)) 'k_))))
           (bmo-lam-b* 3) (crs)))
      (have! (bmo-pw-eq qq (lambda (k) (list '* (list bmo-w-id (list 'succ k))
                                             (list bb k))))
        (lambda () (di) (type-k!) (bmo-lam-b* 4) (crs)))
      (have! (bmo-pw-eq ss (lambda (k) (list '* (list bmo-w-id k) (list bb k))))
        (lambda () (di) (type-k!) (bmo-lam-b* 4) (crs)))
      ;; the induction hypothesis, at the family S
      (have! (bmo-pw-eq ss (lambda (k) (list '* k (list bb k))))
        (lambda () (di) (type-k!) (bmo-lam-b* 3) (crs)))
      ;; Q = S + B pointwise, hence sum-wise
      (have! (bmo-pw-eq qq (lambda (k) (list '+ (list ss k) (list bb k))))
        (lambda () (di) (type-k!) (bmo-lam-b* 4)
           (fact 'nn-succ-plus-one 'k_) (subst '(= (succ k_) (+ k_ 1))) (crs)))
      (subst (dk-fact! 'bernstein-weighted-step n 'x_ bmo-w-id 'h_ qq ss))
      ;; LUTINS instantiation: add-ptwise is instantiated at the basis family.
      (fact 'bernstein-basis-in-fun n 'x_)
      (subst (dk-fact! 'series-partial-sum-add-ptwise (list 'succ n) ss bb qq))
      (subst (dk-fact! 'bernstein-partition n 'x_))
      (subst (dk-deepest (lambda ()
               (inst+ (dk-deepest (lambda () (inst+ ih 'x_))) ss))))
      (fact 'nn-succ-plus-one n)
      (subst (list '= (list 'succ n) (list '+ n 1)))
      (crs)))))
(bmo-check 'bernstein-moment-1)
(qed 'bernstein-moment-1)
(topic! 'bernstein-moment-1 'analysis)
(alias! 'bernstein-moment-1
        "the first moment of the Bernstein basis"
        "Proposition 5.4 (78)")

;;; =====================================================================
;;; 6.  IDENTITY (79) -- the SECOND MOMENT.
;;;
;;;   sum_{l=0}^{n} l(l-1) B_{l,n}(x)  =  n(n-1) x^2
;;;
;;; The weight w(k) = k(k-1).  The shifted weight is w(j+1) = (j+1)j =
;;; j(j-1) + 2j, so the shifted sum splits as M_2(n) + 2 M_1(n) -- and the
;;; doubling is done by ADDING the first moment to itself rather than by
;;; scaling it, which keeps the numeral 2 (and the obligation to type it) out
;;; of the proof entirely.  Then x(M_2 + 2nx) + (1-x)M_2 = M_2 + 2nx^2, and
;;; n(n-1)x^2 + 2nx^2 = (n+1)n x^2 is `crs'.
;;; =====================================================================

(define (bmo-mul-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
(define (bmo-add-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-add-closed a b))

(define bmo-w-kk '(VNB-LAMBDA j_ ZZ (* j_ (- j_ 1))))
(define (bmo-lam-kk n)                  ; j |-> j(j-1) B_{j,n}(x)
  (list 'VNB-LAMBDA 'j_ 'NN
        (list '* '(* j_ (- j_ 1)) (list (bmo-basis n) 'j_))))
(define (bmo-lam-kk-succ n)             ; j |-> (j+1)j B_{j,n}(x)
  (list 'VNB-LAMBDA 'j_ 'NN
        (list '* '(* (succ j_) (- (succ j_) 1)) (list (bmo-basis n) 'j_))))
(define (bmo-lam-twice n)               ; j |-> j B + j B
  (list 'VNB-LAMBDA 'j_ 'NN
        (list '+ (list '* 'j_ (list (bmo-basis n) 'j_))
                 (list '* 'j_ (list (bmo-basis n) 'j_)))))

(define (bmo-m2-heq n)
  (bmo-pw-eq 'h_ (lambda (k) (list '* (list '* k (list '- k 1))
                                   (list (bmo-basis n) k)))))
(define bmo-m2-stmt
  (bmo-nn-ind
    (forall-guarded '(x_ h_) (list '(IN x_ RR) (bmo-m2-heq 'n_))
      '(= (SERIES-PARTIAL-SUM h_ (succ n_)) (* (* n_ (- n_ 1)) (* x_ x_))))))

(quietly (lambda ()
  (sp (make-wff bmo-m2-stmt))
  (let* ((br (use-induction)) (n (cdr (assq 'var br))) (ih (cdr (assq 'ih br)))
         (bb (bmo-basis n)) (qq (bmo-lam-kk-succ n)) (ss (bmo-lam-kk n))
         (s1 (bmo-lam-id n)) (uu (bmo-lam-twice n))
         (type-k! (lambda ()
                    (fact 'nn-subset-zz 'k_) (fact 'nn-in-rr 'k_)
                    (fact 'bt-succ-in-nn 'k_) (fact 'nn-subset-zz '(succ k_))
                    (fact 'nn-in-rr '(succ k_)) (fact 'rr-one-in)
                    (fact 'rr-sub-in-rr 'k_ 1) (fact 'rr-sub-in-rr '(succ k_) 1)
                    (fact 'bernstein-basis-ptwise-in-rr n 'x_ 'k_))))

    ;; ---- BASE: the one-term sum is 0(0-1) B_{0,0}(x) = 0.
    (dk-focus! (cdr (assq 'base br)))
    (bmo-peel!)
    (fact 'nn-zero-in) (fact 'zz-zero-in)
    ;; same as moment-1's base: the recurrence is guarded on its two arguments
    ;; being real, and h_ is a transfer sequence with no realness hypothesis, so
    ;; both facts are landed before dk-sps-succ! fires the rewrite.
    (dk-deepest (lambda () (inst+ (bmo-m2-heq 0) 0)))
    ;; h_(0) is (0 * (0 - 1)) * B(0): typing it needs 1 in RR for the
    ;; SUBTRACTION as well as 0 in RR.
    (fact 'rr-zero-in) (fact 'rr-one-in)
    (fact 'bernstein-basis-ptwise-in-rr 0 'x_ 0)
    (dk-have! '(IN (SERIES-PARTIAL-SUM h_ 0) RR)
      (lambda () (mac 'series-partial-sum-zero) (ass)))
    (dk-have! '(IN (h_ 0) RR)
      (lambda () (subst (list '= '(h_ 0)
                              (list '* '(* 0 (- 0 1)) (list (bmo-basis 0) 0))))
                 (in-rr)))
    (dk-sps-succ! 'h_ 0)
    (mac 'series-partial-sum-zero)
    (subst (list '= '(h_ 0) (list '* '(* 0 (- 0 1)) (list (bmo-basis 0) 0))))
    (crs)

    ;; ---- STEP.
    (dk-focus! (cdr (assq 'step br)))
    (bmo-peel!)
    (fact 'bt-succ-in-nn n) (fact 'nn-subset-zz n) (fact 'zz-zero-in)
    (fact 'rr-one-in) (have! '(AND (IN 1 RR) (IN x_ RR)))
    (fact 'rr-sub-in-rr 1 'x_) (fact 'nn-in-rr n)
    ;; pointwise realness: the weight, the basis, and the four families
    (have! (bmo-pw-real-zz bmo-w-kk)
      (lambda () (di) (bmo-lam-b* 2) (fact 'zz-in-rr 'k_) (fact 'rr-one-in)
         (fact 'rr-sub-in-rr 'k_ 1) (bmo-mul-real! 'k_ '(- k_ 1)) (ass)))
    (have! (bmo-pw-real bb)
      (lambda () (di) (fact 'nn-subset-zz 'k_)
         (fact 'bernstein-basis-ptwise-in-rr n 'x_ 'k_) (ass)))
    (have! (bmo-pw-real ss)
      (lambda () (di) (bmo-lam-b* 2) (type-k!)
         (bmo-mul-real! 'k_ '(- k_ 1))
         (bmo-mul-real! '(* k_ (- k_ 1)) (list bb 'k_)) (ass)))
    (have! (bmo-pw-real qq)
      (lambda () (di) (bmo-lam-b* 2) (type-k!)
         (bmo-mul-real! '(succ k_) '(- (succ k_) 1))
         (bmo-mul-real! '(* (succ k_) (- (succ k_) 1)) (list bb 'k_)) (ass)))
    (have! (bmo-pw-real s1)
      (lambda () (di) (bmo-lam-b* 2) (type-k!)
         (bmo-mul-real! 'k_ (list bb 'k_)) (ass)))
    (have! (bmo-pw-real uu)
      (lambda () (di) (bmo-lam-b* 2) (type-k!)
         (bmo-mul-real! 'k_ (list bb 'k_))
         (bmo-add-real! (list '* 'k_ (list bb 'k_)) (list '* 'k_ (list bb 'k_)))
         (ass)))
    ;; the transfer equations
    (have! (bmo-pw-eq 'h_ (lambda (k) (list '* (list bmo-w-kk k)
                            (list (bmo-basis (list 'succ n)) k))))
      (lambda () (di) (type-k!)
         (fact 'bernstein-basis-ptwise-in-rr (list 'succ n) 'x_ 'k_)
         (dk-deepest (lambda () (inst+ (bmo-m2-heq (list 'succ n)) 'k_)))
         (subst (list '= '(h_ k_) (list '* '(* k_ (- k_ 1))
                                  (list (bmo-basis (list 'succ n)) 'k_))))
         (bmo-lam-b* 3) (crs)))
    (have! (bmo-pw-eq qq (lambda (k) (list '* (list bmo-w-kk (list 'succ k))
                                           (list bb k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 4) (crs)))
    (have! (bmo-pw-eq ss (lambda (k) (list '* (list bmo-w-kk k) (list bb k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 4) (crs)))
    (have! (bmo-pw-eq ss (lambda (k) (list '* (list '* k (list '- k 1))
                                           (list bb k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 3) (crs)))
    (have! (bmo-pw-eq s1 (lambda (k) (list '* k (list bb k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 3) (crs)))
    (have! (bmo-pw-eq uu (lambda (k) (list '+ (list s1 k) (list s1 k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 4) (crs)))
    ;; (j+1)j = j(j-1) + 2j, written as an addition of the first moment twice
    (have! (bmo-pw-eq qq (lambda (k) (list '+ (list ss k) (list uu k))))
      (lambda () (di) (type-k!) (bmo-lam-b* 5)
         (fact 'nn-succ-plus-one 'k_) (subst '(= (succ k_) (+ k_ 1))) (crs)))
    (subst (dk-fact! 'bernstein-weighted-step n 'x_ bmo-w-kk 'h_ qq ss))
    (subst (dk-fact! 'series-partial-sum-add-ptwise (list 'succ n) ss uu qq))
    (subst (dk-fact! 'series-partial-sum-add-ptwise (list 'succ n) s1 s1 uu))
    (subst (dk-fact! 'bernstein-moment-1 n 'x_ s1))
    (subst (dk-deepest (lambda ()
             (inst+ (dk-deepest (lambda () (inst+ ih 'x_))) ss))))
    (fact 'nn-succ-plus-one n)
    (subst (list '= (list 'succ n) (list '+ n 1)))
    (crs))))
(bmo-check 'bernstein-moment-2)
(qed 'bernstein-moment-2)
(topic! 'bernstein-moment-2 'analysis)
(alias! 'bernstein-moment-2
        "the second moment of the Bernstein basis"
        "Proposition 5.4 (79)")

;;; =====================================================================
;;; 7.  IDENTITY (80) -- THE VARIANCE IDENTITY.
;;;
;;;   sum_{l=0}^{n} (l - n x)^2 B_{l,n}(x)  =  n x (1 - x)
;;;
;;; NO INDUCTION.  Expand the square as
;;;   (k - nx)^2  =  k(k-1)  +  (1 - 2nx) k  +  (nx)^2,
;;; which is a ring identity, and read the three pieces off the three moments:
;;; (79), (78) and (75).  The splitting is done by the pointwise linearity of
;;; series-linearity.scm -- two additions and two scalars -- and the arithmetic
;;;   n(n-1)x^2 + (1-2nx)(nx) + (nx)^2 = nx - nx^2
;;; is one `crs'.
;;;
;;; The coefficient 1 - 2nx is written  (1 - nx) - nx  so that no numeral 2
;;; needs typing; the whole file mentions no numeral but 0 and 1.
;;; =====================================================================

(define bmo-nx '(* n_ x_))
(define bmo-c1 '(- (- 1 (* n_ x_)) (* n_ x_)))          ; 1 - 2nx
(define bmo-c2 '(* (* n_ x_) (* n_ x_)))                ; (nx)^2
(define (bmo-sq k) (list '* (list '- k bmo-nx) (list '- k bmo-nx)))

(define bmo-vB  '(BERNSTEIN-BASIS n_ x_))
(define bmo-vA  (list 'VNB-LAMBDA 'j_ 'NN
                      (list '* '(* j_ (- j_ 1)) (list bmo-vB 'j_))))
(define bmo-vS1 (list 'VNB-LAMBDA 'j_ 'NN (list '* 'j_ (list bmo-vB 'j_))))
(define bmo-vB1 (list 'VNB-LAMBDA 'j_ 'NN
                      (list '* bmo-c1 (list '* 'j_ (list bmo-vB 'j_)))))
(define bmo-vC  (list 'VNB-LAMBDA 'j_ 'NN (list '* bmo-c2 (list bmo-vB 'j_))))
(define bmo-vD  (list 'VNB-LAMBDA 'j_ 'NN
                      (list '+ (list '* bmo-c1 (list '* 'j_ (list bmo-vB 'j_)))
                               (list '* bmo-c2 (list bmo-vB 'j_)))))

(define bmo-var-heq
  (bmo-pw-eq 'h_ (lambda (k) (list '* (bmo-sq k) (list bmo-vB k)))))

;;; the curried closure laws (binary-minus-laws.scm) -- `rr-add-closed' /
;;; `rr-mul-closed' state an AND antecedent, and a `have!' of (AND P P), which
;;; `t * t in RR' needs, is refused as an alpha self-loop.
(define (bmo-mulr! a b) (fact 'rr-mul-in-rr a b))
(define (bmo-addr! a b) (fact 'rr-add-in-rr a b))

(define (bmo-var-type-k!)
  (fact 'nn-subset-zz 'k_) (fact 'nn-in-rr 'k_) (fact 'rr-one-in)
  (fact 'rr-sub-in-rr 'k_ 1)
  (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_)
  (fact 'rr-sub-in-rr 'k_ bmo-nx))

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ h_)
        (list '(IN n_ NN) '(IN x_ RR) bmo-var-heq)
        (list '= '(SERIES-PARTIAL-SUM h_ (succ n_))
                 (list '* bmo-nx '(- 1 x_))))))
  (bmo-peel!)
  (fact 'nn-in-rr 'n_) (fact 'rr-one-in) (fact 'nn-subset-zz 'n_)
  (fact 'bt-succ-in-nn 'n_)
  (bmo-mulr! 'n_ 'x_)
  (fact 'rr-sub-in-rr 1 bmo-nx)
  (fact 'rr-sub-in-rr '(- 1 (* n_ x_)) bmo-nx)          ; c1 in RR
  (bmo-mulr! bmo-nx bmo-nx)                             ; c2 in RR
  ;; pointwise realness of the five families
  (have! (bmo-pw-real bmo-vB)
    (lambda () (di) (fact 'nn-subset-zz 'k_)
       (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_) (ass)))
  (have! (bmo-pw-real bmo-vA)
    (lambda () (di) (bmo-lam-b* 2) (bmo-var-type-k!)
       (bmo-mulr! 'k_ '(- k_ 1))
       (bmo-mulr! '(* k_ (- k_ 1)) (list bmo-vB 'k_)) (ass)))
  (have! (bmo-pw-real bmo-vS1)
    (lambda () (di) (bmo-lam-b* 2) (bmo-var-type-k!)
       (bmo-mulr! 'k_ (list bmo-vB 'k_)) (ass)))
  (have! (bmo-pw-real bmo-vB1)
    (lambda () (di) (bmo-lam-b* 2) (bmo-var-type-k!)
       (bmo-mulr! 'k_ (list bmo-vB 'k_))
       (bmo-mulr! bmo-c1 (list '* 'k_ (list bmo-vB 'k_))) (ass)))
  (have! (bmo-pw-real bmo-vC)
    (lambda () (di) (bmo-lam-b* 2) (bmo-var-type-k!)
       (bmo-mulr! bmo-c2 (list bmo-vB 'k_)) (ass)))
  (have! (bmo-pw-real bmo-vD)
    (lambda () (di) (bmo-lam-b* 2) (bmo-var-type-k!)
       (bmo-mulr! 'k_ (list bmo-vB 'k_))
       (bmo-mulr! bmo-c1 (list '* 'k_ (list bmo-vB 'k_)))
       (bmo-mulr! bmo-c2 (list bmo-vB 'k_))
       (bmo-addr! (list '* bmo-c1 (list '* 'k_ (list bmo-vB 'k_)))
                  (list '* bmo-c2 (list bmo-vB 'k_)))
       (ass)))
  ;; the transfer equations -- the square expansion is the first of them
  (have! (bmo-pw-eq 'h_ (lambda (k) (list '+ (list bmo-vA k) (list bmo-vD k))))
    (lambda () (di) (bmo-var-type-k!)
       (dk-deepest (lambda () (inst+ bmo-var-heq 'k_)))
       (subst (list '= '(h_ k_) (list '* (bmo-sq 'k_) (list bmo-vB 'k_))))
       (bmo-lam-b* 4) (crs)))
  (have! (bmo-pw-eq bmo-vD (lambda (k) (list '+ (list bmo-vB1 k) (list bmo-vC k))))
    (lambda () (di) (bmo-var-type-k!) (bmo-lam-b* 4) (crs)))
  (have! (bmo-pw-eq bmo-vB1 (lambda (k) (list '* bmo-c1 (list bmo-vS1 k))))
    (lambda () (di) (bmo-var-type-k!) (bmo-lam-b* 4) (crs)))
  (have! (bmo-pw-eq bmo-vC (lambda (k) (list '* bmo-c2 (list bmo-vB k))))
    (lambda () (di) (bmo-var-type-k!) (bmo-lam-b* 4) (crs)))
  (have! (bmo-pw-eq bmo-vA (lambda (k) (list '* (list '* k (list '- k 1))
                                             (list bmo-vB k))))
    (lambda () (di) (bmo-var-type-k!) (bmo-lam-b* 3) (crs)))
  (have! (bmo-pw-eq bmo-vS1 (lambda (k) (list '* k (list bmo-vB k))))
    (lambda () (di) (bmo-var-type-k!) (bmo-lam-b* 3) (crs)))
  (subst (dk-fact! 'series-partial-sum-add-ptwise '(succ n_) bmo-vA bmo-vD 'h_))
  (subst (dk-fact! 'series-partial-sum-add-ptwise '(succ n_) bmo-vB1 bmo-vC bmo-vD))
  (subst (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) bmo-c1 bmo-vS1 bmo-vB1))
  ;; LUTINS instantiation: scale-ptwise is instantiated at the basis family.
  (fact 'bernstein-basis-in-fun 'n_ 'x_)
  (subst (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) bmo-c2 bmo-vB bmo-vC))
  (subst (dk-fact! 'bernstein-moment-2 'n_ 'x_ bmo-vA))
  (subst (dk-fact! 'bernstein-moment-1 'n_ 'x_ bmo-vS1))
  (subst (dk-fact! 'bernstein-partition 'n_ 'x_))
  (crs)))
(bmo-check 'bernstein-variance)
(qed 'bernstein-variance)
(topic! 'bernstein-variance 'analysis)
(alias! 'bernstein-variance
        "the Bernstein variance identity"
        "Proposition 5.4 (80)")

;;; =====================================================================
;;; 8.  IDENTITY (76) -- THE VARIANCE BOUND.
;;;
;;;   (1/n) sum_{l=0}^{n} (l - n x)^2 B_{l,n}(x)  <=  1
;;;
;;; (80) divided by n, plus x(1-x) <= 1.  The division is the only place
;;; `recip' appears: binary-divide-def opens (1/n) as 1 * recip(n), `crs'
;;; regroups the product so that n * recip(n) stands alone, and
;;; rr-recip-inverse (which needs n /= 0, the one hypothesis of the statement
;;; beyond typing) collapses it.
;;;
;;; STATED WITHOUT 0 <= x <= 1, which the notes carry.  The restriction is not
;;; needed and it is worth saying why: (80) is an ALGEBRAIC identity, valid at
;;; every real x, and the remaining bound x(1-x) <= 1 is unconditional -- `sos'
;;; finds the certificate  1 - x(1-x) = (x - 1/2)^2 + 3/4  with no order
;;; hypothesis at all.  What [0,1] is actually for is NON-NEGATIVITY of the
;;; basis, which Theorem 5.2 needs and this bound does not.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ x_ h_)
        (list '(IN n_ NN) '(NOT (= n_ 0)) '(IN x_ RR) bmo-var-heq)
        '(<= (* (/ 1 n_) (SERIES-PARTIAL-SUM h_ (succ n_))) 1))))
  (bmo-peel!)
  (fact 'nn-in-rr 'n_)
  (subst (dk-fact! 'bernstein-variance 'n_ 'x_ 'h_))
  (mac 'binary-divide-def)
  (have! '(AND (IN n_ RR) (NOT (= n_ 0))))
  (fact 'rr-recip-closed 'n_)
  (fact 'rr-recip-inverse 'n_)
  (have! (list '= (list '* '(* 1 (recip n_)) (list '* bmo-nx '(- 1 x_)))
                  (list '* '(* n_ (recip n_)) '(* x_ (- 1 x_))))
         (lambda () (crs)))
  (subst (list '= (list '* '(* 1 (recip n_)) (list '* bmo-nx '(- 1 x_)))
                  (list '* '(* n_ (recip n_)) '(* x_ (- 1 x_)))))
  (subst '(= (* n_ (recip n_)) 1))
  (sos "x_ - 1/2" "1")))
(bmo-check 'bernstein-variance-bound)
(qed 'bernstein-variance-bound)
(topic! 'bernstein-variance-bound 'analysis)
(alias! 'bernstein-variance-bound
        "the Bernstein variance bound"
        "Proposition 5.4 (76)")
