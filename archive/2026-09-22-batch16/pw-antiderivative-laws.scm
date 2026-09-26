;;; pw-antiderivative-laws.scm -- the laws of IS-PW-CONTINUOUS-ON,
;;; IS-PW-ANTIDERIVATIVE and PW-INT (structure-library/path-integral.scm).
;;;
;;; THE SPECIFICATION is docs/paths-and-line-integrals-2026-09-21.md s.3.2, and
;;; the statement checks that were made before any proof was written are in the
;;; header of the definition file.
;;;
;;; STAGE 1: the read-offs; the two-point partition; the INTRODUCTION rule for a
;;;   function differentiable at every interior point (one piece).
;;; STAGE 2: constancy.  A function continuous on [a,b] whose derivative is 0 on
;;;   an open subinterval takes equal values at that subinterval's endpoints
;;;   (`pw-zero-deriv-subinterval'), and the telescoping version over a whole
;;;   partition (`pw-zero-deriv-partition').
;;; STAGE 3: the WITNESS -- an affine function is a piecewise antiderivative of
;;;   the constant slope, so neither predicate is vacuous -- and uniqueness of
;;;   the endpoint difference for one-piece antiderivatives.
;;;
;;; WHAT IS NOT PROVED HERE, AND EXACTLY WHY.  See the closing block: PW-INT's
;;; `iota-d' obligation is the endpoint difference for antiderivatives with
;;; ARBITRARY and DIFFERENT partitions, and the step it needs is the COMMON
;;; REFINEMENT of two partitions, which the tree cannot yet build.
;;;
;;; Helper prefix: pw-.
;;;
;;; Dependencies: structure-library/path-integral.scm; structure-library/
;;; regulated.scm (IS-PARTITION); structure-library/interval-calculus.scm;
;;; theorem-library/interval-calculus-laws.scm (ooint-*, has-deriv-at-*,
;;; subspace-restrict-continuous-at, restrict-in-fun-of-restrict);
;;; theorem-library/interval-mvt.scm (mvt-abs-bound-on-interval);
;;; theorem-library/has-deriv-at-more.scm (has-deriv-at-const, -affine,
;;; -difference); theorem-library/ccint-basics.scm; monotone-inverse.scm
;;; (ccint-subset-rr); metric-subspace-laws.scm (restrict-apply, restrict-in-fun,
;;; restrict-continuous-at, subspace-pts, subspace-is-metric-space);
;;; ms-continuity-algebra.scm (ms-cont-transfer-ptwise-eq);
;;; differentiation.scm (diff-implies-continuous); directional-derivative.scm
;;; (deriv-affine, affine-lam-in-fun); rr-abs-basics.scm (rr-abs-bound,
;;; rr-abs-zero); rr-order-basics.scm (rr-min-pos, rr-lt-scale-pos);
;;; nn-order-* (nn-in-rr, nn-pos-of-nonzero, nn-one-in); finite-surgery.scm
;;; (nn-lt-succ-le); subset-lemmas.scm (subset-mem-fwd, subset-trans);
;;; interval-membership.scm; contra.

;;; ---- file-local driver helpers ---------------------------------------

(define (pw-head g) (and (pair? g) (car g)))

(define pw-cc '(CCINT a b))
(define pw-sub (list 'SUBSPACE-MS 'RR-MS pw-cc))

;;; the membership of a closed interval, landed as its three conjuncts.
(define (pw-ccint-in! y lo hi)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ccint-membership (list 'IN y (list 'CCINT lo hi)))))))

;;; the membership of an open interval, landed as its three conjuncts.
(define (pw-ooint-in! y lo hi)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN y (list 'OOINT lo hi)))))))

;;; close an AND goal conjunct by conjunct: `ass' when the conjunct is already
;;; in the context, `dk-ineq!' with PREMS named by FORMULA otherwise.
(define (pw-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

;;; unfold an IS-PW-ANTIDERIVATIVE hypothesis and split it into its conjuncts.
(define (pw-open! form)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'IS-PW-ANTIDERIVATIVE form)))))

;;; =====================================================================
;;; (0) ONE NN FACT.  A natural below 1 is 0.  Needed wherever a ONE-PIECE
;;; partition is used: the index universal of IS-PW-ANTIDERIVATIVE runs over
;;; every i in INTERVAL(0,1) with i < 1, and the driver has to know that the
;;; only such i is 0 before it can evaluate p(i) and p(succ i).
;;; =====================================================================
(sp (make-wff '(FORALL pai_ (IMPLIES (IN pai_ NN)
     (IMPLIES (< pai_ 1) (= pai_ 0))))))
(dk-peel!)
(fact 'nn-in-rr 'pai_)
(fact 'rr-one-in)
(fact 'rr-zero-in)
(fact 'nn-zero-in)
(use-em '(= pai_ 0)
  (lambda () (ass))
  (lambda ()
    (fact 'nn-pos-of-nonzero 'pai_)
    (fact 'nn-lt-succ-le 0 'pai_)
    (have! '(= 1 (SUCC 0)) (lambda () (arith)))
    (have! '(<= 1 pai_) (lambda () (subst '(= 1 (SUCC 0))) (ass)))
    ;; `contra' declines here (it reports the context satisfiable), so the
    ;; contradiction is taken by hand: pai_ < 1 denies 1 <= pai_, and `ai' on
    ;; the NOT is NOT-elim, which closes the branch whatever the goal is.
    (fact 'rr-lt-not-le 'pai_ 1)
    (ai '(NOT (<= 1 pai_)))))
(qed 'nn-below-one-is-zero)
(topic! 'nn-below-one-is-zero 'inequalities)
(alias! 'nn-below-one-is-zero "a natural number below one is zero")

;;; =====================================================================
;;; (1) THE READ-OFFS OF IS-PW-ANTIDERIVATIVE.
;;; =====================================================================

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
            (AND (IN a RR) (AND (IN b RR) (< a b))))))))))
(dk-peel!)
(pw-open! '(IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b))
(dk-conj-close! (lambda () (ass)))
(qed 'pw-antiderivative-endpoints)
(topic! 'pw-antiderivative-endpoints 'analysis)

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
            (IN pwf_ (FUN (CCINT a b) RR)))))))))
(dk-peel!)
(pw-open! '(IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b))
(ass)
(qed 'pw-antiderivative-in-fun)
(topic! 'pw-antiderivative-in-fun 'analysis)

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
            (IN pphi_ (FUN (CCINT a b) RR)))))))))
(dk-peel!)
(pw-open! '(IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b))
(ass)
(qed 'pw-antiderivative-integrand-in-fun)
(topic! 'pw-antiderivative-integrand-in-fun 'analysis)

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
            (IS-CONTINUOUS-ON pwf_ (CCINT a b)))))))))
(dk-peel!)
(pw-open! '(IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b))
(ass)
(qed 'pw-antiderivative-continuous)
(topic! 'pw-antiderivative-continuous 'analysis)

;;; the values of a piecewise antiderivative are reals -- what every endpoint
;;; difference needs before it can be an arithmetic term.
(sp (make-wff "forall([pwf_, pphi_, a, b],
   is-pw-antiderivative(pwf_, pphi_, a, b) implies
   forall([pay_ in ccint(a,b)], pwf_(pay_) in rr))"))
(dk-peel!)
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(let ((z (cadr (cadr (dk-goal)))))
  (fact 'fun-apply-type-c 'pwf_ (list 'CCINT 'a 'b) 'RR z)
  (ass))
(qed 'pw-antiderivative-value-in-rr)
(topic! 'pw-antiderivative-value-in-rr 'analysis)

;;; =====================================================================
;;; (2) THE TWO-POINT PARTITION.  p(k) = a + (b - a) * k is a partition of
;;; [a,b] into ONE piece: p(0) = a, p(1) = b, and it is strictly increasing on
;;; the whole of NN, which is more than IS-PARTITION asks for and costs less
;;; than an IF-tower (`rr-lt-scale-pos' once, no case analysis, no appeal to
;;; INTERVAL(0,1) = {0,1}).
;;; =====================================================================
(define pw-p2 '(VNB-LAMBDA pak_ NN (+ a (* (- b a) pak_))))

(sp (make-wff (forall-guarded '(a b) '((IN a RR) (IN b RR))
     (list 'IMPLIES '(< a b) (list 'IS-PARTITION pw-p2 1 'a 'b)))))
(dk-peel!)
(fact 'nn-one-in)
(fact 'nn-zero-in)
(fact 'nn-is-set)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'nn-le-refl 1)
(fact 'rr-sub-in-rr 'b 'a)
(fact 'rr-lt-diff-pos 'a 'b)
(mac 'IS-PARTITION)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ;; the FUN typing
       ((and (eq? (pw-head g) 'IN) (equal? (caddr g) '(FUN NN RR)))
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (pw-head (dk-goal)) 'FORALL)
               (let ((z (dk-di-var!)))
                 (fact 'nn-in-rr z)
                 (have! (list 'AND '(IN (- b a) RR) (list 'IN z 'RR)))
                 (fact 'rr-mul-closed '(- b a) z)
                 (have! (list 'AND '(IN a RR) (list 'IN (list '* '(- b a) z) 'RR)))
                 (fact 'rr-add-closed 'a (list '* '(- b a) z))
                 (ass))
               (ass)))
         (dk-opened (lambda () (lam-t)))))
       ;; the two endpoint values
       ((eq? (pw-head g) '=)
        (dk-lam-b!)
        (crs))
       ;; monotonicity
       ((eq? (pw-head g) 'FORALL)
        (dk-peel!)
        (dk-split-all!)
        (let* ((gl (dk-goal))
               (iv (cadr (cadr gl)))
               (jv (cadr (caddr gl))))
          (fact 'interval-elt-in-nn 0 1 iv)
          (fact 'interval-elt-in-nn 0 1 jv)
          (fact 'nn-in-rr iv)
          (fact 'nn-in-rr jv)
          (have! (list 'AND '(IN (- b a) RR) (list 'IN iv 'RR)))
          (fact 'rr-mul-closed '(- b a) iv)
          (have! (list 'AND '(IN (- b a) RR) (list 'IN jv 'RR)))
          (fact 'rr-mul-closed '(- b a) jv)
          (have! (list 'AND '(< 0 (- b a)) (list '< iv jv)))
          (fact 'rr-lt-scale-pos '(- b a) iv jv)
          (dk-lam-b!)
          (dk-ineq! '(IN a RR)
                    (list 'IN (list '* '(- b a) iv) 'RR)
                    (list 'IN (list '* '(- b a) jv) 'RR)
                    (list '< (list '* '(- b a) iv) (list '* '(- b a) jv)))))
       (#t (ass))))))
(qed 'pw-two-point-partition)
(topic! 'pw-two-point-partition 'analysis)
(alias! 'pw-two-point-partition
        "the two endpoints form a partition of the interval into one piece")

;;; =====================================================================
;;; (3) THE INTRODUCTION RULE.  A function differentiable at EVERY interior
;;; point is a piecewise antiderivative -- the one-piece case, and the only
;;; introduction rule this batch needs.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pwf_, pphi_],
    pwf_ in fun(ccint(a,b), rr) implies
    pphi_ in fun(ccint(a,b), rr) implies
    is-continuous-on(pwf_, ccint(a,b)) implies
    forall([pat_ in ooint(a,b)], has-deriv-at(pwf_, pat_, pphi_(pat_))) implies
    is-pw-antiderivative(pwf_, pphi_, a, b)))"))
(dk-peel!)
(fact 'nn-one-in)
(fact 'nn-zero-in)
(fact 'pw-two-point-partition 'a 'b)
(define pw-ip-univ
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the interior differentiability universal"))
(mac 'IS-PW-ANTIDERIVATIVE)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (pw-head (dk-goal)) 'FORSOME))
       (ass)
       (begin
         (ew 1)
         (ew pw-p2)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (pw-head (dk-goal)) 'FORALL))
                (ass)
                ;; `di' lands NOTHING on either of these two universals -- the
                ;; guard is an AND, not an (IN y _) -- so the eigenvariables are
                ;; read off the GOAL and the CONTEXT after one dk-peel!, never
                ;; from dk-di-var! (which wants a landing).
                (begin
                  (dk-peel!)
                  (dk-split-all!)
                  (let* ((tv (caddr (dk-goal)))
                         (iv (cadr (dk-pick
                                    (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                     (equal? (caddr f) '(INTERVAL 0 1))))
                                    "the index typing"))))
                    (fact 'interval-elt-in-nn 0 1 iv)
                    (fact 'nn-below-one-is-zero iv)
                    (fact 'ccint-elt-in-rr 'a 'b tv)
                    (dk-have! (list '= (list pw-p2 iv) 'a)
                      (lambda ()
                        (subst (list '= iv 0))
                        (dk-lam-b!)
                        (crs)))
                    (dk-have! (list '= (list pw-p2 (list 'SUCC iv)) 'b)
                      (lambda ()
                        (subst (list '= iv 0))
                        (have! '(= (SUCC 0) 1) (lambda () (arith)))
                        (subst '(= (SUCC 0) 1))
                        (dk-lam-b!)
                        (crs)))
                    (dk-have! (list '< 'a tv)
                      (lambda () (subst (list '= 'a (list pw-p2 iv))) (ass)))
                    (dk-have! (list '< tv 'b)
                      (lambda () (subst (list '= 'b (list pw-p2 (list 'SUCC iv)))) (ass)))
                    (dk-have! (list 'IN tv '(OOINT a b))
                      (lambda ()
                        (mac 'ooint-membership)
                        (dk-conj-close! (lambda () (ass)))))
                    (dk-apply! pw-ip-univ tv)
                    (ass))))))))))
(qed 'pw-antiderivative-one-piece)
(topic! 'pw-antiderivative-one-piece 'analysis)
(alias! 'pw-antiderivative-one-piece
        "a function differentiable at every interior point is a piecewise antiderivative")

;;; =====================================================================
;;; (4) AN INNER RADIUS.  Every point of an open interval has a symmetric
;;; open interval about it inside the CLOSED one.  This is `ooint-open' with
;;; the ball replaced by an interval and the conclusion strengthened to land
;;; inside [u,v]; it is what every local argument on an interval needs, and
;;; nothing in interval-calculus-laws.scm states it.
;;; =====================================================================
(sp (make-wff "forall([pbu_ in rr, pbv_ in rr],
   forall([pbt_ in ooint(pbu_, pbv_)],
     forsome([pbr_], pos-rr(pbr_) and
        subset(ooint(pbt_ - pbr_, pbt_ + pbr_), ccint(pbu_, pbv_)))))"))
(dk-peel!)
(pw-ooint-in! 'pbt_ 'pbu_ 'pbv_)
(fact 'rr-sub-in-rr 'pbt_ 'pbu_)
(fact 'rr-sub-in-rr 'pbv_ 'pbt_)
(fact 'rr-zero-in)
(dk-have! '(< 0 (- pbt_ pbu_))
  (lambda () (dk-ineq! '(IN pbu_ RR) '(IN pbt_ RR) '(< pbu_ pbt_))))
(dk-have! '(< 0 (- pbv_ pbt_))
  (lambda () (dk-ineq! '(IN pbv_ RR) '(IN pbt_ RR) '(< pbt_ pbv_))))
(let ((w (dk-skolem! (dk-fact! 'rr-min-pos '(- pbt_ pbu_) '(- pbv_ pbt_)))))
  (dk-split-all!)
  (fact 'rr-pos-rr-of-lt w)
  (fact 'rr-sub-in-rr 'pbt_ w)
  (fact 'rr-add-in-rr 'pbt_ w)
  (ew w)
  (dk-conj-close!
   (lambda ()
     (if (eq? (pw-head (dk-goal)) 'POS-RR)
         (ass)
         (let ((z (subset-by-element!)))
           (pw-ooint-in! z (list '- 'pbt_ w) (list '+ 'pbt_ w))
           (mac 'ccint-membership)
           (pw-conj-ineq!
            (list '(IN pbu_ RR) '(IN pbv_ RR) '(IN pbt_ RR) (list 'IN z 'RR)
                  (list 'IN w 'RR)
                  (list '<= w '(- pbt_ pbu_)) (list '<= w '(- pbv_ pbt_))
                  (list '< (list '- 'pbt_ w) z) (list '< z (list '+ 'pbt_ w)))))))))
(qed 'ooint-inner-radius)
(topic! 'ooint-inner-radius 'topology)
(alias! 'ooint-inner-radius
        "a point interior to an interval has a symmetric interval about it inside")

;;; =====================================================================
;;; (5) CONTINUITY ON THE INTERVAL FROM CONTINUITY ON THE LINE.  A function on
;;; [a,b] that agrees pointwise with a function continuous on the whole line is
;;; continuous on [a,b] IN THE SUBSPACE SENSE -- which is what IS-CONTINUOUS-ON
;;; means and what the witness below has to supply.  Two citations:
;;; `restrict-continuous-at' takes the total function's continuity down to the
;;; subspace, and `ms-cont-transfer-ptwise-eq' moves it along the pointwise
;;; equality to the function that is actually named.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([f, pwf_],
    f in fun(rr, rr) implies
    forall([pay_ in rr], is-continuous-at(rr-ms, rr-ms, f, pay_)) implies
    pwf_ in fun(ccint(a,b), rr) implies
    forall([pay_ in ccint(a,b)], pwf_(pay_) == f(pay_)) implies
    is-continuous-on(pwf_, ccint(a,b))))"))
(dk-peel!)
(fact 'rr-is-metric-space)
(define pw-rc-cont
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
           "the continuity universal"))
(define pw-rc-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pwf_) (dk-contains? fm 'f)))
           "the pointwise agreement"))
(dk-have! '(SUBSET (CCINT a b) (PTS RR-MS))
  (lambda () (slot 'PTS) (fact 'ccint-subset-rr 'a 'b) (ass)))
(fact 'subspace-pts 'RR-MS pw-cc)
(mac 'IS-CONTINUOUS-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (pw-head (dk-goal)) 'FORALL))
       (ass)
       (let ((z (dk-di-var!)))
         (fact 'ccint-elt-in-rr 'a 'b z)
         (dk-apply! pw-rc-cont z)
         (fact 'restrict-continuous-at 'RR-MS pw-cc 'RR-MS 'f z)
         (dk-have! (list 'IN 'pwf_ (list 'FUN (list 'PTS pw-sub) '(PTS RR-MS)))
           (lambda ()
             (subst (list '== (list 'PTS pw-sub) pw-cc))
             (slot 'PTS)
             (ass)))
         (dk-have! (list 'FORALL 'msz_
                     (list 'IMPLIES (list 'IN 'msz_ (list 'PTS pw-sub))
                       (list '= (list 'pwf_ 'msz_)
                             (list (list 'RESTRICT 'f pw-cc) 'msz_))))
           (lambda ()
             (let ((y (dk-di-var!)))
               ;; the GOAL holds CCINT and the context holds PTS(subspace), so
               ;; the rewrite goes CCINT -> PTS: `subst' rewrites in the
               ;; direction of its ARGUMENT, and there is nothing to rewrite the
               ;; other way round.
               (dk-have! (list 'IN y pw-cc)
                 (lambda () (subst (list '== pw-cc (list 'PTS pw-sub))) (ass)))
               (fact 'ccint-elt-in-rr 'a 'b y)
               (fact 'restrict-apply 'f pw-cc y)
               (dk-apply! pw-rc-agree y)
               (subst (list '== (list (list 'RESTRICT 'f pw-cc) y) (list 'f y)))
               (subst (list '== (list 'pwf_ y) (list 'f y)))
               (rfl))))
         (fact 'ms-cont-transfer-ptwise-eq pw-sub 'RR-MS
               (list 'RESTRICT 'f pw-cc) 'pwf_ z)
         (ass)))))
(qed 'pw-restrict-continuous-on)
(topic! 'pw-restrict-continuous-on 'analysis)
(alias! 'pw-restrict-continuous-on
        "a function on an interval agreeing with a continuous function on the line is continuous on it")

;;; =====================================================================
;;; (6) THE WITNESS.  AN AFFINE FUNCTION ON [a,b] IS A PIECEWISE
;;; ANTIDERIVATIVE OF ITS CONSTANT SLOPE.  This is what makes
;;; IS-PW-ANTIDERIVATIVE non-vacuous, and it is the form the line-segment path
;;; of road-laws.scm consumes: the statement is a TRANSFER -- pwf_ and pphi_
;;; are GIVEN, agreeing pointwise with the affine map and with the constant --
;;; so no consumer owes a beta-reduction under a binder.
;;;
;;; The two instances: pam_ = 0 gives the constant function with integrand 0;
;;; (pac_, pam_) = (0, 1) gives the identity with integrand 1.
;;; =====================================================================
(define pw-aff '(VNB-LAMBDA x RR (+ pac_ (* pam_ x))))

(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pac_ in rr, pam_ in rr, pwf_, pphi_],
    pwf_ in fun(ccint(a,b), rr) implies
    pphi_ in fun(ccint(a,b), rr) implies
    forall([pay_ in ccint(a,b)], pwf_(pay_) == pac_ + pam_ * pay_) implies
    forall([pay_ in ccint(a,b)], pphi_(pay_) == pam_) implies
    is-pw-antiderivative(pwf_, pphi_, a, b)))"))
(dk-peel!)
(define pw-af-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pwf_)))
           "the affine agreement"))
(define pw-af-phi
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pphi_)))
           "the integrand agreement"))
(have! '(AND (IN pac_ RR) (IN pam_ RR)))
(fact 'affine-lam-in-fun 'pac_ 'pam_)
;; the total affine map is continuous everywhere ...
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES '(IN pay_ RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS pw-aff 'pay_)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (have! (list 'AND '(IN pac_ RR) (list 'AND '(IN pam_ RR) (list 'IN y 'RR))))
      (fact 'deriv-affine 'pac_ 'pam_ y)
      (fact 'diff-implies-continuous pw-aff y 'pam_)
      (ass))))
;; ... and pwf_ agrees with it on [a,b], so pwf_ is continuous on [a,b].
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pw-cc)
            (list '== (list 'pwf_ 'pay_) (list pw-aff 'pay_))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b y)
      (dk-apply! pw-af-agree y)
      (dk-lam-b!)
      (ass))))
(fact 'pw-restrict-continuous-on 'a 'b pw-aff 'pwf_)
;; the derivative at every interior point.
(dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
            (list 'HAS-DERIV-AT 'pwf_ 'pat_ '(pphi_ pat_))))
  (lambda ()
    (let ((tv (dk-di-var!)))
      (fact 'ooint-elt-in-rr 'a 'b tv)
      (fact 'ooint-subset-ccint 'a 'b)
      (fact 'subset-mem-fwd '(OOINT a b) pw-cc tv)
      (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b tv))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr rv)
        (fact 'rr-sub-in-rr tv rv)
        (fact 'rr-add-in-rr tv rv)
        (let ((oo (list 'OOINT (list '- tv rv) (list '+ tv rv))))
          (fact 'restrict-in-fun 'pwf_ pw-cc 'RR oo)
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ oo)
                      (list '== '(pwf_ hbx_) '(+ pac_ (* pam_ hbx_)))))
            (lambda ()
              (let ((y (dk-di-var!)))
                (fact 'subset-mem-fwd oo pw-cc y)
                (dk-apply! pw-af-agree y)
                (ass))))
          (fact 'has-deriv-at-affine rv 'pwf_ 'pac_ 'pam_ tv)
          (dk-apply! pw-af-phi tv)
          (subst (list '== (list 'pphi_ tv) 'pam_))
          (ass))))))
(fact 'pw-antiderivative-one-piece 'a 'b 'pwf_ 'pphi_)
(ass)
(qed 'pw-affine-antiderivative)
(topic! 'pw-affine-antiderivative 'analysis)
(alias! 'pw-affine-antiderivative
        "an affine function on an interval is a piecewise antiderivative of its slope")

;;; =====================================================================
;;; (7) PW-INT.  THE VALUE THEOREM, WITH THE UNIQUENESS OBLIGATION AS AN
;;; EXPLICIT HYPOTHESIS.
;;;
;;; PW-INT is a definite description, so `iota-d' posts TWO obligations:
;;; EXISTENCE, which the given antiderivative discharges, and UNIQUENESS -- that
;;; ANY piecewise antiderivative of the same phi has the same endpoint
;;; difference.  Uniqueness for antiderivatives with ARBITRARY and DIFFERENT
;;; partitions is NOT proved in this batch (see the closing block), so it is
;;; carried here as a HYPOTHESIS.  Everything else about PW-INT is proved, and
;;; the day the common-refinement lemma lands, this theorem loses its second
;;; antecedent by one citation and `pw-int-value' is unconditional.
;;;
;;; The statement is a strict `=' on an IOTA term, which asserts its
;;; definedness: that is exactly what the two antecedents earn, and it is why
;;; no law of PW-INT is stated without them (definition file, statement check
;;; (2)).
;;; =====================================================================
(define (pw-diff f) (list '- (list f 'b) (list f 'a)))

(define (pw-obtain!)
  (let ((z (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
    (dk-landed* (lambda () (dk-split! z)))))

(define (pw-witness parts)
  (cadr (car (filter (dk-head? 'IS-PW-ANTIDERIVATIVE) parts))))

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
     (IMPLIES (FORALL paw_ (IMPLIES (IS-PW-ANTIDERIVATIVE paw_ pphi_ a b)
                 (= (- (paw_ b) (paw_ a)) (- (pwf_ b) (pwf_ a)))))
              (= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a)))))))))))
(dk-peel-to! '=)
;; CAPTURED BEFORE ANY CITATION.  `fact' lands its WHOLE instantiation chain,
;; the universal theorem included, and `pw-antiderivative-in-fun' is itself a
;; FORALL containing IS-PW-ANTIDERIVATIVE: picked after the citations, this
;; would find the THEOREM and instantiate it at the eigenvariable instead.
(define pw-uniq
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-PW-ANTIDERIVATIVE)))
           "the uniqueness hypothesis"))
(dk-split! (dk-fact! 'pw-antiderivative-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'b)
(dk-have! (list 'IN 'a pw-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(dk-have! (list 'IN 'b pw-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'a)
(fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'b)
(fact 'rr-sub-in-rr '(pwf_ b) '(pwf_ a))
(mac 'pw-int)
(define pw-io (cadr (dk-goal)))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (pw-head (dk-goal)) 'FORSOME)
       (begin
         (ew (pw-diff 'pwf_))
         (for-each
          (lambda (nd)
            (dk-focus! nd)
            (if (eq? (pw-head (dk-goal)) 'FORALL)
                ;; ---- UNIQUENESS: any other value equals pwf_(b) - pwf_(a) --
                (begin
                  (di)
                  (dk-split! (dk-landed-1 (lambda () (di))))
                  (let* ((y  (caddr (dk-goal)))
                         (ps (pw-obtain!))
                         (g  (pw-witness ps)))
                    (dk-apply! pw-uniq g)
                    (fact 'eq-sym (pw-diff g) (pw-diff 'pwf_))
                    (fact 'eq-sym y (pw-diff g))
                    (fact 'eq-trans (pw-diff 'pwf_) (pw-diff g) y)
                    (ass)))
                ;; ---- EXISTENCE: pwf_ itself is the witness ----------------
                (for-each
                 (lambda (m)
                   (dk-focus! m)
                   (if (eq? (pw-head (dk-goal)) 'IN)
                       (ass)
                       (begin
                         (ew 'pwf_)
                         (for-each (lambda (k)
                                     (dk-focus! k)
                                     (if (eq? (pw-head (dk-goal)) '=) (rfl) (ass)))
                                   (dk-opened (lambda () (di)))))))
                 (dk-opened (lambda () (di))))))
          (dk-opened (lambda () (di)))))
       ;; ---- THE MAIN BRANCH ------------------------------------------------
       (let ((def (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'AND)
                                                (dk-contains? z 'IOTA)))
                               (dk-asms)))))
         (dk-split! def)
         (let* ((ps (pw-obtain!))
                (g  (pw-witness ps)))
           (dk-apply! pw-uniq g)
           (fact 'eq-trans pw-io (pw-diff g) (pw-diff 'pwf_))
           (ass)))))
 (dk-opened (lambda () (iota-d pw-io))))
(qed 'pw-int-value)
(topic! 'pw-int-value 'analysis)
(alias! 'pw-int-value
        "the piecewise integral is F(b) - F(a) for any piecewise antiderivative F")

;;; pw-int-in-rr: the integral is a REAL wherever it is defined -- i.e. the
;;; description is non-empty there.  One `subst' off pw-int-value.
(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
     (IMPLIES (FORALL paw_ (IMPLIES (IS-PW-ANTIDERIVATIVE paw_ pphi_ a b)
                 (= (- (paw_ b) (paw_ a)) (- (pwf_ b) (pwf_ a)))))
              (IN (PW-INT pphi_ a b) RR)))))))))
(dk-peel-to! 'IN)
(dk-split! (dk-fact! 'pw-antiderivative-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'b)
(dk-have! (list 'IN 'a pw-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(dk-have! (list 'IN 'b pw-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'a)
(fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'b)
(fact 'rr-sub-in-rr '(pwf_ b) '(pwf_ a))
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(subst (list '= '(PW-INT pphi_ a b) (pw-diff 'pwf_)))
(ass)
(qed 'pw-int-in-rr)
(topic! 'pw-int-in-rr 'analysis)
(alias! 'pw-int-in-rr "the piecewise integral of an antiderivable function is a real")

;;; =====================================================================
;;; WHAT IS NOT PROVED, AND EXACTLY WHAT IT NEEDS.
;;;
;;; THE ONE MISSING FACT is the UNCONDITIONAL uniqueness obligation of PW-INT:
;;;
;;;    IS-PW-ANTIDERIVATIVE(F, phi, a, b)  and  IS-PW-ANTIDERIVATIVE(G, phi, a, b)
;;;         ==>  F(b) - F(a) = G(b) - G(a)
;;;
;;; With it, `pw-int-value' and `pw-int-in-rr' above lose their second
;;; antecedent by ONE citation and PW-INT, CC-INT and LINE-INT all become
;;; computable; without it the two theorems are still usable, but the caller
;;; carries the hypothesis.
;;;
;;; WHY IT IS NOT HERE.  The mathematics is the mean value theorem on each
;;; piece: H = F - G has derivative 0 at every interior point of every piece,
;;; so `mvt-abs-bound-on-interval' at m = 0 makes H constant across each piece,
;;; and continuity at the partition points telescopes.  THE STEP THAT IS
;;; MISSING IS NOT THE ANALYSIS: it is that F and G carry DIFFERENT partitions,
;;; and the argument runs on a COMMON REFINEMENT -- an increasing enumeration
;;; of the union of two finite sets of reals.  The tree has no such lemma, and
;;; building one means enumerating a finite subset of RR in increasing order,
;;; which is a combinatorial development of its own.
;;;
;;; THE ROUTE THAT AVOIDS THE REFINEMENT, written down so that the next agent
;;; does not rediscover it.  State constancy with the exceptional set given as
;;; an arbitrary FINITE SET rather than as a partition, and with the function's
;;; interval [c,d] SEPARATE from the interval [u,v] the conclusion is about:
;;;
;;;   forall finite S.  forall H, c, d, u, v:
;;;      H in FUN(CCINT(c,d), RR),  IS-CONTINUOUS-ON(H, CCINT(c,d)),
;;;      c <= u,  u < v,  v <= d,
;;;      (forall t in OOINT(u,v) with t not in S:  HAS-DERIV-AT(H, t, 0))
;;;         ==>  H(v) = H(u)
;;;
;;; by `finite-set-induction' on S (rake-card-star-laws.scm).  Base S = {}: the
;;; subinterval form of `mvt-abs-bound-on-interval' at m = 0.  Step S u {s}:
;;; if s is not in OOINT(u,v) the induction hypothesis applies unchanged; if it
;;; is, apply it TWICE, to (u,s) and to (s,v), and compose -- which is why the
;;; ambient interval [c,d] must be a separate pair, so that no restriction of H
;;; is ever formed.  The union of the two partitions' point sets is then
;;; IMAGE(p, INTERVAL(0,n)) u IMAGE(q, INTERVAL(0,m)), finite by
;;; `card-image-finite', and `partition-locates-point' puts every t outside it
;;; strictly inside a piece of each partition.
;;;
;;; STILL OWED after that: PW-INT of a constant and linearity (both one
;;; `pw-int-value' plus `pw-affine-antiderivative' once uniqueness is
;;; unconditional), additivity over adjacent intervals, the estimate (45),
;;; juxtaposition, and LINE-INT(1, gamma, dgamma, a, b) = gamma(b) - gamma(a)
;;; -- which is `pw-int-value' on each coordinate of a road (the two
;;; IS-PW-ANTIDERIVATIVE conjuncts are read off by `is-road-re-antiderivative'
;;; and `is-road-im-antiderivative', road-laws.scm) plus `cc-re-im-decompose'.
;;; =====================================================================
