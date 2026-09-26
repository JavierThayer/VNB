;;; has-deriv-at-chain.scm -- THE CHAIN RULE FOR THE LOCAL DERIVATIVE, and the
;;; corollary at an affine inner map.
;;;
;;; THE SOURCE IS THE USER'S NOTES, ~/docs/calculus.pdf, section 2.3 "Chain
;;; Rule", Proposition 2.8:
;;;
;;;     "Suppose f --> R is defined in a neighborhood U of a and g is defined
;;;      in a neighborhood V of f(a).  Suppose f is differentiable at a and g
;;;      is differentiable at f(a).  Then g o f is differentiable at a and
;;;                                                                     (13)
;;;              (g o f)'(a) = g'(f(a)) . f'(a)."
;;;
;;; Here `f is differentiable at a' is HAS-DERIV-AT(f, a, l), which already
;;; SAYS "f is defined in a neighbourhood of a": HAS-DERIV-AT is false, not
;;; undefined, when the domain of f misses a neighbourhood of the point
;;; (structure-library/interval-calculus.scm, the header).  So the notes' two
;;; neighbourhood clauses are not extra hypotheses below; they are carried by
;;; the two HAS-DERIV-AT hypotheses.
;;;
;;; ---------------------------------------------------------------------
;;; HOW `g o f' IS WRITTEN, AND WHY.
;;;
;;; The tree has no composition operator on functions defined on different
;;; sets, and a sum or a composite of two functions on an interval is not a
;;; term it can form.  Every rule of interval-calculus-laws.scm section (8)
;;; -- `has-deriv-at-sum', `has-deriv-at-product' -- is therefore stated for
;;; ANY h that agrees with the combination on a neighbourhood of the point,
;;; which is the shape every caller has in hand and is exactly what locality
;;; makes harmless.  This file keeps that shape:
;;;
;;;     restrict(h, ooint(x - r, x + r)) in fun(ooint(x - r, x + r), rr)
;;;     forall([y in ooint(x - r, x + r)], h(y) == g(f(y)))
;;;
;;; is the transfer form of `h = g o f near x'.  The FUN typing of the
;;; restriction is a hypothesis and is not redundant: pointwise agreement with
;;; a composite says nothing about h being a set of pairs at all
;;; (diff-transfer.scm:42, and the same note in `has-deriv-at-local').
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT CHECKS, against CLAUDE.md's species of false or
;;; underdetermined statement, made before any proof was written.
;;;
;;; (1) THE COMPOSITE NEEDS f TO MAP A NEIGHBOURHOOD OF x INTO THE DOMAIN OF
;;;     g.  This is the one place where a false statement could hide, and it is
;;;     NOT taken as a hypothesis, because it is a CONSEQUENCE: f has a
;;;     derivative at x, hence is continuous at x (`diff-on-implies-continuous'
;;;     through the window HAS-DERIV-AT provides), and g has a derivative at
;;;     f(x), hence is defined on a whole open interval about f(x); continuity
;;;     pulls that interval back to a window about x.  `has-deriv-at-maps-into'
;;;     below is exactly that statement, proven, and it is what discharges the
;;;     third antecedent of `diff-on-chain'.
;;;
;;; (2) NO STRICT `=' BETWEEN POSSIBLY UNDEFINED TERMS.  The conclusion is a
;;;     PREDICATE application, HAS-DERIV-AT(h, x, m * l); m and l are reals
;;;     (`has-deriv-at-in-rr'), so `m * l' is arithmetic on number-typed
;;;     arguments and is certified defined.  The agreement hypotheses use `=='
;;;     (quasi-equality), not `='.
;;;
;;; (3) EVERY INSTANTIATION AT f(x) IS EARNED FIRST.  `f(x)' is an APPLICATION
;;;     and the LUTINS certificate never accepts one on its own; the very first
;;;     citation of each proof is `has-deriv-at-value-in-rr', which lands
;;;     (IN (f x) RR) and thereby certifies the term for everything after it.
;;;
;;; (4) NO GUARD IS MISSING ON THE RADII.  r, and every radius minted below, is
;;;     POS-RR; the windows are OOINT(x - r, x + r), which is EMPTY for a
;;;     non-positive radius -- deliberately, and harmlessly, since nothing here
;;;     is stated for one.
;;;
;;; (5) THE AFFINE COROLLARY's inner map is total.  `has-deriv-at-affine-chain'
;;;     is the composite with t |-> p + q t, p and q real; the inner map is the
;;;     VNB-LAMBDA on all of RR, so its own derivative is `has-deriv-at-affine'
;;;     and no extra domain condition arises.  With p = a + b and q = -1 it is
;;;     the reflection of [a, b] that the opposite road needs.
;;;
;;; ---------------------------------------------------------------------
;;; Helper prefix: cr-.  Binder names: crr_ crx_ cry_ crz_ crl_ crm_ crd_ crb_
;;; crw_ crp_ crq_ crv_ -- none folds onto a registered constant, a class name
;;; (NN ZZ QQ RR CC ORD SET EMPTY-SET POS-INF NEG-INF RR-STAR RR-POS-STAR) or
;;; an accessor, and none is a name a predicate body in the cone instantiates
;;; at.
;;;
;;; Dependencies: structure-library/interval-calculus.scm;
;;; theorem-library/interval-calculus-laws.scm (has-deriv-at-intro / -shrink /
;;; -pt-in-rr / -in-rr, diff-on-ooint-shrink, ooint-*), diff-on-laws.scm
;;; (diff-on-implies-continuous, nf-rr-agree-dist, rr-nf-*), diff-on-laws-2.scm
;;; (diff-on-chain), holomorphic-basics-2.scm (diff-on-transfer-ptwise-eq),
;;; metric-subspace-laws.scm (subspace-pts, subspace-dist, restrict-apply,
;;; restrict-in-fun), has-deriv-at-more.scm (has-deriv-at-value-in-rr,
;;; has-deriv-at-affine).

;;; ---- file-local driver helpers ---------------------------------------

(define (cr-head g) (and (pair? g) (car g)))

;;; the membership of an open interval, landed as its three conjuncts
(define (cr-ooint-in! y a b)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN y (list 'OOINT a b)))))))

;;; close an AND goal conjunct by conjunct: `ass' when the conjunct is already
;;; in the context, otherwise `ineq' with the premises named by FORMULA
(define (cr-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

(define cr-nfm '(NF-METRIC-SPACE RR-NORMED-FIELD))

;;; =====================================================================
;;; (1) THE DOMAIN CONDITION, PROVEN: f MAPS A WINDOW INTO ANY WINDOW
;;;     ABOUT f(x).
;;;
;;; This is the notes' "for h in R sufficiently small, f(a + h) is defined and
;;; g(f(a + h)) is also defined", and it is the whole content of the first line
;;; of the notes' proof, "f is continuous at a".
;;; =====================================================================

(sp (make-wff "forall([f, crx_, crl_],
   has-deriv-at(f, crx_, crl_) implies
   forall([crd_], pos-rr(crd_) implies
   forall([crb_], pos-rr(crb_) implies
     forsome([crw_], pos-rr(crw_) and crw_ <= crb_ and
       forall([cry_ in ooint(crx_ - crw_, crx_ + crw_)],
              f(cry_) in ooint(f(crx_) - crd_, f(crx_) + crd_))))))"))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-carr)
(fact 'has-deriv-at-pt-in-rr 'f 'crx_ 'crl_)
(fact 'has-deriv-at-value-in-rr 'f 'crx_ 'crl_)
(fact 'rr-pos-rr-in-rr 'crd_)
(fact 'rr-lt-of-pos-rr 'crd_)
(fact 'rr-pos-rr-in-rr 'crb_)
(fact 'rr-lt-of-pos-rr 'crb_)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(dk-have! '(IN crx_ (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(dk-have! '(IN (f crx_) (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(let ((w1 (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'f 'crx_ 'crl_ 'crb_))))
  (dk-split-all!)
  (fact 'rr-pos-rr-in-rr w1)
  (fact 'rr-lt-of-pos-rr w1)
  (fact 'rr-sub-in-rr 'crx_ w1)
  (fact 'rr-add-in-rr 'crx_ w1)
  (let* ((v1 (list 'OOINT (list '- 'crx_ w1) (list '+ 'crx_ w1)))
         (rf (list 'RESTRICT 'f v1))
         (sub (list 'SUBSPACE-MS cr-nfm v1)))
    (fact 'ooint-center 'crx_ w1)
    (fact 'subspace-pts cr-nfm v1)
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v1 rf 'crx_ 'crl_)
    (dk-have! (list 'IN rf (list 'FUN v1 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (fact 'restrict-apply 'f v1 'crx_)
    (fact 'diff-on-implies-continuous 'RR-NORMED-FIELD v1 rf 'crx_ 'crl_)
    (let ((hd (dk-halve! 'crd_)))
      (dk-split-all!
       (dk-landed* (lambda ()
         (mac-h 'IS-CONTINUOUS-AT (list 'IS-CONTINUOUS-AT sub cr-nfm rf 'crx_)))))
      (let* ((epsu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                              (dk-contains? fm 'FORSOME)
                                              (dk-contains? fm 'DIST)))
                            "the eps universal"))
             (dl (dk-skolem! (dk-apply! epsu hd))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr dl)
        (fact 'rr-lt-of-pos-rr dl)
        (let ((bodyu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                (dk-contains? fm 'DIST)
                                                (not (dk-contains? fm 'FORSOME))))
                              "the delta body")))
          (let ((w (dk-skolem! (dk-fact! 'rr-min-pos dl w1))))
            (dk-split-all!)
            (fact 'rr-pos-rr-of-lt w)
            (fact 'rr-sub-in-rr 'crx_ w)
            (fact 'rr-add-in-rr 'crx_ w)
            (dk-have! (list '<= w 'crb_)
              (lambda () (dk-ineq! (list '<= w w1) (list '<= w1 'crb_)
                                   (list 'IN w 'RR) (list 'IN w1 'RR) '(IN crb_ RR))))
            (ew w)
            (dk-conj-close!
             (lambda ()
               (if (not (eq? (cr-head (dk-goal)) 'FORALL))
                   (ass)
                   (let ((y (dk-di-var!)))
                     (cr-ooint-in! y (list '- 'crx_ w) (list '+ 'crx_ w))
                     (dk-have! (list 'IN y v1)
                       (lambda ()
                         (mac 'ooint-membership)
                         (cr-conj-ineq!
                          (list '(IN crx_ RR) (list 'IN w 'RR) (list 'IN w1 'RR)
                                (list 'IN y 'RR) (list '<= w w1)
                                (list '< 0 w) (list '< 0 w1)
                                (list '< (list '- 'crx_ w) y)
                                (list '< y (list '+ 'crx_ w))))))
                     (dk-have! (list 'IN y (list 'PTS sub))
                       (lambda () (subst (list '== (list 'PTS sub) v1)) (ass)))
                     (dk-have! (list 'IN y '(PTS RR-MS))
                       (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
                     (fact 'subspace-dist cr-nfm v1 'crx_ y)
                     (fact 'nf-rr-agree-dist 'crx_ y)
                     (fact 'rr-ms-dist 'crx_ y)
                     (fact 'rr-sub-in-rr 'crx_ y)
                     (dk-have! (list '<= (list (list 'DIST sub) 'crx_ y) dl)
                       (lambda ()
                         (subst (list '== (list (list 'DIST sub) 'crx_ y)
                                      (list (list 'DIST cr-nfm) 'crx_ y)))
                         (subst (list '== (list (list 'DIST cr-nfm) 'crx_ y)
                                      (list '(DIST RR-MS) 'crx_ y)))
                         (subst (list '== (list '(DIST RR-MS) 'crx_ y)
                                      (list 'abs (list '- 'crx_ y))))
                         ;; `ineq' neither proves nor consumes an `abs' bound:
                         ;; `rr-abs-bound' (guarded, so the two typings land
                         ;; first) turns it into a pair of linear inequalities.
                         (mac 'rr-abs-bound)
                         (dk-conj-close!
                          (lambda ()
                            (dk-ineq! '(IN crx_ RR) (list 'IN y 'RR)
                                      (list 'IN dl 'RR) (list 'IN w 'RR)
                                      (list '<= w dl)
                                      (list '< (list '- 'crx_ w) y)
                                      (list '< y (list '+ 'crx_ w)))))))
                     (dk-apply! bodyu y)
                     (fact 'restrict-apply 'f v1 y)
                     (fact 'fun-apply-type-c rf v1 'RR y)
                     (dk-have! (list 'IN (list 'f y) 'RR)
                       (lambda () (subst (list '== (list 'f y) (list rf y))) (ass)))
                     (dk-have! (list 'IN (list 'f y) '(PTS RR-MS))
                       (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
                     (fact 'nf-rr-agree-dist '(f crx_) (list 'f y))
                     (fact 'rr-ms-dist '(f crx_) (list 'f y))
                     (dk-have! (list '<= (list 'abs (list '- '(f crx_) (list 'f y))) hd)
                       (lambda ()
                         (subst (list '== (list 'abs (list '- '(f crx_) (list 'f y)))
                                      (list '(DIST RR-MS) '(f crx_) (list 'f y))))
                         (subst (list '== (list '(DIST RR-MS) '(f crx_) (list 'f y))
                                      (list (list 'DIST cr-nfm) '(f crx_) (list 'f y))))
                         (subst (list '== '(f crx_) (list rf 'crx_)))
                         (subst (list '== (list 'f y) (list rf y)))
                         (ass)))
                     (fact 'rr-sub-in-rr '(f crx_) (list 'f y))
                     (dk-split-all!
                      (dk-landed*
                       (lambda ()
                         (mac-h 'rr-abs-bound
                                (list '<= (list 'abs (list '- '(f crx_) (list 'f y)))
                                      hd)))))
                     (mac 'ooint-membership)
                     (cr-conj-ineq!
                      (list '(IN (f crx_) RR) (list 'IN (list 'f y) 'RR)
                            '(IN crd_ RR) (list 'IN hd 'RR)
                            (list '<= (list '- hd) (list '- '(f crx_) (list 'f y)))
                            (list '<= (list '- '(f crx_) (list 'f y)) hd)
                            (list '= (list '+ hd hd) 'crd_)
                            (list '< 0 hd)))))))))))))
(qed 'has-deriv-at-maps-into)
(topic! 'has-deriv-at-maps-into 'analysis)
(alias! 'has-deriv-at-maps-into
        "a function with a derivative at a point maps small windows into small windows")

;;; =====================================================================
;;; (2) THE CHAIN RULE -- the notes' Proposition 2.8, equation (13).
;;; =====================================================================

(sp (make-wff "forall([crr_], pos-rr(crr_) implies
  forall([f, g, h, crx_, crl_, crm_],
    restrict(h, ooint(crx_ - crr_, crx_ + crr_))
        in fun(ooint(crx_ - crr_, crx_ + crr_), rr) implies
    forall([cry_ in ooint(crx_ - crr_, crx_ + crr_)], h(cry_) == g(f(cry_))) implies
    has-deriv-at(f, crx_, crl_) implies
    has-deriv-at(g, f(crx_), crm_) implies
    has-deriv-at(h, crx_, crm_ * crl_)))"))
(dk-peel!)
(fact 'rr-is-normed-field)
(fact 'rr-nf-carr)
(fact 'has-deriv-at-value-in-rr 'f 'crx_ 'crl_)
(fact 'has-deriv-at-pt-in-rr 'f 'crx_ 'crl_)
(fact 'has-deriv-at-in-rr 'f 'crx_ 'crl_)
(fact 'has-deriv-at-in-rr 'g '(f crx_) 'crm_)
(fact 'rr-pos-rr-in-rr 'crr_)
(fact 'rr-lt-of-pos-rr 'crr_)
(fact 'rr-one-in)
(dk-have! '(POS-RR 1)
  (lambda () (dk-have! '(< 0 1) (lambda () (ineq))) (fact 'rr-pos-rr-of-lt 1) (ass)))
(define cr-big '(OOINT (- crx_ crr_) (+ crx_ crr_)))
(define cr-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'h) (dk-contains? fm 'g)))
           "the pointwise agreement"))
(let ((d0 (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'g '(f crx_) 'crm_ 1))))
  (dk-split-all!)
  (fact 'rr-pos-rr-in-rr d0)
  (fact 'rr-lt-of-pos-rr d0)
  (fact 'rr-sub-in-rr '(f crx_) d0)
  (fact 'rr-add-in-rr '(f crx_) d0)
  (let* ((sset (list 'OOINT (list '- '(f crx_) d0) (list '+ '(f crx_) d0)))
         (rg (list 'RESTRICT 'g sset)))
    (let ((w1 (dk-skolem! (dk-fact! 'has-deriv-at-shrink 'f 'crx_ 'crl_ 'crr_))))
      (dk-split-all!)
      (fact 'rr-pos-rr-in-rr w1)
      (fact 'rr-lt-of-pos-rr w1)
      (let ((w (dk-skolem! (dk-fact! 'has-deriv-at-maps-into 'f 'crx_ 'crl_ d0 w1))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr w)
        (fact 'rr-lt-of-pos-rr w)
        (fact 'rr-sub-in-rr 'crx_ w)
        (fact 'rr-add-in-rr 'crx_ w)
        (let* ((v (list 'OOINT (list '- 'crx_ w) (list '+ 'crx_ w)))
               (rf (list 'RESTRICT 'f v))
               (lam (list 'VNB-LAMBDA 'd2x_ v (list rg (list rf 'd2x_))))
               (mapsu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                 (dk-contains? fm 'f)
                                                 (not (dk-contains? fm 'h))
                                                 (not (dk-contains? fm 'g))))
                               "the maps-into universal")))
          (fact 'diff-on-ooint-shrink 'crx_ w1 w 'f 'crl_)
          (fact 'ooint-center 'crx_ w)
          (fact 'restrict-apply 'f v 'crx_)
          (dk-have! (list 'IS-DIFF-ON 'RR-NORMED-FIELD sset rg (list rf 'crx_) 'crm_)
            (lambda () (subst (list '== (list rf 'crx_) '(f crx_))) (ass)))
          (dk-have! (list 'FORALL 'crz_ (list 'IMPLIES (list 'IN 'crz_ v)
                      (list 'IN (list rf 'crz_) sset)))
            (lambda ()
              (let ((z (dk-di-var!)))
                (fact 'restrict-apply 'f v z)
                (dk-apply! mapsu z)
                (subst (list '== (list rf z) (list 'f z)))
                (ass))))
          (fact 'rr-nf-mul-apply 'crm_ 'crl_)
          (dk-apply! (dk-apply! (dk-fact! 'diff-on-chain 'RR-NORMED-FIELD) v sset rf)
                     rg 'crx_ 'crl_ 'crm_)
          (dk-have! (list 'IS-DIFF-ON 'RR-NORMED-FIELD v lam 'crx_ '(* crm_ crl_))
            (lambda ()
              (subst '(== (* crm_ crl_) ((MUL RR-NORMED-FIELD) crm_ crl_)))
              (ass)))
          (dk-have! (list '<= w 'crr_)
            (lambda () (dk-ineq! (list '<= w w1) (list '<= w1 'crr_)
                                 (list 'IN w 'RR) (list 'IN w1 'RR) '(IN crr_ RR))))
          (dk-have! (list 'SUBSET v cr-big)
            (lambda ()
              (let ((z (subset-by-element!)))
                (cr-ooint-in! z (list '- 'crx_ w) (list '+ 'crx_ w))
                (mac 'ooint-membership)
                (cr-conj-ineq!
                 (list '(IN crx_ RR) '(IN crr_ RR) (list 'IN w 'RR) (list 'IN z 'RR)
                       (list '<= w 'crr_) (list '< 0 w) '(< 0 crr_)
                       (list '< (list '- 'crx_ w) z)
                       (list '< z (list '+ 'crx_ w)))))))
          (fact 'restrict-in-fun-of-restrict 'h cr-big 'RR v)
          (dk-have! (list 'IN (list 'RESTRICT 'h v) (list 'FUN v '(CARR RR-NORMED-FIELD)))
            (lambda () (subst '(== (CARR RR-NORMED-FIELD) RR)) (ass)))
          (dk-have! (list 'FORALL 'crz_ (list 'IMPLIES (list 'IN 'crz_ v)
                      (list '== (list (list 'RESTRICT 'h v) 'crz_) (list lam 'crz_))))
            (lambda ()
              (let ((z (dk-di-var!)))
                (fact 'subset-mem-fwd v cr-big z)
                (fact 'restrict-apply 'h v z)
                (fact 'restrict-apply 'f v z)
                (dk-apply! mapsu z)
                (fact 'restrict-apply 'g sset (list 'f z))
                (dk-apply! cr-agree z)
                (dk-lam-b!)
                (subst (list '== (list (list 'RESTRICT 'h v) z) (list 'h z)))
                (subst (list '== (list rf z) (list 'f z)))
                (subst (list '== (list rg (list 'f z)) (list 'g (list 'f z))))
                (subst (list '== (list 'h z) (list 'g (list 'f z))))
                (qrfl))))
          (fact 'diff-on-transfer-ptwise-eq 'RR-NORMED-FIELD v
                (list 'RESTRICT 'h v) lam 'crx_ '(* crm_ crl_))
          (fact 'has-deriv-at-intro 'h 'crx_ '(* crm_ crl_) w)
          (ass))))))
(qed 'has-deriv-at-chain)
(topic! 'has-deriv-at-chain 'analysis)
(alias! 'has-deriv-at-chain "the chain rule for the derivative at a point")

;;; =====================================================================
;;; (3) THE AFFINE INNER MAP.
;;;
;;; The composite with t |-> p + q t.  With p = a + b and q = -1 this is the
;;; reflection of [a, b] onto itself, which is what Dieudonne's opposite road
;;; (9.6.1) differentiates.
;;; =====================================================================

(sp (make-wff "forall([crr_], pos-rr(crr_) implies
  forall([g, h, crp_ in rr, crq_ in rr, crx_ in rr, crm_],
    restrict(h, ooint(crx_ - crr_, crx_ + crr_))
        in fun(ooint(crx_ - crr_, crx_ + crr_), rr) implies
    forall([cry_ in ooint(crx_ - crr_, crx_ + crr_)],
           h(cry_) == g(crp_ + crq_ * cry_)) implies
    has-deriv-at(g, crp_ + crq_ * crx_, crm_) implies
    has-deriv-at(h, crx_, crm_ * crq_)))"))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'crr_)
(fact 'rr-lt-of-pos-rr 'crr_)
(fact 'rr-is-set)
(define cr-abig '(OOINT (- crx_ crr_) (+ crx_ crr_)))
(define cr-aff '(VNB-LAMBDA crv_ RR (+ crp_ (* crq_ crv_))))
(define cr-aagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'h) (dk-contains? fm 'g)))
           "the pointwise agreement"))
(dk-have! (list 'IN cr-aff '(FUN RR RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (cr-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (have! (list 'AND '(IN crq_ RR) (list 'IN z 'RR)))
             (fact 'rr-mul-closed 'crq_ z)
             (fact 'rr-add-in-rr 'crp_ (list '* 'crq_ z))
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(fact 'ooint-subset-rr '(- crx_ crr_) '(+ crx_ crr_))
(fact 'restrict-in-fun cr-aff 'RR 'RR cr-abig)
;; NAMED HERE, not found later by shape: `fact'/`inst*!' land the whole
;; instantiation chain, and a shape finder run after the citation of
;; `has-deriv-at-affine' picks a LINK of that chain (CLAUDE.md, Navigation).
(define cr-affval
  (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ cr-abig)
        (list '== (list cr-aff 'hbx_) '(+ crp_ (* crq_ hbx_))))))
(dk-have! cr-affval
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'subset-mem-fwd cr-abig 'RR z)
      (dk-lam-b!)
      (qrfl))))
;; staged (radius first, then the four terms), so that what is instantiated is
;; visible: `has-deriv-at-affine' has five binders and batch 16-A's `fact'
;; defect shows up at eight.
(dk-apply! (dk-fact! 'has-deriv-at-affine 'crr_) cr-aff 'crp_ 'crq_ 'crx_)
(fact 'ooint-center 'crx_ 'crr_)
(dk-have! (list '== (list cr-aff 'crx_) '(+ crp_ (* crq_ crx_)))
  (lambda () (dk-lam-b!) (qrfl)))
(dk-have! (list 'HAS-DERIV-AT 'g (list cr-aff 'crx_) 'crm_)
  (lambda () (subst (list '== (list cr-aff 'crx_) '(+ crp_ (* crq_ crx_)))) (ass)))
(dk-have! (list 'FORALL 'cry_ (list 'IMPLIES (list 'IN 'cry_ cr-abig)
            (list '== '(h cry_) (list 'g (list cr-aff 'cry_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (dk-apply! cr-aagree z)
      (dk-apply! cr-affval z)
      (subst (list '== (list cr-aff z) (list '+ 'crp_ (list '* 'crq_ z))))
      (ass))))
(dk-apply! (dk-apply! (dk-fact! 'has-deriv-at-chain 'crr_) cr-aff 'g 'h)
           'crx_ 'crq_ 'crm_)
(ass)
(qed 'has-deriv-at-affine-chain)
(topic! 'has-deriv-at-affine-chain 'analysis)
(alias! 'has-deriv-at-affine-chain
        "the chain rule at an affine change of variable")
