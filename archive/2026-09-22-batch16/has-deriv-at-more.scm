;;; has-deriv-at-more.scm -- the four HAS-DERIV-AT laws that
;;; theorem-library/interval-calculus-laws.scm did not prove: the VALUE typing,
;;; the AFFINE function (and with it the constant and the identity), the REAL
;;; MULTIPLE and the DIFFERENCE.
;;;
;;; 15-A's report lists them as OWED ("has-deriv-at real multiple and
;;; difference; has-deriv-at-const first"); they belong with the other rules in
;;; interval-calculus-laws.scm section (8) and should be SPLICED there when
;;; that file is next touched.  They are here, and not there, only because that
;;; file is not this agent's to edit.
;;;
;;; THE SHAPE OF EVERY RULE IN SECTION (8), kept verbatim: a sum, a product or
;;; a multiple of two functions on an interval is not a term the tree can form
;;; -- there is no addition on FUN(A, RR) -- so each rule is stated for ANY h
;;; that agrees with the combination on an open interval about the point, which
;;; is the shape every caller has in hand and is exactly what
;;; `has-deriv-at-local' makes harmless.  The radius `hdr_' and the agreement
;;; binder `hbx_' are the ones interval-calculus-laws.scm uses, so a caller
;;; that already has a sum or a product in hand needs no translation.
;;;
;;; WHAT IS NEW AND WHAT IS CITED.
;;;
;;;   has-deriv-at-value-in-rr  f(x) is a real when f has a derivative at x.
;;;       Not derivable from the two typings interval-calculus-laws.scm proves
;;;       (`has-deriv-at-pt-in-rr', `has-deriv-at-in-rr'), which give x and the
;;;       derivative; this one goes through the restriction the definition
;;;       hands over and `diff-on-in-fun'.  The product rule's conclusion names
;;;       f(x) and g(x), so every consumer of it needs this.
;;;
;;;   has-deriv-at-affine       the AFFINE function, from the TOTAL-function
;;;       theorem `deriv-affine' (directional-derivative.scm) through
;;;       `has-deriv-at-iff-diff-at' and then `has-deriv-at-local'.  This is the
;;;       cheap route and it is the reason the constant and the identity are
;;;       four lines each below rather than two diff-on drivers: the total
;;;       theory already has them, and HAS-DERIV-AT is local, so the ONLY work
;;;       is to say that f agrees with the total affine map near x.
;;;
;;;   has-deriv-at-const, has-deriv-at-identity   instances of the affine rule
;;;       at lam = 0 and at (c, lam) = (0, 1).
;;;
;;;   has-deriv-at-real-mul     from `has-deriv-at-product'
;;;       (interval-calculus-laws.scm) with the first factor the TOTAL constant
;;;       map, whose derivative is 0 by has-deriv-at-const.  The product rule
;;;       concludes about `icl_ * g(icx_) + icm_ * f(icx_)'; with icl_ = 0 and
;;;       f the constant that is 0 * g(x) + m * c, and the rewrite to c * m is
;;;       one `crs' -- which is why has-deriv-at-value-in-rr comes first: `crs'
;;;       will not touch g(x) until it is typed.
;;;
;;;   has-deriv-at-difference   the real multiple at c = -1, then
;;;       `has-deriv-at-sum'.  IT CARRIES ONE HYPOTHESIS THE SUM RULE DOES NOT:
;;;       `restrict(g, OO) in fun(OO, rr)'.  The reason is that the negation has
;;;       to be FORMED, as the lambda `z |-> -(g z)' on the interval OO, and
;;;       `lam-t' owes the typing of its body at every point of OO --
;;;       has-deriv-at(g, x, m) guarantees that only on SOME smaller interval
;;;       whose radius is opaque.  Every caller has the hypothesis: in the
;;;       intended use g is a function on the whole of CCINT(a,b) and OO is an
;;;       open interval inside it, so the typing is `restrict-in-fun'.  Chasing
;;;       the opaque radius instead would add a shrink-to-a-common-radius dance
;;;       (the `ic-common-radius!' of interval-calculus-laws.scm) and buy
;;;       nothing.
;;;
;;; Helper prefix: hd-.
;;;
;;; Dependencies: structure-library/interval-calculus.scm;
;;; theorem-library/interval-calculus-laws.scm (has-deriv-at-local, -intro,
;;; -shrink, -iff-diff-at, -product, -sum, -pt-in-rr, -in-rr, ooint-*,
;;; restrict-in-fun-of-restrict); theorem-library/directional-derivative.scm
;;; (deriv-affine, affine-lam-in-fun); theorem-library/continuity-basics.scm
;;; (const-lam-in-fun); theorem-library/diff-on-laws.scm (diff-on-in-fun,
;;; rr-nf-carr); theorem-library/metric-subspace-laws.scm (restrict-apply,
;;; restrict-in-fun); fun-apply-type-proof (fun-apply-type-c).

;;; ---- file-local driver helpers ---------------------------------------

;;; the open interval the statements are written about.
(define hd-oo '(OOINT (- hdx_ hdr_) (+ hdx_ hdr_)))

;;; POS-RR t -> (IN t RR), (< 0 t).
(define (hd-pos! t)
  (fact 'rr-pos-rr-in-rr t)
  (fact 'rr-lt-of-pos-rr t))

;;; the radius `hdr_' typed, and the two endpoints of hd-oo.
(define (hd-radius!)
  (hd-pos! 'hdr_)
  (fact 'rr-sub-in-rr 'hdx_ 'hdr_)
  (fact 'rr-add-in-rr 'hdx_ 'hdr_))

;;; (IN t RR) from (IN t (CARR RR-NORMED-FIELD)), and the reverse; the slot
;;; equation is `rr-nf-carr' and `subst' takes it in either orientation.
(define (hd-carr!) (fact 'rr-nf-carr))

;;; skolemize a HAS-DERIV-AT hypothesis and return its radius eigenvariable,
;;; with the IS-DIFF-ON and the POS-RR both landed and split.
(define (hd-open-deriv! form)
  (let ((e (dk-skolem! (dk-landed-find (lambda () (mac-h 'HAS-DERIV-AT form))
                                       (dk-head? 'FORSOME)))))
    (dk-split-all!)
    e))

;;; =====================================================================
;;; (1) THE VALUE OF A DIFFERENTIABLE FUNCTION IS A REAL.
;;; =====================================================================
(sp (make-wff '(FORALL f (FORALL hdx_ (FORALL hdl_
   (IMPLIES (HAS-DERIV-AT f hdx_ hdl_) (IN (f hdx_) RR)))))))
(dk-peel!)
(fact 'has-deriv-at-pt-in-rr 'f 'hdx_ 'hdl_)
(hd-carr!)
(let ((e (hd-open-deriv! '(HAS-DERIV-AT f hdx_ hdl_))))
  (hd-pos! e)
  (fact 'rr-sub-in-rr 'hdx_ e)
  (fact 'rr-add-in-rr 'hdx_ e)
  (let* ((v  (list 'OOINT (list '- 'hdx_ e) (list '+ 'hdx_ e)))
         (rf (list 'RESTRICT 'f v)))
    (fact 'ooint-center 'hdx_ e)
    (fact 'diff-on-in-fun 'RR-NORMED-FIELD v rf 'hdx_ 'hdl_)
    (dk-have! (list 'IN rf (list 'FUN v 'RR))
      (lambda () (subst '(== RR (CARR RR-NORMED-FIELD))) (ass)))
    (fact 'fun-apply-type-c rf v 'RR 'hdx_)
    (fact 'restrict-apply 'f v 'hdx_)
    (subst (list '== (list 'f 'hdx_) (list rf 'hdx_)))
    (ass)))
(qed 'has-deriv-at-value-in-rr)
(topic! 'has-deriv-at-value-in-rr 'analysis)
(alias! 'has-deriv-at-value-in-rr
        "a function differentiable at a point takes a real value there")

;;; =====================================================================
;;; (2) THE AFFINE FUNCTION.
;;;
;;; `deriv-affine' (directional-derivative.scm) says
;;;    IS-DIFF-AT(x |-> c + lam*x, a, lam)
;;; for the TOTAL map.  `has-deriv-at-iff-diff-at' turns that into a
;;; HAS-DERIV-AT of the same total map -- the lambda is in FUN(RR,RR) by
;;; `affine-lam-in-fun' -- and `has-deriv-at-local' carries it to any f that
;;; agrees with it near the point.
;;; =====================================================================
(sp (make-wff "forall([hdr_], pos-rr(hdr_) implies
  forall([f, hdc_ in rr, hdm_ in rr, hdx_ in rr],
    restrict(f, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    forall([hbx_ in ooint(hdx_ - hdr_, hdx_ + hdr_)],
           f(hbx_) == hdc_ + hdm_ * hbx_) implies
    has-deriv-at(f, hdx_, hdm_)))"))
(dk-peel!)
(hd-radius!)
(define hd-aff '(VNB-LAMBDA x RR (+ hdc_ (* hdm_ x))))
(define hd-aff-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'f) (dk-contains? fm 'hdc_)))
           "the pointwise agreement"))
(have! '(AND (IN hdc_ RR) (AND (IN hdm_ RR) (IN hdx_ RR))))
(have! '(AND (IN hdc_ RR) (IN hdm_ RR)))
(fact 'deriv-affine 'hdc_ 'hdm_ 'hdx_)
(fact 'affine-lam-in-fun 'hdc_ 'hdm_)
(fact 'has-deriv-at-iff-diff-at hd-aff 'hdx_ 'hdm_)
(dk-have! (list 'HAS-DERIV-AT hd-aff 'hdx_ 'hdm_) (lambda () (prop)))
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list 'f 'hbx_) (list hd-aff 'hbx_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (dk-apply! hd-aff-agree z)
      (dk-lam-b!)
      (ass))))
(fact 'has-deriv-at-local 'hdr_ 'f hd-aff 'hdx_ 'hdm_)
(ass)
(qed 'has-deriv-at-affine)
(topic! 'has-deriv-at-affine 'analysis)
(alias! 'has-deriv-at-affine
        "a function affine near a point has the slope as its derivative")

;;; =====================================================================
;;; (3) THE CONSTANT AND THE IDENTITY -- the affine rule at lam = 0 and at
;;; (c, lam) = (0, 1).  Each is the affine agreement plus one ring identity.
;;; =====================================================================
(sp (make-wff "forall([hdr_], pos-rr(hdr_) implies
  forall([f, hdc_ in rr, hdx_ in rr],
    restrict(f, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    forall([hbx_ in ooint(hdx_ - hdr_, hdx_ + hdr_)], f(hbx_) == hdc_) implies
    has-deriv-at(f, hdx_, 0)))"))
(dk-peel!)
(hd-radius!)
(fact 'rr-zero-in)
(define hd-cst-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'f) (dk-contains? fm 'hdc_)))
           "the pointwise agreement"))
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list 'f 'hbx_) '(+ hdc_ (* 0 hbx_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (dk-apply! hd-cst-agree z)
      (have! (list '= (list '+ 'hdc_ (list '* 0 z)) 'hdc_) (lambda () (crs)))
      (subst (list '= (list '+ 'hdc_ (list '* 0 z)) 'hdc_))
      (ass))))
(fact 'has-deriv-at-affine 'hdr_ 'f 'hdc_ 0 'hdx_)
(ass)
(qed 'has-deriv-at-const)
(topic! 'has-deriv-at-const 'analysis)
(alias! 'has-deriv-at-const "a function constant near a point has derivative zero")

(sp (make-wff "forall([hdr_], pos-rr(hdr_) implies
  forall([f, hdx_ in rr],
    restrict(f, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    forall([hbx_ in ooint(hdx_ - hdr_, hdx_ + hdr_)], f(hbx_) == hbx_) implies
    has-deriv-at(f, hdx_, 1)))"))
(dk-peel!)
(hd-radius!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(define hd-id-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'f)))
           "the pointwise agreement"))
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list 'f 'hbx_) '(+ 0 (* 1 hbx_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (dk-apply! hd-id-agree z)
      (have! (list '= (list '+ 0 (list '* 1 z)) z) (lambda () (crs)))
      (subst (list '= (list '+ 0 (list '* 1 z)) z))
      (ass))))
(fact 'has-deriv-at-affine 'hdr_ 'f 0 1 'hdx_)
(ass)
(qed 'has-deriv-at-identity)
(topic! 'has-deriv-at-identity 'analysis)
(alias! 'has-deriv-at-identity
        "a function equal to the parameter near a point has derivative one")

;;; =====================================================================
;;; (4) THE REAL MULTIPLE.  `has-deriv-at-product' with the first factor the
;;; TOTAL constant map c, whose derivative is 0.
;;; =====================================================================
(sp (make-wff "forall([hdr_], pos-rr(hdr_) implies
  forall([g, h, hdc_ in rr, hdx_, hdm_],
    restrict(h, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    forall([hbx_ in ooint(hdx_ - hdr_, hdx_ + hdr_)],
           h(hbx_) == hdc_ * g(hbx_)) implies
    has-deriv-at(g, hdx_, hdm_) implies
    has-deriv-at(h, hdx_, hdc_ * hdm_)))"))
(dk-peel!)
(fact 'has-deriv-at-pt-in-rr 'g 'hdx_ 'hdm_)
(fact 'has-deriv-at-in-rr 'g 'hdx_ 'hdm_)
(fact 'has-deriv-at-value-in-rr 'g 'hdx_ 'hdm_)
(hd-radius!)
(fact 'rr-zero-in)
(define hd-con '(VNB-LAMBDA x RR hdc_))
(define hd-mul-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'h) (dk-contains? fm 'g)))
           "the pointwise agreement"))
;; the total constant map is a function on the line, so its restriction to the
;; interval is a function on the interval.
(fact 'const-lam-in-fun 'hdc_)
(fact 'ooint-subset-rr '(- hdx_ hdr_) '(+ hdx_ hdr_))
(fact 'restrict-in-fun hd-con 'RR 'RR hd-oo)
;; ... and it is constant there, so its derivative is 0.
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list hd-con 'hbx_) 'hdc_)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (dk-lam-b!)
      (qrfl))))
(fact 'has-deriv-at-const 'hdr_ hd-con 'hdc_ 'hdx_)
;; h agrees with the PRODUCT of the constant map and g.
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list 'h 'hbx_) (list '* (list hd-con 'hbx_) (list 'g 'hbx_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (dk-apply! hd-mul-agree z)
      (dk-lam-b!)
      (ass))))
(fact 'has-deriv-at-product 'hdr_ hd-con 'g 'h 'hdx_ 0 'hdm_)
;; 0 * g(x) + m * c  =  c * m, once g(x) is typed.  The landed conclusion names
;; the constant map APPLIED, so the equation is stated with the redex standing
;; and `dk-lam-b!' contracts it inside the lane.
(define hd-mul-val
  (list '+ (list '* 0 '(g hdx_)) (list '* 'hdm_ (list hd-con 'hdx_))))
(dk-have! (list '= '(* hdc_ hdm_) hd-mul-val)
  (lambda () (dk-lam-b!) (crs)))
(subst (list '= '(* hdc_ hdm_) hd-mul-val))
(ass)
(qed 'has-deriv-at-real-mul)
(topic! 'has-deriv-at-real-mul 'analysis)
(alias! 'has-deriv-at-real-mul
        "the derivative of a real multiple is the multiple of the derivative")

;;; =====================================================================
;;; (5) THE DIFFERENCE.  The real multiple at c = -1 builds the negation as a
;;; lambda ON the interval, and `has-deriv-at-sum' finishes.  See the header
;;; for why the typing of g on the interval is a hypothesis.
;;; =====================================================================
(sp (make-wff "forall([hdr_], pos-rr(hdr_) implies
  forall([f, g, h, hdx_, hdl_, hdm_],
    restrict(h, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    restrict(g, ooint(hdx_ - hdr_, hdx_ + hdr_))
        in fun(ooint(hdx_ - hdr_, hdx_ + hdr_), rr) implies
    forall([hbx_ in ooint(hdx_ - hdr_, hdx_ + hdr_)],
           h(hbx_) == f(hbx_) - g(hbx_)) implies
    has-deriv-at(f, hdx_, hdl_) implies
    has-deriv-at(g, hdx_, hdm_) implies
    has-deriv-at(h, hdx_, hdl_ - hdm_)))"))
(dk-peel!)
(fact 'has-deriv-at-pt-in-rr 'f 'hdx_ 'hdl_)
(fact 'has-deriv-at-in-rr 'f 'hdx_ 'hdl_)
(fact 'has-deriv-at-in-rr 'g 'hdx_ 'hdm_)
(hd-radius!)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(define hd-rg (list 'RESTRICT 'g hd-oo))
(define hd-neg (list 'VNB-LAMBDA 'hbz_ hd-oo (list '- (list hd-rg 'hbz_))))
(define hd-sub-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'h) (dk-contains? fm 'g)
                             (dk-contains? fm 'f)))
           "the pointwise agreement"))
;; the negation is a function ON the interval ...
(fact 'fun-domain-in-set hd-oo 'RR hd-rg)
(dk-have! (list 'IN hd-neg (list 'FUN hd-oo 'RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'fun-apply-type-c hd-rg hd-oo 'RR z)
             (fact 'rr-neg-closed (list hd-rg z))
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
(fact 'subset-refl hd-oo)
(fact 'restrict-in-fun hd-neg hd-oo 'RR hd-oo)
;; ... and it is (-1) times g there.
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list hd-neg 'hbx_) (list '* '(- 1) (list 'g 'hbx_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (fact 'restrict-apply 'g hd-oo z)
      (fact 'fun-apply-type-c hd-rg hd-oo 'RR z)
      (dk-have! (list 'IN (list 'g z) 'RR)
        (lambda () (subst (list '== (list 'g z) (list hd-rg z))) (ass)))
      (dk-lam-b!)
      (subst (list '== (list hd-rg z) (list 'g z)))
      (have! (list '= (list '- (list 'g z)) (list '* '(- 1) (list 'g z)))
             (lambda () (crs)))
      (subst (list '= (list '- (list 'g z)) (list '* '(- 1) (list 'g z))))
      (qrfl))))
(fact 'has-deriv-at-real-mul 'hdr_ 'g hd-neg '(- 1) 'hdx_ 'hdm_)
;; h agrees with the SUM of f and the negation.
(dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ hd-oo)
            (list '== (list 'h 'hbx_) (list '+ (list 'f 'hbx_) (list hd-neg 'hbx_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ooint-elt-in-rr '(- hdx_ hdr_) '(+ hdx_ hdr_) z)
      (fact 'restrict-apply 'g hd-oo z)
      (dk-apply! hd-sub-agree z)
      (dk-lam-b!)
      (subst (list '== (list hd-rg z) (list 'g z)))
      (subst (list '== (list 'h z) (list '- (list 'f z) (list 'g z))))
      (mac 'binary-minus-def)
      (qrfl))))
(fact 'has-deriv-at-sum 'hdr_ 'f hd-neg 'h 'hdx_ 'hdl_ '(* (- 1) hdm_))
(dk-have! '(= (- hdl_ hdm_) (+ hdl_ (* (- 1) hdm_))) (lambda () (crs)))
(subst '(= (- hdl_ hdm_) (+ hdl_ (* (- 1) hdm_))))
(ass)
(qed 'has-deriv-at-difference)
(topic! 'has-deriv-at-difference 'analysis)
(alias! 'has-deriv-at-difference
        "the derivative of a difference is the difference of the derivatives")
