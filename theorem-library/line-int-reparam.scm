;;; line-int-reparam.scm -- THE AFFINE CHANGE OF PARAMETER (the notes' (48),
;;; affine case) AND THE SEGMENT LEMMAS OF GOURSAT'S DEFINITION-FREE HALF.
;;; Batch 29-A, 2026-09-25.
;;;
;;; THE SOURCE.  complex-analysis.pdf 3.1: (48) "If gamma : [alpha, beta] -> C
;;; is a path and phi : [xi, eta] -> [alpha, beta] is a continuously
;;; differentiable strictly increasing function such that phi(xi) = alpha and
;;; phi(eta) = beta, then rho(s) = gamma(phi(s)) is a path and int_gamma f =
;;; int_rho f ... In particular, we can shift the domain of definition of a path
;;; by an affine mapping without affecting the value of the integral."  Here phi
;;; is AFFINE: phi(s) = mu + lam*s with lam > 0, mu + lam*c = a, mu + lam*d = b.
;;; Lemma 3.4 (56) "int_<a,b> f = int_<a,c> f + int_<c,b> f" for c on the
;;; segment; (54) the bound |int_gamma f| <= int |f(gamma)| |gamma'|; and
;;; "reversing the path gamma changes the sign of the integral".
;;;
;;; A SEGMENT IS WRITTEN AS `segment-is-road' WRITES IT: SEG(z0, w) is the road
;;; (vnb-lambda(psx_, ccint(0,1), z0 + psx_ * w), vnb-lambda(psx_, ccint(0,1), w))
;;; on [0,1].  The tree has no segment object (that definition is the user's
;;; decision, not this file's): <z0, z0 + w> is SEG(z0, w) literally, and the
;;; point z0 + t w, 0 < t < 1, splits it into SEG(z0, t w) and
;;; SEG(z0 + t w, (1 - t) w).
;;;
;;; THE FILE IN ORDER.
;;;   (a) affine-reparam-ccint-in / -ooint-in / -solve / -inverse /
;;;       -inverse-value: s |-> mu + lam*s maps [c,d] into [a,b] and (c,d) into
;;;       (a,b); z in [a,b] has the preimage (z - mu)/lam in [c,d].
;;;   (b) affine-reparam-continuous-at-sub / -continuous-on: the continuity
;;;       engine (the model is `reflect-continuous-at-sub', road-laws-2.scm).
;;;   (c) affine-reparam-image-countable / -not-in-image: the exceptional set
;;;       of the reparametrised primitive is the IMAGE of the old one under the
;;;       inverse map.
;;;   (d) affine-reparam-regulated: a regulated function stays regulated.
;;;   (1) pw-int-affine-subst: w(mu + lam s) is a primitive of
;;;       lam * phi(mu + lam s) on [c,d], and the integral is unchanged.
;;;   (2) cc-int-affine-subst: the same for CC-INT, componentwise.
;;;   (3) trace-affine-reparam, road-affine-reparam, line-int-affine-reparam:
;;;       the reparametrised road is a road with the same trace and the same
;;;       integral -- (48) for phi affine.
;;;   trace-restrict-subset: the trace of a restriction lies in the trace.
;;;   (4) segment-int-split: Lemma 3.4 for a segment.
;;;   (5) segment-int-abs-bound: (54) for a segment, |int| <= |w| M.
;;;   (6) segment-int-reverse: the reversed segment changes the sign.
;;;
;;; THE STATEMENT CHECKS (CLAUDE.md's species), made before any proof:
;;; * every function lives ON its interval (FUN(CCINT(c,d), _)); the
;;;   reparametrised functions are GIVEN by their pointwise agreement (`=='),
;;;   the house style of `pw-int-reflect' / `opposite-is-road', so the lambda
;;;   of the brief is one instance and any function equal to it pointwise is
;;;   another;
;;; * no strict `=' on a PW-INT / CC-INT / LINE-INT without the primitives that
;;;   earn its definedness: (1) takes IS-PRIMITIVE, (2) the two coordinate
;;;   primitives, (3)-(6) the hypotheses of `line-int-exists' (f continuous on
;;;   u, the road's trace in u), exactly as line-int-laws.scm states its laws;
;;; * mu + lam*s and the preimage (z - mu)/lam are shown to lie in the
;;;   interval before any function is applied to them ((a));
;;; * lam > 0 is a hypothesis: the notes' phi is strictly INCREASING;
;;; * binders: lrpc_ lrpd_ (c, d), lrpl_ (lam), lrpm_ (mu), lrpz_ lrpt_ lrpq_
;;;   lrpe_ lrpn_ lrpy_ (points, sets, bound), lrpg_ lrph_ lrps_ lrpb_ lrpr_
;;;   lrpk_ (functions), lrpv_ (the binder of every lambda this file BUILDS);
;;;   no other file binds an `lrp' name, none folds onto a class name or an
;;;   accessor; `pwf_', `pphi_', `paw_', `pat_', `pgam', `dgam', `psx_', `pz0_',
;;;   `pzw_', `rgy_' are kept from the statements they must match.
;;;
;;; THE DERIVATIVE STEP is `has-deriv-at-affine-chain' (has-deriv-at-chain.scm),
;;; the chain rule with an affine inner map, whose open-ball hypothesis is met
;;; by `ooint-inner-radius': no epsilon argument was needed.
;;;
;;; Helper prefix: lrp-.  Load window: after theorem-library/line-int-laws
;;; (line-int-adjacent, line-int-abs-bound, line-int-opposite-road, road-restrict,
;;; line-int-in-cc) and road-laws-2 / regulated-algebra (line-int-exists,
;;; road-integrand-regulated, regulated-on-magnitude).  window.py is the judge.

;;; ---- file-local driver helpers ---------------------------------------

(define (lrp-head g) (and (pair? g) (car g)))

(define lrp-cd '(CCINT lrpc_ lrpd_))
(define lrp-ab '(CCINT a b))
(define (lrp-map z) (list '+ 'lrpm_ (list '* 'lrpl_ z)))

(define (lrp-and! x y)
  (dk-have! (list 'AND x y) (lambda () (dk-conj-close! (lambda () (ass))))))

;;; type an arithmetic term over RR-typed atoms in RR; returns the typing.
(define (lrp-rr! t)
  (let ((typ (list 'IN t 'RR)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'rr-zero-in) typ)
          ((eqv? t 1) (fact 'rr-one-in) typ)
          ((and (pair? t) (memq (car t) '(+ *)) (= (length t) 3))
           (lrp-rr! (cadr t)) (lrp-rr! (caddr t))
           (lrp-and! (list 'IN (cadr t) 'RR) (list 'IN (caddr t) 'RR))
           (fact (if (eq? (car t) '+) 'rr-add-closed 'rr-mul-closed) (cadr t) (caddr t))
           typ)
          ((and (pair? t) (eq? (car t) '-) (= (length t) 3))
           (lrp-rr! (cadr t)) (lrp-rr! (caddr t))
           (fact 'rr-sub-in-rr (cadr t) (caddr t)) typ)
          ((and (pair? t) (eq? (car t) '-) (= (length t) 2))
           (lrp-rr! (cadr t)) (fact 'rr-neg-closed (cadr t)) typ)
          (#t (error "lrp-rr!: cannot type" (expression->string t))))))

;;; L * X < L * Y (STRICT? #t, from 0 < L and X < Y) or L * X <= L * Y (from
;;; 0 <= L and X <= Y), both premises in context.
(define (lrp-scale! strict? l x y)
  (lrp-rr! l) (lrp-rr! x) (lrp-rr! y)
  (if strict?
      (begin (lrp-and! (list '< 0 l) (list '< x y))
             (fact 'rr-lt-scale-pos l x y))
      (begin (lrp-and! (list '<= 0 l) (list '<= x y))
             (fact 'rr-le-scale-nonneg l x y)))
  (lrp-rr! (list '* l x)) (lrp-rr! (list '* l y))
  (list (if strict? '< '<=) (list '* l x) (list '* l y)))

;;; the standing hypotheses of the affine change of variable s |-> mu + lam*s,
;;; [c,d] onto [a,b] increasingly.
(define lrp-hyp
  "forall([a in rr, b in rr, lrpc_ in rr, lrpd_ in rr, lrpl_ in rr, lrpm_ in rr],
     0 < lrpl_ implies lrpm_ + lrpl_ * lrpc_ = a implies lrpm_ + lrpl_ * lrpd_ = b implies ")

(define (lrp-hyp-setup!)
  (fact 'rr-lt-implies-le 0 'lrpl_))

;;; =====================================================================
;;; (a) THE AFFINE MAP s |-> mu + lam*s SENDS [c,d] INTO [a,b] AND (c,d) INTO
;;; (a,b); A POINT OF [a,b] HAS ITS PREIMAGE (z - mu) / lam IN [c,d].
;;; =====================================================================

(sp (make-wff (string-append lrp-hyp
  "forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpm_ + lrpl_ * lrpz_ in ccint(a, b)))")))
(dk-peel!)
(lrp-hyp-setup!)
(dk-split-all! (list (dk-fact! 'ccint-parts 'lrpc_ 'lrpd_ 'lrpz_)))
(lrp-scale! #f 'lrpl_ 'lrpc_ 'lrpz_)
(lrp-scale! #f 'lrpl_ 'lrpz_ 'lrpd_)
(lrp-rr! (lrp-map 'lrpz_))
(mac 'ccint-membership)
(dk-conj-close!
 (lambda ()
   (if (dk-asm? (dk-goal))
       (ass)
       (dk-ineq! '(IN lrpm_ RR) '(IN (* lrpl_ lrpc_) RR) '(IN (* lrpl_ lrpd_) RR)
                 '(IN (* lrpl_ lrpz_) RR) '(IN a RR) '(IN b RR)
                 '(= (+ lrpm_ (* lrpl_ lrpc_)) a) '(= (+ lrpm_ (* lrpl_ lrpd_)) b)
                 '(<= (* lrpl_ lrpc_) (* lrpl_ lrpz_)) '(<= (* lrpl_ lrpz_) (* lrpl_ lrpd_))))))
(qed 'affine-reparam-ccint-in)

(sp (make-wff (string-append lrp-hyp
  "forall([lrpz_ in ooint(lrpc_, lrpd_)], lrpm_ + lrpl_ * lrpz_ in ooint(a, b)))")))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'ooint-membership '(IN lrpz_ (OOINT lrpc_ lrpd_))))))
(lrp-scale! #t 'lrpl_ 'lrpc_ 'lrpz_)
(lrp-scale! #t 'lrpl_ 'lrpz_ 'lrpd_)
(lrp-rr! (lrp-map 'lrpz_))
(mac 'ooint-membership)
(dk-conj-close!
 (lambda ()
   (if (dk-asm? (dk-goal))
       (ass)
       (dk-ineq! '(IN lrpm_ RR) '(IN (* lrpl_ lrpc_) RR) '(IN (* lrpl_ lrpd_) RR)
                 '(IN (* lrpl_ lrpz_) RR) '(IN a RR) '(IN b RR)
                 '(= (+ lrpm_ (* lrpl_ lrpc_)) a) '(= (+ lrpm_ (* lrpl_ lrpd_)) b)
                 '(< (* lrpl_ lrpc_) (* lrpl_ lrpz_)) '(< (* lrpl_ lrpz_) (* lrpl_ lrpd_))))))
(qed 'affine-reparam-ooint-in)

;;; the preimage, with the quotient a VARIABLE q (z - mu = q * lam): both
;;; products are then atoms `ineq' certifies.
(sp (make-wff (string-append lrp-hyp
  "forall([lrpz_ in ccint(a, b), lrpq_ in rr], lrpz_ - lrpm_ = lrpq_ * lrpl_ implies
     lrpq_ in ccint(lrpc_, lrpd_) and lrpm_ + lrpl_ * lrpq_ = lrpz_))")))
(dk-peel!)
(dk-split-all! (list (dk-fact! 'ccint-parts 'a 'b 'lrpz_)))
(lrp-rr! '(* lrpl_ lrpq_))
(lrp-rr! '(* lrpq_ lrpl_))
(lrp-rr! '(* lrpc_ lrpl_))
(lrp-rr! '(* lrpd_ lrpl_))
(lrp-rr! '(* lrpl_ lrpc_))
(lrp-rr! '(* lrpl_ lrpd_))
(have! '(= (* lrpl_ lrpq_) (* lrpq_ lrpl_)) (lambda () (crs)))
(have! '(= (* lrpc_ lrpl_) (* lrpl_ lrpc_)) (lambda () (crs)))
(have! '(= (* lrpd_ lrpl_) (* lrpl_ lrpd_)) (lambda () (crs)))
(define lrp-atoms '((IN lrpm_ RR) (IN lrpz_ RR) (IN a RR) (IN b RR) (IN lrpq_ RR)
                    (IN (* lrpl_ lrpq_) RR) (IN (* lrpq_ lrpl_) RR) (IN (* lrpc_ lrpl_) RR)
                    (IN (* lrpd_ lrpl_) RR) (IN (* lrpl_ lrpc_) RR) (IN (* lrpl_ lrpd_) RR)
                    (= (* lrpl_ lrpq_) (* lrpq_ lrpl_)) (= (* lrpc_ lrpl_) (* lrpl_ lrpc_))
                    (= (* lrpd_ lrpl_) (* lrpl_ lrpd_)) (= (- lrpz_ lrpm_) (* lrpq_ lrpl_))
                    (= (+ lrpm_ (* lrpl_ lrpc_)) a) (= (+ lrpm_ (* lrpl_ lrpd_)) b)))
(dk-have! '(<= (* lrpc_ lrpl_) (* lrpq_ lrpl_))
  (lambda () (apply dk-ineq! (append lrp-atoms '((<= a lrpz_))))))
(dk-have! '(<= (* lrpq_ lrpl_) (* lrpd_ lrpl_))
  (lambda () (apply dk-ineq! (append lrp-atoms '((<= lrpz_ b))))))
(fact 'rr-mul-le-cancel-pos 'lrpc_ 'lrpl_ 'lrpq_)
(fact 'rr-mul-le-cancel-pos 'lrpq_ 'lrpl_ 'lrpd_)
(dk-conj-close!
 (lambda ()
   (if (eq? (lrp-head (dk-goal)) 'IN)
       (begin (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))
       (apply dk-ineq! lrp-atoms))))
(qed 'affine-reparam-solve)

(sp (make-wff (string-append lrp-hyp
  "forall([lrpz_ in ccint(a, b)],
     (lrpz_ - lrpm_) * recip(lrpl_) in ccint(lrpc_, lrpd_) and
     lrpm_ + lrpl_ * ((lrpz_ - lrpm_) * recip(lrpl_)) = lrpz_))")))
(dk-peel!)
(fact 'ccint-elt-in-rr 'a 'b 'lrpz_)
(fact 'rr-pos-ne-zero 'lrpl_)
(lrp-and! '(IN lrpl_ RR) '(NOT (= lrpl_ 0)))
(fact 'rr-recip-closed 'lrpl_)
(lrp-rr! '(* (- lrpz_ lrpm_) (recip lrpl_)))
(fact 'rr-recip-cancel-right '(- lrpz_ lrpm_) 'lrpl_)
(dk-apply! (dk-deepest (lambda () (fact 'affine-reparam-solve 'a 'b 'lrpc_ 'lrpd_ 'lrpl_ 'lrpm_)))
           'lrpz_ '(* (- lrpz_ lrpm_) (recip lrpl_)))
(ass)
(qed 'affine-reparam-inverse)

;;; the inverse undoes the map: ((mu + lam s) - mu) / lam = s.
(sp (make-wff "forall([lrpl_ in rr, lrpm_ in rr, lrpz_ in rr], 0 < lrpl_ implies
   ((lrpm_ + lrpl_ * lrpz_) - lrpm_) * recip(lrpl_) = lrpz_)"))
(dk-peel!)
(fact 'rr-pos-ne-zero 'lrpl_)
(have! '(= (- (+ lrpm_ (* lrpl_ lrpz_)) lrpm_) (* lrpz_ lrpl_)) (lambda () (crs)))
(subst '(= (- (+ lrpm_ (* lrpl_ lrpz_)) lrpm_) (* lrpz_ lrpl_)))
(fact 'rr-mul-recip-cancel 'lrpz_ 'lrpl_)
(subst '(= (* (* lrpz_ lrpl_) (recip lrpl_)) lrpz_))
(rfl)
(qed 'affine-reparam-inverse-value)

;;; the citation of an affine-reparam lemma at the six standing parameters: the
;;; three hypotheses are in context, so what comes back is the inner universal.
(define (lrp-h6 name) (dk-cite! name 'a 'b 'lrpc_ 'lrpd_ 'lrpl_ 'lrpm_))

;;; the image of z under the map, typed in [a,b]; returns the image.
(define (lrp-in-ab! z)
  (dk-apply! (lrp-h6 'affine-reparam-ccint-in) z)
  (lrp-map z))

(define (lrp-sets!)
  (fact 'rr-is-set)
  (fact 'ccint-subset-rr 'a 'b)
  (fact 'ccint-subset-rr 'lrpc_ 'lrpd_)
  (fact 'subclass-of-set-is-set lrp-ab 'RR)
  (fact 'subclass-of-set-is-set lrp-cd 'RR))

(define (lrp-open-leaf-close! leaf closer)
  (if (not (sequent-node-grounded? leaf)) (closer)))

;;; =====================================================================
;;; (b) THE CONTINUITY ENGINE: f continuous at mu + lam*t in the subspace of
;;; [a,b] and g = f o (mu + lam *) pointwise on [c,d] give g continuous at t in
;;; the subspace of [c,d].  The model is `reflect-continuous-at-sub'
;;; (road-laws-2.scm): the map is the restriction of the affine map of the line
;;; (`restrict-continuous-at'), corestricted to [a,b] (`ms-corestrict-continuous'),
;;; composed with f (`ms-compose-continuous-at'), transferred to g
;;; (`ms-cont-transfer-ptwise-eq').
;;; =====================================================================

(define lrp-aff '(VNB-LAMBDA x RR (+ lrpm_ (* lrpl_ x))))
(define lrp-raff (list 'RESTRICT lrp-aff lrp-cd))
(define lrp-subcd (list 'SUBSPACE-MS 'RR-MS lrp-cd))
(define lrp-subab (list 'SUBSPACE-MS 'RR-MS lrp-ab))

;;; RESTRICT(aff, [c,d])(z) = mu + lam*z for z in [c,d].
(define (lrp-raff-value! z)
  (lrp-rr! (lrp-map z))
  (dk-have! (list '= (list lrp-raff z) (lrp-map z))
    (lambda ()
      (let ((leaf (proof-state-focus *ps*)))
        (fact 'restrict-apply lrp-aff lrp-cd z)
        (subst (list '== (list lrp-raff z) (list lrp-aff z)))
        (dk-lam-b!)
        (lrp-open-leaf-close! leaf rfl)))))

(sp (make-wff (string-append lrp-hyp
  "forall([f, lrpg_ in fun(ccint(lrpc_, lrpd_), rr)],
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpg_(lrpz_) == f(lrpm_ + lrpl_ * lrpz_)) implies
     forall([lrpt_ in ccint(lrpc_, lrpd_)],
       is-continuous-at(subspace-ms(rr-ms, ccint(a, b)), rr-ms, f, lrpm_ + lrpl_ * lrpt_) implies
       is-continuous-at(subspace-ms(rr-ms, ccint(lrpc_, lrpd_)), rr-ms, lrpg_, lrpt_))))")))
(dk-peel!)
(let* ((pt    (list-ref (dk-goal) 4))
       (u     (lrp-map pt))
       (agree (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpg_)))
                       "the pointwise agreement"))
       (contf (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'IS-CONTINUOUS-AT) (dk-contains? fm 'f)))
                       "the continuity of f"))
       (l1    (list 'VNB-LAMBDA 'msz_ (list 'PTS lrp-subcd) (list 'f (list lrp-raff 'msz_)))))
  (fact 'rr-is-metric-space)
  (fact 'ccint-subset-rr 'a 'b)
  (fact 'ccint-subset-rr 'lrpc_ 'lrpd_)
  (dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
  (dk-have! (list 'SUBSET lrp-ab '(PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
  (dk-have! (list 'SUBSET lrp-cd '(PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
  (fact 'subspace-is-metric-space 'RR-MS lrp-ab)
  (fact 'subspace-is-metric-space 'RR-MS lrp-cd)
  (fact 'subspace-pts 'RR-MS lrp-ab)
  (fact 'subspace-pts 'RR-MS lrp-cd)
  ;; f is a function on [a,b]
  (dk-have! (list 'IN 'f (list 'FUN lrp-ab 'RR))
    (lambda ()
      (mac-h 'IS-CONTINUOUS-AT contf)
      (dk-split-all!)
      (subst (list '== lrp-ab (list 'PTS lrp-subab)))
      (subst '(== RR (PTS RR-MS)))
      (ass)))
  ;; the affine map, restricted to [c,d]
  (lrp-and! '(IN lrpm_ RR) '(IN lrpl_ RR))
  (fact 'affine-lam-in-fun 'lrpm_ 'lrpl_)
  (fact 'restrict-in-fun lrp-aff 'RR 'RR lrp-cd)
  (dk-have! (list 'IN pt (list 'PTS lrp-subcd))
    (lambda () (subst (list '== (list 'PTS lrp-subcd) lrp-cd)) (ass)))
  (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ pt)
  (lrp-raff-value! pt)
  (lrp-in-ab! pt)
  (dk-have! (list 'IN (list lrp-raff pt) lrp-ab)
    (lambda () (subst (list '= (list lrp-raff pt) u)) (ass)))
  (dk-have! (list 'FORALL 'lrpy_ (list 'IMPLIES (list 'IN 'lrpy_ (list 'PTS lrp-subcd))
              (list 'IN (list lrp-raff 'lrpy_) lrp-ab)))
    (lambda ()
      (let ((y (dk-di-var!)))
        (dk-have! (list 'IN y lrp-cd)
          (lambda () (subst (list '== lrp-cd (list 'PTS lrp-subcd))) (ass)))
        (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ y)
        (lrp-raff-value! y)
        (lrp-in-ab! y)
        (subst (list '= (list lrp-raff y) (lrp-map y)))
        (ass))))
  (have! (list 'AND '(IN lrpm_ RR) (list 'AND '(IN lrpl_ RR) (list 'IN pt 'RR))))
  (fact 'affine-continuous-at 'lrpm_ 'lrpl_ pt)
  (fact 'restrict-continuous-at 'RR-MS lrp-cd 'RR-MS lrp-aff pt)
  (fact 'ms-corestrict-continuous lrp-subcd 'RR-MS lrp-ab lrp-raff pt)
  (dk-have! (list 'IS-CONTINUOUS-AT lrp-subab 'RR-MS 'f (list lrp-raff pt))
    (lambda () (subst (list '= (list lrp-raff pt) u)) (ass)))
  (fact 'ms-compose-continuous-at lrp-subcd lrp-subab 'RR-MS lrp-raff 'f pt)
  (dk-have! (list 'IN 'lrpg_ (list 'FUN (list 'PTS lrp-subcd) '(PTS RR-MS)))
    (lambda ()
      (subst (list '== (list 'PTS lrp-subcd) lrp-cd))
      (subst '(== (PTS RR-MS) RR))
      (ass)))
  (dk-have! (list 'FORALL 'lrpy_ (list 'IMPLIES (list 'IN 'lrpy_ (list 'PTS lrp-subcd))
              (list '= (list 'lrpg_ 'lrpy_) (list l1 'lrpy_))))
    (lambda ()
      (let* ((y (dk-di-var!))
             (leaf (proof-state-focus *ps*)))
        (dk-have! (list 'IN y lrp-cd)
          (lambda () (subst (list '== lrp-cd (list 'PTS lrp-subcd))) (ass)))
        (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ y)
        (lrp-raff-value! y)
        (lrp-in-ab! y)
        (fact 'fun-apply-type-c 'f lrp-ab 'RR (lrp-map y))
        (dk-apply! agree y)
        (dk-lam-b!)
        (subst (list '= (list lrp-raff y) (lrp-map y)))
        (subst (list '== (list 'lrpg_ y) (list 'f (lrp-map y))))
        (lrp-open-leaf-close! leaf rfl))))
  (fact 'ms-cont-transfer-ptwise-eq lrp-subcd 'RR-MS l1 'lrpg_ pt)
  (ass))
(qed 'affine-reparam-continuous-at-sub)

(sp (make-wff (string-append lrp-hyp
  "forall([f, lrpg_ in fun(ccint(lrpc_, lrpd_), rr)],
     is-continuous-on(f, ccint(a, b)) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpg_(lrpz_) == f(lrpm_ + lrpl_ * lrpz_)) implies
     is-continuous-on(lrpg_, ccint(lrpc_, lrpd_))))")))
(dk-peel!)
(let* ((contf (dk-split-all!
               (dk-landed* (lambda ()
                 (mac-h 'IS-CONTINUOUS-ON (list 'IS-CONTINUOUS-ON 'f lrp-ab))))))
       (univ (car (filter (lambda (fm) (and (eq? (lrp-head fm) 'FORALL)
                                            (dk-contains? fm 'IS-CONTINUOUS-AT)))
                          contf))))
  (mac 'IS-CONTINUOUS-ON)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (lrp-head (dk-goal)) 'FORALL))
         (ass)
         (let ((z (dk-di-var!)))
           (lrp-in-ab! z)
           (dk-apply! univ (lrp-map z))
           (dk-apply! (lrp-h6 'affine-reparam-continuous-at-sub) 'f 'lrpg_ z)
           (ass))))))
(qed 'affine-reparam-continuous-on)

;;; =====================================================================
;;; (c) THE EXCEPTIONAL SET: the image of D under the INVERSE map
;;; z |-> (z - mu)/lam of [a,b], countable when D is (`countable-image'), inside
;;; [c,d] (`affine-reparam-inverse'); t in [c,d] is outside it only if
;;; mu + lam*t is outside D -- by the contrapositive, the inverse of
;;; mu + lam*t is t (`affine-reparam-inverse-value').
;;; =====================================================================

(define lrp-inv (list 'VNB-LAMBDA 'lrpv_ lrp-ab '(* (- lrpv_ lrpm_) (recip lrpl_))))
(define (lrp-inv-of z) (list '* (list '- z 'lrpm_) '(recip lrpl_)))

(define (lrp-recip!)
  (fact 'rr-pos-ne-zero 'lrpl_)
  (lrp-and! '(IN lrpl_ RR) '(NOT (= lrpl_ 0)))
  (fact 'rr-recip-closed 'lrpl_))

(sp (make-wff (string-append lrp-hyp
  "forall([lrpe_], is-countable(lrpe_) implies subset(lrpe_, ccint(a, b)) implies
     is-countable(image(vnb-lambda(lrpv_, ccint(a, b), (lrpv_ - lrpm_) * recip(lrpl_)), lrpe_)) and
     subset(image(vnb-lambda(lrpv_, ccint(a, b), (lrpv_ - lrpm_) * recip(lrpl_)), lrpe_), ccint(lrpc_, lrpd_))))")))
(dk-peel!)
(lrp-sets!)
(lrp-recip!)
(dk-have! (list 'IN lrp-inv (list 'FUN lrp-ab 'RR))
  (lambda ()
    (dk-lam-type!
     (lambda ()
       (let ((z (dk-di-var!)))
         (fact 'ccint-elt-in-rr 'a 'b z)
         (lrp-rr! (lrp-inv-of z))
         (ass))))))
(fact 'countable-image 'lrpe_ lrp-inv lrp-ab 'RR)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (lrp-head (dk-goal)) 'SUBSET))
       (ass)
       (let ((w (subset-by-element!)))
         (dk-image-hyp! (list 'IN w (list 'IMAGE lrp-inv 'lrpe_)))
         (let ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
           (dk-split-all!)
           (fact 'subset-mem-fwd 'lrpe_ lrp-ab z)
           (dk-split-all! (list (dk-apply! (lrp-h6 'affine-reparam-inverse) z)))
           (dk-have! (list '= (list lrp-inv z) (lrp-inv-of z))
             (lambda () (dk-lam-b!) (rfl)))
           (subst (list '= w (list lrp-inv z)))
           (subst (list '= (list lrp-inv z) (lrp-inv-of z)))
           (ass))))))
(qed 'affine-reparam-image-countable)

(sp (make-wff (string-append lrp-hyp
  "forall([lrpe_], subset(lrpe_, ccint(a, b)) implies
     forall([lrpt_ in ccint(lrpc_, lrpd_)],
       not(lrpt_ in image(vnb-lambda(lrpv_, ccint(a, b), (lrpv_ - lrpm_) * recip(lrpl_)), lrpe_)) implies
       not(lrpm_ + lrpl_ * lrpt_ in lrpe_))))")))
(dk-peel!)
(fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ 'lrpt_)
(lrp-in-ab! 'lrpt_)
(lrp-rr! (lrp-map 'lrpt_))
(let ((imp (list 'IMPLIES (list 'IN (lrp-map 'lrpt_) 'lrpe_)
                 (list 'IN 'lrpt_ (list 'IMAGE lrp-inv 'lrpe_))))
      (neg (list 'NOT (list 'IN 'lrpt_ (list 'IMAGE lrp-inv 'lrpe_)))))
  (dk-have! imp
    (lambda ()
      (di)
      (dk-image-goal!)
      (ew (lrp-map 'lrpt_))
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (lrp-head (dk-goal)) '=))
             (ass)
             (let ((leaf (proof-state-focus *ps*)))
               (dk-lam-b!)
               (fact 'affine-reparam-inverse-value 'lrpl_ 'lrpm_ 'lrpt_)
               (lrp-open-leaf-close! leaf ass)))))))
  (dk-only! (dk-ctx-form imp) (dk-ctx-form neg))
  (prop))
(qed 'affine-reparam-not-in-image)

;;; =====================================================================
;;; (d) A REGULATED FUNCTION STAYS REGULATED (Dieudonne VII.6).  A right limit
;;; l of f at u = mu + lam*x is a right limit of g = f o (mu + lam *) at x: for
;;; eps, take f's delta, halve it (h + h = delta), and take d' with lam*t <= h
;;; for 0 <= t <= d' (`rr-scale-eps'); for x < t < x + d', s = mu + lam*t has
;;; u < s <= u + h < u + delta.  The left limit is the mirror.  The model is
;;; `regulated-on-reflect' (road-laws-2.scm), where the sides swap.
;;; =====================================================================

;;; the eps-clause.  Goal on entry: the eps-universal of g's one-sided limit at X
;;; with value L0; CLAUSE is f's eps-clause at U = mu + lam*X; AGREE g's values.
(define (lrp-reg-eps! right? x u l0 clause agree)
  (let* ((pe (dk-peel!))
         (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (dl (dk-skolem! (dk-apply! clause e)))
         (dc (dk-pick (lambda (g) (and (eq? (lrp-head g) 'FORALL) (dk-contains? g dl)))
                      "the delta clause of f")))
    (fact 'rr-pos-rr-in-rr dl)
    (let* ((h  (dk-halve! dl))
           (dp (dk-skolem! (dk-fact! 'rr-scale-eps 'lrpl_ h)))
           (sc (dk-pick (lambda (g) (and (eq? (lrp-head g) 'FORALL) (dk-contains? g dp)
                                         (dk-contains? g 'lrpl_)))
                        "the scaling clause")))
      (fact 'rr-pos-rr-in-rr dp)
      (ew dp)
      (dk-conj-close!
       (lambda ()
         (if (eq? (lrp-head (dk-goal)) 'POS-RR)
             (ass)
             (let* ((ls  (dk-peel!))
                    (t   (cadr (car (filter (lambda (g) (and (eq? (lrp-head g) 'IN)
                                                              (equal? (caddr g) lrp-cd)))
                                            ls))))
                    (s   (lrp-map t))
                    (hi  (if right? t x))
                    (lo  (if right? x t))
                    (gap (list '- hi lo))
                    (lg  (list '* 'lrpl_ gap))
                    (base (list '(IN lrpm_ RR) (list 'IN x 'RR) (list 'IN t 'RR)
                                (list 'IN (list '* 'lrpl_ x) 'RR) (list 'IN (list '* 'lrpl_ t) 'RR))))
               (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ t)
               (lrp-in-ab! t)
               (lrp-scale! #t 'lrpl_ lo hi)
               (lrp-rr! gap)
               (lrp-rr! lg)
               (dk-have! (list '<= 0 gap)
                 (lambda () (dk-ineq! (list 'IN x 'RR) (list 'IN t 'RR) (list '< lo hi))))
               (dk-have! (list '<= gap dp)
                 (lambda ()
                   (dk-ineq! (list 'IN x 'RR) (list 'IN t 'RR) (list 'IN dp 'RR)
                             (if right? (list '< t (list '+ x dp)) (list '< (list '- x dp) t)))))
               (dk-apply! sc gap)
               (have! (list '= lg (list '- (list '* 'lrpl_ hi) (list '* 'lrpl_ lo)))
                      (lambda () (crs)))
               (for-each
                (lambda (goal)
                  (dk-have! goal
                    (lambda ()
                      (apply dk-ineq!
                             (append base
                                     (list (list 'IN lg 'RR) (list 'IN h 'RR) (list 'IN dl 'RR)
                                           (list '< (list '* 'lrpl_ lo) (list '* 'lrpl_ hi))
                                           (list '<= lg h)
                                           (list '= lg (list '- (list '* 'lrpl_ hi) (list '* 'lrpl_ lo)))
                                           (list '= (list '+ h h) dl) (list '< 0 h)))))))
                (if right?
                    (list (list '< u s) (list '< s (list '+ u dl)))
                    (list (list '< (list '- u dl) s) (list '< s u))))
               (dk-apply! dc s)
               (dk-apply! agree t)
               (subst (list '== (list 'lrpg_ t) (list 'f s)))
               (ass))))))))

;;; one clause of g's IS-REGULATED-ON.  Goal on entry: the right-limit (RIGHT?
;;; #t) or left-limit universal of g.  FR / FL: f's two clauses.
(define (lrp-reg-side! right? fr fl agree)
  (let* ((x (dk-di-var!))
         (u (lrp-map x)))
    (dk-peel!)
    (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ x)
    (lrp-in-ab! x)
    (if right? (lrp-scale! #t 'lrpl_ x 'lrpd_) (lrp-scale! #t 'lrpl_ 'lrpc_ x))
    (lrp-rr! '(* lrpl_ lrpc_))
    (lrp-rr! '(* lrpl_ lrpd_))
    (dk-have! (if right? (list '< u 'b) (list '< 'a u))
      (lambda ()
        (dk-ineq! '(IN lrpm_ RR) '(IN a RR) '(IN b RR)
                  (list 'IN (list '* 'lrpl_ x) 'RR) '(IN (* lrpl_ lrpd_) RR) '(IN (* lrpl_ lrpc_) RR)
                  '(= (+ lrpm_ (* lrpl_ lrpc_)) a) '(= (+ lrpm_ (* lrpl_ lrpd_)) b)
                  (if right?
                      (list '< (list '* 'lrpl_ x) '(* lrpl_ lrpd_))
                      (list '< '(* lrpl_ lrpc_) (list '* 'lrpl_ x))))))
    (let* ((l0 (dk-skolem! (dk-apply! (if right? fr fl) u)))
           (lim (list (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN) 'f lrp-ab u l0))
           (parts (dk-split-all! (dk-landed* (lambda () (mac-h (car lim) lim)))))
           (clause (car (filter (lambda (g) (and (eq? (lrp-head g) 'FORALL) (dk-contains? g l0)))
                                parts))))
      (ew l0)
      (mac (car lim))
      (dk-conj-close!
       (lambda ()
         (if (eq? (lrp-head (dk-goal)) 'FORALL)
             (lrp-reg-eps! right? x u l0 clause agree)
             (ass)))))))

(sp (make-wff (string-append lrp-hyp
  "lrpc_ < lrpd_ implies
   forall([f, lrpg_ in fun(ccint(lrpc_, lrpd_), rr)],
     is-regulated-on(f, a, b) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpg_(lrpz_) == f(lrpm_ + lrpl_ * lrpz_)) implies
     is-regulated-on(lrpg_, lrpc_, lrpd_)))")))
(dk-peel!)
(lrp-hyp-setup!)
(lrp-sets!)
(let* ((agree (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpg_)))
                       "the pointwise agreement"))
       (reg (dk-split-all! (dk-landed* (lambda ()
              (mac-h 'IS-REGULATED-ON '(IS-REGULATED-ON f a b))))))
       (fr (car (filter (lambda (g) (and (eq? (lrp-head g) 'FORALL)
                                         (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN)))
                        reg)))
       (fl (car (filter (lambda (g) (and (eq? (lrp-head g) 'FORALL)
                                         (dk-contains? g 'IS-LEFT-LIMIT-WITHIN)))
                        reg))))
  (mac 'IS-REGULATED-ON)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (if (eq? (lrp-head g) 'FORALL)
           (lrp-reg-side! (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN) fr fl agree)
           (ass))))))
(qed 'affine-reparam-regulated)

;;; =====================================================================
;;; (1) THE NOTES' (48), AFFINE CASE, FOR THE REAL INTEGRAL.
;;;
;;;   W(s) = w(mu + lam*s) is a primitive on [c,d] of s |-> lam*phi(mu + lam*s),
;;;   and  PW-INT(s |-> lam*phi(mu + lam*s), c, d) = PW-INT(phi, a, b).
;;;
;;; The derivative step is `has-deriv-at-affine-chain' (a direct form of the
;;; chain rule with the affine inner map, whose open-ball hypothesis is met by
;;; `ooint-inner-radius'); continuity is (b); the exceptional set is the image
;;; of w's under the inverse map, (c).  The value: W(d) - W(c) = w(b) - w(a).
;;; =====================================================================

(sp (make-wff (string-append lrp-hyp
  "lrpc_ < lrpd_ implies
   forall([pwf_, pphi_], is-primitive(pwf_, pphi_, a, b) implies
     forall([lrph_ in fun(ccint(lrpc_, lrpd_), rr), lrps_ in fun(ccint(lrpc_, lrpd_), rr)],
       forall([lrpz_ in ccint(lrpc_, lrpd_)], lrph_(lrpz_) == pwf_(lrpm_ + lrpl_ * lrpz_)) implies
       forall([lrpz_ in ccint(lrpc_, lrpd_)], lrps_(lrpz_) == lrpl_ * pphi_(lrpm_ + lrpl_ * lrpz_)) implies
       is-primitive(lrph_, lrps_, lrpc_, lrpd_) and
       pw-int(lrps_, lrpc_, lrpd_) = pw-int(pphi_, a, b))))")))
(dk-peel!)
(define lrp-hagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrph_)))
           "the pointwise value of the reparametrised primitive"))
(define lrp-sagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrps_)))
           "the pointwise value of the reparametrised integrand"))
(lrp-hyp-setup!)
(lrp-sets!)
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'ooint-subset-ccint 'lrpc_ 'lrpd_)
(fact 'ooint-subset-ccint 'a 'b)
(dk-apply! (lrp-h6 'affine-reparam-continuous-on) 'pwf_ 'lrph_)
(define lrp-prim '(IS-PRIMITIVE lrph_ lrps_ lrpc_ lrpd_))
(dk-have! lrp-prim
  (lambda ()
    (let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set 'pwf_ 'pphi_ 'a 'b)))
           (d1 (begin (dk-split-all!)
                      (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL)
                                                 (dk-contains? fm 'HAS-DERIV-AT)
                                                 (dk-contains? fm s1)))
                               "the derivative universal")))
           (img (list 'IMAGE lrp-inv s1)))
      (dk-split-all! (list (dk-apply! (lrp-h6 'affine-reparam-image-countable) s1)))
      (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT lrpc_ lrpd_))
                  (list 'IMPLIES (list 'NOT (list 'IN 'pat_ img))
                        '(HAS-DERIV-AT lrph_ pat_ (lrps_ pat_)))))
        (lambda ()
          (dk-peel!)
          (let* ((tv (caddr (dk-goal)))
                 (u  (lrp-map tv))
                 (leaf (proof-state-focus *ps*)))
            (fact 'subset-mem-fwd '(OOINT lrpc_ lrpd_) lrp-cd tv)
            (fact 'ccint-elt-in-rr 'lrpc_ 'lrpd_ tv)
            (dk-apply! (lrp-h6 'affine-reparam-ooint-in) tv)
            (fact 'subset-mem-fwd '(OOINT a b) lrp-ab u)
            (dk-apply! (lrp-h6 'affine-reparam-not-in-image) s1 tv)
            (dk-apply! d1 u)
            (fact 'fun-apply-type-c 'pphi_ lrp-ab 'RR u)
            (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'lrpc_ 'lrpd_ tv))))
              (dk-split-all!)
              (fact 'rr-pos-rr-in-rr rv)
              (let ((oo (list 'OOINT (list '- tv rv) (list '+ tv rv))))
                (fact 'restrict-in-fun 'lrph_ lrp-cd 'RR oo)
                (dk-have! (list 'FORALL 'cry_ (list 'IMPLIES (list 'IN 'cry_ oo)
                            (list '== '(lrph_ cry_) (list 'pwf_ (lrp-map 'cry_)))))
                  (lambda ()
                    (let ((y (dk-di-var!)))
                      (fact 'subset-mem-fwd oo lrp-cd y)
                      (dk-apply! lrp-hagree y)
                      (ass))))
                (fact 'has-deriv-at-affine-chain rv 'pwf_ 'lrph_ 'lrpm_ 'lrpl_ tv
                      (list 'pphi_ u))
                (dk-apply! lrp-sagree tv)
                (have! (list '= (list '* 'lrpl_ (list 'pphi_ u)) (list '* (list 'pphi_ u) 'lrpl_))
                       (lambda () (crs)))
                (subst (list '== (list 'lrps_ tv) (list '* 'lrpl_ (list 'pphi_ u))))
                (subst (list '= (list '* 'lrpl_ (list 'pphi_ u)) (list '* (list 'pphi_ u) 'lrpl_)))
                (lrp-open-leaf-close! leaf ass))))))
      (mac 'IS-PRIMITIVE)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (lrp-head (dk-goal)) 'FORSOME))
             (ass)
             (begin (ew img) (dk-conj-close! (lambda () (ass))))))))))
;; the value
(fact 'pw-int-value 'lrph_ 'lrps_ 'lrpc_ 'lrpd_)
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(define (lrp-endpoint! z lo hi)
  (fact 'rr-leq-reflexive z)
  (fact 'rr-lt-implies-le lo hi)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))))
(lrp-endpoint! 'lrpc_ 'lrpc_ 'lrpd_)
(lrp-endpoint! 'lrpd_ 'lrpc_ 'lrpd_)
(lrp-endpoint! 'a 'a 'b)
(lrp-endpoint! 'b 'a 'b)
(fact 'fun-apply-type-c 'pwf_ lrp-ab 'RR 'a)
(fact 'fun-apply-type-c 'pwf_ lrp-ab 'RR 'b)
(fact 'rr-sub-in-rr '(pwf_ b) '(pwf_ a))
(dk-apply! lrp-hagree 'lrpc_)
(dk-apply! lrp-hagree 'lrpd_)
(dk-conj-close!
 (lambda ()
   (if (eq? (lrp-head (dk-goal)) 'IS-PRIMITIVE)
       (ass)
       (begin
         (subst '(= (PW-INT lrps_ lrpc_ lrpd_) (- (lrph_ lrpd_) (lrph_ lrpc_))))
         (subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
         (subst (list '== '(lrph_ lrpd_) (list 'pwf_ (lrp-map 'lrpd_))))
         (subst (list '== '(lrph_ lrpc_) (list 'pwf_ (lrp-map 'lrpc_))))
         (subst '(= (+ lrpm_ (* lrpl_ lrpd_)) b))
         (subst '(= (+ lrpm_ (* lrpl_ lrpc_)) a))
         (rfl)))))
(qed 'pw-int-affine-subst)

;;; =====================================================================
;;; (2) THE SAME FOR CC-INT -- equation (44) is componentwise, so this is (1)
;;; twice.  For lam REAL, re(lam * z) = lam * re(z) and im(lam * z) =
;;; lam * im(z) (`cc-re-real-mul', `cc-im-real-mul').  The primitives of the two
;;; coordinates of phi are hypotheses, as in every CC-INT law of the tree
;;; (`cc-int-reflect', `cc-int-real-mul').
;;; =====================================================================

(define (lrp-proj proj f dom) (list 'VNB-LAMBDA 'pat_ dom (list proj (list f 'pat_))))

;;; ONE COORDINATE of the reparametrised CC-valued integrand LRPB_: typings,
;;; the two pointwise values, and (1).  PRIM is the given primitive of the
;;; coordinate of PPHI_.
(define (lrp-cc-coord! proj inr mullaw prim bagree)
  (let ((r  (lrp-proj proj 'pphi_ lrp-ab))
        (rb (lrp-proj proj 'lrpb_ lrp-cd))
        (h  (list 'VNB-LAMBDA 'lrpv_ lrp-cd (list prim (lrp-map 'lrpv_)))))
    (fact 'primitive-in-fun prim r 'a 'b)
    (dk-have! (list 'IN rb (list 'FUN lrp-cd 'RR))
      (lambda ()
        (dk-lam-type!
         (lambda ()
           (let ((z (dk-di-var!)))
             (fact 'fun-apply-type-c 'lrpb_ lrp-cd 'CC z)
             (fact inr (list 'lrpb_ z))
             (ass))))))
    (dk-have! (list 'IN h (list 'FUN lrp-cd 'RR))
      (lambda ()
        (dk-lam-type!
         (lambda ()
           (let ((z (dk-di-var!)))
             (lrp-in-ab! z)
             (fact 'fun-apply-type-c prim lrp-ab 'RR (lrp-map z))
             (ass))))))
    (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
                (list '== (list h 'lrpz_) (list prim (lrp-map 'lrpz_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (lrp-in-ab! z)
          (if (not (dk-lam-b!)) (qrfl)))))
    (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
                (list '== (list rb 'lrpz_) (list '* 'lrpl_ (list r (lrp-map 'lrpz_))))))
      (lambda ()
        (let* ((z (dk-di-var!))
               (u (lrp-in-ab! z))
               (leaf (proof-state-focus *ps*)))
          (fact 'fun-apply-type-c 'lrpb_ lrp-cd 'CC z)
          (fact 'fun-apply-type-c 'pphi_ lrp-ab 'CC u)
          (dk-apply! bagree z)
          (dk-lam-b!)
          (subst (list '== (list 'lrpb_ z) (list '* 'lrpl_ (list 'pphi_ u))))
          (fact mullaw 'lrpl_ (list 'pphi_ u))
          (subst (list '= (list proj (list '* 'lrpl_ (list 'pphi_ u)))
                       (list '* 'lrpl_ (list proj (list 'pphi_ u)))))
          (lrp-open-leaf-close! leaf qrfl))))
    (dk-split-all! (list (dk-apply! (lrp-h6 'pw-int-affine-subst) prim r h rb)))
    (fact 'pw-int-in-rr prim r 'a 'b)))

(sp (make-wff (string-append lrp-hyp
  "lrpc_ < lrpd_ implies
   forall([pphi_, lrpb_], pphi_ in fun(ccint(a, b), cc) implies lrpb_ in fun(ccint(lrpc_, lrpd_), cc) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpb_(lrpz_) == lrpl_ * pphi_(lrpm_ + lrpl_ * lrpz_)) implies
     forall([pwf_, paw_],
       is-primitive(pwf_, vnb-lambda(pat_, ccint(a, b), real-part(pphi_(pat_))), a, b) implies
       is-primitive(paw_, vnb-lambda(pat_, ccint(a, b), imag-part(pphi_(pat_))), a, b) implies
       cc-int(lrpb_, lrpc_, lrpd_) = cc-int(pphi_, a, b))))")))
(dk-peel!)
(lrp-hyp-setup!)
(lrp-sets!)
(define lrp-bagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpb_)))
           "the pointwise value of the reparametrised integrand"))
(lrp-cc-coord! 'real-part 'real-part-in-rr 'cc-re-real-mul 'pwf_ lrp-bagree)
(lrp-cc-coord! 'imag-part 'imag-part-in-rr 'cc-im-real-mul 'paw_ lrp-bagree)
(mac 'CC-INT)
(subst (list '= (list 'PW-INT (lrp-proj 'real-part 'lrpb_ lrp-cd) 'lrpc_ 'lrpd_)
             (list 'PW-INT (lrp-proj 'real-part 'pphi_ lrp-ab) 'a 'b)))
(subst (list '= (list 'PW-INT (lrp-proj 'imag-part 'lrpb_ lrp-cd) 'lrpc_ 'lrpd_)
             (list 'PW-INT (lrp-proj 'imag-part 'pphi_ lrp-ab) 'a 'b)))
(let ((pi-re (list 'PW-INT (lrp-proj 'real-part 'pphi_ lrp-ab) 'a 'b))
      (pi-im (list 'PW-INT (lrp-proj 'imag-part 'pphi_ lrp-ab) 'a 'b)))
  (fact 'cc-i-in)
  (fact 'rr-subset-cc pi-re)
  (fact 'rr-subset-cc pi-im)
  (lrp-and! (list 'IN pi-im 'CC) '(IN +i CC))
  (fact 'cc-mul-closed pi-im '+i)
  (lrp-and! (list 'IN pi-re 'CC) (list 'IN (list '* pi-im '+i) 'CC))
  (fact 'cc-add-closed pi-re (list '* pi-im '+i))
  (rfl))
(qed 'cc-int-affine-subst)

;;; =====================================================================
;;; (3) THE REPARAMETRISED ROAD (the notes' (48), affine case): rho(s) =
;;; gamma(mu + lam*s), rho'(s) = lam * gamma'(mu + lam*s) on [c,d] is a road
;;; with the same trace, and the integral along it is the integral along gamma.
;;; =====================================================================

(sp (make-wff (string-append lrp-hyp
  "forall([pgam, lrpr_], pgam in fun(ccint(a, b), cc) implies lrpr_ in fun(ccint(lrpc_, lrpd_), cc) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpr_(lrpz_) == pgam(lrpm_ + lrpl_ * lrpz_)) implies
     subset(trace(lrpr_, lrpc_, lrpd_), trace(pgam, a, b)) and
     subset(trace(pgam, a, b), trace(lrpr_, lrpc_, lrpd_))))")))
(dk-peel!)
(define lrp-ragree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpr_)))
           "the pointwise value of the reparametrised path"))
(fact 'trace-unfold 'lrpr_ 'lrpc_ 'lrpd_)
(fact 'trace-unfold 'pgam 'a 'b)
(dk-conj-close!
 (lambda ()
   (let* ((fwd? (equal? (cadr (dk-goal)) '(TRACE lrpr_ lrpc_ lrpd_)))
          (w (subset-by-element!)))
     (if fwd?
         (begin
           (dk-have! (list 'IN w (list 'IMAGE 'lrpr_ lrp-cd))
             (lambda () (subst (list '== (list 'IMAGE 'lrpr_ lrp-cd) '(TRACE lrpr_ lrpc_ lrpd_))) (ass)))
           (dk-image-hyp! (list 'IN w (list 'IMAGE 'lrpr_ lrp-cd)))
           (let* ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential")))
                  (u (begin (dk-split-all!) (lrp-in-ab! z))))
             (dk-apply! lrp-ragree z)
             (fact 'trace-value-in 'pgam 'a 'b u)
             (subst (list '= w (list 'lrpr_ z)))
             (subst (list '== (list 'lrpr_ z) (list 'pgam u)))
             (ass)))
         (begin
           (dk-have! (list 'IN w (list 'IMAGE 'pgam lrp-ab))
             (lambda () (subst (list '== (list 'IMAGE 'pgam lrp-ab) '(TRACE pgam a b))) (ass)))
           (dk-image-hyp! (list 'IN w (list 'IMAGE 'pgam lrp-ab)))
           (let* ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential")))
                  (q (begin (dk-split-all!) (lrp-inv-of z))))
             (dk-split-all! (list (dk-apply! (lrp-h6 'affine-reparam-inverse) z)))
             (dk-apply! lrp-ragree q)
             (fact 'trace-value-in 'lrpr_ 'lrpc_ 'lrpd_ q)
             (fact 'fun-apply-type-c 'pgam lrp-ab 'CC z)
             (dk-have! (list '= (list 'pgam z) (list 'lrpr_ q))
               (lambda ()
                 (let ((leaf (proof-state-focus *ps*)))
                   (subst (list '== (list 'lrpr_ q) (list 'pgam (lrp-map q))))
                   (subst (list '= (lrp-map q) z))
                   (lrp-open-leaf-close! leaf rfl))))
             (subst (list '= w (list 'pgam z)))
             (subst (list '= (list 'pgam z) (list 'lrpr_ q)))
             (ass)))))))
(qed 'trace-affine-reparam)

;;; ONE COORDINATE of the reparametrised road.
(define (lrp-road-coord! proj inr mullaw regoff pagree dagree)
  (let* ((g  (lrp-proj proj 'pgam lrp-ab))
         (dd (lrp-proj proj 'dgam lrp-ab))
         (bg (lrp-proj proj 'lrpr_ lrp-cd))
         (bd (lrp-proj proj 'lrpk_ lrp-cd))
         (ee (list 'VNB-LAMBDA 'lrpv_ lrp-cd (list proj (list 'dgam (lrp-map 'lrpv_))))))
    (fact regoff 'pgam 'dgam 'a 'b)
    (for-each
     (lambda (lam src)
       (dk-have! (list 'IN lam (list 'FUN lrp-cd 'RR))
         (lambda ()
           (dk-lam-type!
            (lambda ()
              (let ((z (dk-di-var!)))
                (if (eq? src 'dgam)
                    (let ((u (lrp-in-ab! z)))
                      (fact 'fun-apply-type-c 'dgam lrp-ab 'CC u)
                      (fact inr (list 'dgam u)))
                    (begin
                      (fact 'fun-apply-type-c src lrp-cd 'CC z)
                      (fact inr (list src z))))
                (ass)))))))
     (list bg bd ee) '(lrpr_ lrpk_ dgam))
    ;; bg(z) == g(mu + lam z)
    (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
                (list '== (list bg 'lrpz_) (list g (lrp-map 'lrpz_)))))
      (lambda ()
        (let* ((z (dk-di-var!)) (u (lrp-in-ab! z)) (leaf (proof-state-focus *ps*)))
          (fact 'fun-apply-type-c 'lrpr_ lrp-cd 'CC z)
          (fact 'fun-apply-type-c 'pgam lrp-ab 'CC u)
          (dk-apply! pagree z)
          (dk-lam-b!)
          (subst (list '== (list 'lrpr_ z) (list 'pgam u)))
          (lrp-open-leaf-close! leaf qrfl))))
    ;; bd(z) == lam * dd(mu + lam z), and bd(z) == lam * ee(z)
    (for-each
     (lambda (rhs-of)
       (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
                   (list '== (list bd 'lrpz_) (list '* 'lrpl_ (rhs-of 'lrpz_)))))
         (lambda ()
           (let* ((z (dk-di-var!)) (u (lrp-in-ab! z)) (leaf (proof-state-focus *ps*)))
             (fact 'fun-apply-type-c 'lrpk_ lrp-cd 'CC z)
             (fact 'fun-apply-type-c 'dgam lrp-ab 'CC u)
             (dk-apply! dagree z)
             (dk-lam-b!)
             (subst (list '== (list 'lrpk_ z) (list '* 'lrpl_ (list 'dgam u))))
             (fact mullaw 'lrpl_ (list 'dgam u))
             (subst (list '= (list proj (list '* 'lrpl_ (list 'dgam u)))
                          (list '* 'lrpl_ (list proj (list 'dgam u)))))
             (lrp-open-leaf-close! leaf qrfl)))))
     (list (lambda (z) (list dd (lrp-map z))) (lambda (z) (list ee z))))
    ;; ee(z) == dd(mu + lam z)
    (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
                (list '== (list ee 'lrpz_) (list dd (lrp-map 'lrpz_)))))
      (lambda ()
        (let* ((z (dk-di-var!)) (u (lrp-in-ab! z)))
          (if (not (dk-lam-b!)) (qrfl)))))
    ;; the primitive, the regulated derivative, the continuity
    (dk-split-all! (list (dk-apply! (lrp-h6 'pw-int-affine-subst) g dd bg bd)))
    (dk-apply! (lrp-h6 'affine-reparam-regulated) dd ee)
    (fact 'regulated-on-scalar ee bd 'lrpc_ 'lrpd_ 'lrpl_)
    (fact 'primitive-continuous bg bd 'lrpc_ 'lrpd_)
    ;; the value equation `is-path-of-coords' asks for
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ lrp-cd)
                (list '= (list proj '(lrpr_ pay_)) (list bg 'pay_))))
      (lambda ()
        (let* ((z (dk-di-var!)) (leaf (proof-state-focus *ps*)))
          (fact 'fun-apply-type-c 'lrpr_ lrp-cd 'CC z)
          (fact inr (list 'lrpr_ z))
          (dk-lam-b!)
          (lrp-open-leaf-close! leaf rfl))))
    bg))

(sp (make-wff (string-append lrp-hyp
  "lrpc_ < lrpd_ implies
   forall([pgam, dgam, lrpr_, lrpk_], is-road(pgam, dgam, a, b) implies
     lrpr_ in fun(ccint(lrpc_, lrpd_), cc) implies lrpk_ in fun(ccint(lrpc_, lrpd_), cc) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpr_(lrpz_) == pgam(lrpm_ + lrpl_ * lrpz_)) implies
     forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpk_(lrpz_) == lrpl_ * dgam(lrpm_ + lrpl_ * lrpz_)) implies
     is-road(lrpr_, lrpk_, lrpc_, lrpd_)))")))
(dk-peel!)
(define lrp-pagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpr_)))
           "the pointwise value of the reparametrised path"))
(define lrp-dagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpk_)))
           "the pointwise value of the reparametrised derivative"))
(lrp-hyp-setup!)
(lrp-sets!)
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(fact 'is-road-re-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-im-antiderivative 'pgam 'dgam 'a 'b)
(define lrp-bgr (lrp-road-coord! 'real-part 'real-part-in-rr 'cc-re-real-mul 'is-road-re-regulated
                                 lrp-pagree lrp-dagree))
(define lrp-bgi (lrp-road-coord! 'imag-part 'imag-part-in-rr 'cc-im-real-mul 'is-road-im-regulated
                                 lrp-pagree lrp-dagree))
(fact 'is-path-of-coords 'lrpc_ 'lrpd_ 'lrpr_ lrp-bgr lrp-bgi)
(mac 'IS-ROAD)
(dk-conj-close! (lambda () (ass)))
(qed 'road-affine-reparam)

;;; the standing hypotheses of every line-integral law: f continuous on u, the
;;; road's trace in u -- `line-int-exists'' hypotheses, verbatim (binder rgy_).
(define lrp-fcont
  "subset(u, cc) implies f in fun(u, cc) implies
   forall([rgy_ in u], is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u),
                                        nf-metric-space(cc-normed-field), f, rgy_)) implies ")

(sp (make-wff (string-append
  "forall([u, f, pgam, dgam, a, b], " lrp-fcont
  "is-road(pgam, dgam, a, b) implies subset(trace(pgam, a, b), u) implies
   forall([lrpc_ in rr, lrpd_ in rr, lrpl_ in rr, lrpm_ in rr],
     0 < lrpl_ implies lrpm_ + lrpl_ * lrpc_ = a implies lrpm_ + lrpl_ * lrpd_ = b implies
     lrpc_ < lrpd_ implies
     forall([lrpr_, lrpk_], lrpr_ in fun(ccint(lrpc_, lrpd_), cc) implies lrpk_ in fun(ccint(lrpc_, lrpd_), cc) implies
       forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpr_(lrpz_) == pgam(lrpm_ + lrpl_ * lrpz_)) implies
       forall([lrpz_ in ccint(lrpc_, lrpd_)], lrpk_(lrpz_) == lrpl_ * dgam(lrpm_ + lrpl_ * lrpz_)) implies
       line-int(f, lrpr_, lrpk_, lrpc_, lrpd_) = line-int(f, pgam, dgam, a, b))))")))
(dk-peel!)
(define lrp-lpagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpr_)))
           "the pointwise value of the reparametrised path"))
(define lrp-ldagree
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpk_)))
           "the pointwise value of the reparametrised derivative"))
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(lrp-hyp-setup!)
(lrp-sets!)
(define lrp-lw
  (let* ((ex (dk-fact! 'line-int-exists 'u 'f 'pgam 'dgam 'a 'b))
         (w1 (dk-skolem! ex))
         (w2 (dk-skolem! (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORSOME)
                                                   (dk-contains? fm w1)))
                                  "the second primitive"))))
    (dk-split-all!)
    (list w1 w2)))
(define lrp-theta '(VNB-LAMBDA pat_ (CCINT a b) (* (f (pgam pat_)) (dgam pat_))))
(define lrp-thr '(VNB-LAMBDA pat_ (CCINT lrpc_ lrpd_) (* (f (lrpr_ pat_)) (lrpk_ pat_))))
(fact 'line-int-integrand-in-fun 'a 'b 'pgam 'dgam 'f 'u)
(dk-split-all! (list (dk-apply! (lrp-h6 'trace-affine-reparam) 'pgam 'lrpr_)))
(fact 'subset-trans '(TRACE lrpr_ lrpc_ lrpd_) '(TRACE pgam a b) 'u)
(fact 'line-int-integrand-in-fun 'lrpc_ 'lrpd_ 'lrpr_ 'lrpk_ 'f 'u)
(fact 'rr-subset-cc 'lrpl_)
(dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-cd)
            (list '== (list lrp-thr 'lrpz_) (list '* 'lrpl_ (list lrp-theta (lrp-map 'lrpz_))))))
  (lambda ()
    (let* ((z  (dk-di-var!))
           (up (lrp-in-ab! z))
           (leaf (proof-state-focus *ps*))
           (aa (list 'f (list 'pgam up)))
           (ww (list 'dgam up))
           (c1 'lrpl_))
      (fact 'fun-apply-type-c 'pgam lrp-ab 'CC up)
      (fact 'trace-value-in 'pgam 'a 'b up)
      (fact 'subset-mem-fwd '(TRACE pgam a b) 'u (list 'pgam up))
      (fact 'fun-apply-type-c 'f 'u 'CC (list 'pgam up))
      (fact 'fun-apply-type-c 'dgam lrp-ab 'CC up)
      (fact 'fun-apply-type-c 'lrpr_ lrp-cd 'CC z)
      (fact 'fun-apply-type-c 'lrpk_ lrp-cd 'CC z)
      (dk-apply! lrp-lpagree z)
      (dk-apply! lrp-ldagree z)
      (dk-lam-b!)
      (subst (list '== (list 'lrpr_ z) (list 'pgam up)))
      (subst (list '== (list 'lrpk_ z) (list '* c1 ww)))
      ;; A * (c * W) = c * (A * W), by two associativities and one commutation
      (lrp-and! (list 'IN aa 'CC) (list 'AND (list 'IN c1 'CC) (list 'IN ww 'CC)))
      (fact 'cc-mul-assoc aa c1 ww)
      (lrp-and! (list 'IN aa 'CC) (list 'IN c1 'CC))
      (fact 'cc-mul-comm aa c1)
      (lrp-and! (list 'IN c1 'CC) (list 'AND (list 'IN aa 'CC) (list 'IN ww 'CC)))
      (fact 'cc-mul-assoc c1 aa ww)
      (subst (list '= (list '* aa (list '* c1 ww)) (list '* (list '* aa c1) ww)))
      (subst (list '= (list '* aa c1) (list '* c1 aa)))
      (subst (list '= (list '* (list '* c1 aa) ww) (list '* c1 (list '* aa ww))))
      (lrp-open-leaf-close! leaf qrfl))))
(dk-apply! (lrp-h6 'cc-int-affine-subst) lrp-theta lrp-thr (car lrp-lw) (cadr lrp-lw))
(fact 'line-int-unfold 'f 'lrpr_ 'lrpk_ 'lrpc_ 'lrpd_)
(fact 'line-int-unfold 'f 'pgam 'dgam 'a 'b)
(subst (list '== '(LINE-INT f lrpr_ lrpk_ lrpc_ lrpd_) (list 'CC-INT lrp-thr 'lrpc_ 'lrpd_)))
(subst (list '== '(LINE-INT f pgam dgam a b) (list 'CC-INT lrp-theta 'a 'b)))
(ass)
(qed 'line-int-affine-reparam)

;;; =====================================================================
;;; THE TRACE OF A RESTRICTED PATH lies in the trace of the path.
;;; =====================================================================

(sp (make-wff "forall([pgam, a, b, lrpc_ in rr, lrpd_ in rr],
   pgam in fun(ccint(a, b), cc) implies a in rr implies b in rr implies
   a <= lrpc_ implies lrpd_ <= b implies
   subset(trace(restrict(pgam, ccint(lrpc_, lrpd_)), lrpc_, lrpd_), trace(pgam, a, b)))"))
(dk-peel!)
(let ((rg (list 'RESTRICT 'pgam lrp-cd)))
  (fact 'trace-unfold rg 'lrpc_ 'lrpd_)
  (fact 'ccint-subset-ccint 'a 'b 'lrpc_ 'lrpd_)
  (let ((w (subset-by-element!)))
    (dk-have! (list 'IN w (list 'IMAGE rg lrp-cd))
      (lambda () (subst (list '== (list 'IMAGE rg lrp-cd) (list 'TRACE rg 'lrpc_ 'lrpd_))) (ass)))
    (dk-image-hyp! (list 'IN w (list 'IMAGE rg lrp-cd)))
    (let ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
      (dk-split-all!)
      (fact 'subset-mem-fwd lrp-cd lrp-ab z)
      (fact 'restrict-apply 'pgam lrp-cd z)
      (fact 'trace-value-in 'pgam 'a 'b z)
      (subst (list '= w (list rg z)))
      (subst (list '== (list rg z) (list 'pgam z)))
      (ass))))
(qed 'trace-restrict-subset)

;;; =====================================================================
;;; (4) LEMMA 3.4 FOR A SEGMENT.  SEG(z0, w) is the road s |-> z0 + s*w,
;;; s |-> w on [0,1] of `segment-is-road'.  For 0 < t < 1,
;;;
;;;   int_{SEG(z0,w)} f = int_{SEG(z0, t w)} f + int_{SEG(z0 + t w, (1-t) w)} f.
;;;
;;; `line-int-adjacent' splits the road at t; each restriction, reparametrised
;;; onto [0,1] by (3) -- s |-> t*s on the first piece, s |-> t + (1-t)*s on the
;;; second -- IS the smaller segment, pointwise.
;;; =====================================================================

(define lrp-seg '(VNB-LAMBDA psx_ (CCINT 0 1) (+ pz0_ (* psx_ pzw_))))
(define lrp-dseg '(VNB-LAMBDA psx_ (CCINT 0 1) pzw_))
(define lrp-01 '(CCINT 0 1))

;;; the segment SEG(Z0, W) and its derivative are functions on [0,1]; its road.
(define (lrp-seg-road! z0 w)
  (let ((r (dk-cite! 'segment-is-road z0 w)))
    (fact 'is-road-is-path (list-ref r 1) (list-ref r 2) 0 1)
    (fact 'is-path-in-fun (list-ref r 1) 0 1)
    (fact 'is-road-dgam-in-fun (list-ref r 1) (list-ref r 2) 0 1)
    r))

;;; one piece [LO, HI] of [0,1], reparametrised by s |-> MU + LAM*s onto it,
;;; against the smaller segment (SG, DSG) given literally.  Returns the landed
;;; equation LINE-INT(f, SG, DSG, 0, 1) = LINE-INT(f, restrict..., LO, HI).
(define (lrp-piece! lo hi lam mu sg dsg)
  (let* ((ek  (list 'CCINT lo hi))
         (rs  (list 'RESTRICT lrp-seg ek))
         (rds (list 'RESTRICT lrp-dseg ek))
         (mp  (lambda (z) (list '+ mu (list '* lam z)))))
    (lrp-rr! lam) (lrp-rr! mu)
    (for-each (lambda (eq) (dk-have! eq (lambda () (crs))))
              (list (list '= (mp 0) lo) (list '= (mp 1) hi)))
    (fact 'road-restrict lrp-seg lrp-dseg 0 1 lo hi)
    (fact 'trace-restrict-subset lrp-seg 0 1 lo hi)
    (fact 'subset-trans (list 'TRACE rs lo hi) (list 'TRACE lrp-seg 0 1) 'u)
    (fact 'ccint-subset-ccint 0 1 lo hi)
    (let ((inab (dk-cite! 'affine-reparam-ccint-in lo hi 0 1 lam mu)))
      (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-01)
                  (list '== (list sg 'lrpz_) (list rs (mp 'lrpz_)))))
        (lambda ()
          (let* ((z (dk-di-var!)) (v (mp z)) (leaf (proof-state-focus *ps*)))
            (fact 'ccint-elt-in-rr 0 1 z)
            (dk-apply! inab z)
            (fact 'subset-mem-fwd ek lrp-01 v)
            (fact 'ccint-elt-in-rr lo hi v)
            (fact 'restrict-apply lrp-seg ek v)
            (subst (list '== (list rs v) (list lrp-seg v)))
            (dk-lam-b!)
            (if (not (sequent-node-grounded? leaf))
                (let ((g (dk-goal)))
                  (dk-have! (list '= (cadr g) (caddr g)) (lambda () (crs)))
                  (subst (list '= (cadr g) (caddr g)))
                  (lrp-open-leaf-close! leaf qrfl))))))
      (dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-01)
                  (list '== (list dsg 'lrpz_) (list '* lam (list rds (mp 'lrpz_))))))
        (lambda ()
          (let* ((z (dk-di-var!)) (v (mp z)) (leaf (proof-state-focus *ps*)))
            (fact 'ccint-elt-in-rr 0 1 z)
            (dk-apply! inab z)
            (fact 'subset-mem-fwd ek lrp-01 v)
            (fact 'restrict-apply lrp-dseg ek v)
            (subst (list '== (list rds v) (list lrp-dseg v)))
            (dk-lam-b!)
            (lrp-open-leaf-close! leaf qrfl)))))
    (dk-apply! (dk-cite! 'line-int-affine-reparam 'u 'f rs rds lo hi) 0 1 lam mu sg dsg)))

(sp (make-wff (string-append
  "forall([u, f], " lrp-fcont
  "forall([pz0_ in cc, pzw_ in cc, lrpt_ in ooint(0, 1)],
     subset(trace(vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_), 0, 1), u) implies
     line-int(f, vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_), vnb-lambda(psx_, ccint(0, 1), pzw_), 0, 1) =
       line-int(f, vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * (lrpt_ * pzw_)),
                   vnb-lambda(psx_, ccint(0, 1), lrpt_ * pzw_), 0, 1) +
       line-int(f, vnb-lambda(psx_, ccint(0, 1), (pz0_ + lrpt_ * pzw_) + psx_ * ((1 - lrpt_) * pzw_)),
                   vnb-lambda(psx_, ccint(0, 1), (1 - lrpt_) * pzw_), 0, 1)))")))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'ooint-membership '(IN lrpt_ (OOINT 0 1))))))
(dk-have! '(IN lrpt_ (OOINT 0 1))
  (lambda () (mac 'ooint-membership) (dk-conj-close! (lambda () (ass)))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(fact 'rr-leq-reflexive 0)
(fact 'rr-leq-reflexive 1)
(fact 'rr-lt-implies-le 0 'lrpt_)
(fact 'rr-lt-implies-le 'lrpt_ 1)
(fact 'rr-is-set)
(fact 'rr-subset-cc 'lrpt_)
(lrp-rr! '(- 1 lrpt_))
(fact 'rr-subset-cc '(- 1 lrpt_))
(dk-have! '(< 0 (- 1 lrpt_)) (lambda () (dk-ineq! '(IN lrpt_ RR) '(< lrpt_ 1))))
(lrp-seg-road! 'pz0_ 'pzw_)
(define lrp-s-goal (dk-goal))
(define lrp-s-p1 (cadr (caddr lrp-s-goal)))
(define lrp-s-p2 (caddr (caddr lrp-s-goal)))
(lrp-and! '(IN lrpt_ CC) '(IN pzw_ CC))
(fact 'cc-mul-closed 'lrpt_ 'pzw_)
(lrp-and! '(IN (- 1 lrpt_) CC) '(IN pzw_ CC))
(fact 'cc-mul-closed '(- 1 lrpt_) 'pzw_)
(lrp-and! '(IN pz0_ CC) '(IN (* lrpt_ pzw_) CC))
(fact 'cc-add-closed 'pz0_ '(* lrpt_ pzw_))
(lrp-seg-road! 'pz0_ '(* lrpt_ pzw_))
(lrp-seg-road! '(+ pz0_ (* lrpt_ pzw_)) '(* (- 1 lrpt_) pzw_))
(define lrp-s-adj (dk-apply! (dk-cite! 'line-int-adjacent 'u 'f lrp-seg lrp-dseg 0 1) 'lrpt_))
(define lrp-s-e1 (lrp-piece! 0 'lrpt_ 'lrpt_ 0 (list-ref lrp-s-p1 2) (list-ref lrp-s-p1 3)))
(define lrp-s-e2 (lrp-piece! 'lrpt_ 1 '(- 1 lrpt_) 'lrpt_ (list-ref lrp-s-p2 2) (list-ref lrp-s-p2 3)))
(subst (list '= (cadr lrp-s-e1) (caddr lrp-s-e1)))
(subst (list '= (cadr lrp-s-e2) (caddr lrp-s-e2)))
(ass)
(qed 'segment-int-split)

;;; =====================================================================
;;; (5) THE NOTES' (54) FOR A SEGMENT:
;;;     |f| <= M on the trace  =>  |int_{SEG(z0,w)} f| <= |w| * M.
;;; `line-int-abs-bound' bounds the integral by PW-INT of t |-> |f(z0 + t w)| |w|;
;;; that function has a primitive (it is regulated: `road-integrand-regulated',
;;; `regulated-on-magnitude'), it is <= the constant |w| M pointwise, and the
;;; constant integrates to |w| M (`pw-affine-antiderivative', `pw-int-monotone',
;;; `pw-int-const').  No LENGTH is needed.
;;; =====================================================================

(define (lrp-segv z) (list '+ 'pz0_ (list '* z 'pzw_)))
(define lrp-tr (list 'TRACE lrp-seg 0 1))

;;; a point Z of [0,1]: z0 + z w typed in CC, in the trace, in u, and f of it
;;; typed with its magnitude.
(define (lrp-seg-pt! z)
  (let ((sv (lrp-segv z)))
    (fact 'ccint-elt-in-rr 0 1 z)
    (fact 'rr-subset-cc z)
    (lrp-and! (list 'IN z 'CC) '(IN pzw_ CC))
    (fact 'cc-mul-closed z 'pzw_)
    (lrp-and! '(IN pz0_ CC) (list 'IN (list '* z 'pzw_) 'CC))
    (fact 'cc-add-closed 'pz0_ (list '* z 'pzw_))
    (fact 'trace-value-in lrp-seg 0 1 z)
    (dk-have! (list '= (list lrp-seg z) sv)
      (lambda ()
        (let ((leaf (proof-state-focus *ps*)))
          (dk-lam-b!)
          (lrp-open-leaf-close! leaf rfl))))
    (dk-have! (list 'IN sv lrp-tr)
      (lambda () (subst (list '= sv (list lrp-seg z))) (ass)))
    (fact 'subset-mem-fwd lrp-tr 'u sv)
    (fact 'fun-apply-type-c 'f 'u 'CC sv)
    (fact 'cc-magnitude-closed (list 'f sv))
    sv))

(sp (make-wff (string-append
  "forall([u, f], " lrp-fcont
  "forall([pz0_ in cc, pzw_ in cc],
     subset(trace(vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_), 0, 1), u) implies
     forall([lrpn_ in rr],
       forall([lrpy_ in trace(vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_), 0, 1)],
         magnitude(f(lrpy_)) <= lrpn_) implies
       magnitude(line-int(f, vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_),
                             vnb-lambda(psx_, ccint(0, 1), pzw_), 0, 1)) <= magnitude(pzw_) * lrpn_)))")))
(dk-peel!)
(define lrp-b-bound
  (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'FORALL) (dk-contains? fm 'lrpn_)))
           "the bound on the trace"))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 0 1)
(fact 'subclass-of-set-is-set lrp-01 'RR)
(lrp-seg-road! 'pz0_ 'pzw_)
(fact 'cc-magnitude-closed 'pzw_)
(fact 'cc-magnitude-nonneg 'pzw_)
(define lrp-km '(* (magnitude pzw_) lrpn_))
(lrp-rr! lrp-km)
(define lrp-ab-lam
  (list 'VNB-LAMBDA 'lrpv_ lrp-01 (list '* (list 'magnitude (list 'f (lrp-segv 'lrpv_))) '(magnitude pzw_))))
(define lrp-k-lam (list 'VNB-LAMBDA 'lrpv_ lrp-01 lrp-km))
(define lrp-kp-lam (list 'VNB-LAMBDA 'lrpv_ lrp-01 (list '+ 0 (list '* lrp-km 'lrpv_))))
(dk-have! (list 'IN lrp-ab-lam (list 'FUN lrp-01 'RR))
  (lambda ()
    (dk-lam-type!
     (lambda ()
       (let* ((z (dk-di-var!)) (sv (lrp-seg-pt! z)))
         (lrp-rr! (list '* (list 'magnitude (list 'f sv)) '(magnitude pzw_)))
         (ass))))))
(dk-have! (list 'IN lrp-k-lam (list 'FUN lrp-01 'RR))
  (lambda () (dk-lam-type! (lambda () (dk-di-var!) (ass)))))
(dk-have! (list 'IN lrp-kp-lam (list 'FUN lrp-01 'RR))
  (lambda ()
    (dk-lam-type!
     (lambda ()
       (let ((z (dk-di-var!)))
         (fact 'ccint-elt-in-rr 0 1 z)
         (lrp-rr! (list '+ 0 (list '* lrp-km z)))
         (ass))))))
;; the bound (54) along the road
(define lrp-b-e1
  (dk-chain! (inst*! (dk-cite! 'line-int-abs-bound 'u 'f lrp-seg lrp-dseg 0 1) lrp-ab-lam)
    (lambda (ante)
      (lambda ()
        (let ((z (dk-di-var!)))
          (lrp-seg-pt! z)
          (dk-lam-b!)
          (dk-lane-if! qrfl))))))
;; the bounding function has a primitive: it is regulated
(dk-split-all! (list (dk-cite! 'road-integrand-regulated 'u 'f lrp-seg lrp-dseg 0 1)))
(define (lrp-b-reg proj)
  (cadr (dk-pick (lambda (fm) (and (eq? (lrp-head fm) 'IS-REGULATED-ON)
                                   (dk-contains? fm proj) (dk-contains? fm lrp-seg)))
                 "a regulated coordinate of the integrand")))
(dk-chain! (dk-cite! 'regulated-on-magnitude (lrp-b-reg 'real-part) (lrp-b-reg 'imag-part)
                     lrp-ab-lam 0 1)
  (lambda (ante)
    (lambda ()
      (let* ((z  (dk-di-var!))
             (sv (lrp-seg-pt! z))
             (fy (list 'f sv))
             (q  (list '* fy 'pzw_))
             (rq (list 'real-part q))
             (iq (list 'imag-part q)))
        (lrp-and! (list 'IN fy 'CC) '(IN pzw_ CC))
        (fact 'cc-mul-closed fy 'pzw_)
        (fact 'real-part-in-rr q)
        (fact 'imag-part-in-rr q)
        (dk-lam-b!)
        (fact 'cc-re-im-decompose q)
        (fact 'rr-subset-cc iq)
        (fact 'cc-i-in)
        (lrp-and! (list 'IN iq 'CC) '(IN +i CC))
        (fact 'cc-mul-comm iq '+i)
        (subst (list '= (list '* iq '+i) (list '* '+i iq)))
        (subst (list '= (list '+ rq (list '* '+i iq)) q))
        (fact 'cc-magnitude-mul fy 'pzw_)
        (subst (list '= (list 'magnitude q) (list '* (list 'magnitude fy) '(magnitude pzw_))))
        (dk-lane-if! qrfl)))))
(define lrp-b-pb (dk-skolem! (dk-fact! 'regulated-on-has-primitive 0 1 lrp-ab-lam)))
;; the constant |w| M and its primitive t |-> 0 + |w| M t
(dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-01)
            (list '== (list lrp-k-lam 'lrpz_) lrp-km)))
  (lambda () (dk-di-var!) (if (not (dk-lam-b!)) (qrfl))))
(dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-01)
            (list '== (list lrp-kp-lam 'lrpz_) (list '+ 0 (list '* lrp-km 'lrpz_)))))
  (lambda () (dk-di-var!) (if (not (dk-lam-b!)) (qrfl))))
(fact 'pw-affine-antiderivative 0 1 0 lrp-km lrp-kp-lam lrp-k-lam)
;; pointwise, |f(z0 + t w)| |w| <= |w| M
(dk-have! (list 'FORALL 'lrpz_ (list 'IMPLIES (list 'IN 'lrpz_ lrp-01)
            (list '<= (list lrp-ab-lam 'lrpz_) (list lrp-k-lam 'lrpz_))))
  (lambda ()
    (let* ((z  (dk-di-var!))
           (sv (lrp-seg-pt! z))
           (mf (list 'magnitude (list 'f sv)))
           (leaf (proof-state-focus *ps*)))
      (dk-apply! lrp-b-bound sv)
      (dk-lam-b!)
      (lrp-and! (list 'IN mf 'RR) (list 'AND '(IN lrpn_ RR) '(IN (magnitude pzw_) RR)))
      (fact 'rr-mul-le-right mf 'lrpn_ '(magnitude pzw_))
      (lrp-rr! (list '* mf '(magnitude pzw_)))
      (lrp-rr! '(* lrpn_ (magnitude pzw_)))
      (have! '(= (* lrpn_ (magnitude pzw_)) (* (magnitude pzw_) lrpn_)) (lambda () (crs)))
      (lrp-open-leaf-close! leaf
        (lambda ()
          (dk-ineq! (list 'IN (list '* mf '(magnitude pzw_)) 'RR) '(IN (* lrpn_ (magnitude pzw_)) RR)
                    (list 'IN lrp-km 'RR)
                    (list '<= (list '* mf '(magnitude pzw_)) '(* lrpn_ (magnitude pzw_)))
                    '(= (* lrpn_ (magnitude pzw_)) (* (magnitude pzw_) lrpn_))))))))
(fact 'pw-int-monotone lrp-b-pb lrp-ab-lam lrp-kp-lam lrp-k-lam 0 1)
(dk-apply! (dk-cite! 'pw-int-const 0 1) lrp-km lrp-k-lam)
(fact 'pw-int-in-rr lrp-b-pb lrp-ab-lam 0 1)
(fact 'pw-int-in-rr lrp-kp-lam lrp-k-lam 0 1)
(fact 'line-int-in-cc 'u 'f lrp-seg lrp-dseg 0 1)
(define lrp-b-li (list 'LINE-INT 'f lrp-seg lrp-dseg 0 1))
(fact 'cc-magnitude-closed lrp-b-li)
(have! (list '= (list '* lrp-km '(- 1 0)) lrp-km) (lambda () (crs)))
(dk-ineq! (list 'IN (list 'magnitude lrp-b-li) 'RR)
          (list 'IN (list 'PW-INT lrp-ab-lam 0 1) 'RR)
          (list 'IN (list 'PW-INT lrp-k-lam 0 1) 'RR)
          (list 'IN lrp-km 'RR)
          (list '<= (list 'magnitude lrp-b-li) (list 'PW-INT lrp-ab-lam 0 1))
          (list '<= (list 'PW-INT lrp-ab-lam 0 1) (list 'PW-INT lrp-k-lam 0 1))
          (list '= (list 'PW-INT lrp-k-lam 0 1) (list '* lrp-km '(- 1 0)))
          (list '= (list '* lrp-km '(- 1 0)) lrp-km))
(qed 'segment-int-abs-bound)

;;; =====================================================================
;;; (6) THE REVERSED SEGMENT: int_{SEG(z0 + w, -w)} f = - int_{SEG(z0, w)} f.
;;; SEG(z0 + w, -1*w) is, pointwise, the opposite of SEG(z0, w) on [0,1]
;;; (t |-> z0 + (1 - t) w), with derivative -1 * w; `line-int-opposite-road'.
;;; =====================================================================

(sp (make-wff (string-append
  "forall([u, f], " lrp-fcont
  "forall([pz0_ in cc, pzw_ in cc],
     subset(trace(vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_), 0, 1), u) implies
     line-int(f, vnb-lambda(psx_, ccint(0, 1), (pz0_ + pzw_) + psx_ * (-1 * pzw_)),
                 vnb-lambda(psx_, ccint(0, 1), -1 * pzw_), 0, 1) =
       -1 * line-int(f, vnb-lambda(psx_, ccint(0, 1), pz0_ + psx_ * pzw_),
                        vnb-lambda(psx_, ccint(0, 1), pzw_), 0, 1)))")))
(dk-peel!)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-one-in)
(lrp-rr! '(- 1))
(fact 'rr-subset-cc '(- 1))
(lrp-and! '(IN (- 1) CC) '(IN pzw_ CC))
(fact 'cc-mul-closed '(- 1) 'pzw_)
(lrp-and! '(IN pz0_ CC) '(IN pzw_ CC))
(fact 'cc-add-closed 'pz0_ 'pzw_)
(lrp-seg-road! 'pz0_ 'pzw_)
(define lrp-r-lhs (cadr (dk-goal)))
(define lrp-r-opp (list-ref lrp-r-lhs 2))
(define lrp-r-dopp (list-ref lrp-r-lhs 3))
(lrp-seg-road! '(+ pz0_ pzw_) '(* (- 1) pzw_))
(define (lrp-refl z) (list '- '(+ 0 1) z))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ lrp-01)
            (list '== (list lrp-r-opp 'pay_) (list lrp-seg (lrp-refl 'pay_)))))
  (lambda ()
    (let* ((z (dk-di-var!)) (leaf (proof-state-focus *ps*)))
      (fact 'ccint-elt-in-rr 0 1 z)
      (fact 'ccint-reflect-in 0 1 z)
      (dk-lam-b!)
      (if (not (sequent-node-grounded? leaf))
          (let ((g (dk-goal)))
            (dk-have! (list '= (cadr g) (caddr g)) (lambda () (crs)))
            (subst (list '= (cadr g) (caddr g)))
            (lrp-open-leaf-close! leaf qrfl))))))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ lrp-01)
            (list '== (list lrp-r-dopp 'pay_) (list '* '(- 1) (list lrp-dseg (lrp-refl 'pay_))))))
  (lambda ()
    (let* ((z (dk-di-var!)) (leaf (proof-state-focus *ps*)))
      (fact 'ccint-elt-in-rr 0 1 z)
      (fact 'ccint-reflect-in 0 1 z)
      (dk-lam-b!)
      (lrp-open-leaf-close! leaf qrfl))))
(dk-apply! (dk-cite! 'line-int-opposite-road 'u 'f lrp-seg lrp-dseg 0 1) lrp-r-opp lrp-r-dopp)
(ass)
(qed 'segment-int-reverse)
