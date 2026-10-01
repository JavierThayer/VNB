;;; road-laws-2.scm -- THE OPPOSITE ROAD AND DIEUDONNE (9.6.1).
;;;
;;; THE SOURCE IS DIEUDONNE, Foundations of Modern Analysis, 9.6, verbatim:
;;;
;;;   "The mapping gamma^o of I into C such that gamma^o(t) = gamma(a + b - t)
;;;    is a path which is said to be OPPOSITE to gamma."
;;;   "It is clear that the opposite of a road is a road, and so is the
;;;    juxtaposition of two roads."
;;;   (9.6.1)   int_{gamma^o} f(z) dz  =  - int_{gamma} f(z) dz
;;;
;;; and the notes' complex-analysis.pdf 3.1 for CC-INT (equation (44)).
;;;
;;; WHAT IS PROVED HERE, in order (16 theorems, every one `modulo 0'):
;;;
;;;   (a) `ccint-reflect-in' / `ooint-reflect-in' -- rho(t) = a + b - t maps
;;;       [a,b] into [a,b] and (a,b) into (a,b).
;;;   (b) `reflect-continuous-at-sub' -- THE ONE CONTINUITY ENGINE: if f is
;;;       continuous at a + b - t in the metric SUBSPACE of [a,b], and g agrees
;;;       pointwise with c * (f o rho), then g is continuous at t there.
;;;       `reflect-continuous-on' (the whole interval) and
;;;       `pw-continuous-reflect' (off a finite set) are its two corollaries.
;;;   (b') `regulated-on-reflect' (batch 21) -- c * f(a + b - t) is regulated
;;;       on [a,b] when f is: one-sided limits change sides (Dieudonne VII.6).
;;;   (c) `reflect-image-finite' / `reflect-image-countable' /
;;;       `reflect-not-in-image' -- the reflected exceptional set IMAGE(rho, D)
;;;       is a finite (resp. countable) subset of [a,b] when D is, and t is
;;;       outside it exactly when a + b - t is outside D.
;;;   (d) `pw-antiderivative-reflect' -- F(a + b - t) is a primitive
;;;       (IS-PRIMITIVE, countable exceptional set) of t |-> -1 * phi(a + b - t).
;;;   (e) `pw-int-reflect' -- the integral is UNCHANGED by the reflection of
;;;       the integrand; `cc-int-reflect' -- the same for CC-INT (equation
;;;       (44)), componentwise.
;;;   (f) `trace-opposite-subset' / `trace-opposite' -- the opposite path has
;;;       the SAME trace, which is what types f on it.
;;;   (g) `opposite-is-road' -- Dieudonne's "the opposite of a road is a road".
;;;   (h) `line-int-opposite' -- Dieudonne (9.6.1).
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT CHECKS, against CLAUDE.md's species of false or
;;; underdetermined statement.  Each was made before any proof was written.
;;;
;;; (1) THE REFLECTION STAYS IN THE INTERVAL.  For t in [a,b], a <= t <= b
;;;     gives a <= a + b - t <= b, so a + b - t is in [a,b]; for t in (a,b) the
;;;     two inequalities are strict, so a + b - t is in (a,b).  Both are proved
;;;     first (`ccint-reflect-in', `ooint-reflect-in') and every later statement
;;;     leans on them: without them f(a + b - t) is an APPLICATION OUTSIDE THE
;;;     DOMAIN, which in this system does not denote, and the LUTINS rule would
;;;     refuse to certify it.  Note that a + b - t is defined for every real t;
;;;     what the two lemmas buy is that it is a point of the interval where the
;;;     functions of this file live.
;;;
;;; (2) NO STRICT `=' ON A PW-INT, CC-INT OR LINE-INT TERM WITHOUT THE
;;;     ANTIDERIVATIVES THAT EARN IT.  PW-INT is an IOTA and an IOTA is never
;;;     certified defined, so `pw-int-reflect' concludes its equation only
;;;     under IS-PW-ANTIDERIVATIVE hypotheses (one given, one PROVED here for
;;;     the reflected function), and `cc-int-reflect' and `line-int-opposite'
;;;     carry the two COORDINATE antiderivatives of the integrand, exactly as
;;;     `cc-int-value', `cc-int-sum' and `cc-int-real-mul' do.  The existence
;;;     of those primitives is Dieudonne 8.7.2 (a regulated function has a
;;;     primitive), which this tree does not have yet, so it is a HYPOTHESIS
;;;     and not a lemma -- the house style of every CC-INT law in
;;;     pw-int-laws-2.scm.
;;;
;;; (3) THE REFLECTED EXCEPTIONAL SET IS OF THE SAME KIND.  For
;;;     IS-PW-CONTINUOUS-ON the exceptional set is a finite SET, and the image
;;;     of a finite set under any map is finite (`card-image-finite') and is a
;;;     set (`image-set').  For IS-PRIMITIVE (batch 21, Dieudonne VIII.7) it is
;;;     COUNTABLE, and the image of a countable set under a map TYPED on a
;;;     superset of it is countable (`countable-image').  It is written IMAGE(rho, S) for rho the VNB-LAMBDA
;;;     of the reflection over [a,b]; the membership read-off is
;;;     `image-membership-iff', and the direction that matters -- t is outside
;;;     IMAGE(rho, S) implies a + b - t is outside S -- is proved by its
;;;     contrapositive, rho(a + b - t) = t.
;;;
;;; (4) THE TRACE OF THE OPPOSITE ROAD IS THE TRACE OF THE ROAD.  f is typed on
;;;     the trace of gamma; LINE-INT of f along gamma^o needs f typed on the
;;;     trace of gamma^o.  That is `trace-opposite' (both inclusions), and it
;;;     is not decoration: without it the integrand of the opposite integral is
;;;     not a function and the statement would be about a term that does not
;;;     denote.  The reflection being its own inverse is what makes both
;;;     inclusions the same three lines.
;;;
;;; (5) THE MINUS SIGN IS WRITTEN `-1 * z', NOT `-z'.  The derivative of the
;;;     opposite road is -gamma'(a + b - t), a COMPLEX value, and the tree's
;;;     law for the coordinates of a scalar multiple is `cc-re-real-mul' /
;;;     `cc-im-real-mul' (real-part(c * z) = c * real-part(z), c real).  There
;;;     is no `real-part(-z) = -real-part(z)' in the library, so writing the
;;;     negation as the real multiple by -1 is what lets the coordinates come
;;;     out by citation.  The two readings are the same number.
;;;
;;; (6) `F' AND `f' ARE ONE SYMBOL (both readers fold to lower case).  The
;;;     parameters keep the spellings of path-integral.scm -- `pwf_' the
;;;     primitive, `pphi_' the integrand, `pgam' / `dgam' the road, `pf' the
;;;     integrand of the line integral.  The binders added here are `prc_' (the
;;;     scalar), `prq_' / `prg_' / `prh_' / `prs_' / `prb_' / `prgb_' / `prdb_'
;;;     (the reflected functions), `prt_' (the point), `pry_' (a driver-built
;;;     universal), `prx_' / `prv_' (the binders of the lambdas this file
;;;     BUILDS).  None folds onto a class name (NN ZZ QQ RR CC ORD SET
;;;     EMPTY-SET POS-INF NEG-INF RR-STAR RR-POS-STAR), onto an accessor
;;;     (CARR PTS DIST IDEN ADD MUL NEG ZERO ONE FNRM), or onto `pas_' /
;;;     `pat_' / `pav_' / `paw_' / `pax_', which the bodies of
;;;     IS-PW-ANTIDERIVATIVE, IS-PW-CONTINUOUS-ON, IS-PATH and IS-ROAD bind.
;;;     The coordinate lambdas are spelled with `pat_' ON PURPOSE: that is the
;;;     binder CC-INT's own body builds them with, and a different one would
;;;     not match after `mac'.
;;;
;;; (7) THE ANTECEDENTS ARE CURRIED, and no statement has more than five
;;;     adjacent unguarded binders: with eight of them `fact' MIS-INSTANTIATES
;;;     (batch 16-A).
;;;
;;; ---------------------------------------------------------------------
;;; Helper prefix: pr-.
;;;
;;; Dependencies: structure-library/path-integral.scm;
;;; theorem-library/pw-antiderivative-laws.scm (the read-offs, pw-int-value,
;;; ooint-inner-radius, pw-restrict-continuous-on); pw-int-laws-2.scm
;;; (pw-antiderivative-real-mul, cc-int-value, cc-int-real-mul);
;;; has-deriv-at-chain.scm (has-deriv-at-affine-chain); road-laws.scm
;;; (the IS-ROAD read-offs, is-path-of-coords, pw-continuous-one-piece);
;;; cc-int-laws.scm (trace-unfold, trace-value-in, line-int-integrand-in-fun);
;;; interval-calculus-laws.scm (affine-continuous-at, affine-lam-in-fun);
;;; metric-subspace-laws.scm (restrict-continuous-at, restrict-apply,
;;; restrict-in-fun, subspace-pts, subspace-is-metric-space);
;;; ms-continuity-algebra.scm (ms-compose-continuous-at,
;;; ms-corestrict-continuous, ms-cont-transfer-ptwise-eq);
;;; injection.scm (image-set, image-membership-iff); card-laws.scm
;;; (card-image-finite); cc-coords-laws.scm (cc-re-real-mul, cc-im-real-mul);
;;; regulated-primitive-laws.scm (countable-image, the IS-PRIMITIVE read-offs);
;;; rr-null-scale.scm (rr-scale-eps); rr-abs-basics.scm (rr-abs-mult).

;;; ---- file-local driver helpers ---------------------------------------

(define (pr-head g) (and (pair? g) (car g)))

(define pr-cc '(CCINT a b))
(define pr-sub (list 'SUBSPACE-MS 'RR-MS pr-cc))

;;; the reflection, and its restriction to the interval.  `x' is the binder
;;; `affine-lam-in-fun' and `affine-continuous-at' use; the term below is
;;; literally their instance at c = a + b, lam = -1, so both cite without a
;;; rewrite.
(define pr-aff '(VNB-LAMBDA x RR (+ (+ a b) (* (- 1) x))))
(define pr-raff (list 'RESTRICT pr-aff pr-cc))

;;; t |-> a + b - t as a map of the interval: the term IMAGE is taken of.
(define pr-rho (list 'VNB-LAMBDA 'prx_ pr-cc '(- (+ a b) prx_)))

(define (pr-refl z) (list '- '(+ a b) z))

;;; the coordinate lambda of a function, in the spelling CC-INT's body builds.
(define (pr-proj proj f) (list 'VNB-LAMBDA 'pat_ pr-cc (list proj (list f 'pat_))))

;;; the value of the restricted reflection at a point of the interval:
;;; RESTRICT(aff, [a,b])(z) = a + b - z.  `restrict-apply' takes the RESTRICT
;;; off, `lam-b' the lambda, and one `crs' turns (a+b) + (-1)z into a + b - z.
(define (pr-raff-value! z)
  (dk-have! (list '= (list pr-raff z) (pr-refl z))
    (lambda ()
      (fact 'restrict-apply pr-aff pr-cc z)
      (subst (list '== (list pr-raff z) (list pr-aff z)))
      (dk-lam-b!)
      (crs))))

;;; =====================================================================
;;; (a) THE REFLECTION MAPS THE INTERVAL ONTO ITSELF.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr, pay_ in ccint(a,b)],
   a + b - pay_ in ccint(a,b))"))
(dk-peel!)
(dk-split-all! (list (dk-fact! 'ccint-parts 'a 'b 'pay_)))
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
(fact 'rr-sub-in-rr '(+ a b) 'pay_)
(mac 'ccint-membership)
(dk-conj-close!
 (lambda ()
   (if (dk-ctx-form (dk-goal))
       (ass)
       (dk-ineq! '(IN a RR) '(IN b RR) '(IN pay_ RR) '(<= a pay_) '(<= pay_ b)))))
(qed 'ccint-reflect-in)
(topic! 'ccint-reflect-in 'analysis)
(alias! 'ccint-reflect-in "the reflection a + b - t maps [a,b] into itself")

(sp (make-wff "forall([a in rr, b in rr, pay_ in ooint(a,b)],
   a + b - pay_ in ooint(a,b))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'ooint-membership '(IN pay_ (OOINT a b))))))
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
(fact 'rr-sub-in-rr '(+ a b) 'pay_)
(mac 'ooint-membership)
(dk-conj-close!
 (lambda ()
   (if (dk-ctx-form (dk-goal))
       (ass)
       (dk-ineq! '(IN a RR) '(IN b RR) '(IN pay_ RR) '(< a pay_) '(< pay_ b)))))
(qed 'ooint-reflect-in)
(topic! 'ooint-reflect-in 'analysis)
(alias! 'ooint-reflect-in "the reflection a + b - t maps the open interval into itself")

;;; =====================================================================
;;; (b) THE CONTINUITY ENGINE.
;;;
;;; If f is continuous at a + b - t in the metric subspace of [a,b] and g
;;; agrees pointwise with c * (f o rho), then g is continuous at t there.
;;;
;;; THE ROUTE, and why it is not the EXTEND-CONST route of
;;; `pw-restrict-continuous-on'.  f is continuous only at ONE point and only in
;;; the SUBSPACE sense; there is no total function on the line agreeing with it,
;;; so the reflection has to be composed INSIDE the subspace.  The reflection
;;; is continuous there because it is the restriction of the affine map
;;; t |-> (a+b) + (-1)t (`restrict-continuous-at'), corestricted to the
;;; interval it maps into (`ms-corestrict-continuous'); the composite is
;;; `ms-compose-continuous-at', the scalar is the SAME affine lemma at
;;; c = 0, lam = prc_, and the transfer from the composite lambda to g is
;;; `ms-cont-transfer-ptwise-eq'.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr],
  forall([f, prc_ in rr, prq_ in fun(ccint(a,b), rr)],
    forall([pay_ in ccint(a,b)], prq_(pay_) == prc_ * f(a + b - pay_)) implies
    forall([prt_ in ccint(a,b)],
      is-continuous-at(subspace-ms(rr-ms, ccint(a,b)), rr-ms, f, a + b - prt_)
        implies
      is-continuous-at(subspace-ms(rr-ms, ccint(a,b)), rr-ms, prq_, prt_))))"))
(dk-peel!)
(let* ((pt    (list-ref (dk-goal) 4))
       (u     (pr-refl pt))
       (agree (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                         (dk-contains? fm 'prq_)))
                       "the pointwise agreement"))
       (contf (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IS-CONTINUOUS-AT)
                                         (dk-contains? fm 'f)))
                       "the continuity of f at the reflected point"))
       (l1    (list 'VNB-LAMBDA 'msz_ (list 'PTS pr-sub) (list 'f (list pr-raff 'msz_))))
       (sc    (list 'VNB-LAMBDA 'x 'RR '(+ 0 (* prc_ x))))
       (l2    (list 'VNB-LAMBDA 'msz_ (list 'PTS pr-sub) (list sc (list l1 'msz_)))))
  ;; ---- the two metric spaces and their point sets
  (fact 'rr-is-metric-space)
  (fact 'ccint-subset-rr 'a 'b)
  (dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
  (dk-have! (list 'SUBSET pr-cc '(PTS RR-MS))
    (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
  (fact 'subspace-is-metric-space 'RR-MS pr-cc)
  (fact 'subspace-pts 'RR-MS pr-cc)
  ;; ---- f is a function on the interval (read off the continuity hypothesis)
  (dk-have! (list 'IN 'f (list 'FUN pr-cc 'RR))
    (lambda ()
      (mac-h 'IS-CONTINUOUS-AT contf)
      (dk-split-all!)
      (subst (list '== pr-cc (list 'PTS pr-sub)))
      (subst '(== RR (PTS RR-MS)))
      (ass)))
  ;; ---- the reflection: total, restricted, and its value
  (fact 'rr-one-in)
  (fact 'rr-neg-closed 1)
  (have! '(AND (IN a RR) (IN b RR)))
  (fact 'rr-add-closed 'a 'b)
  (have! '(AND (IN (+ a b) RR) (IN (- 1) RR)))
  (fact 'affine-lam-in-fun '(+ a b) '(- 1))
  (fact 'restrict-in-fun pr-aff 'RR 'RR pr-cc)
  (dk-have! (list 'IN pt (list 'PTS pr-sub))
    (lambda () (subst (list '== (list 'PTS pr-sub) pr-cc)) (ass)))
  (fact 'ccint-elt-in-rr 'a 'b pt)
  (pr-raff-value! pt)
  (fact 'ccint-reflect-in 'a 'b pt)
  (dk-have! (list 'IN (list pr-raff pt) pr-cc)
    (lambda () (subst (list '= (list pr-raff pt) u)) (ass)))
  ;; ---- the reflection is a continuous self-map of the subspace
  (dk-have! (list 'FORALL 'pry_ (list 'IMPLIES (list 'IN 'pry_ (list 'PTS pr-sub))
              (list 'IN (list pr-raff 'pry_) pr-cc)))
    (lambda ()
      (let ((y (dk-di-var!)))
        (dk-have! (list 'IN y pr-cc)
          (lambda () (subst (list '== pr-cc (list 'PTS pr-sub))) (ass)))
        (fact 'ccint-elt-in-rr 'a 'b y)
        (pr-raff-value! y)
        (fact 'ccint-reflect-in 'a 'b y)
        (subst (list '= (list pr-raff y) (pr-refl y)))
        (ass))))
  (have! (list 'AND '(IN (+ a b) RR) (list 'AND '(IN (- 1) RR) (list 'IN pt 'RR))))
  (fact 'affine-continuous-at '(+ a b) '(- 1) pt)
  (fact 'restrict-continuous-at 'RR-MS pr-cc 'RR-MS pr-aff pt)
  (fact 'ms-corestrict-continuous pr-sub 'RR-MS pr-cc pr-raff pt)
  ;; ---- f o rho is continuous at t
  (dk-have! (list 'IS-CONTINUOUS-AT pr-sub 'RR-MS 'f (list pr-raff pt))
    (lambda () (subst (list '= (list pr-raff pt) u)) (ass)))
  (fact 'ms-compose-continuous-at pr-sub pr-sub 'RR-MS pr-raff 'f pt)
  ;; ---- ... and so is c * (f o rho)
  (fact 'fun-apply-type-c 'f pr-cc 'RR (list pr-raff pt))
  (dk-have! (list 'IN (list l1 pt) 'RR) (lambda () (dk-lam-b!) (ass)))
  (fact 'rr-zero-in)
  (have! (list 'AND '(IN 0 RR) (list 'AND '(IN prc_ RR) (list 'IN (list l1 pt) 'RR))))
  (fact 'affine-continuous-at 0 'prc_ (list l1 pt))
  (fact 'ms-compose-continuous-at pr-sub 'RR-MS 'RR-MS l1 sc pt)
  ;; ---- and g is that, pointwise
  (dk-have! (list 'IN 'prq_ (list 'FUN (list 'PTS pr-sub) '(PTS RR-MS)))
    (lambda ()
      (subst (list '== (list 'PTS pr-sub) pr-cc))
      (subst '(== (PTS RR-MS) RR))
      (ass)))
  (dk-have! (list 'FORALL 'pry_ (list 'IMPLIES (list 'IN 'pry_ (list 'PTS pr-sub))
              (list '= (list 'prq_ 'pry_) (list l2 'pry_))))
    (lambda ()
      (let ((y (dk-di-var!)))
        (dk-have! (list 'IN y pr-cc)
          (lambda () (subst (list '== pr-cc (list 'PTS pr-sub))) (ass)))
        (fact 'ccint-elt-in-rr 'a 'b y)
        (pr-raff-value! y)
        (fact 'ccint-reflect-in 'a 'b y)
        (dk-have! (list 'IN (list pr-raff y) pr-cc)
          (lambda () (subst (list '= (list pr-raff y) (pr-refl y))) (ass)))
        (fact 'fun-apply-type-c 'f pr-cc 'RR (list pr-raff y))
        (fact 'fun-apply-type-c 'f pr-cc 'RR (pr-refl y))
        (dk-have! (list 'IN (list l1 y) 'RR) (lambda () (dk-lam-b!) (ass)))
        (dk-apply! agree y)
        (dk-lam-b!)
        (subst (list '= (list pr-raff y) (pr-refl y)))
        (subst (list '== (list 'prq_ y) (list '* 'prc_ (list 'f (pr-refl y)))))
        (crs))))
  (fact 'ms-cont-transfer-ptwise-eq pr-sub 'RR-MS l2 'prq_ pt)
  (ass))
(qed 'reflect-continuous-at-sub)
(topic! 'reflect-continuous-at-sub 'analysis)
(alias! 'reflect-continuous-at-sub
        "a scalar multiple of a continuous function composed with the reflection is continuous")

;;; the whole interval: every point of [a,b] is the reflection of a point of
;;; [a,b], so IS-CONTINUOUS-ON transports.
(sp (make-wff "forall([a in rr, b in rr],
  forall([f, prc_ in rr, prq_ in fun(ccint(a,b), rr)],
    is-continuous-on(f, ccint(a,b)) implies
    forall([pay_ in ccint(a,b)], prq_(pay_) == prc_ * f(a + b - pay_)) implies
    is-continuous-on(prq_, ccint(a,b))))"))
(dk-peel!)
(let ((agree (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                        (dk-contains? fm 'prq_)))
                      "the pointwise agreement"))
      (contf (dk-split-all!
              (dk-landed* (lambda ()
                (mac-h 'IS-CONTINUOUS-ON (list 'IS-CONTINUOUS-ON 'f pr-cc)))))))
  (let ((univ (car (filter (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
                           contf))))
    (mac 'IS-CONTINUOUS-ON)
    (dk-conj-close!
     (lambda ()
       (if (not (eq? (pr-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'ccint-reflect-in 'a 'b z)
             (dk-apply! univ (pr-refl z))
             (fact 'reflect-continuous-at-sub 'a 'b 'f 'prc_ 'prq_ z)
             (ass)))))))
(qed 'reflect-continuous-on)
(topic! 'reflect-continuous-on 'analysis)
(alias! 'reflect-continuous-on
        "a scalar multiple of a continuous function composed with the reflection is continuous on the interval")
;;; =====================================================================
;;; (b') REGULATED FUNCTIONS UNDER THE REFLECTION (batch 21).
;;;
;;; Dieudonne VII.6: "A mapping f of I into F is called a regulated function if
;;; it has one-sided limits at every point of I"; a right limit of f at
;;; a + b - x is a LEFT limit of t |-> f(a + b - t) at x, and vice versa.  (The
;;; same observation is what 8.7.4 calls "follows at once from ... the
;;; definition of a regulated function" for a monotone change of variable.)
;;; The statement carries the real scalar c, as `reflect-continuous-on' does:
;;; the opposite road needs c = -1, and the brief's form is c = 1.
;;;
;;; THE ROUTE, for the right limit of g = c * (f o rho) at x < b: u = a + b - x
;;; has a < u, so f has a left limit l at u; the witness is c * l.  Given eps,
;;; halve it (h + h = eps), take d with |c| * t <= h for 0 <= t <= d
;;; (`rr-scale-eps'), and the delta of f's left limit at d; for t in the
;;; window, s = a + b - t is in f's window, |g(t) - c l| = |c| |f(s) - l|
;;; (`rr-abs-mult') <= h < eps.  The left limit is the mirror.
;;; =====================================================================

;;; the eps-clause of one side.  Goal on entry: the eps-universal of the
;;; goal's one-sided limit of prq_ at X with value c * L0.  CLAUSE is f's
;;; eps-clause at U = a + b - X with value L0; AGREE the pointwise value of prq_.
(define (pr-reg-eps! right? x u l0 clause agree)
  (let* ((pe (dk-peel!))
         (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (h  (dk-halve! e)))
    (fact 'rr-pos-rr-in-rr e)
    (fact 'rr-abs-closed 'prc_)
    (fact 'rr-abs-nonneg 'prc_)
    (let* ((d  (dk-skolem! (dk-fact! 'rr-scale-eps '(ABS prc_) h)))
           (sc (dk-pick (lambda (g) (and (eq? (pr-head g) 'FORALL) (dk-contains? g d)
                                         (dk-contains? g '(ABS prc_))))
                        "the scaling clause")))
      (fact 'rr-pos-rr-in-rr d)
      (let* ((dl (dk-skolem! (dk-apply! clause d)))
             (dc (dk-pick (lambda (g) (and (eq? (pr-head g) 'FORALL) (dk-contains? g dl)))
                          "the delta clause of f")))
        (fact 'rr-pos-rr-in-rr dl)
        (ew dl)
        (dk-conj-close!
         (lambda ()
           (if (eq? (pr-head (dk-goal)) 'POS-RR)
               (ass)
               (let* ((ls (dk-peel!))
                      (t  (cadr (car (filter (lambda (g) (and (eq? (pr-head g) 'IN)
                                                              (equal? (caddr g) pr-cc)))
                                             ls))))
                      (s  (pr-refl t))
                      (fs (list 'f s))
                      (y  (list '- fs l0))
                      (ay (list 'ABS y))
                      (pr (list '* '(ABS prc_) ay))
                      (base (list '(IN a RR) '(IN b RR) (list 'IN x 'RR) (list 'IN t 'RR)
                                  (list 'IN dl 'RR))))
                 (fact 'ccint-elt-in-rr 'a 'b t)
                 (fact 'ccint-reflect-in 'a 'b t)
                 ;; s is in f's window at u
                 (for-each
                  (lambda (ineq-goal)
                    (dk-have! ineq-goal
                      (lambda ()
                        (apply dk-ineq!
                               (append base
                                       (if right?
                                           (list (list '< x t) (list '< t (list '+ x dl)))
                                           (list (list '< (list '- x dl) t) (list '< t x))))))))
                  (if right?
                      (list (list '< (list '- u dl) s) (list '< s u))
                      (list (list '< u s) (list '< s (list '+ u dl)))))
                 (dk-apply! dc s)
                 (fact 'fun-apply-type-c 'f pr-cc 'RR s)
                 (fact 'rr-sub-in-rr fs l0)
                 (fact 'rr-abs-closed y)
                 (fact 'rr-abs-nonneg y)
                 (fact 'rr-lt-implies-le ay d)
                 (dk-apply! sc ay)
                 (have! (list 'AND '(IN (ABS prc_) RR) (list 'IN ay 'RR)))
                 (fact 'rr-mul-closed '(ABS prc_) ay)
                 (dk-have! (list '< pr e)
                   (lambda ()
                     (dk-ineq! (list 'IN pr 'RR) (list 'IN h 'RR) (list 'IN e 'RR)
                               (list '<= pr h) (list '= (list '+ h h) e) (list '< 0 h))))
                 ;; |g(t) - c l0| = |c| |f(s) - l0|
                 (dk-apply! agree t)
                 (subst (list '== (list 'prq_ t) (list '* 'prc_ fs)))
                 (have! (list '= (list '- (list '* 'prc_ fs) (list '* 'prc_ l0))
                              (list '* 'prc_ y))
                        (lambda () (crs)))
                 (subst (list '= (list '- (list '* 'prc_ fs) (list '* 'prc_ l0))
                              (list '* 'prc_ y)))
                 (have! (list 'AND '(IN prc_ RR) (list 'IN y 'RR)))
                 (fact 'rr-abs-mult 'prc_ y)
                 (subst (list '= (list 'ABS (list '* 'prc_ y)) pr))
                 (ass)))))))))

;;; one clause of the goal's IS-REGULATED-ON.  Goal on entry: the right-limit
;;; (RIGHT? #t) or left-limit universal of prq_.  FR / FL: f's two clauses.
(define (pr-reg-side! right? fr fl agree)
  (let* ((x (dk-di-var!))
         (u (pr-refl x)))
    (dk-peel!)
    (fact 'ccint-elt-in-rr 'a 'b x)
    (fact 'ccint-reflect-in 'a 'b x)
    (dk-have! (if right? (list '< 'a u) (list '< u 'b))
      (lambda ()
        (dk-ineq! '(IN a RR) '(IN b RR) (list 'IN x 'RR)
                  (if right? (list '< x 'b) (list '< 'a x)))))
    (let* ((l0 (dk-skolem! (dk-apply! (if right? fl fr) u)))
           (lim (list (if right? 'IS-LEFT-LIMIT-WITHIN 'IS-RIGHT-LIMIT-WITHIN) 'f pr-cc u l0))
           (parts (dk-split-all! (dk-landed* (lambda () (mac-h (car lim) lim)))))
           (clause (car (filter (lambda (g) (and (eq? (pr-head g) 'FORALL)
                                                 (dk-contains? g l0)))
                                parts))))
      (have! (list 'AND '(IN prc_ RR) (list 'IN l0 'RR)))
      (fact 'rr-mul-closed 'prc_ l0)
      (ew (list '* 'prc_ l0))
      (mac (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN))
      (dk-conj-close!
       (lambda ()
         (if (eq? (pr-head (dk-goal)) 'FORALL)
             (pr-reg-eps! right? x u l0 clause agree)
             (ass)))))))

(sp (make-wff "forall([a in rr, b in rr],
  forall([f, prc_ in rr, prq_ in fun(ccint(a,b), rr)],
    is-regulated-on(f, a, b) implies
    forall([pay_ in ccint(a,b)], prq_(pay_) == prc_ * f(a + b - pay_)) implies
    is-regulated-on(prq_, a, b)))"))
(dk-peel!)
(let* ((agree (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                         (dk-contains? fm 'prq_)))
                       "the pointwise agreement"))
       (reg (dk-split-all! (dk-landed* (lambda ()
              (mac-h 'IS-REGULATED-ON '(IS-REGULATED-ON f a b))))))
       (fr (car (filter (lambda (g) (and (eq? (pr-head g) 'FORALL)
                                         (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN)))
                        reg)))
       (fl (car (filter (lambda (g) (and (eq? (pr-head g) 'FORALL)
                                         (dk-contains? g 'IS-LEFT-LIMIT-WITHIN)))
                        reg))))
  (fact 'ccint-subset-rr 'a 'b)
  (have! '(AND (IN a RR) (IN b RR)))
  (fact 'rr-add-closed 'a 'b)
  (mac 'IS-REGULATED-ON)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (if (eq? (pr-head g) 'FORALL)
           (pr-reg-side! (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN) fr fl agree)
           (ass))))))
(qed 'regulated-on-reflect)
(topic! 'regulated-on-reflect 'analysis)
(alias! 'regulated-on-reflect
        "a scalar multiple of a regulated function composed with the reflection is regulated")

;;; =====================================================================
;;; (c) THE REFLECTED EXCEPTIONAL SET.
;;;
;;; IMAGE(rho, D) for rho the reflection: a finite (countable) subset of
;;; [a,b] whenever D is one, and t is outside it exactly when a + b - t is outside D -- the
;;; second by the contrapositive, rho(a + b - t) = t.
;;; =====================================================================

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'prd_
         (list 'IMPLIES '(IN prd_ SET)
         (list 'IMPLIES '(IN (CARD prd_) NN)
         (list 'IMPLIES (list 'SUBSET 'prd_ pr-cc)
           (list 'AND (list 'IN (list 'IMAGE pr-rho 'prd_) 'SET)
             (list 'AND (list 'IN (list 'CARD (list 'IMAGE pr-rho 'prd_)) 'NN)
                        (list 'SUBSET (list 'IMAGE pr-rho 'prd_) pr-cc))))))))))
(dk-peel!)
(fact 'image-set pr-rho 'prd_)
(fact 'card-image-finite pr-rho 'prd_)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (pr-head (dk-goal)) 'SUBSET))
       (ass)
       (let ((w (subset-by-element!)))
         (dk-image-hyp! (list 'IN w (list 'IMAGE pr-rho 'prd_)))
         (let ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
           (dk-split-all!)
           (fact 'subset-mem-fwd 'prd_ pr-cc z)
           (fact 'ccint-elt-in-rr 'a 'b z)
           (fact 'ccint-reflect-in 'a 'b z)
           (dk-have! (list '= (list pr-rho z) (pr-refl z))
             (lambda () (dk-lam-b!) (rfl)))
           (subst (list '= w (list pr-rho z)))
           (subst (list '= (list pr-rho z) (pr-refl z)))
           (ass))))))
(qed 'reflect-image-finite)
(topic! 'reflect-image-finite 'analysis)
(alias! 'reflect-image-finite
        "the reflection of a finite exceptional set is a finite exceptional set")

;;; the COUNTABLE form (batch 21), for IS-PRIMITIVE's exceptional set: the
;;; image of a countable set under the reflection, a map of [a,b] into RR, is
;;; countable (`countable-image'), and it lies in [a,b] as above.
(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'prd_
         (list 'IMPLIES '(IS-COUNTABLE prd_)
         (list 'IMPLIES (list 'SUBSET 'prd_ pr-cc)
           (list 'AND (list 'IS-COUNTABLE (list 'IMAGE pr-rho 'prd_))
                      (list 'SUBSET (list 'IMAGE pr-rho 'prd_) pr-cc))))))))
(dk-peel!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
(dk-have! (list 'IN pr-rho (list 'FUN pr-cc 'RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pr-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'ccint-elt-in-rr 'a 'b z)
             (fact 'rr-sub-in-rr '(+ a b) z)
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(fact 'countable-image 'prd_ pr-rho pr-cc 'RR)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (pr-head (dk-goal)) 'SUBSET))
       (ass)
       (let ((w (subset-by-element!)))
         (dk-image-hyp! (list 'IN w (list 'IMAGE pr-rho 'prd_)))
         (let ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
           (dk-split-all!)
           (fact 'subset-mem-fwd 'prd_ pr-cc z)
           (fact 'ccint-elt-in-rr 'a 'b z)
           (fact 'ccint-reflect-in 'a 'b z)
           (dk-have! (list '= (list pr-rho z) (pr-refl z))
             (lambda () (dk-lam-b!) (rfl)))
           (subst (list '= w (list pr-rho z)))
           (subst (list '= (list pr-rho z) (pr-refl z)))
           (ass))))))
(qed 'reflect-image-countable)
(topic! 'reflect-image-countable 'analysis)
(alias! 'reflect-image-countable
        "the reflection of a countable exceptional set is a countable exceptional set")

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'prd_
         (list 'IMPLIES (list 'SUBSET 'prd_ pr-cc)
           (list 'FORALL 'prt_
             (list 'IMPLIES (list 'IN 'prt_ pr-cc)
               (list 'IMPLIES (list 'NOT (list 'IN 'prt_ (list 'IMAGE pr-rho 'prd_)))
                     (list 'NOT (list 'IN (pr-refl 'prt_) 'prd_))))))))))
(dk-peel!)
(fact 'ccint-elt-in-rr 'a 'b 'prt_)
(fact 'ccint-reflect-in 'a 'b 'prt_)
(let ((imp (list 'IMPLIES (list 'IN (pr-refl 'prt_) 'prd_)
                 (list 'IN 'prt_ (list 'IMAGE pr-rho 'prd_))))
      (neg (list 'NOT (list 'IN 'prt_ (list 'IMAGE pr-rho 'prd_)))))
  (dk-have! imp
    (lambda ()
      (di)
      (dk-image-goal!)
      (ew (pr-refl 'prt_))
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (pr-head (dk-goal)) '=))
             (ass)
             (begin (dk-lam-b!) (crs)))))))
  (dk-only! (dk-ctx-form imp) (dk-ctx-form neg))
  (prop))
(qed 'reflect-not-in-image)
(topic! 'reflect-not-in-image 'analysis)
(alias! 'reflect-not-in-image
        "a point outside the reflected exceptional set reflects to a point outside it")

;;; =====================================================================
;;; (d) THE REFLECTED PRIMITIVE.
;;;
;;;   F' = phi off a countable set  =>  (t |-> F(a + b - t))' = -phi(a + b - t)
;;;
;;; The derivative step is `has-deriv-at-affine-chain' (batch 18-A) at
;;; p = a + b, q = -1; the continuity is `reflect-continuous-on' at c = 1; the
;;; exceptional set is IMAGE(rho, D), countable by `reflect-image-countable'.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr],
  forall([pwf_, pphi_],
    is-primitive(pwf_, pphi_, a, b) implies
    forall([prg_ in fun(ccint(a,b), rr), prk_ in fun(ccint(a,b), rr)],
      forall([pay_ in ccint(a,b)], prg_(pay_) == pwf_(a + b - pay_)) implies
      forall([pay_ in ccint(a,b)], prk_(pay_) == -1 * pphi_(a + b - pay_)) implies
      is-primitive(prg_, prk_, a, b))))"))
(dk-peel!)
(define pr-gagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prg_)))
           "the pointwise value of the reflected primitive"))
(define pr-kagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prk_)))
           "the pointwise value of the reflected integrand"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'ooint-subset-ccint 'a 'b)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-add-closed 'a 'b)
;; the reflected primitive is continuous on [a,b] -- `reflect-continuous-on'
;; at the scalar 1.
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== '(prg_ pay_) (list '* 1 (list 'pwf_ (pr-refl 'pay_))))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (fact 'ccint-reflect-in 'a 'b y)
      (fact 'fun-apply-type-c 'pwf_ pr-cc 'RR (pr-refl y))
      (dk-apply! pr-gagree y)
      (have! (list '= (list '* 1 (list 'pwf_ (pr-refl y))) (list 'pwf_ (pr-refl y)))
             (lambda () (crs)))
      (subst (list '= (list '* 1 (list 'pwf_ (pr-refl y))) (list 'pwf_ (pr-refl y))))
      (ass))))
(fact 'reflect-continuous-on 'a 'b 'pwf_ 1 'prg_)
;; the exceptional set, and the derivative off it
(let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'pwf_ 'pphi_ 'a 'b)))
       (d1 (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)
                                             (dk-contains? fm s1)))
                           "the derivative universal")))
       (img (list 'IMAGE pr-rho s1)))
  (fact 'reflect-image-countable 'a 'b s1)
  (dk-split-all!)
  (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
              (list 'IMPLIES (list 'NOT (list 'IN 'pat_ img))
                    '(HAS-DERIV-AT prg_ pat_ (prk_ pat_)))))
    (lambda ()
      (dk-peel!)
      (let* ((tv (caddr (dk-goal)))
             (u  (pr-refl tv)))
        (fact 'subset-mem-fwd '(OOINT a b) pr-cc tv)
        (fact 'ccint-elt-in-rr 'a 'b tv)
        (fact 'ooint-reflect-in 'a 'b tv)
        (fact 'subset-mem-fwd '(OOINT a b) pr-cc u)
        (fact 'reflect-not-in-image 'a 'b s1 tv)
        (dk-apply! d1 u)
        (fact 'fun-apply-type-c 'pphi_ pr-cc 'RR u)
        (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b tv))))
          (dk-split-all!)
          (fact 'rr-pos-rr-in-rr rv)
          (fact 'rr-sub-in-rr tv rv)
          (fact 'rr-add-in-rr tv rv)
          (let ((oo (list 'OOINT (list '- tv rv) (list '+ tv rv)))
                (pq (lambda (z) (list '+ '(+ a b) (list '* '(- 1) z)))))
            (fact 'restrict-in-fun 'prg_ pr-cc 'RR oo)
            (dk-have! (list 'FORALL 'cry_ (list 'IMPLIES (list 'IN 'cry_ oo)
                        (list '== '(prg_ cry_) (list 'pwf_ (pq 'cry_)))))
              (lambda ()
                (let ((y (dk-di-var!)))
                  (fact 'subset-mem-fwd oo pr-cc y)
                  (fact 'ccint-elt-in-rr 'a 'b y)
                  (dk-apply! pr-gagree y)
                  (have! (list '= (pq y) (pr-refl y)) (lambda () (crs)))
                  (subst (list '= (pq y) (pr-refl y)))
                  (ass))))
            (have! (list '= (pq tv) u) (lambda () (crs)))
            (dk-have! (list 'HAS-DERIV-AT 'pwf_ (pq tv) (list 'pphi_ u))
              (lambda () (subst (list '= (pq tv) u)) (ass)))
            (fact 'has-deriv-at-affine-chain rv 'pwf_ 'prg_ '(+ a b) '(- 1) tv
                  (list 'pphi_ u))
            (dk-apply! pr-kagree tv)
            (have! (list '= (list '* '(- 1) (list 'pphi_ u))
                         (list '* (list 'pphi_ u) '(- 1)))
                   (lambda () (crs)))
            (subst (list '== (list 'prk_ tv) (list '* '(- 1) (list 'pphi_ u))))
            (subst (list '= (list '* '(- 1) (list 'pphi_ u))
                         (list '* (list 'pphi_ u) '(- 1))))
            (ass))))))
  (mac 'IS-PRIMITIVE)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (pr-head (dk-goal)) 'FORSOME))
         (ass)
         (begin (ew img) (dk-conj-close! (lambda () (ass))))))))
(qed 'pw-antiderivative-reflect)
(topic! 'pw-antiderivative-reflect 'analysis)
(alias! 'pw-antiderivative-reflect
        "F(a + b - t) is a primitive of -phi(a + b - t)")

;;; =====================================================================
;;; (e) THE INTEGRAL IS UNCHANGED BY THE REFLECTION OF THE INTEGRAND.
;;;
;;;   PW-INT(t |-> phi(a + b - t), a, b)  =  PW-INT(phi, a, b)
;;;
;;; The reflected primitive of t |-> phi(a + b - t) is -F(a + b - t): by (d),
;;; t |-> F(a + b - t) is a primitive of t |-> -phi(a + b - t), and
;;; `pw-antiderivative-real-mul' at -1 turns both into what is wanted.  The
;;; VALUE is then F(a) - F(b) multiplied by -1, which is F(b) - F(a).
;;; =====================================================================

;;; the two lambdas the proof builds: their binder is `prv_', which no
;;; predicate body and no statement above binds.
(define pr-glam (list 'VNB-LAMBDA 'prv_ pr-cc (list 'pwf_ (pr-refl 'prv_))))
(define pr-klam (list 'VNB-LAMBDA 'prv_ pr-cc
                      (list '* '(- 1) (list 'pphi_ (pr-refl 'prv_)))))

(sp (make-wff "forall([a in rr, b in rr],
  forall([pwf_, pphi_],
    is-primitive(pwf_, pphi_, a, b) implies
    forall([prh_ in fun(ccint(a,b), rr), prs_ in fun(ccint(a,b), rr)],
      forall([pay_ in ccint(a,b)], prh_(pay_) == -1 * pwf_(a + b - pay_)) implies
      forall([pay_ in ccint(a,b)], prs_(pay_) == pphi_(a + b - pay_)) implies
      is-primitive(prh_, prs_, a, b) and
      pw-int(prs_, a, b) = pw-int(pphi_, a, b))))"))
(dk-peel!)
(define pr-hagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prh_)))
           "the pointwise value of the reflected primitive"))
(define pr-sagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prs_)))
           "the pointwise value of the reflected integrand"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
;; the two constructed lambdas are functions on [a,b]
(dk-have! (list 'IN pr-glam (list 'FUN pr-cc 'RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pr-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'ccint-reflect-in 'a 'b z)
             (fact 'fun-apply-type-c 'pwf_ pr-cc 'RR (pr-refl z))
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'IN pr-klam (list 'FUN pr-cc 'RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pr-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'ccint-reflect-in 'a 'b z)
             (fact 'fun-apply-type-c 'pphi_ pr-cc 'RR (pr-refl z))
             (have! (list 'AND '(IN (- 1) RR) (list 'IN (list 'pphi_ (pr-refl z)) 'RR)))
             (fact 'rr-mul-closed '(- 1) (list 'pphi_ (pr-refl z)))
             (ass))))
     (dk-opened (lambda () (lam-t))))))
;; ... with the values (d) asks for
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== (list pr-glam 'pay_) (list 'pwf_ (pr-refl 'pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-reflect-in 'a 'b z)
      (dk-lam-b!)
      (qrfl))))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== (list pr-klam 'pay_)
                  (list '* '(- 1) (list 'pphi_ (pr-refl 'pay_))))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-reflect-in 'a 'b z)
      (dk-lam-b!)
      (qrfl))))
(fact 'pw-antiderivative-reflect 'a 'b 'pwf_ 'pphi_ pr-glam pr-klam)
;; the real multiple by -1 turns (d) into the statement
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== '(prh_ pay_) (list '* '(- 1) (list pr-glam 'pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-reflect-in 'a 'b z)
      (dk-apply! pr-hagree z)
      (dk-lam-b!)
      (ass))))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== '(prs_ pay_) (list '* '(- 1) (list pr-klam 'pay_)))))
  (lambda ()
    (let* ((z (dk-di-var!))
           (x (list 'pphi_ (pr-refl z))))
      (fact 'ccint-reflect-in 'a 'b z)
      (fact 'fun-apply-type-c 'pphi_ pr-cc 'RR (pr-refl z))
      (dk-apply! pr-sagree z)
      (dk-lam-b!)
      (have! (list '= (list '* '(- 1) (list '* '(- 1) x)) x) (lambda () (crs)))
      (subst (list '= (list '* '(- 1) (list '* '(- 1) x)) x))
      (ass))))
(fact 'pw-antiderivative-real-mul 'a 'b pr-glam pr-klam '(- 1) 'prh_ 'prs_)
(dk-split-all!)
;; the VALUE: the endpoints swap, and -1 puts the difference back in order
(fact 'pw-int-value pr-glam pr-klam 'a 'b)
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'b)
(dk-have! (list 'IN 'a pr-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(dk-have! (list 'IN 'b pr-cc)
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(fact 'fun-apply-type-c 'pwf_ pr-cc 'RR 'a)
(fact 'fun-apply-type-c 'pwf_ pr-cc 'RR 'b)
(have! '(= (- (+ a b) b) a) (lambda () (crs)))
(have! '(= (- (+ a b) a) b) (lambda () (crs)))
(dk-have! (list '= (list pr-glam 'b) '(pwf_ a))
  (lambda () (dk-lam-b!) (subst '(= (- (+ a b) b) a)) (rfl)))
(dk-have! (list '= (list pr-glam 'a) '(pwf_ b))
  (lambda () (dk-lam-b!) (subst '(= (- (+ a b) a) b)) (rfl)))
(dk-conj-close!
 (lambda ()
   (if (eq? (pr-head (dk-goal)) 'IS-PRIMITIVE)
       (ass)
       (begin
         (subst (list '= '(PW-INT prs_ a b)
                      (list '* '(- 1) (list 'PW-INT pr-klam 'a 'b))))
         (subst (list '= (list 'PW-INT pr-klam 'a 'b)
                      (list '- (list pr-glam 'b) (list pr-glam 'a))))
         (subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
         (subst (list '= (list pr-glam 'b) '(pwf_ a)))
         (subst (list '= (list pr-glam 'a) '(pwf_ b)))
         (crs)))))
(qed 'pw-int-reflect)
(topic! 'pw-int-reflect 'analysis)
(alias! 'pw-int-reflect
        "the piecewise integral is unchanged when the integrand is reflected in the midpoint")

;;; =====================================================================
;;; (f) PIECEWISE CONTINUITY UNDER THE REFLECTION.
;;;
;;; The same shape as (d): the exceptional set is IMAGE(rho, D) and the
;;; continuity at a point off it is `reflect-continuous-at-sub'.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr],
  forall([pphi_, prc_ in rr, prq_ in fun(ccint(a,b), rr)],
    is-pw-continuous-on(pphi_, a, b) implies
    forall([pay_ in ccint(a,b)], prq_(pay_) == prc_ * pphi_(a + b - pay_)) implies
    is-pw-continuous-on(prq_, a, b)))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-PW-CONTINUOUS-ON '(IS-PW-CONTINUOUS-ON pphi_ a b)))))
(fact 'ooint-subset-ccint 'a 'b)
(let* ((s1 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the exceptional set")))
       (c1 (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                      (dk-contains? fm 'IS-CONTINUOUS-AT)
                                      (dk-contains? fm s1)))
                    "the continuity universal"))
       (img (list 'IMAGE pr-rho s1)))
  (dk-split-all!)
  (fact 'reflect-image-finite 'a 'b s1)
  (dk-split-all!)
  (mac 'IS-PW-CONTINUOUS-ON)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (pr-head (dk-goal)) 'FORSOME))
         (ass)
         (begin
           (ew img)
           (dk-conj-close!
            (lambda ()
              (if (not (eq? (pr-head (dk-goal)) 'FORALL))
                  (ass)
                  (begin
                    (dk-peel!)
                    (let* ((tv (list-ref (dk-goal) 4))
                           (u  (pr-refl tv)))
                      (fact 'subset-mem-fwd '(OOINT a b) pr-cc tv)
                      (fact 'ooint-reflect-in 'a 'b tv)
                      (fact 'subset-mem-fwd '(OOINT a b) pr-cc u)
                      (fact 'reflect-not-in-image 'a 'b s1 tv)
                      (dk-apply! c1 u)
                      (fact 'reflect-continuous-at-sub 'a 'b 'pphi_ 'prc_ 'prq_ tv)
                      (ass)))))))))))
(qed 'pw-continuous-reflect)
(topic! 'pw-continuous-reflect 'analysis)
(alias! 'pw-continuous-reflect
        "a scalar multiple of a piecewise continuous function composed with the reflection is piecewise continuous")

;;; =====================================================================
;;; (g) THE TRACE OF THE OPPOSITE PATH.
;;;
;;; Dieudonne's gamma^o runs over the same set of points: the reflection is a
;;; bijection of [a,b] onto itself, and it is its own inverse, so ONE inclusion
;;; lemma gives both.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr],
  forall([pgam, prgb_],
    pgam in fun(ccint(a,b), cc) implies
    prgb_ in fun(ccint(a,b), cc) implies
    forall([pay_ in ccint(a,b)], prgb_(pay_) == pgam(a + b - pay_)) implies
    subset(trace(prgb_, a, b), trace(pgam, a, b))))"))
(dk-peel!)
(let ((agree (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                        (dk-contains? fm 'prgb_)))
                      "the pointwise value of the opposite path")))
  (fact 'trace-unfold 'prgb_ 'a 'b)
  (let ((w (subset-by-element!)))
    (dk-have! (list 'IN w (list 'IMAGE 'prgb_ pr-cc))
      (lambda ()
        (subst (list '== (list 'IMAGE 'prgb_ pr-cc) '(TRACE prgb_ a b)))
        (ass)))
    (dk-image-hyp! (list 'IN w (list 'IMAGE 'prgb_ pr-cc)))
    (let ((z (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image existential"))))
      (dk-split-all!)
      (fact 'ccint-reflect-in 'a 'b z)
      (dk-apply! agree z)
      (fact 'trace-value-in 'pgam 'a 'b (pr-refl z))
      (subst (list '= w (list 'prgb_ z)))
      (subst (list '== (list 'prgb_ z) (list 'pgam (pr-refl z))))
      (ass))))
(qed 'trace-opposite-subset)
(topic! 'trace-opposite-subset 'analysis)
(alias! 'trace-opposite-subset "the trace of the opposite path is inside the trace of the path")

(sp (make-wff "forall([a in rr, b in rr],
  forall([pgam, prgb_],
    pgam in fun(ccint(a,b), cc) implies
    prgb_ in fun(ccint(a,b), cc) implies
    forall([pay_ in ccint(a,b)], prgb_(pay_) == pgam(a + b - pay_)) implies
    subset(trace(prgb_, a, b), trace(pgam, a, b)) and
    subset(trace(pgam, a, b), trace(prgb_, a, b))))"))
(dk-peel!)
(let ((agree (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                        (dk-contains? fm 'prgb_)))
                      "the pointwise value of the opposite path")))
  (fact 'trace-opposite-subset 'a 'b 'pgam 'prgb_)
  ;; the reflection is its own inverse: gamma(t) = gamma^o(a + b - t)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
              (list '== '(pgam pay_) (list 'prgb_ (pr-refl 'pay_)))))
    (lambda ()
      (let* ((z (dk-di-var!))
             (u (pr-refl z)))
        (fact 'ccint-elt-in-rr 'a 'b z)
        (fact 'ccint-reflect-in 'a 'b z)
        (dk-apply! agree u)
        (have! (list '= (pr-refl u) z) (lambda () (crs)))
        (subst (list '== (list 'prgb_ u) (list 'pgam (pr-refl u))))
        (subst (list '= (pr-refl u) z))
        (qrfl))))
  (fact 'trace-opposite-subset 'a 'b 'prgb_ 'pgam)
  (dk-conj-close! (lambda () (ass))))
(qed 'trace-opposite)
(topic! 'trace-opposite 'analysis)
(alias! 'trace-opposite "the opposite path has the same trace as the path")

;;; =====================================================================
;;; (h) THE OPPOSITE OF A ROAD IS A ROAD.
;;;
;;; Dieudonne 9.6: "It is clear that the opposite of a road is a road."  Each
;;; of IS-ROAD's four analytic conjuncts is one citation per COORDINATE:
;;; `pw-antiderivative-reflect' for the two primitives, `regulated-on-reflect'
;;; for the two regulated derivatives (batch 21; read off by
;;; `is-road-re-regulated' / `is-road-im-regulated'), `reflect-continuous-on' plus
;;; `is-path-of-coords' for the path.  The coordinates of -1 * dgamma(a+b-t)
;;; come out by `cc-re-real-mul' / `cc-im-real-mul'.
;;; =====================================================================

(define pr-roadhyp '(IS-ROAD pgam dgam a b))

;;; prove FORM, then hand back the context's own copy of it (dk-have! returns
;;; the node, and a rebuilt formula is not what `inst*!' will match).
(define (pr-univ! form thunk) (dk-have! form thunk) (dk-ctx-form form))

;;; ONE COORDINATE of the opposite road: the typings, the three pointwise
;;; value universals, and the three citations they feed.
(define (pr-road-coord! proj inr mullaw regoff)
  (let ((g  (pr-proj proj 'pgam))
        (d  (pr-proj proj 'dgam))
        (bg (pr-proj proj 'prgb_))
        (bd (pr-proj proj 'prdb_)))
    (fact 'primitive-in-fun g d 'a 'b)
    (fact 'primitive-integrand-in-fun g d 'a 'b)
    (fact 'primitive-continuous g d 'a 'b)
    ;; the coordinate lambdas of the opposite road are functions on [a,b]
    (for-each
     (lambda (pair)
       (dk-have! (list 'IN (car pair) (list 'FUN pr-cc 'RR))
         (lambda ()
           (for-each
            (lambda (leaf)
              (dk-focus! leaf)
              (if (not (eq? (pr-head (dk-goal)) 'FORALL))
                  (ass)
                  (let ((z (dk-di-var!)))
                    (fact 'fun-apply-type-c (cdr pair) pr-cc 'CC z)
                    (fact inr (list (cdr pair) z))
                    (ass))))
            (dk-opened (lambda () (lam-t)))))))
     (list (cons bg 'prgb_) (cons bd 'prdb_)))
    ;; bg(y) == g(a + b - y), and the scaled form `reflect-continuous-on' wants
    (let ((a1 (pr-univ!
               (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                 (list '== (list bg 'pay_) (list g (pr-refl 'pay_)))))
               (lambda ()
                 (let* ((z (dk-di-var!)) (u (pr-refl z)))
                   (fact 'ccint-reflect-in 'a 'b z)
                   (fact 'fun-apply-type-c 'prgb_ pr-cc 'CC z)
                   (fact 'fun-apply-type-c 'pgam pr-cc 'CC u)
                   (dk-apply! pr-bg-agree z)
                   (dk-lam-b!)
                   (subst (list '== (list 'prgb_ z) (list 'pgam u)))
                   (qrfl))))))
      (dk-have!
       (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
         (list '== (list bg 'pay_) (list '* 1 (list g (pr-refl 'pay_))))))
       (lambda ()
         (let* ((z (dk-di-var!)) (u (pr-refl z)))
           (fact 'ccint-reflect-in 'a 'b z)
           (fact 'fun-apply-type-c g pr-cc 'RR u)
           (dk-apply! a1 z)
           (have! (list '= (list '* 1 (list g u)) (list g u)) (lambda () (crs)))
           (subst (list '= (list '* 1 (list g u)) (list g u)))
           (ass)))))
    ;; bd(y) == -1 * d(a + b - y)
    (dk-have!
     (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
       (list '== (list bd 'pay_) (list '* '(- 1) (list d (pr-refl 'pay_))))))
     (lambda ()
       (let* ((z (dk-di-var!)) (u (pr-refl z)))
         (fact 'ccint-reflect-in 'a 'b z)
         (fact 'fun-apply-type-c 'prdb_ pr-cc 'CC z)
         (fact 'fun-apply-type-c 'dgam pr-cc 'CC u)
         (dk-apply! pr-bd-agree z)
         (dk-lam-b!)
         (subst (list '== (list 'prdb_ z) (list '* '(- 1) (list 'dgam u))))
         (fact mullaw '(- 1) (list 'dgam u))
         (subst (list '= (list proj (list '* '(- 1) (list 'dgam u)))
                      (list '* '(- 1) (list proj (list 'dgam u)))))
         (qrfl))))
    ;; the three citations
    (fact 'pw-antiderivative-reflect 'a 'b g d bg bd)
    (fact regoff 'pgam 'dgam 'a 'b)
    (fact 'regulated-on-reflect 'a 'b d '(- 1) bd)
    (fact 'reflect-continuous-on 'a 'b g 1 bg)
    ;; the value equation `is-path-of-coords' asks for
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                (list '= (list proj '(prgb_ pay_)) (list bg 'pay_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'fun-apply-type-c 'prgb_ pr-cc 'CC z)
          (fact inr (list 'prgb_ z))
          (dk-lam-b!)
          (rfl))))))

(sp (make-wff "forall([a in rr, b in rr],
  forall([pgam, dgam, prgb_, prdb_],
    is-road(pgam, dgam, a, b) implies
    prgb_ in fun(ccint(a,b), cc) implies
    prdb_ in fun(ccint(a,b), cc) implies
    forall([pay_ in ccint(a,b)], prgb_(pay_) == pgam(a + b - pay_)) implies
    forall([pay_ in ccint(a,b)], prdb_(pay_) == -1 * dgam(a + b - pay_)) implies
    is-road(prgb_, prdb_, a, b)))"))
(dk-peel!)
(define pr-bg-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prgb_)))
           "the pointwise value of the opposite path"))
(define pr-bd-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prdb_)))
           "the pointwise value of the opposite derivative"))
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(fact 'is-road-re-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-im-antiderivative 'pgam 'dgam 'a 'b)
(pr-road-coord! 'real-part 'real-part-in-rr 'cc-re-real-mul 'is-road-re-regulated)
(pr-road-coord! 'imag-part 'imag-part-in-rr 'cc-im-real-mul 'is-road-im-regulated)
(fact 'is-path-of-coords 'a 'b 'prgb_
      (pr-proj 'real-part 'prgb_) (pr-proj 'imag-part 'prgb_))
(mac 'IS-ROAD)
(dk-conj-close! (lambda () (ass)))
(qed 'opposite-is-road)
(topic! 'opposite-is-road 'analysis)
(alias! 'opposite-is-road
        "Dieudonne 9.6: the opposite of a road is a road")

;;; =====================================================================
;;; (i) CC-INT UNDER THE REFLECTION: equation (44) is componentwise, so this
;;; is `pw-int-reflect' twice.  The two primitives of the coordinates of phi
;;; are hypotheses -- the existence theorem (Dieudonne 8.7.2) is not in the
;;; tree -- exactly as in `cc-int-value' and `cc-int-real-mul'.
;;; =====================================================================

(define (pr-relam f) (pr-proj 'real-part f))
(define (pr-imlam f) (pr-proj 'imag-part f))

;;; the reflected primitive of a coordinate: -F(a + b - t).
(define (pr-hlam prim)
  (list 'VNB-LAMBDA 'prv_ pr-cc (list '* '(- 1) (list prim (pr-refl 'prv_)))))

;;; ONE COORDINATE of a reflected CC-valued integrand: the typings, the two
;;; pointwise values, and `pw-int-reflect'.  PHI is the integrand, RB the
;;; reflected one, PRIM the given primitive of PHI's coordinate.
(define (pr-cc-coord! proj inr phi rb-of prim)
  (let ((r  (pr-proj proj phi))
        (rb (pr-proj proj rb-of))
        (h  (pr-hlam prim)))
    (fact 'primitive-in-fun prim r 'a 'b)
    (dk-have! (list 'IN rb (list 'FUN pr-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (pr-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c rb-of pr-cc 'CC z)
                 (fact inr (list rb-of z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'IN h (list 'FUN pr-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (pr-head (dk-goal)) 'FORALL))
               (ass)
               (let* ((z (dk-di-var!)) (u (pr-refl z)))
                 (fact 'ccint-reflect-in 'a 'b z)
                 (fact 'fun-apply-type-c prim pr-cc 'RR u)
                 (have! (list 'AND '(IN (- 1) RR) (list 'IN (list prim u) 'RR)))
                 (fact 'rr-mul-closed '(- 1) (list prim u))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                (list '== (list h 'pay_)
                      (list '* '(- 1) (list prim (pr-refl 'pay_))))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-reflect-in 'a 'b z)
          (dk-lam-b!)
          (qrfl))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                (list '== (list rb 'pay_) (list r (pr-refl 'pay_)))))
      (lambda ()
        (let* ((z (dk-di-var!)) (u (pr-refl z)))
          (fact 'ccint-reflect-in 'a 'b z)
          (fact 'fun-apply-type-c rb-of pr-cc 'CC z)
          (fact 'fun-apply-type-c phi pr-cc 'CC u)
          (dk-apply! (dk-ctx-form
                      (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                        (list '== (list rb-of 'pay_) (list phi (pr-refl 'pay_))))))
                     z)
          (dk-lam-b!)
          ;; when RB-OF is itself a lambda, `dk-lam-b!' has already contracted
          ;; both sides and there is nothing left to rewrite: substituting then
          ;; would be a no-op, and a no-op step is not recorded.
          (if (dk-contains? (dk-goal) (list rb-of z))
              (subst (list '== (list rb-of z) (list phi u))))
          (qrfl))))
    (fact 'pw-int-reflect 'a 'b prim r h rb)
    (dk-split-all!)
    (fact 'pw-int-in-rr prim r 'a 'b)))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'prb_
         (list 'IMPLIES (list 'IN 'pphi_ (list 'FUN pr-cc 'CC))
         (list 'IMPLIES (list 'IN 'prb_ (list 'FUN pr-cc 'CC))
         (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                          (list '== '(prb_ pay_) (list 'pphi_ (pr-refl 'pay_)))))
           (list 'FORALL 'pwf_ (list 'FORALL 'paw_
             (list 'IMPLIES (list 'IS-PRIMITIVE 'pwf_ (pr-relam 'pphi_) 'a 'b)
             (list 'IMPLIES (list 'IS-PRIMITIVE 'paw_ (pr-imlam 'pphi_) 'a 'b)
               (list '= (list 'CC-INT 'prb_ 'a 'b)
                     (list 'CC-INT 'pphi_ 'a 'b))))))))))))))
(dk-peel!)
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ (pr-relam 'pphi_) 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(pr-cc-coord! 'real-part 'real-part-in-rr 'pphi_ 'prb_ 'pwf_)
(pr-cc-coord! 'imag-part 'imag-part-in-rr 'pphi_ 'prb_ 'paw_)
(mac 'CC-INT)
(subst (list '= (list 'PW-INT (pr-relam 'prb_) 'a 'b)
             (list 'PW-INT (pr-relam 'pphi_) 'a 'b)))
(subst (list '= (list 'PW-INT (pr-imlam 'prb_) 'a 'b)
             (list 'PW-INT (pr-imlam 'pphi_) 'a 'b)))
;; `rfl' is STRICT: the two sides are the same term, but it must be certified
;; DEFINED, and a PW-INT is an IOTA.  Type the whole right-hand side of (44)
;; in CC -- a term typed in context IS certified (the LUTINS rule).
(let ((pi-re (list 'PW-INT (pr-relam 'pphi_) 'a 'b))
      (pi-im (list 'PW-INT (pr-imlam 'pphi_) 'a 'b)))
  (fact 'cc-i-in)
  (fact 'rr-subset-cc pi-re)
  (fact 'rr-subset-cc pi-im)
  (have! (list 'AND (list 'IN pi-im 'CC) '(IN +i CC)))
  (fact 'cc-mul-closed pi-im '+i)
  (have! (list 'AND (list 'IN pi-re 'CC) (list 'IN (list '* pi-im '+i) 'CC)))
  (fact 'cc-add-closed pi-re (list '* pi-im '+i))
  (rfl))
(qed 'cc-int-reflect)
(topic! 'cc-int-reflect 'analysis)
(alias! 'cc-int-reflect
        "the complex integral is unchanged when the integrand is reflected in the midpoint")

;;; =====================================================================
;;; (j) DIEUDONNE (9.6.1).
;;;
;;;     int_{gamma^o} f(z) dz  =  - int_{gamma} f(z) dz
;;;
;;; The integrand of the opposite road at t is
;;;   f(gamma^o(t)) gamma^o'(t)  =  f(gamma(a+b-t)) * (-1 * gamma'(a+b-t)),
;;; which is -1 times the REFLECTION of the integrand of gamma (one
;;; commutation in CC: `cc-mul-assoc' twice and `cc-mul-comm' once).
;;; `cc-int-reflect' removes the reflection and `cc-int-real-mul' takes the -1
;;; outside.  The two primitives of the coordinates of the ORIGINAL integrand
;;; are hypotheses -- Dieudonne gets them from 8.7.2, which this tree does not
;;; have; the primitives of the REFLECTED integrand are then built here.
;;;
;;; A CONSUMER MUST INSTANTIATE IN STAGES: the statement has ten terms
;;; (a, b, gamma, dgamma, f, D, gamma^o, dgamma^o, F, G) and `fact' with eight
;;; or more MIS-INSTANTIATES (batch 16-A); nest `dk-apply!'.
;;; =====================================================================

(define pr-theta '(VNB-LAMBDA pat_ (CCINT a b) (* (pf (pgam pat_)) (dgam pat_))))
(define pr-thetab '(VNB-LAMBDA pat_ (CCINT a b) (* (pf (prgb_ pat_)) (prdb_ pat_))))
(define pr-xi (list 'VNB-LAMBDA 'prv_ pr-cc
                    (list '* (list 'pf (list 'pgam (pr-refl 'prv_)))
                             (list 'dgam (pr-refl 'prv_)))))

;;; the typings of f(gamma(u)) * dgamma(u) at a point u of the interval.
(define (pr-theta-point! u)
  (fact 'fun-apply-type-c 'pgam pr-cc 'CC u)
  (fact 'trace-value-in 'pgam 'a 'b u)
  (fact 'subset-mem-fwd '(TRACE pgam a b) 'pad_ (list 'pgam u))
  (fact 'fun-apply-type-c 'pf 'pad_ 'CC (list 'pgam u))
  (fact 'fun-apply-type-c 'dgam pr-cc 'CC u)
  (have! (list 'AND (list 'IN (list 'pf (list 'pgam u)) 'CC)
               (list 'IN (list 'dgam u) 'CC)))
  (fact 'cc-mul-closed (list 'pf (list 'pgam u)) (list 'dgam u)))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pgam (list 'FORALL 'dgam (list 'FORALL 'pf (list 'FORALL 'pad_
         (list 'IMPLIES '(IS-ROAD pgam dgam a b)
         (list 'IMPLIES '(IN pf (FUN pad_ CC))
         (list 'IMPLIES '(SUBSET (TRACE pgam a b) pad_)
           (list 'FORALL 'prgb_ (list 'FORALL 'prdb_
             (list 'IMPLIES (list 'IN 'prgb_ (list 'FUN pr-cc 'CC))
             (list 'IMPLIES (list 'IN 'prdb_ (list 'FUN pr-cc 'CC))
             (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                              (list '== '(prgb_ pay_) (list 'pgam (pr-refl 'pay_)))))
             (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
                              (list '== '(prdb_ pay_)
                                    (list '* '(- 1) (list 'dgam (pr-refl 'pay_))))))
               (list 'FORALL 'pwf_ (list 'FORALL 'paw_
                 (list 'IMPLIES (list 'IS-PRIMITIVE 'pwf_ (pr-relam pr-theta) 'a 'b)
                 (list 'IMPLIES (list 'IS-PRIMITIVE 'paw_ (pr-imlam pr-theta) 'a 'b)
                   '(= (LINE-INT pf prgb_ prdb_ a b)
                       (* (- 1) (LINE-INT pf pgam dgam a b)))))))))))))))))))))))
(dk-peel!)
(define pr-og-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prgb_)))
           "the pointwise value of the opposite path"))
(define pr-od-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'prdb_)))
           "the pointwise value of the opposite derivative"))
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pr-cc 'RR)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(fact 'rr-subset-cc '(- 1))
;; the three integrands are functions on [a,b] into CC
(fact 'line-int-integrand-in-fun 'a 'b 'pgam 'dgam 'pf 'pad_)
(fact 'trace-opposite-subset 'a 'b 'pgam 'prgb_)
(fact 'subset-trans '(TRACE prgb_ a b) '(TRACE pgam a b) 'pad_)
(fact 'line-int-integrand-in-fun 'a 'b 'prgb_ 'prdb_ 'pf 'pad_)
(dk-have! (list 'IN pr-xi (list 'FUN pr-cc 'CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pr-head (dk-goal)) 'FORALL))
           (ass)
           (let* ((z (dk-di-var!)) (u (pr-refl z)))
             (fact 'ccint-reflect-in 'a 'b z)
             (pr-theta-point! u)
             (ass))))
     (dk-opened (lambda () (lam-t))))))
;; Xi is the REFLECTION of the integrand of gamma ...
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== (list pr-xi 'pay_) (list pr-theta (pr-refl 'pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-reflect-in 'a 'b z)
      (dk-lam-b!)
      (qrfl))))
(fact 'cc-int-reflect 'a 'b pr-theta pr-xi 'pwf_ 'paw_)
;; ... and the integrand of the opposite road is -1 times it
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pr-cc)
            (list '== (list pr-thetab 'pay_) (list '* '(- 1) (list pr-xi 'pay_)))))
  (lambda ()
    (let* ((z  (dk-di-var!))
           (u  (pr-refl z))
           (aa (list 'pf (list 'pgam u)))
           (ww (list 'dgam u))
           (c1 '(- 1)))
      (fact 'ccint-reflect-in 'a 'b z)
      (pr-theta-point! u)
      (fact 'fun-apply-type-c 'prgb_ pr-cc 'CC z)
      (fact 'fun-apply-type-c 'prdb_ pr-cc 'CC z)
      (dk-apply! pr-og-agree z)
      (dk-apply! pr-od-agree z)
      (dk-lam-b!)
      (subst (list '== (list 'prgb_ z) (list 'pgam u)))
      (subst (list '== (list 'prdb_ z) (list '* c1 ww)))
      ;; A * (c * W) = c * (A * W), by two associativities and one commutation
      (have! (list 'AND (list 'IN aa 'CC)
                   (list 'AND (list 'IN c1 'CC) (list 'IN ww 'CC))))
      (fact 'cc-mul-assoc aa c1 ww)
      (have! (list 'AND (list 'IN aa 'CC) (list 'IN c1 'CC)))
      (fact 'cc-mul-comm aa c1)
      (have! (list 'AND (list 'IN c1 'CC)
                   (list 'AND (list 'IN aa 'CC) (list 'IN ww 'CC))))
      (fact 'cc-mul-assoc c1 aa ww)
      (subst (list '= (list '* aa (list '* c1 ww)) (list '* (list '* aa c1) ww)))
      (subst (list '= (list '* aa c1) (list '* c1 aa)))
      (subst (list '= (list '* (list '* c1 aa) ww) (list '* c1 (list '* aa ww))))
      (qrfl))))
;; the primitives of the coordinates of the REFLECTED integrand
(pr-cc-coord! 'real-part 'real-part-in-rr pr-theta pr-xi 'pwf_)
(pr-cc-coord! 'imag-part 'imag-part-in-rr pr-theta pr-xi 'paw_)
(fact 'cc-int-real-mul 'a 'b pr-xi pr-thetab '(- 1)
      (pr-hlam 'pwf_) (pr-hlam 'paw_))
;; the two line integrals, unfolded, and the four substitutions
(fact 'line-int-unfold 'pf 'prgb_ 'prdb_ 'a 'b)
(fact 'line-int-unfold 'pf 'pgam 'dgam 'a 'b)
(fact 'cc-int-in-cc 'a 'b pr-theta 'pwf_ 'paw_)
(have! (list 'AND '(IN (- 1) CC) (list 'IN (list 'CC-INT pr-theta 'a 'b) 'CC)))
(fact 'cc-mul-closed '(- 1) (list 'CC-INT pr-theta 'a 'b))
(subst (list '== '(LINE-INT pf prgb_ prdb_ a b) (list 'CC-INT pr-thetab 'a 'b)))
(subst (list '== '(LINE-INT pf pgam dgam a b) (list 'CC-INT pr-theta 'a 'b)))
(subst (list '= (list 'CC-INT pr-thetab 'a 'b)
             (list '* '(- 1) (list 'CC-INT pr-xi 'a 'b))))
(subst (list '= (list 'CC-INT pr-xi 'a 'b) (list 'CC-INT pr-theta 'a 'b)))
(rfl)
(qed 'line-int-opposite)
(topic! 'line-int-opposite 'analysis)
(alias! 'line-int-opposite
        "Dieudonne (9.6.1): the integral along the opposite road is the negative of the integral")
