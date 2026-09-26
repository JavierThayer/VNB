;;; line-int-fundamental.scm -- THE FUNDAMENTAL THEOREM FOR INTEGRALS ALONG A
;;; ROAD (the user's notes, ~/docs/complex-analysis.pdf, section 3.1,
;;; Proposition 3.2 and equation (50)), and the chain rule it rests on.
;;;
;;; THE SOURCE.  "Proposition 3.2.  If f is holomorphic in the open set U and
;;; gamma is a path in U,  int_gamma f'(z) dz = f(gamma(beta)) - f(gamma(alpha))."
;;; The proof in the notes: int_gamma f' dz = int f'(gamma(t)) gamma'(t) dt =
;;; int [f o gamma]'(t) dt = f(gamma(beta)) - f(gamma(alpha)), "as follows from
;;; the chain rule, the definition of path integral and the Fundamental Theorem
;;; of Calculus".  Dieudonne's road (structure-library/path-integral.scm) is the
;;; library's path; the notes' reduction to a smooth path "by Proposition 3.1"
;;; is not needed, because the exceptional set of a road is finite and the
;;; primitive below is taken off it.
;;;
;;; CONTENTS.
;;;   (1) cc-compose-continuous-at, cc-product-continuous-at: continuity of a
;;;       composite through a map on a subspace of the normed field CC, and of a
;;;       product, for maps of an ARBITRARY metric space into CC-MS.
;;;   (2) lfn-cc-factor-identity: a ring identity with the unit i quantified.
;;;   (3) holomorphic-chain-within: THE MIXED CHAIN RULE in Caratheodory form --
;;;       g a map of a set dm of reals into CC whose two coordinates have a
;;;       Caratheodory package at x on a window w (HAS-DERIV-AT-WITHIN), f
;;;       differentiable over CC at g(x) with derivative l (IS-DIFF-ON): the two
;;;       coordinates of f o g have Caratheodory packages at x on w, with
;;;       derivatives real-part(l * d) and imag-part(l * d), d = the derivative
;;;       of g.  The factor is re/im of  phi(g(y)) * (psi_r(y) + psi_i(y) i),
;;;       phi the factor of f and psi_r, psi_i those of the coordinates: the
;;;       notes' Caratheodory factorisation of f composed with the coordinatewise
;;;       one of g.
;;;   (4) holomorphic-chain: the same for the LOCAL derivative HAS-DERIV-AT, the
;;;       form the notes use ((f o g)'(x) = f'(g(x)) g'(x)); ooint-center-nested.
;;;   (5) line-int-of-derivative: PROPOSITION 3.2.
;;;
;;; WHY NEITHER EXISTING CHAIN RULE SERVES.  `cc-diff-at-chain-real' is a REAL
;;; inner map inside a CC-valued map of a real variable; `diff-on-chain' is the
;;; chain rule over ONE normed field (both maps over CC, or both over RR).  Here
;;; the inner map is a map of a real variable into CC and the outer map is
;;; differentiable over CC: the coordinates MIX (re (f o g)' = re f' re g' -
;;; im f' im g'), which is why the derivative is stated as real-part(l * d).
;;;
;;; WHY df IS A PARAMETER.  The notes write f'; the statement takes any
;;; df in FUN(U, CC) with IS-DIFF-ON(CC-NORMED-FIELD, U, f, z, df(z)) at every z
;;; of U.  LINE-INT needs a FUNCTION as its integrand, and the derivative as an
;;; operator (DERIV-ON, an IOTA) is not a function on U without a VNB-LAMBDA and
;;; the uniqueness theorem around it; the parameter form is what the caller
;;; holds for every concrete f and is exactly as strong (DERIV-ON's lambda is
;;; one instance).  HOLOMORPHIC-ON(U, f) is kept because the notes say it; it
;;; is implied by the derivative hypothesis together with U open.
;;;
;;; THE STATEMENT CHECKS (CLAUDE.md, the species of false or underdetermined
;;; statement), made before the proof was written.
;;;   * The trace lies in U: TRACE(gamma, a, b) subset U is a hypothesis; it is
;;;     what types f(gamma(t)) and df(gamma(t)) (statement check (8) of
;;;     path-integral.scm).
;;;   * No strict `=' on a term that might not denote: LINE-INT is a CC-INT, two
;;;     PW-INT IOTAs; its definedness is EARNED in the proof -- the two
;;;     coordinates of f o gamma are exhibited as piecewise antiderivatives of
;;;     the two coordinates of the integrand, so `pw-int-value' applies.  The
;;;     right side is typed by f in FUN(U, CC) and gamma(a), gamma(b) in U.
;;;   * THE PRIMITIVES ARE NOT HYPOTHESES.  line-int-opposite (road-laws-2.scm)
;;;     and the cc-int value laws carry "the integrand's coordinates have
;;;     piecewise antiderivatives" as hypotheses, because Dieudonne 8.7.2 is not
;;;     proven.  Here F = f o gamma IS the primitive, so nothing of the kind is
;;;     assumed.
;;;   * The exceptional set is the UNION of the road's two (one per coordinate),
;;;     finite by `card-union-nn'.
;;;   * holomorphic-chain(-within) carries the continuity of g at x on the
;;;     subspace dm as a HYPOTHESIS.  It is DERIVABLE (each coordinate has a
;;;     Caratheodory package at x, so is continuous there on the window) and is
;;;     free for a path (IS-PATH); deriving it needs "a Caratheodory package on
;;;     w gives continuity at x on SUBSPACE-MS(RR-MS, w)" and the locality of
;;;     continuity from the window to dm, neither of which is in the tree.
;;;   * No binder folds onto a class name or an accessor; the driver's own
;;;     lambdas use `lfk_' and the universals `lft_', names nothing else binds.
;;;
;;; TRAPS MET (recorded for the next driver).
;;;   * A conjunction whose second conjunct is the goal of the lam-t leaf being
;;;     proved is hash-consed ONTO that leaf, open: `have!' of it cannot close.
;;;   * `dk-only!' run twice on sequents that come out equal (a lane repeated for
;;;     a second coordinate mints the SAME eigenvariable name, `icp_') weakens
;;;     onto a node the first run grounded; the focus drifts to the MAIN leaf and
;;;     the weakening continues there (the known dk-only! defect).  Cure used
;;;     here: ONE lane per point for both coordinates, then read each off.
;;;   * `dk-apply!' of a universal whose instance is already in context errors
;;;     ("landed no assumption"): guard with `dk-ctx-form'.
;;;
;;; LOAD WINDOW.  lo = theorem-library/road-laws (is-road-*, is-path-*); the
;;; other citations -- one-sided-derivative-laws (has-deriv-at-iff-within-ooint,
;;; has-deriv-at-to-within-ooint, deriv-within-*), the diff-on laws, holomorphic-basics (cc-nf-*, nf-cc-agree-*), cc-coords-laws
;;; (cc-continuous-at-iff-coords, cc-re-*, cc-im-*), metric-subspace laws,
;;; pw-antiderivative-laws, cc-int-laws -- all load before it.  hi = none.
;;;
;;; Helper prefix: lfn-.

;;; ---- file-local driver helpers ---------------------------------------

(define lfn-nfc '(NF-METRIC-SPACE CC-NORMED-FIELD))

(define (lfn-head g) (and (pair? g) (car g)))
;;; the base facts about the two spellings of the complex plane.
(define (lfn-cc-setup!)
  (fact 'cc-is-normed-field)
  (fact 'cc-is-metric-space)
  (fact 'nf-cc-is-metric-space)
  (fact 'nf-cc-agree-pts)
  (fact 'nf-cc-agree-dist)
  (fact 'ms-agree-pts-sym 'CC-MS lfn-nfc)
  (fact 'ms-agree-dist-sym 'CC-MS lfn-nfc)
  (fact 'cc-nf-carr)
  (dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl))))

;;; the (trivial) agreement of a space with itself, in the shape
;;; `ms-agree-continuous-at' asks for.
(define (lfn-self-agree! s)
  (dk-have! (list '== (list 'PTS s) (list 'PTS s)) (lambda () (qrfl)))
  (dk-have! (list 'FORALL 'dfu_
              (list 'IMPLIES (list 'IN 'dfu_ (list 'PTS s))
                (list 'FORALL 'dfv_
                  (list 'IMPLIES (list 'IN 'dfv_ (list 'PTS s))
                    (list '== (list (list 'DIST s) 'dfu_ 'dfv_)
                              (list (list 'DIST s) 'dfu_ 'dfv_))))))
    (lambda () (dk-peel!) (qrfl))))

;;; cite, and demand that the deepest landing satisfies PRED.
(define (lfn-cite! pred what . args)
  (let ((r (apply dk-fact! args)))
    (if (not (pred r))
        (error (string-append "lfn-cite!: expected " what ", landed")
               (expression->string r)))
    r))

(define (lfn-cont? s tt f x)
  (lambda (r) (equal? r (list 'IS-CONTINUOUS-AT s tt f x))))

;;; move a continuity statement into CC-MS over to the normed field's metric
;;; space, and back.  lfn-cc-setup! and lfn-self-agree! (of S) first.
(define (lfn-to-nf! s f x)
  (lfn-cite! (lfn-cont? s lfn-nfc f x) "continuity into the normed field"
             'ms-agree-continuous-at s s 'CC-MS lfn-nfc f x))
(define (lfn-to-cc! s f x)
  (lfn-cite! (lfn-cont? s 'CC-MS f x) "continuity into CC-MS"
             'ms-agree-continuous-at s s lfn-nfc 'CC-MS f x))

;;; =====================================================================
;;; (1) TWO CONTINUITY LAWS FOR CC-VALUED MAPS ON AN ARBITRARY METRIC SPACE.
;;; =====================================================================

;;; A map g into CC, continuous at x and landing in u, followed by phi,
;;; continuous at g(x) as a map on the subspace u of the normed field CC.
(sp (make-wff "forall([s, u, g, phi, x],
   is-metric-space(s) implies
   subset(u, cc) implies
   is-continuous-at(s, cc-ms, g, x) implies
   forall([msy_ in pts(s)], g(msy_) in u) implies
   is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u),
                    nf-metric-space(cc-normed-field), phi, g(x)) implies
   is-continuous-at(s, cc-ms, vnb-lambda(msz_, pts(s), phi(g(msz_))), x))"))
(dk-peel!)
(lfn-cc-setup!)
(lfn-self-agree! 's)
(lfn-to-nf! 's 'g 'x)
(dk-have! (list 'SUBSET 'u (list 'PTS lfn-nfc))
  (lambda ()
    (subst (list '== (list 'PTS lfn-nfc) '(PTS CC-MS)))
    (subst '(== (PTS CC-MS) CC))
    (ass)))
(define lfn-subu (list 'SUBSPACE-MS lfn-nfc 'u))
(lfn-cite! (lfn-cont? 's lfn-subu 'g 'x) "the corestriction"
           'ms-corestrict-continuous 's lfn-nfc 'u 'g 'x)
(define lfn-comp '(VNB-LAMBDA msz_ (PTS s) (phi (g msz_))))
(lfn-cite! (lfn-cont? 's lfn-nfc lfn-comp 'x) "the composite"
           'ms-compose-continuous-at 's lfn-subu lfn-nfc 'g 'phi 'x)
(lfn-to-cc! 's lfn-comp 'x)
(ass)
(qed 'cc-compose-continuous-at)
(topic! 'cc-compose-continuous-at 'analysis)
(alias! 'cc-compose-continuous-at "a map into C followed by a map continuous on a subspace of C is continuous")

;;; The product of two maps into CC continuous at x is continuous at x.
(sp (make-wff "forall([s, p, q, x],
   is-continuous-at(s, cc-ms, p, x) implies
   is-continuous-at(s, cc-ms, q, x) implies
   is-continuous-at(s, cc-ms, vnb-lambda(msz_, pts(s), p(msz_) * q(msz_)), x))"))
(dk-peel!)
(lfn-cc-setup!)
(define (lfn-cont-parts! f)
  (let ((hyp (list 'IS-CONTINUOUS-AT 's 'CC-MS f 'x)))
    (dk-project! '(IS-METRIC-SPACE s) 'IS-CONTINUOUS-AT hyp)
    (dk-project! (list 'IN f '(FUN (PTS s) (PTS CC-MS))) 'IS-CONTINUOUS-AT hyp)
    (dk-project! '(IN x (PTS s)) 'IS-CONTINUOUS-AT hyp)))
(lfn-cont-parts! 'p)
(lfn-cont-parts! 'q)
(lfn-self-agree! 's)
(lfn-to-nf! 's 'p 'x)
(lfn-to-nf! 's 'q 'x)
(define lfn-p1 '(VNB-LAMBDA msz_ (PTS s) ((MUL CC-NORMED-FIELD) (p msz_) (q msz_))))
(define lfn-p2 '(VNB-LAMBDA msz_ (PTS s) (* (p msz_) (q msz_))))
(lfn-cite! (lfn-cont? 's lfn-nfc lfn-p1 'x) "the normed-field product"
           'nf-product-continuous-at 'CC-NORMED-FIELD 's 'p 'q 'x)
(fact 'ms-pts-is-set 's)
(dk-have! '(IN p (FUN (PTS s) CC)) (lambda () (subst '(== CC (PTS CC-MS))) (ass)))
(dk-have! '(IN q (FUN (PTS s) CC)) (lambda () (subst '(== CC (PTS CC-MS))) (ass)))
(define (lfn-pq-at! y)
  (fact 'fun-apply-type-c 'p '(PTS s) 'CC y)
  (fact 'fun-apply-type-c 'q '(PTS s) 'CC y)
  (have! (list 'AND (list 'IN (list 'p y) 'CC) (list 'IN (list 'q y) 'CC)))
  (fact 'cc-mul-closed (list 'p y) (list 'q y)))
(dk-have! (list 'IN lfn-p2 (list 'FUN '(PTS s) (list 'PTS lfn-nfc)))
  (lambda ()
    (subst (list '== (list 'PTS lfn-nfc) '(PTS CC-MS)))
    (subst '(== (PTS CC-MS) CC))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
           (ass)
           (let ((y (dk-di-var!))) (lfn-pq-at! y) (ass))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'FORALL 'msz_ (list 'IMPLIES '(IN msz_ (PTS s))
            (list '= (list lfn-p2 'msz_) (list lfn-p1 'msz_))))
  (lambda ()
    (let ((y (dk-di-var!)))
      (lfn-pq-at! y)
      (dk-lam-b!)
      (fact 'cc-nf-mul-apply (list 'p y) (list 'q y))
      (subst (list '== (list '(MUL CC-NORMED-FIELD) (list 'p y) (list 'q y))
                   (list '* (list 'p y) (list 'q y))))
      (rfl))))
(lfn-cite! (lfn-cont? 's lfn-nfc lfn-p2 'x) "the numeric product"
           'ms-cont-transfer-ptwise-eq 's lfn-nfc lfn-p1 lfn-p2 'x)
(lfn-to-cc! 's lfn-p2 'x)
(ass)
(qed 'cc-product-continuous-at)
(topic! 'cc-product-continuous-at 'analysis)
(alias! 'cc-product-continuous-at "the product of two maps into C continuous at a point is continuous there")

;;; =====================================================================
;;; (2) A RING IDENTITY OVER CC WITH THE IMAGINARY UNIT AS A VARIABLE.
;;; `crs' is not handed `+i' itself; the identity is proved with the unit
;;; quantified (pe_) and instantiated at +i where it is used.
;;; =====================================================================
(sp (make-wff "forall([pa_ in cc, pb_ in cc, pc_ in cc, pe_ in cc, ph_ in cc],
   pa_ * (pb_ * ph_ + pe_ * (pc_ * ph_)) = ph_ * (pa_ * (pb_ + pc_ * pe_)))"))
(dk-peel!)
(crs)
(qed 'lfn-cc-factor-identity)
(topic! 'lfn-cc-factor-identity 'analysis)

;;; =====================================================================
;;; (3) THE CHAIN RULE, CARATHEODORY FORM: a holomorphic f after a map g of
;;; a real variable into CC.
;;; =====================================================================

(define lfn-srr '(SUBSPACE-MS RR-MS dm))
(define lfn-srw '(SUBSPACE-MS RR-MS w))
(define (lfn-lam proj f) (list 'VNB-LAMBDA 'pat_ 'dm (list proj f)))

(sp (make-wff "forall([dm, w, g, x, u, f, l, d],
   subset(dm, rr) implies
   subset(w, dm) implies
   g in fun(dm, cc) implies
   is-continuous-at(subspace-ms(rr-ms, dm), cc-ms, g, x) implies
   forall([msy_ in dm], g(msy_) in u) implies
   is-diff-on(cc-normed-field, u, f, g(x), l) implies
   d in cc implies
   has-deriv-at-within(vnb-lambda(pat_, dm, real-part(g(pat_))), w, x, real-part(d)) implies
   has-deriv-at-within(vnb-lambda(pat_, dm, imag-part(g(pat_))), w, x, imag-part(d)) implies
   has-deriv-at-within(vnb-lambda(pat_, dm, real-part(f(g(pat_)))), w, x, real-part(l * d)) and
   has-deriv-at-within(vnb-lambda(pat_, dm, imag-part(f(g(pat_)))), w, x, imag-part(l * d)))"))
(dk-peel!)
(define lfn-gr (lfn-lam 'real-part '(g pat_)))
(define lfn-gi (lfn-lam 'imag-part '(g pat_)))
(define lfn-fr (lfn-lam 'real-part '(f (g pat_))))
(define lfn-fi (lfn-lam 'imag-part '(f (g pat_))))
(define lfn-gu
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'u)
                             (not (dk-contains? fm 'IS-DIFF-ON))))
           "g maps dm into u"))
(define (lfn-in-u! y)
  (if (not (dk-ctx-form (list 'IN (list 'g y) 'u))) (dk-apply! lfn-gu y)))
(lfn-cc-setup!)
(fact 'rr-is-metric-space)
(fact 'rr-is-set)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(fact 'deriv-within-pt-in lfn-gr 'w 'x '(real-part d))
(fact 'subset-mem-fwd 'w 'dm 'x)
(fact 'subset-mem-fwd 'dm 'RR 'x)
(fact 'subset-trans 'w 'dm 'RR)
(dk-have! '(SUBSET dm (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(dk-have! '(SUBSET w (PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(fact 'subspace-is-metric-space 'RR-MS 'dm)
(fact 'subspace-is-metric-space 'RR-MS 'w)
(fact 'subspace-pts 'RR-MS 'dm)
(fact 'subspace-pts 'RR-MS 'w)
(fact 'subclass-of-set-is-set 'dm 'RR)
(fact 'subclass-of-set-is-set 'w 'RR)
(fact 'real-part-in-rr 'd)
(fact 'imag-part-in-rr 'd)
(fact 'cc-i-in)
(fact 'fun-apply-type-c 'g 'dm 'CC 'x)
(lfn-in-u! 'x)

;;; ---- the derivative of f at g(x), opened.
(fact 'diff-on-open 'CC-NORMED-FIELD 'u 'f '(g x) 'l)
(fact 'diff-on-in-fun 'CC-NORMED-FIELD 'u 'f '(g x) 'l)
(fact 'diff-on-deriv-in-carr 'CC-NORMED-FIELD 'u 'f '(g x) 'l)
(dk-have! '(IN f (FUN u CC)) (lambda () (subst '(= CC (CARR CC-NORMED-FIELD))) (ass)))
(dk-have! '(IN l CC) (lambda () (subst '(= CC (CARR CC-NORMED-FIELD))) (ass)))
(dk-project! (list 'SUBSET 'u (list 'PTS lfn-nfc)) 'IS-OPEN
             (list 'IS-OPEN lfn-nfc 'u))
(dk-have! '(SUBSET u CC)
  (lambda ()
    (subst '(= CC (PTS CC-MS)))
    (subst (list '= '(PTS CC-MS) (list 'PTS lfn-nfc)))
    (ass)))
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-DIFF-ON '(IS-DIFF-ON CC-NORMED-FIELD u f (g x) l)))))
(define lfn-phi (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the factor of f")))
(dk-split-all!)
(define lfn-cara-f
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm lfn-phi) (dk-contains? fm 'f)))
           "the Caratheodory equation of f"))
(dk-have! (list 'IN lfn-phi '(FUN u CC))
  (lambda () (subst '(= CC (CARR CC-NORMED-FIELD))) (ass)))

;;; ---- the two coordinate derivatives of g at x, opened.
(define (lfn-open-within! lam dval)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'HAS-DERIV-AT-WITHIN (list 'HAS-DERIV-AT-WITHIN lam 'w 'x dval)))))
  (let ((psi (dk-skolem! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORSOME)
                                                     (dk-contains? fm lam)))
                                  "the factor of a coordinate"))))
    (dk-split-all!)
    psi))
(define lfn-psr (lfn-open-within! lfn-gr '(real-part d)))
(define lfn-psi (lfn-open-within! lfn-gi '(imag-part d)))
(define (lfn-cara-of psi lam)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm psi) (dk-contains? fm lam)))
           "the Caratheodory equation of a coordinate"))
(define lfn-cara-r (lfn-cara-of lfn-psr lfn-gr))
(define lfn-cara-i (lfn-cara-of lfn-psi lfn-gi))


;;; ---- continuity of the factor.  C = phi o g on the subspace dm, then
;;; restricted to w; Psi = psi_r + psi_i * i on w; their product P.
(dk-have! (list 'FORALL 'msy_ (list 'IMPLIES (list 'IN 'msy_ (list 'PTS lfn-srr))
            '(IN (g msy_) u)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (dk-have! (list 'IN y 'dm)
        (lambda () (subst (list '= 'dm (list 'PTS lfn-srr))) (ass)))
      (lfn-in-u! y)
      (ass))))
(define lfn-c-cont
  (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IS-CONTINUOUS-AT)))
             "the continuity of phi o g"
             'cc-compose-continuous-at lfn-srr 'u 'g lfn-phi 'x))
(define lfn-c (list-ref lfn-c-cont 3))
(define lfn-rc-cont
  (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IS-CONTINUOUS-AT)))
             "the restriction of phi o g to w"
             'subspace-restrict-continuous-at 'RR-MS 'dm 'w 'CC-MS lfn-c 'x))
(define lfn-rc (list-ref lfn-rc-cont 3))

(define lfn-psiexp (lambda (v) (list '+ (list lfn-psr v) (list '* (list lfn-psi v) '+i))))
(define lfn-psil (list 'VNB-LAMBDA 'lfk_ 'w (lfn-psiexp 'lfk_)))

;;; a point of w: its typings and those of everything evaluated there.
(define (lfn-and! a b)
  (dk-have! (list 'AND a b) (lambda () (dk-conj-close! (lambda () (ass))))))
(define (lfn-w-point0! y)
  (fact 'subset-mem-fwd 'w 'dm y)
  (fact 'subset-mem-fwd 'dm 'RR y)
  (fact 'fun-apply-type-c 'g 'dm 'CC y)
  (lfn-in-u! y)
  (fact 'fun-apply-type-c 'f 'u 'CC (list 'g y))
  (fact 'fun-apply-type-c lfn-phi 'u 'CC (list 'g y))
  (fact 'fun-apply-type-c lfn-psr 'w 'RR y)
  (fact 'fun-apply-type-c lfn-psi 'w 'RR y)
  (fact 'rr-subset-cc (list lfn-psr y))
  (fact 'rr-subset-cc (list lfn-psi y))
  (lfn-and! (list 'IN (list lfn-psi y) 'CC) '(IN +i CC))
  (fact 'cc-mul-closed (list lfn-psi y) '+i)
  (lfn-and! (list 'IN (list lfn-psr y) 'CC)
               (list 'IN (list '* (list lfn-psi y) '+i) 'CC))
  (fact 'cc-add-closed (list lfn-psr y) (list '* (list lfn-psi y) '+i)))
;;; ... and the factor's value there.  NOT inside the lam-t leaf of Psi's own
;;; typing: that leaf IS (IN Psi(y) CC), and the conjunction below would be
;;; hash-consed onto it, open.
(define (lfn-w-point! y)
  (lfn-w-point0! y)
  (lfn-and! (list 'IN (list lfn-phi (list 'g y)) 'CC)
               (list 'IN (lfn-psiexp y) 'CC))
  (fact 'cc-mul-closed (list lfn-phi (list 'g y)) (lfn-psiexp y))
  (fact 'real-part-in-rr (list '* (list lfn-phi (list 'g y)) (lfn-psiexp y)))
  (fact 'imag-part-in-rr (list '* (list lfn-phi (list 'g y)) (lfn-psiexp y))))

;;; a point of PTS(S_w): the same, after reading it as a point of w.
(define (lfn-pts-point! y)
  (dk-have! (list 'IN y 'w)
    (lambda () (subst (list '= 'w (list 'PTS lfn-srw))) (ass)))
  (lfn-w-point! y))

;;; typing of a lambda over w (or over PTS(S_w)), closing each lam-t leaf.
(define (lfn-lam-type! claim point!)
  (dk-have! claim
    (lambda ()
      (if (dk-contains? (dk-goal) (list 'PTS lfn-srw))
          (subst (list '== (list 'PTS lfn-srw) 'w)))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
             (ass)
             (let ((y (dk-di-var!))) (point! y) (lfn-lam-b-if!) (ass))))
       (dk-opened (lambda () (lam-t)))))))
(define (lfn-lam-b-if!) (if (dk--redex? (dk-goal)) (dk-lam-b!)))

(lfn-lam-type! (list 'IN lfn-psil '(FUN w CC)) lfn-w-point0!)
(dk-have! (list 'IN lfn-psil (list 'FUN (list 'PTS lfn-srw) 'CC))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))
(dk-have! (list 'IN lfn-psr (list 'FUN (list 'PTS lfn-srw) 'RR))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))
(dk-have! (list 'IN lfn-psi (list 'FUN (list 'PTS lfn-srw) 'RR))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))
(dk-have! (list 'IN 'x (list 'PTS lfn-srw))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))

;;; re / im of Psi(y) are psi_r(y) / psi_i(y).
(define (lfn-psi-coord! proj)
  (dk-have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'PTS lfn-srw))
              (list '= (list proj (list lfn-psil 'u_))
                    (list (if (eq? proj 'real-part) lfn-psr lfn-psi) 'u_))))
    (lambda ()
      (let ((y (dk-di-var!)))
        (lfn-pts-point! y)
        (dk-lam-b!)
        (let ((ro (dk-fact! 'cc-re-im-of (lfn-psiexp y) (list lfn-psr y) (list lfn-psi y))))
          (if (and (pair? ro) (eq? (car ro) 'IMPLIES))
              (detach-with! ro (lambda () (rfl)))))
        (dk-split-all!)
        (ass)))))
(lfn-psi-coord! 'real-part)
(lfn-psi-coord! 'imag-part)
(define lfn-psi-iff
  (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IFF))) "the coordinate iff for Psi"
             'cc-continuous-at-iff-coords lfn-srw lfn-psil lfn-psr lfn-psi 'x))
(define lfn-psi-cont (list 'IS-CONTINUOUS-AT lfn-srw 'CC-MS lfn-psil 'x))
(have! (list 'AND (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-psr 'x)
             (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-psi 'x)))
(dk-have! lfn-psi-cont
  (lambda ()
    (dk-only! lfn-psi-iff
              (list 'AND (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-psr 'x)
                    (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-psi 'x)))
    (prop)))
(define lfn-p-cont
  (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IS-CONTINUOUS-AT)))
             "the continuity of the product"
             'cc-product-continuous-at lfn-srw lfn-rc lfn-psil 'x))
(define lfn-p (list-ref lfn-p-cont 3))

;;; P(y) = phi(g(y)) * Psi(y) on w: reduce a goal that mentions P(y).
(define (lfn-p-beta! y)
  (dk-have! (list 'IN y (list 'PTS lfn-srr))
    (lambda () (subst (list '== (list 'PTS lfn-srr) 'dm)) (ass)))
  (if (dk--redex? (dk-goal)) (dk-lam-b!))
  (let ((ra (dk-fact! 'restrict-apply lfn-c 'w y)))
    (subst ra))
  (if (dk--redex? (dk-goal)) (dk-lam-b!)))

(define lfn-kexp (lambda (v) (list '* (list lfn-phi (list 'g v)) (lfn-psiexp v))))
(define lfn-chr (list 'VNB-LAMBDA 'lfk_ 'w (list 'real-part (lfn-kexp 'lfk_))))
(define lfn-chi (list 'VNB-LAMBDA 'lfk_ 'w (list 'imag-part (lfn-kexp 'lfk_))))

(dk-have! (list 'IN lfn-p (list 'FUN (list 'PTS lfn-srw) 'CC))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
           (begin (subst (list '== (list 'PTS lfn-srw) 'w)) (ass))
           (let ((y (dk-di-var!)))
             (lfn-pts-point! y)
             (lfn-p-beta! y)
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(lfn-lam-type! (list 'IN lfn-chr '(FUN w RR)) lfn-w-point!)
(lfn-lam-type! (list 'IN lfn-chi '(FUN w RR)) lfn-w-point!)
(dk-have! (list 'IN lfn-chr (list 'FUN (list 'PTS lfn-srw) 'RR))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))
(dk-have! (list 'IN lfn-chi (list 'FUN (list 'PTS lfn-srw) 'RR))
  (lambda () (subst (list '== (list 'PTS lfn-srw) 'w)) (ass)))
(define (lfn-p-coord! proj chi)
  (dk-have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'PTS lfn-srw))
              (list '= (list proj (list lfn-p 'u_)) (list chi 'u_))))
    (lambda ()
      (let ((y (dk-di-var!)))
        (lfn-pts-point! y)
        (lfn-p-beta! y)
        (rfl)))))
(lfn-p-coord! 'real-part lfn-chr)
(lfn-p-coord! 'imag-part lfn-chi)
(define lfn-p-iff
  (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IFF))) "the coordinate iff for P"
             'cc-continuous-at-iff-coords lfn-srw lfn-p lfn-chr lfn-chi 'x))
(define lfn-chr-cont (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-chr 'x))
(define lfn-chi-cont (list 'IS-CONTINUOUS-AT lfn-srw 'RR-MS lfn-chi 'x))
(dk-have! (list 'AND lfn-chr-cont lfn-chi-cont)
  (lambda () (dk-only! lfn-p-iff lfn-p-cont) (prop)))
(dk-split-all!)

;;; ---- the values of the two factors at x.
(lfn-w-point! 'x)
(fact 'rr-subset-cc '(imag-part d))
(lfn-and! '(IN (imag-part d) CC) '(IN +i CC))
(fact 'cc-mul-comm '(imag-part d) '+i)
(fact 'cc-re-im-decompose 'd)
(lfn-and! '(IN l CC) '(IN d CC))
(fact 'cc-mul-closed 'l 'd)
(fact 'real-part-in-rr '(* l d))
(fact 'imag-part-in-rr '(* l d))
(define (lfn-value! proj chi)
  (dk-have! (list '= (list chi 'x) (list proj '(* l d)))
    (lambda ()
      (dk-lam-b!)
      (subst (list '= (list lfn-phi '(g x)) 'l))
      (subst (list '= (list lfn-psr 'x) '(real-part d)))
      (subst (list '= (list lfn-psi 'x) '(imag-part d)))
      (subst '(= (* (imag-part d) +i) (* +i (imag-part d))))
      (subst '(= (+ (real-part d) (* +i (imag-part d))) d))
      (rfl))))
(lfn-value! 'real-part lfn-chr)
(lfn-value! 'imag-part lfn-chi)

;;; ---- the Caratheodory equation of the composite, in CC:
;;;     f(g(y)) - f(g(x))  =  (y - x) * (phi(g(y)) * (psi_r(y) + psi_i(y) * i)).
(define (lfn-coord-eq! y proj cara lam psi)
  (dk-apply! cara y)
  (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr) (list 'g y))
  (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr) '(g x))
  (dk-have! (list '= (list lam y) (list proj (list 'g y))) (lambda () (dk-lam-b!) (rfl)))
  (dk-have! (list '= (list lam 'x) (list proj '(g x))) (lambda () (dk-lam-b!) (rfl)))
  (dk-have! (list '= (list '- (list proj (list 'g y)) (list proj '(g x)))
                  (list '* (list psi y) (list '- y 'x)))
    (lambda ()
      (subst (list '= (list proj (list 'g y)) (list lam y)))
      (subst (list '= (list proj '(g x)) (list lam 'x)))
      (ass))))
(define (lfn-composite-eq! y)
  (let* ((gy (list 'g y)) (fgy (list 'f gy)) (pgy (list lfn-phi gy))
         (h (list '- y 'x)) (dg (list '- gy '(g x)))
         (ef (list '= (list '- fgy '(f (g x))) (list '* pgy dg)))
         (eg (list '= dg (list '+ (list '* (list lfn-psr y) h)
                                   (list '* '+i (list '* (list lfn-psi y) h))))))
    (dk-apply! lfn-cara-f gy)
    (fact 'cc-nf-sub fgy '(f (g x)))
    (fact 'cc-nf-sub gy '(g x))
    (fact 'cc-sub-in-cc gy '(g x))
    (fact 'cc-nf-mul-apply pgy dg)
    (dk-have! ef
      (lambda ()
        (subst (list '= (list '* pgy dg) (list '(MUL CC-NORMED-FIELD) pgy dg)))
        (subst (list '= dg (list '(ADD CC-NORMED-FIELD) gy '((NEG CC-NORMED-FIELD) (g x)))))
        (subst (list '= (list '- fgy '(f (g x)))
                     (list '(ADD CC-NORMED-FIELD) fgy '((NEG CC-NORMED-FIELD) (f (g x))))))
        (ass)))
    (lfn-coord-eq! y 'real-part lfn-cara-r lfn-gr lfn-psr)
    (lfn-coord-eq! y 'imag-part lfn-cara-i lfn-gi lfn-psi)
    (fact 'cc-re-sub gy '(g x))
    (fact 'cc-im-sub gy '(g x))
    (fact 'cc-re-im-decompose dg)
    (fact 'rr-sub-in-rr y 'x)
    (fact 'rr-subset-cc h)
    (fact 'rr-mul-in-rr (list lfn-psr y) h)
    (fact 'rr-mul-in-rr (list lfn-psi y) h)
    (let ((a1 (list '* (list lfn-psr y) h))
          (a2 (list '* (list lfn-psi y) h)))
      (fact 'rr-subset-cc a1)
      (fact 'rr-subset-cc a2)
      (lfn-and! '(IN +i CC) (list 'IN a2 'CC))
      (fact 'cc-mul-closed '+i a2)
      (lfn-and! (list 'IN a1 'CC) (list 'IN (list '* '+i a2) 'CC))
      (fact 'cc-add-closed a1 (list '* '+i a2)))
    (dk-have! eg
      (lambda ()
        (subst (list '= dg (list '+ (list 'real-part dg) (list '* '+i (list 'imag-part dg)))))
        (subst (list '= (list 'real-part dg) (list '- (list 'real-part gy) '(real-part (g x)))))
        (subst (list '= (list 'imag-part dg) (list '- (list 'imag-part gy) '(imag-part (g x)))))
        (subst (list '= (list '- (list 'real-part gy) '(real-part (g x)))
                     (list '* (list lfn-psr y) h)))
        (subst (list '= (list '- (list 'imag-part gy) '(imag-part (g x)))
                     (list '* (list lfn-psi y) h)))
        (rfl)))
    (fact 'lfn-cc-factor-identity pgy (list lfn-psr y) (list lfn-psi y) '+i h)
    (dk-have! (list '= (list '- fgy '(f (g x))) (list '* h (lfn-kexp y)))
      (lambda ()
        (subst ef)
        (subst eg)
        (ass)))))

;;; ---- the two Caratheodory packages of the composite.
(define (lfn-within! proj chi fl dval sublaw mullaw inlaw)
  (lfn-lam-type! (list 'IN fl '(FUN dm RR))
    (lambda (y)
      (fact 'fun-apply-type-c 'g 'dm 'CC y)
      (lfn-in-u! y)
      (fact 'fun-apply-type-c 'f 'u 'CC (list 'g y))
      (fact inlaw (list 'f (list 'g y)))))
  (fact 'restrict-in-fun fl 'dm 'RR 'w)
  (dk-have! (list 'HAS-DERIV-AT-WITHIN fl 'w 'x dval)
    (lambda ()
      (mac 'HAS-DERIV-AT-WITHIN)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (lfn-head (dk-goal)) 'FORSOME))
             (ass)
             (begin
               (ew chi)
               (dk-conj-close!
                (lambda ()
                  (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
                      (ass)
                      (let* ((y (dk-di-var!))
                             (h (list '- y 'x))
                             (k (lfn-kexp y))
                             (fgy (list 'f (list 'g y))))
                        (lfn-w-point! y)
                        (lfn-composite-eq! y)
                        (fact inlaw fgy)
                        (fact inlaw '(f (g x)))
                        (fact 'cc-sub-in-cc fgy '(f (g x)))
                        (fact sublaw fgy '(f (g x)))
                        (fact mullaw h k)
                        (lfn-and! (list 'IN h 'RR) (list 'IN (list proj k) 'RR))
                        (fact 'rr-mul-comm h (list proj k))
                        (dk-lam-b!)
                        (subst (list '= (list '- (list proj fgy) (list proj '(f (g x))))
                                     (list proj (list '- fgy '(f (g x))))))
                        (subst (list '= (list '- fgy '(f (g x))) (list '* h k)))
                        (subst (list '= (list proj (list '* h k)) (list '* h (list proj k))))
                        (subst (list '= (list '* h (list proj k)) (list '* (list proj k) h)))
                        (rfl))))))))))))

(lfn-within! 'real-part lfn-chr lfn-fr '(real-part (* l d))
             'cc-re-sub 'cc-re-real-mul 'real-part-in-rr)
(lfn-within! 'imag-part lfn-chi lfn-fi '(imag-part (* l d))
             'cc-im-sub 'cc-im-real-mul 'imag-part-in-rr)
(dk-conj-close! (lambda () (ass)))
(qed 'holomorphic-chain-within)
(topic! 'holomorphic-chain-within 'analysis)
(alias! 'holomorphic-chain-within "the chain rule for a holomorphic function after a map of a real variable, Caratheodory form")

;;; =====================================================================
;;; (4) THE CHAIN RULE FOR THE LOCAL DERIVATIVE: the notes' form.
;;; =====================================================================

;;; nested windows.
(sp (make-wff "forall([x in rr, lfv_, lfr_ in rr],
   pos-rr(lfv_) implies lfv_ <= lfr_ implies
   subset(ooint(x - lfv_, x + lfv_), ooint(x - lfr_, x + lfr_)))"))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'lfv_)
(fact 'rr-lt-of-pos-rr 'lfv_)
(let ((y (subset-by-element!)))
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN y '(OOINT (- x lfv_) (+ x lfv_)))))))
  (mac 'ooint-membership)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (dk-ineq! '(IN x RR) '(IN lfv_ RR) '(IN lfr_ RR) (list 'IN y 'RR) '(<= lfv_ lfr_)
                   (list '< '(- x lfv_) y) (list '< y '(+ x lfv_)))))))
(qed 'ooint-center-nested)
(topic! 'ooint-center-nested 'analysis)

(define lfn-grh (lfn-lam 'real-part '(g pat_)))
(define lfn-gih (lfn-lam 'imag-part '(g pat_)))
(define lfn-frh (lfn-lam 'real-part '(f (g pat_))))
(define lfn-fih (lfn-lam 'imag-part '(f (g pat_))))
(define (lfn-win v) (list 'OOINT (list '- 'x v) (list '+ 'x v)))

(sp (make-wff "forall([dm, g, x, u, f, l, d],
   subset(dm, rr) implies
   g in fun(dm, cc) implies
   is-continuous-at(subspace-ms(rr-ms, dm), cc-ms, g, x) implies
   forall([msy_ in dm], g(msy_) in u) implies
   is-diff-on(cc-normed-field, u, f, g(x), l) implies
   d in cc implies
   has-deriv-at(vnb-lambda(pat_, dm, real-part(g(pat_))), x, real-part(d)) implies
   has-deriv-at(vnb-lambda(pat_, dm, imag-part(g(pat_))), x, imag-part(d)) implies
   has-deriv-at(vnb-lambda(pat_, dm, real-part(f(g(pat_)))), x, real-part(l * d)) and
   has-deriv-at(vnb-lambda(pat_, dm, imag-part(f(g(pat_)))), x, imag-part(l * d)))"))
(dk-peel!)
(fact 'has-deriv-at-pt-in-rr lfn-grh 'x '(real-part d))
(fact 'rr-is-set)
(fact 'subclass-of-set-is-set 'dm 'RR)
(define lfn-b-iff (dk-fact! 'has-deriv-at-iff-within-ooint lfn-grh 'x '(real-part d)))
(define lfn-b-ex (caddr lfn-b-iff))
(dk-have! lfn-b-ex
  (lambda () (dk-only! lfn-b-iff (list 'HAS-DERIV-AT lfn-grh 'x '(real-part d))) (prop)))
(define lfn-v1 (dk-skolem! (dk-ctx-form lfn-b-ex)))
(dk-split-all!)
(define lfn-b-to (dk-fact! 'has-deriv-at-to-within-ooint lfn-gih 'x '(imag-part d)))
(define lfn-v2 (dk-skolem! (dk-apply! lfn-b-to lfn-v1)))
(dk-split-all!)
(fact 'rr-pos-rr-in-rr lfn-v1)
(fact 'rr-pos-rr-in-rr lfn-v2)
(fact 'ooint-subset-rr (list '- 'x lfn-v1) (list '+ 'x lfn-v1))
(fact 'ooint-center-nested 'x lfn-v2 lfn-v1)
(fact 'ooint-center 'x lfn-v2)
(fact 'deriv-within-shrink lfn-grh (lfn-win lfn-v1) (lfn-win lfn-v2) 'x '(real-part d))
;;; the window lies in dm: read off the FUN typing of the restriction.
(define (lfn-b-point! y)
  (fact 'fun-apply-type-c 'g 'dm 'CC y))
(lfn-lam-type! (list 'IN lfn-grh '(FUN dm RR))
  (lambda (y) (fact 'fun-apply-type-c 'g 'dm 'CC y) (fact 'real-part-in-rr (list 'g y))))
(fact 'deriv-within-restrict-in-fun lfn-grh (lfn-win lfn-v2) 'x '(real-part d))
(fact 'restrict-fun-domain-subset lfn-grh 'dm 'RR (lfn-win lfn-v2) 'RR)
(define lfn-b-a (dk-fact! 'holomorphic-chain-within 'dm (lfn-win lfn-v2) 'g 'x))
(dk-split-all! (list (dk-apply! lfn-b-a 'u 'f 'l 'd)))
(fact 'has-deriv-at-of-within-ooint 'x lfn-v2 lfn-frh '(real-part (* l d)))
(fact 'has-deriv-at-of-within-ooint 'x lfn-v2 lfn-fih '(imag-part (* l d)))
(dk-conj-close! (lambda () (ass)))
(qed 'holomorphic-chain)
(topic! 'holomorphic-chain 'analysis)
(alias! 'holomorphic-chain "the chain rule for a holomorphic function after a map of a real variable into C")

;;; =====================================================================
;;; (5) PROPOSITION 3.2 OF THE NOTES, equation (50).
;;; =====================================================================

(define lfn-cc '(CCINT a b))
(define lfn-scc (list 'SUBSPACE-MS 'RR-MS lfn-cc))
(define (lfn-plam body) (list 'VNB-LAMBDA 'pat_ lfn-cc body))
(define lfn-pgr (lfn-plam '(real-part (pgam pat_))))
(define lfn-pgi (lfn-plam '(imag-part (pgam pat_))))
(define lfn-pdr (lfn-plam '(real-part (dgam pat_))))
(define lfn-pdi (lfn-plam '(imag-part (dgam pat_))))
(define lfn-pfr (lfn-plam '(real-part (f (pgam pat_)))))
(define lfn-pfi (lfn-plam '(imag-part (f (pgam pat_)))))

(sp (make-wff "forall([u, f, df, pgam, dgam, a, b],
   holomorphic-on(u, f) implies
   df in fun(u, cc) implies
   forall([hbz_ in u], is-diff-on(cc-normed-field, u, f, hbz_, df(hbz_))) implies
   is-road(pgam, dgam, a, b) implies
   subset(trace(pgam, a, b), u) implies
   line-int(df, pgam, dgam, a, b) = f(pgam(b)) - f(pgam(a)))"))
(dk-peel!)
(define lfn-dfu
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'IS-DIFF-ON)))
           "the derivative of f on u"))
(lfn-cc-setup!)
(fact 'rr-is-metric-space)
(fact 'rr-is-set)
(dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
(fact 'holomorphic-on-in-fun 'u 'f)
(fact 'holomorphic-on-open 'u 'f)
(dk-project! (list 'SUBSET 'u (list 'PTS lfn-nfc)) 'IS-OPEN (list 'IS-OPEN lfn-nfc 'u))
(dk-have! '(SUBSET u CC)
  (lambda ()
    (subst '(= CC (PTS CC-MS)))
    (subst (list '= '(PTS CC-MS) (list 'PTS lfn-nfc)))
    (ass)))
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(fact 'is-path-in-fun 'pgam 'a 'b)
(fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(define lfn-pcont (dk-fact! 'is-path-continuous 'pgam 'a 'b))
(fact 'is-road-re-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-im-antiderivative 'pgam 'dgam 'a 'b)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set lfn-cc 'RR)
(fact 'ooint-subset-ccint 'a 'b)
(dk-have! (list 'SUBSET lfn-cc '(PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
(fact 'subspace-is-metric-space 'RR-MS lfn-cc)
(fact 'subspace-pts 'RR-MS lfn-cc)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'b)
(define (lfn-endpoint! z)
  (dk-have! (list 'IN z lfn-cc)
    (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass))))))
(lfn-endpoint! 'a)
(lfn-endpoint! 'b)

;;; the trace lies in u, pointwise.
(dk-have! (list 'FORALL 'msy_ (list 'IMPLIES (list 'IN 'msy_ lfn-cc) '(IN (pgam msy_) u)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (fact 'trace-value-in 'pgam 'a 'b y)
      (fact 'subset-mem-fwd '(TRACE pgam a b) 'u (list 'pgam y))
      (ass))))
(define lfn-pgu
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'msy_)
                             (dk-contains? fm '(pgam msy_))))
           "the trace lies in u"))
(define (lfn-pt! y)
  (fact 'fun-apply-type-c 'pgam lfn-cc 'CC y)
  (if (not (dk-ctx-form (list 'IN (list 'pgam y) 'u))) (dk-apply! lfn-pgu y))
  (fact 'fun-apply-type-c 'f 'u 'CC (list 'pgam y))
  (fact 'fun-apply-type-c 'df 'u 'CC (list 'pgam y))
  (fact 'fun-apply-type-c 'dgam lfn-cc 'CC y)
  (fact 'real-part-in-rr (list 'f (list 'pgam y)))
  (fact 'imag-part-in-rr (list 'f (list 'pgam y)))
  (lfn-and! (list 'IN (list 'df (list 'pgam y)) 'CC) (list 'IN (list 'dgam y) 'CC))
  (fact 'cc-mul-closed (list 'df (list 'pgam y)) (list 'dgam y))
  (fact 'real-part-in-rr (list '* (list 'df (list 'pgam y)) (list 'dgam y)))
  (fact 'imag-part-in-rr (list '* (list 'df (list 'pgam y)) (list 'dgam y))))
(lfn-pt! 'a)
(lfn-pt! 'b)

;;; the coordinates of F = f o gamma are functions on [a,b].
(define (lfn-ptype! claim)
  (dk-have! claim
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
             (ass)
             (let ((y (dk-di-var!))) (lfn-pt! y) (lfn-lam-b-if!) (ass))))
       (dk-opened (lambda () (lam-t)))))))
(lfn-ptype! (list 'IN lfn-pfr (list 'FUN lfn-cc 'RR)))
(lfn-ptype! (list 'IN lfn-pfi (list 'FUN lfn-cc 'RR)))

;;; ---- F = f o gamma is continuous on [a,b], coordinatewise.
(dk-have! (list 'FORALL 'msy_ (list 'IMPLIES (list 'IN 'msy_ (list 'PTS lfn-scc))
            '(IN (pgam msy_) u)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (dk-have! (list 'IN y lfn-cc)
        (lambda () (subst (list '= lfn-cc (list 'PTS lfn-scc))) (ass)))
      (dk-apply! lfn-pgu y)
      (ass))))
(dk-have! '(IN pgam (FUN (PTS (SUBSPACE-MS RR-MS (CCINT a b))) CC))
  (lambda () (subst (list '== (list 'PTS lfn-scc) lfn-cc)) (ass)))
(define (lfn-f-cont! y)
  (lfn-pt! y)
  (dk-have! (list 'IN y (list 'PTS lfn-scc))
    (lambda () (subst (list '== (list 'PTS lfn-scc) lfn-cc)) (ass)))
  (dk-apply! lfn-pcont y)
  (dk-apply! lfn-dfu (list 'pgam y))
  (fact 'diff-on-implies-continuous 'CC-NORMED-FIELD 'u 'f (list 'pgam y)
        (list 'df (list 'pgam y)))
  (let* ((r (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IS-CONTINUOUS-AT)))
                       "the continuity of f o gamma"
                       'cc-compose-continuous-at lfn-scc 'u 'pgam 'f y))
         (c (list-ref r 3)))
    (dk-have! (list 'IN c (list 'FUN (list 'PTS lfn-scc) 'CC))
      (lambda ()
        (fact 'ms-pts-is-set lfn-scc)
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (dk-have! (list 'IN z lfn-cc)
                   (lambda () (subst (list '= lfn-cc (list 'PTS lfn-scc))) (ass)))
                 (lfn-pt! z)
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'IN lfn-pfr (list 'FUN (list 'PTS lfn-scc) 'RR))
      (lambda () (subst (list '== (list 'PTS lfn-scc) lfn-cc)) (ass)))
    (dk-have! (list 'IN lfn-pfi (list 'FUN (list 'PTS lfn-scc) 'RR))
      (lambda () (subst (list '== (list 'PTS lfn-scc) lfn-cc)) (ass)))
    (for-each
     (lambda (proj fl)
       (dk-have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'PTS lfn-scc))
                   (list '= (list proj (list c 'u_)) (list fl 'u_))))
         (lambda ()
           (let ((z (dk-di-var!)))
             (dk-have! (list 'IN z lfn-cc)
               (lambda () (subst (list '= lfn-cc (list 'PTS lfn-scc))) (ass)))
             (lfn-pt! z)
             (dk-lam-b!)
             (rfl)))))
     '(real-part imag-part) (list lfn-pfr lfn-pfi))
    (let ((iff (lfn-cite! (lambda (r) (and (pair? r) (eq? (car r) 'IFF)))
                          "the coordinate iff for f o gamma"
                          'cc-continuous-at-iff-coords lfn-scc c lfn-pfr lfn-pfi y)))
      (cons iff r))))
;;; ONE lane for both coordinates.  Run twice, the second run's `dk-only!'
;;; weakens onto the sequent the first run grounded (the eigenvariable is the
;;; same `icp_' in both lanes), the focus drifts to the MAIN leaf and the
;;; weakening continues there -- the `dk-only!' defect CLAUDE.md lists.
(define lfn-both-cont
  (list 'FORALL 'icp_ (list 'IMPLIES (list 'IN 'icp_ lfn-cc)
    (list 'AND (list 'IS-CONTINUOUS-AT lfn-scc 'RR-MS lfn-pfr 'icp_)
               (list 'IS-CONTINUOUS-AT lfn-scc 'RR-MS lfn-pfi 'icp_)))))
(dk-have! lfn-both-cont
  (lambda ()
    (let* ((y (dk-di-var!))
           (ir (lfn-f-cont! y)))
      ;; the goal IS the conjunction the iff delivers
      (dk-only! (car ir) (cdr ir))
      (prop))))
(define (lfn-cont-on! fl)
  (dk-have! (list 'IS-CONTINUOUS-ON fl lfn-cc)
    (lambda ()
      (mac 'IS-CONTINUOUS-ON)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (lfn-head (dk-goal)) 'FORALL))
             (ass)
             (let ((y (dk-di-var!)))
               (dk-split-all! (list (dk-apply! (dk-ctx-form lfn-both-cont) y)))
               (ass))))))))
(lfn-cont-on! lfn-pfr)
(lfn-cont-on! lfn-pfi)

;;; ---- the goal, unfolded: CC-INT's two coordinate integrals.
(mac 'LINE-INT)
(mac 'CC-INT)
(define lfn-goal0 (dk-goal))
(define lfn-ir (cadr (cadr (cadr lfn-goal0))))
(define lfn-ii (cadr (cadr (caddr (cadr lfn-goal0)))))
(lfn-ptype! (list 'IN lfn-ir (list 'FUN lfn-cc 'RR)))
(lfn-ptype! (list 'IN lfn-ii (list 'FUN lfn-cc 'RR)))

;;; ---- the exceptional set: the union of the two of the road.
(define lfn-s1 (dk-skolem! (dk-fact! 'pw-antiderivative-exceptional-set lfn-pgr lfn-pdr 'a 'b)))
(dk-split-all!)
(define lfn-d1 (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm 'HAS-DERIV-AT)
                                          (dk-contains? fm lfn-s1)))
                        "the derivative universal of re gamma"))
(define lfn-s2 (dk-skolem! (dk-fact! 'pw-antiderivative-exceptional-set lfn-pgi lfn-pdi 'a 'b)))
(dk-split-all!)
(define lfn-d2 (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm 'HAS-DERIV-AT)
                                          (dk-contains? fm lfn-s2)))
                        "the derivative universal of im gamma"))
(define lfn-un (list 'UNION lfn-s1 lfn-s2))
(lfn-and! (list 'IN lfn-s1 'SET) (list 'IN lfn-s2 'SET))
(fact 'union-set-closure lfn-s1 lfn-s2)
(fact 'card-union-nn lfn-s1 lfn-s2)
(dk-have! (list 'SUBSET lfn-un lfn-cc)
  (lambda ()
    (let* ((w  (subset-by-element!))
           (um (dk-fact! 'union-membership lfn-s1 lfn-s2 w)))
      (fact 'subset-mem-fwd lfn-s1 lfn-cc w)
      (fact 'subset-mem-fwd lfn-s2 lfn-cc w)
      (dk-only! um
                (list 'IN w lfn-un)
                (list 'IMPLIES (list 'IN w lfn-s1) (list 'IN w lfn-cc))
                (list 'IMPLIES (list 'IN w lfn-s2) (list 'IN w lfn-cc)))
      (prop))))

;;; ---- THE DERIVATIVE of each coordinate of F, off the union: the chain rule.
(define lfn-both-deriv
  (list 'FORALL 'lft_ (list 'IMPLIES '(IN lft_ (OOINT a b))
    (list 'IMPLIES (list 'NOT (list 'IN 'lft_ lfn-un))
      (list 'AND (list 'HAS-DERIV-AT lfn-pfr 'lft_ (list lfn-ir 'lft_))
                 (list 'HAS-DERIV-AT lfn-pfi 'lft_ (list lfn-ii 'lft_)))))))
(dk-have! lfn-both-deriv
  (lambda ()
    (dk-peel!)
    (let* ((tv (cadr (cadr (dk-goal))))
           (tv (caddr (cadr (dk-goal))))
           (um (dk-fact! 'union-membership lfn-s1 lfn-s2 tv))
           (dt (list 'dgam tv))
           (dft (list 'df (list 'pgam tv))))
      (dk-have! (list 'AND (list 'NOT (list 'IN tv lfn-s1)) (list 'NOT (list 'IN tv lfn-s2)))
        (lambda () (dk-only! um (list 'NOT (list 'IN tv lfn-un))) (prop)))
      (dk-split-all!)
      (fact 'subset-mem-fwd '(OOINT a b) lfn-cc tv)
      (lfn-pt! tv)
      (fact 'fun-apply-type-c lfn-pdr lfn-cc 'RR tv)
      (fact 'fun-apply-type-c lfn-pdi lfn-cc 'RR tv)
      (dk-apply! lfn-d1 tv)
      (dk-apply! lfn-d2 tv)
      (fact 'real-part-in-rr dt)
      (fact 'imag-part-in-rr dt)
      (for-each
       (lambda (gl dl pj)
         (dk-have! (list '= (list dl tv) (list pj dt)) (lambda () (dk-lam-b!) (rfl)))
         (dk-have! (list 'HAS-DERIV-AT gl tv (list pj dt))
           (lambda () (subst (list '= (list pj dt) (list dl tv))) (ass))))
       (list lfn-pgr lfn-pgi) (list lfn-pdr lfn-pdi) '(real-part imag-part))
      (dk-apply! lfn-pcont tv)
      (dk-apply! lfn-dfu (list 'pgam tv))
      (dk-split-all!
       (list (dk-apply! (dk-fact! 'holomorphic-chain lfn-cc 'pgam tv) 'u 'f dft dt)))
      (for-each
       (lambda (il pj)
         (dk-have! (list '= (list il tv) (list pj (list '* dft dt)))
           (lambda () (dk-lam-b!) (rfl))))
       (list lfn-ir lfn-ii) '(real-part imag-part))
      (subst (list '= (list lfn-ir tv) (list 'real-part (list '* dft dt))))
      (subst (list '= (list lfn-ii tv) (list 'imag-part (list '* dft dt))))
      (dk-conj-close! (lambda () (ass))))))
(define (lfn-deriv-univ! fl il)
  (dk-have! (list 'FORALL 'lft_ (list 'IMPLIES '(IN lft_ (OOINT a b))
              (list 'IMPLIES (list 'NOT (list 'IN 'lft_ lfn-un))
                    (list 'HAS-DERIV-AT fl 'lft_ (list il 'lft_)))))
    (lambda ()
      (dk-peel!)
      (let ((tv (caddr (dk-goal))))
        (dk-split-all! (list (dk-apply! (dk-ctx-form lfn-both-deriv) tv)))
        (ass)))))
(lfn-deriv-univ! lfn-pfr lfn-ir)
(lfn-deriv-univ! lfn-pfi lfn-ii)

;;; ---- each coordinate of F is a piecewise antiderivative of the
;;; corresponding coordinate of the integrand.
(define (lfn-pw! fl il)
  (dk-have! (list 'IS-PW-ANTIDERIVATIVE fl il 'a 'b)
    (lambda ()
      (mac 'IS-PW-ANTIDERIVATIVE)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (lfn-head (dk-goal)) 'FORSOME))
             (ass)
             (begin
               (ew lfn-un)
               (dk-conj-close! (lambda () (ass))))))))))
(lfn-pw! lfn-pfr lfn-ir)
(lfn-pw! lfn-pfi lfn-ii)

;;; ---- the value: each coordinate integral is the increment of the
;;; corresponding coordinate of F, and the two are put back together.
(define (lfn-coord-value! fl il proj)
  (fact 'pw-int-value fl il 'a 'b)
  (for-each
   (lambda (e)
     (dk-have! (list '= (list fl e) (list proj (list 'f (list 'pgam e))))
       (lambda () (dk-lam-b!) (rfl))))
   '(a b))
  (subst (list '= (list 'PW-INT il 'a 'b) (list '- (list fl 'b) (list fl 'a))))
  (subst (list '= (list fl 'b) (list proj '(f (pgam b)))))
  (subst (list '= (list fl 'a) (list proj '(f (pgam a))))))
(lfn-coord-value! lfn-pfr lfn-ir 'real-part)
(lfn-coord-value! lfn-pfi lfn-ii 'imag-part)
(define lfn-z '(- (f (pgam b)) (f (pgam a))))
(fact 'cc-i-in)
(fact 'cc-sub-in-cc '(f (pgam b)) '(f (pgam a)))
(fact 'cc-re-sub '(f (pgam b)) '(f (pgam a)))
(fact 'cc-im-sub '(f (pgam b)) '(f (pgam a)))
(fact 'cc-re-im-decompose lfn-z)
(fact 'real-part-in-rr lfn-z)
(fact 'imag-part-in-rr lfn-z)
(subst (list '= '(- (real-part (f (pgam b))) (real-part (f (pgam a))))
             (list 'real-part lfn-z)))
(subst (list '= '(- (imag-part (f (pgam b))) (imag-part (f (pgam a))))
             (list 'imag-part lfn-z)))
(fact 'rr-subset-cc (list 'imag-part lfn-z))
(lfn-and! (list 'IN (list 'imag-part lfn-z) 'CC) '(IN +i CC))
(fact 'cc-mul-comm (list 'imag-part lfn-z) '+i)
(subst (list '= (list '* (list 'imag-part lfn-z) '+i) (list '* '+i (list 'imag-part lfn-z))))
(fact 'eq-sym lfn-z (list '+ (list 'real-part lfn-z) (list '* '+i (list 'imag-part lfn-z))))
(ass)
(qed 'line-int-of-derivative)
(topic! 'line-int-of-derivative 'analysis)
(alias! 'line-int-of-derivative "Proposition 3.2: the integral of f' along a road is f(end) - f(start)")
