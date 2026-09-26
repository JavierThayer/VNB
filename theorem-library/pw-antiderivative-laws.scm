;;; pw-antiderivative-laws.scm -- the laws of IS-PW-ANTIDERIVATIVE and PW-INT
;;; (structure-library/path-integral.scm), with the exceptional set a FINITE
;;; SET.
;;;
;;; THE SPECIFICATION is docs/paths-and-line-integrals-2026-09-21.md s.3.2 and
;;; Dieudonne 8.7; the statement checks made before any proof was written are
;;; in the header of the definition file.  The user's notes
;;; (~/docs/calculus.pdf) give the three statements this file has to reach:
;;;
;;;   Corollary 2.15   f continuous on [a,b], f' = 0 on (a,b)  =>  f constant
;;;                    on [a,b].                     `deriv-zero-constant-on-interval'
;;;   Proposition 4.10 two antiderivatives of phi on [a,b] differ by a
;;;                    constant.                     `pw-antiderivative-differ-by-constant'
;;;   Corollary 4.11   two antiderivatives of phi have the same endpoint
;;;                    difference.                   `pw-antiderivative-endpoint-difference'
;;;
;;; 4.11 IS the uniqueness half of PW-INT's `iota-d' obligation, which is why
;;; `pw-int-value' and `pw-int-in-rr' are UNCONDITIONAL here: the definite
;;; integral of the notes' equation (64) is well defined.
;;;
;;; THE ROUTE, and why it is the one that works.  Batch 15-B wrote the
;;; exceptional set as an increasing ENUMERATION and could not prove 4.11,
;;; because two antiderivatives carry two enumerations and the telescoping
;;; argument runs on a COMMON REFINEMENT the library cannot build.  With a SET
;;; the refinement is not needed: what replaces it is
;;;
;;;   `pw-zero-deriv-off-finite-set' -- a function continuous on the WHOLE LINE
;;;   whose derivative is 0 at every point of (u,v) OFF A FINITE SET S takes
;;;   equal values at u and v
;;;
;;; proved by `finite-set-induction' on S.  The BASE is
;;; `deriv-zero-implies-constant' (the library's total-function Corollary
;;; 2.15).  The STEP splits at the new point s: if s is outside (u,v) the
;;; induction hypothesis applies unchanged; if u < s < v it is applied TWICE,
;;; to (u,s) and to (s,v), and the two equations compose.  THE INTERVAL (u,v)
;;; IS A PARAMETER OF THE INDUCTION -- the class the induction runs over
;;; quantifies over h, u and v -- which is exactly what lets the step halve the
;;; interval without ever forming a restriction of h.  (15-B's route kept a
;;; function interval [c,d] separate from a conclusion interval [u,v] for the
;;; same reason; taking h TOTAL is the same device with [c,d] = the line, and
;;; it costs nothing, because `EXTEND-CONST' carries a function on [c,d] to the
;;; line with its continuity and its interior derivatives intact -- that is
;;; what theorem-library/interval-calculus-laws.scm proved it for.)
;;;
;;; THE FILE IN ORDER.
;;;   (1) the read-offs of IS-PRIMITIVE live in regulated-primitive-laws.scm (primitive-*);
;;;       here, the values of a primitive are reals;
;;;   (2) `pw-not-in-insert' and the inner radius of an interval (`pw-lt-ne' moved to
;;;       zero-deriv-off-countable.scm, 2026-09-23);
;;;   (3) constancy with NO exceptional set, total (`pw-zero-deriv-total') and
;;;       on an interval -- the notes' Corollary 2.15;
;;;   (4) constancy OFF A FINITE SET, by finite-set-induction;
;;;   (5) Proposition 4.10 and Corollary 4.11;
;;;   (6) PW-INT: `pw-int-value', `pw-int-in-rr', both UNCONDITIONAL, and the
;;;       congruence laws;
;;;   (7) the introduction rule and the AFFINE witness;
;;;   (8) PW-INT of a constant, and linearity (Propositions 4.12 / 4.13).
;;;
;;; Helper prefix: pw-.
;;;
;;; Dependencies: structure-library/path-integral.scm; structure-library/
;;; interval-calculus.scm; structure-library/cardinality.scm (CARD);
;;; theorem-library/interval-calculus-laws.scm (ooint-*, has-deriv-at-*,
;;; extend-const-*); theorem-library/has-deriv-at-more.scm (has-deriv-at-const,
;;; -affine, -real-mul, -difference); theorem-library/differentiation.scm
;;; (deriv-zero-implies-constant, deriv-difference, deriv-sum,
;;; deriv-scalar-mult, diff-implies-continuous);
;;; theorem-library/regulated-primitive-laws.scm (primitive-* read-offs,
;;; countable-empty, countable-union-2); theorem-library/zero-deriv-off-countable.scm
;;; (zero-deriv-off-countable; it loads BEFORE this file since 2026-09-23, and
;;; `pw-lt-ne' lives there);
;;; theorem-library/continuity-basics.scm (sub-continuous-at, sum-continuous-at,
;;; const-continuous-at); theorem-library/rake-card-star-laws.scm
;;; (finite-set-induction, section (5) only); theorem-library/ccint-basics.scm; monotone-inverse.scm
;;; (ccint-subset-rr); metric-subspace-laws.scm (restrict-apply, restrict-in-fun,
;;; restrict-continuous-at, subspace-pts); ms-continuity-algebra.scm
;;; (ms-cont-transfer-ptwise-eq); directional-derivative.scm (deriv-affine,
;;; affine-lam-in-fun); rr-order-basics.scm (rr-min-pos); subset-lemmas.scm
;;; (subset-mem-fwd); interval-membership.scm.

;;; ---- file-local driver helpers ---------------------------------------

(define (pw-head g) (and (pair? g) (car g)))

(define pw-cc '(CCINT a b))
(define pw-sub (list 'SUBSPACE-MS 'RR-MS pw-cc))

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
    (mac-h 'IS-PRIMITIVE form)))))

;;; x in CCINT(lo,hi) from x in RR, lo <= x, x <= hi (all in context).
(define (pw-in-ccint! z lo hi prems)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (pw-conj-ineq! prems))))

;;; x in OOINT(lo,hi) from x in RR, lo < x, x < hi.
(define (pw-in-ooint! z lo hi prems)
  (dk-have! (list 'IN z (list 'OOINT lo hi))
    (lambda () (mac 'ooint-membership) (pw-conj-ineq! prems))))

;;; (1) THE READ-OFFS of IS-PRIMITIVE are `primitive-endpoints / -in-fun / -integrand-in-fun /
;;; -continuous / -exceptional-set` (theorem-library/regulated-primitive-laws.scm, 20-D).  The five
;;; finite-set read-offs that stood here were retired 2026-09-23 (original: archive/2026-09-23-batch20/).

;;; the values of a piecewise antiderivative are reals -- what every endpoint
;;; difference needs before it can be an arithmetic term.
(sp (make-wff "forall([pwf_, pphi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   forall([pay_ in ccint(a,b)], pwf_(pay_) in rr))"))
(dk-peel!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(let ((z (cadr (cadr (dk-goal)))))
  (fact 'fun-apply-type-c 'pwf_ (list 'CCINT 'a 'b) 'RR z)
  (ass))
(qed 'pw-antiderivative-value-in-rr)
(topic! 'pw-antiderivative-value-in-rr 'analysis)

;;; `pw-lt-ne' (a strict inequality denies both orientations of the equation) MOVED 2026-09-23 to
;;; theorem-library/zero-deriv-off-countable.scm, which loads BEFORE this file and cites it (batch 21 broke
;;; the cycle: this file cites `zero-deriv-off-countable').

;;; =====================================================================
;;; (2) TWO SMALL FACTS.
;;; =====================================================================
;;; `pw-not-in-insert': a point outside S and different from the inserted one
;;; is outside S u {x}.  Proved ONCE, here, where the context is shallow enough
;;; for `prop' to see the two membership equivalences; inside the induction
;;; step the context carries the whole class term and `prop' drops the relevant
;;; pair (CLAUDE.md: "in a deep context its atom cap drops the relevant pair").
(sp (make-wff '(FORALL pcy_ (IMPLIES (IN pcy_ SET)
   (FORALL pcw_ (FORALL pct_
     (IMPLIES (NOT (IN pct_ pcw_))
       (IMPLIES (NOT (= pct_ pcy_))
         (NOT (IN pct_ (UNION pcw_ (PAIR pcy_ pcy_))))))))))))
(dk-peel!)
(have! '(AND (IN pcy_ SET) (IN pcy_ SET)))
(fact 'pairing 'pcy_ 'pcy_)
;; `prop' declines with an EMPTY countermodel until the context is cut down to
;; the two membership equivalences and the two negations -- the atom cap again.
(let* ((um (dk-fact! 'union-membership 'pcw_ '(PAIR pcy_ pcy_) 'pct_))
       (pm (dk-apply! (dk-fact! 'pairing-membership 'pcy_ 'pcy_) 'pct_))
       (as (car (dk-landed* (lambda () (di))))))
  (dk-only! um pm '(NOT (IN pct_ pcw_)) '(NOT (= pct_ pcy_)) as)
  (prop))
(qed 'pw-not-in-insert)
(topic! 'pw-not-in-insert 'plumbing)
(alias! 'pw-not-in-insert
        "a point outside a set and distinct from an inserted one is outside the enlarged set")

;;; =====================================================================
;;; (3) AN INNER RADIUS.  Every point of an open interval has a symmetric
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
;;; (4) CONSTANCY WITH NO EXCEPTIONAL SET.
;;;
;;; The total form first: it is the base case of the induction of section (5)
;;; and it is one citation of the library's `deriv-zero-implies-constant'.
;;; =====================================================================
(sp (make-wff "forall([pah_], pah_ in fun(rr, rr) implies
   forall([pax_ in rr], is-continuous-at(rr-ms, rr-ms, pah_, pax_)) implies
   forall([pau_ in rr, pav_ in rr], pau_ < pav_ implies
     forall([pat_], pat_ in ooint(pau_, pav_) implies is-diff-at(pah_, pat_, 0))
       implies
     pah_(pau_) = pah_(pav_)))"))
(dk-peel!)
(define pw-zt-cont
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
           "the continuity universal"))
(define pw-zt-diff
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-DIFF-AT)))
           "the differentiability universal"))
(have! '(AND (IN pah_ (FUN RR RR))
             (AND (IN pau_ RR) (AND (IN pav_ RR) (< pau_ pav_)))))
(dk-have! '(FORALL x (IMPLIES (IN x (CCINT pau_ pav_))
              (IS-CONTINUOUS-AT RR-MS RR-MS pah_ x)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'pau_ 'pav_ z)
      (dk-apply! pw-zt-cont z)
      (ass))))
(dk-have! '(FORALL x (IMPLIES (AND (IN x RR) (AND (< pau_ x) (< x pav_)))
              (IS-DIFF-AT pah_ x 0)))
  (lambda ()
    (dk-peel!)
    (dk-split-all!)
    (pw-in-ooint! 'x 'pau_ 'pav_ (list '(IN x RR) '(< pau_ x) '(< x pav_)))
    (dk-apply! pw-zt-diff 'x)
    (ass)))
(fact 'deriv-zero-implies-constant 'pah_ 'pau_ 'pav_)
(fact 'rr-leq-reflexive 'pau_)
(fact 'rr-leq-reflexive 'pav_)
(fact 'rr-lt-implies-le 'pau_ 'pav_)
(pw-in-ccint! 'pau_ 'pau_ 'pav_
  (list '(IN pau_ RR) '(<= pau_ pau_) '(<= pau_ pav_)))
(pw-in-ccint! 'pav_ 'pau_ 'pav_
  (list '(IN pav_ RR) '(<= pav_ pav_) '(<= pau_ pav_)))
(have! (list 'AND (list 'IN 'pau_ '(CCINT pau_ pav_))
             (list 'IN 'pav_ '(CCINT pau_ pav_))))
(dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                      (dk-contains? fm '(CCINT pau_ pav_))
                                      (dk-contains? fm 'pah_)
                                      (not (dk-contains? fm 'IS-CONTINUOUS-AT))))
                    "the constancy conclusion")
           'pau_ 'pav_)
(ass)
(qed 'pw-zero-deriv-total)
(topic! 'pw-zero-deriv-total 'analysis)
(alias! 'pw-zero-deriv-total
        "a function on the line with vanishing derivative on an interval is constant there")

;;; THE NOTES' COROLLARY 2.15, for a function ON its interval.
;;;
;;;   "Suppose a < b are real numbers and f is a continuous real-valued
;;;    function on [a, b] which is differentiable on the open interval (a, b)
;;;    and f'(theta) = 0 for all theta in (a, b).  Then f is a constant on
;;;    [a, b]."
;;;
;;; "f is a constant on [a,b]" is written as it has to be written here -- f
;;; takes the same value at any two points of [a,b] -- because the tree has no
;;; term for "the constant that f is".
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([h], h in fun(ccint(a,b), rr) implies
     is-continuous-on(h, ccint(a,b)) implies
     forall([pat_ in ooint(a,b)], has-deriv-at(h, pat_, 0)) implies
     forall([pau_ in ccint(a,b), pav_ in ccint(a,b)], h(pau_) = h(pav_))))"))
(dk-peel!)
(define pw-c215-diff
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the interior differentiability hypothesis"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'extend-const-in-fun 'a 'b 'h)
(define pw-c215-ext '(EXTEND-CONST h a b))
;; the library's own total-function Corollary 2.15 does the three-way case
;; analysis on u, v; the work here is only to put the extension in its terms.
(have! (list 'AND (list 'IN pw-c215-ext '(FUN RR RR))
             '(AND (IN a RR) (AND (IN b RR) (< a b)))))
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS pw-c215-ext 'x)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (fact 'extend-const-continuous-at 'a 'b 'h z)
      (ass))))
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(AND (IN x RR) (AND (< a x) (< x b)))
            (list 'IS-DIFF-AT pw-c215-ext 'x 0)))
  (lambda ()
    (dk-peel!)
    (dk-split-all!)
    (pw-in-ooint! 'x 'a 'b (list '(IN x RR) '(< a x) '(< x b)))
    (dk-apply! pw-c215-diff 'x)
    (fact 'extend-const-deriv-fwd 'a 'b 'h 'x 0)
    (ass)))
(let ((cst (dk-fact! 'deriv-zero-implies-constant pw-c215-ext 'a 'b))
      (uu  (cadr (cadr (dk-goal))))
      (vv  (cadr (caddr (dk-goal)))))
  (fact 'ccint-elt-in-rr 'a 'b uu)
  (fact 'ccint-elt-in-rr 'a 'b vv)
  (have! (list 'AND (list 'IN uu pw-cc) (list 'IN vv pw-cc)))
  (dk-apply! cst uu vv)
  (dk-split-all! (dk-landed* (lambda () (mac-h 'ccint-membership (list 'IN uu pw-cc)))))
  (dk-split-all! (dk-landed* (lambda () (mac-h 'ccint-membership (list 'IN vv pw-cc)))))
  (fact 'extend-const-fixes 'a 'b uu 'h)
  (fact 'extend-const-fixes 'a 'b vv 'h)
  (subst (list '== (list 'h uu) (list pw-c215-ext uu)))
  (subst (list '== (list 'h vv) (list pw-c215-ext vv)))
  (ass))
(qed 'deriv-zero-constant-on-interval)
(topic! 'deriv-zero-constant-on-interval 'analysis)
(alias! 'deriv-zero-constant-on-interval
        "Corollary 2.15"
        "a function on a closed interval whose derivative vanishes inside is constant")

;;; =====================================================================
;;; (5) CONSTANCY OFF A FINITE EXCEPTIONAL SET, BY finite-set-induction.
;;;
;;; The class the induction runs over is
;;;
;;;    { S : for every h continuous on the line, every u < v, if h has
;;;          derivative 0 at every t in (u,v) outside S then h(u) = h(v) }
;;;
;;; with h, u and v QUANTIFIED INSIDE, so that the step may apply the
;;; induction hypothesis to (u,s) and to (s,v) for the same h.
;;; =====================================================================

(define (pw-fin-body sv)
  (list 'FORALL 'pah_
   (list 'IMPLIES '(IN pah_ (FUN RR RR))
   (list 'IMPLIES '(FORALL pax_ (IMPLIES (IN pax_ RR)
                     (IS-CONTINUOUS-AT RR-MS RR-MS pah_ pax_)))
   (list 'FORALL 'pau_
   (list 'IMPLIES '(IN pau_ RR)
   (list 'FORALL 'pav_
   (list 'IMPLIES '(IN pav_ RR)
   (list 'IMPLIES '(< pau_ pav_)
   (list 'IMPLIES
     (list 'FORALL 'pat_
       (list 'IMPLIES '(IN pat_ (OOINT pau_ pav_))
         (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
               '(IS-DIFF-AT pah_ pat_ 0))))
     '(= (pah_ pau_) (pah_ pav_))))))))))))

(define pw-cls (list 'COMP 'pcs_ (pw-fin-body 'pcs_)))

(define pw-fin-stmt
  (list 'FORALL 'pas_
    (list 'IMPLIES '(IN pas_ SET)
      (list 'IMPLIES '(IN (CARD pas_) NN) (pw-fin-body 'pas_)))))

(define pw-base-claim (list 'IN 'EMPTY-SET pw-cls))

(define pw-step-claim
  (list 'FORALL 'pcs_
    (list 'IMPLIES
      (list 'AND '(IN pcs_ SET)
            (list 'AND '(IN (CARD pcs_) NN) (list 'IN 'pcs_ pw-cls)))
      (list 'FORALL 'pcx_
        (list 'IMPLIES (list 'AND '(IN pcx_ SET) '(NOT (IN pcx_ pcs_)))
              (list 'IN '(UNION pcs_ (PAIR pcx_ pcx_)) pw-cls))))))

;;; the derivative universal of the CURRENT goal-body, discriminated on the
;;; exceptional set it names: the induction hypothesis is a FORALL containing
;;; IS-DIFF-AT too.
(define (pw-deriv-univ sv)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-DIFF-AT)
                             (dk-contains? fm 'OOINT)
                             (dk-contains? fm sv)))
           "the derivative universal"))

;;; THE EIGENVARIABLES OF THE CLASS BODY ARE READ OFF THE GOAL, NEVER NAMED.
;;; The body is driven inside a `have!' LANE whose context already holds the
;;; outer proof's own pah_, pau_, pav_, so `di' RENAMES every one of them
;;; (pah__11641 and the like) -- CLAUDE.md, "read eigenvariables off the GOAL".
;;; The goal after the peel is `h(u) = h(v)'.
(define (pw-body-vars)
  (let ((g (dk-goal)))
    (list (car (cadr g)) (cadr (cadr g)) (cadr (caddr g)))))

;;; peel a `forall t in OOINT(lo,hi). not(t in S) => ...' goal and return the
;;; eigenvariable, read off the MEMBERSHIP that landed: `di' lands the guard
;;; and the negation in one call and the order is not the written one.
(define (pw-peel-point! oo)
  (let* ((ls (dk-peel!))
         (m  (car (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                           (equal? (caddr f) oo)))
                          ls))))
    (cadr m)))

;;; the BASE.  S = {} : `not (t in {})' is `empty-set-has-no-members', so the
;;; guard disappears and `pw-zero-deriv-total' closes it.
(define (pw-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (pw-head (dk-goal)) 'IN)
         (begin (fact 'empty-set-is-set) (ass))
         (begin
           (dk-peel!)
           (let* ((vs (pw-body-vars))
                  (hv (car vs)) (uv (cadr vs)) (vv (caddr vs))
                  (dd (pw-deriv-univ 'EMPTY-SET)))
             (dk-have! (list 'FORALL 'pat_
                         (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT uv vv))
                               (list 'IS-DIFF-AT hv 'pat_ 0)))
               (lambda ()
                 (let ((tv (pw-peel-point! (list 'OOINT uv vv))))
                   (fact 'empty-set-has-no-members tv)
                   (dk-apply! dd tv)
                   (ass))))
             (fact 'pw-zero-deriv-total hv uv vv)
             (ass)))))
   (dk-opened (lambda () (comp-mi)))))

;;; t is not in S u {x}, given `not (t in S)' and `not (t = x)': one citation.
(define (pw-not-in-union! t sv xv)
  (fact 'pw-not-in-insert xv sv t))

;;; the STEP.
(define (pw-step!)
  (dk-peel!)
  (dk-split-all!)
  (let* ((g  (dk-goal))                       ; (IN (UNION S {x}) cls)
         (un (cadr g))
         (sv (cadr un))
         (xv (cadr (caddr un))))
    (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
    (fact 'pairing xv xv)
    (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'PAIR xv xv) 'SET)))
    (fact 'union-set-closure sv (list 'PAIR xv xv))
    (fact 'pairing-membership xv xv)
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN sv pw-cls)))
                              (dk-head? 'FORALL))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (pw-head (dk-goal)) 'IN)
             (ass)
             (pw-step-body! ih sv xv)))
       (dk-opened (lambda () (comp-mi)))))))

(define (pw-step-body! ih sv xv)
  (dk-peel!)
  (let* ((vs (pw-body-vars))
         (hv (car vs)) (uv (cadr vs)) (vv (caddr vs))
         (dd (pw-deriv-univ 'UNION))
         (half!
          (lambda (lo hi prems flip)
            ;; the derivative universal on the HALF interval (lo,hi), off S
            (dk-have! (list 'FORALL 'pat_
                        (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT lo hi))
                          (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
                                (list 'IS-DIFF-AT hv 'pat_ 0))))
              (lambda ()
                (let ((tv (pw-peel-point! (list 'OOINT lo hi))))
                  (pw-ooint-in! tv lo hi)
                  (pw-in-ooint! tv uv vv (prems tv))
                  (dk-split-all!
                   (list (if flip (dk-fact! 'pw-lt-ne xv tv)
                                  (dk-fact! 'pw-lt-ne tv xv))))
                  (pw-not-in-union! tv sv xv)
                  (dk-apply! dd tv)
                  (ass)))))))
    (use-em (list 'IN xv (list 'OOINT uv vv))
      ;; ---- the inserted point IS interior: halve the interval ------------
      (lambda ()
        (pw-ooint-in! xv uv vv)
        (half! uv xv
               (lambda (tv) (list (list 'IN tv 'RR) (list 'IN xv 'RR)
                                  (list '< uv tv) (list '< tv xv) (list '< xv vv)))
               #f)
        ;; THE INDUCTION HYPOTHESIS IS INSTANTIATED AT h ONCE.  `dk-apply!'
        ;; lands the whole chain and errors when a call lands NOTHING NEW, so a
        ;; second `(dk-apply! ih hv ...)' -- same first argument -- would die on
        ;; its own first link.  Peel h off once, then apply the result to each
        ;; half separately.
        (let ((ihh (dk-apply! ih hv)))
          (dk-apply! ihh uv xv)
          (half! xv vv
                 (lambda (tv) (list (list 'IN tv 'RR) (list 'IN xv 'RR)
                                    (list '< uv xv) (list '< xv tv) (list '< tv vv)))
                 #t)
          (dk-apply! ihh xv vv))
        (fact 'eq-trans (list hv uv) (list hv xv) (list hv vv))
        (ass))
      ;; ---- the inserted point is OUTSIDE: nothing changes ----------------
      (lambda ()
        (dk-have! (list 'FORALL 'pat_
                    (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT uv vv))
                      (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
                            (list 'IS-DIFF-AT hv 'pat_ 0))))
          (lambda ()
            (let ((tv (pw-peel-point! (list 'OOINT uv vv))))
              (dk-have! (list 'NOT (list '= tv xv))
                (lambda ()
                  (di)
                  (dk-have! (list 'IN xv (list 'OOINT uv vv))
                    (lambda () (subst (list '= xv tv)) (ass)))
                  (ai (list 'NOT (list 'IN xv (list 'OOINT uv vv))))))
              (pw-not-in-union! tv sv xv)
              (dk-apply! dd tv)
              (ass))))
        (dk-apply! ih hv uv vv)
        (ass)))))

(sp (make-wff pw-fin-stmt))
(dk-peel!)
(have! pw-base-claim (lambda () (pw-base!)))
(have! pw-step-claim (lambda () (pw-step!)))
(have! (list 'AND pw-base-claim pw-step-claim))
(let* ((vs  (pw-body-vars))
       (hv  (car vs)) (uv (cadr vs)) (vv (caddr vs))
       (sv  (cadr (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                             (eq? (caddr fm) 'SET)))
                           "the exceptional set typing")))
       (ind (dk-fact! 'finite-set-induction pw-cls)))
  (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'CARD sv) 'NN)))
  (let* ((int  (dk-apply! ind sv))
         (body (dk-landed-find (lambda () (comp-me int)) (dk-head? 'FORALL))))
    (dk-apply! body hv uv vv)
    (ass)))
(qed 'pw-zero-deriv-off-finite-set)
(topic! 'pw-zero-deriv-off-finite-set 'analysis)
(alias! 'pw-zero-deriv-off-finite-set
        "a function whose derivative vanishes off a finite set is constant")

;;; =====================================================================
;;; (6) COROLLARY 4.11 -- THE UNIQUENESS OF THE ENDPOINT DIFFERENCE.
;;;
;;; The difference of the two constant EXTENSIONS is a function on the line;
;;; it is continuous (`sub-continuous-at'), and at every interior point off the
;;; UNION of the two exceptional sets -- a COUNTABLE set, by `countable-union-2',
;;; inside [a,b] and so inside RR -- its derivative is phi(t) - phi(t) = 0
;;; (`deriv-difference').  `zero-deriv-off-countable' (theorem-library/
;;; zero-deriv-off-countable.scm, 20-A; the countable drop-in for section (5),
;;; same argument order, one extra antecedent `S subset RR') then makes it
;;; constant, which is 4.10; 4.11 is one ring identity away.  (Batch 21, R1:
;;; the exceptional set of IS-PRIMITIVE is countable, Dieudonne 8.7.)
;;; =====================================================================

;;; s1 u s2 is inside [a,b] when s1 and s2 are (both inclusions in context).
(define (pw-union-sub! s1 s2)
  (let ((un (list 'UNION s1 s2)))
    (dk-have! (list 'SUBSET un pw-cc)
      (lambda ()
        (let* ((w  (subset-by-element!))
               (um (dk-fact! 'union-membership s1 s2 w)))
          (fact 'subset-mem-fwd s1 pw-cc w)
          (fact 'subset-mem-fwd s2 pw-cc w)
          (dk-only! um
                    (list 'IN w un)
                    (list 'IMPLIES (list 'IN w s1) (list 'IN w pw-cc))
                    (list 'IMPLIES (list 'IN w s2) (list 'IN w pw-cc)))
          (prop))))))

(define pw-hdiff
  '(VNB-LAMBDA x RR (- ((EXTEND-CONST pwf_ a b) x) ((EXTEND-CONST paw_ a b) x))))

;;; the block common to 4.10 and 4.11: both antiderivatives opened, both
;;; extensions typed, the difference lambda typed and continuous, and the
;;; constancy equation H(a) = H(b) landed.  Returns nothing; everything is in
;;; the context.
(define (pw-differ-block!)
  (dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
  (dk-split-all!)
  (dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
  (fact 'rr-leq-reflexive 'a)
  (fact 'rr-leq-reflexive 'b)
  (fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-in-fun 'paw_ 'pphi_ 'a 'b)
  (fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-continuous 'paw_ 'pphi_ 'a 'b)
  (fact 'extend-const-in-fun 'a 'b 'pwf_)
  (fact 'extend-const-in-fun 'a 'b 'paw_)
  (fact 'extend-const-fixes 'a 'b 'a 'pwf_)
  (fact 'extend-const-fixes 'a 'b 'b 'pwf_)
  (fact 'extend-const-fixes 'a 'b 'a 'paw_)
  (fact 'extend-const-fixes 'a 'b 'b 'paw_)
  (pw-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
  (pw-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b)))
  (fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'a)
  (fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'b)
  (fact 'fun-apply-type-c 'paw_ pw-cc 'RR 'a)
  (fact 'fun-apply-type-c 'paw_ pw-cc 'RR 'b)
  ;; the difference of the extensions is a function on the line
  (dk-have! (list 'IN pw-hdiff '(FUN RR RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (pw-head (dk-goal)) 'FORALL))
             (begin (fact 'rr-is-set) (ass))
             (let ((z (dk-di-var!)))
               (fact 'fun-apply-type-c '(EXTEND-CONST pwf_ a b) 'RR 'RR z)
               (fact 'fun-apply-type-c '(EXTEND-CONST paw_ a b) 'RR 'RR z)
               (fact 'rr-sub-in-rr (list '(EXTEND-CONST pwf_ a b) z)
                                   (list '(EXTEND-CONST paw_ a b) z))
               (ass))))
       (dk-opened (lambda () (lam-t))))))
  ;; ... and is continuous everywhere
  (dk-have! (list 'FORALL 'pax_ (list 'IMPLIES '(IN pax_ RR)
              (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS pw-hdiff 'pax_)))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'extend-const-continuous-at 'a 'b 'pwf_ z)
        (fact 'extend-const-continuous-at 'a 'b 'paw_ z)
        (fact 'sub-continuous-at '(EXTEND-CONST pwf_ a b) '(EXTEND-CONST paw_ a b) z)
        (ass))))
  ;; the two exceptional sets, and their union
  (let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                   'pwf_ 'pphi_ 'a 'b)))
         (d1 (begin (dk-split-all!)
                    (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                               (dk-contains? fm 'HAS-DERIV-AT)
                                               (dk-contains? fm s1)))
                             "the first derivative universal")))
         (s2 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                   'paw_ 'pphi_ 'a 'b)))
         (d2 (begin (dk-split-all!)
                    (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                               (dk-contains? fm 'HAS-DERIV-AT)
                                               (dk-contains? fm s2)))
                             "the second derivative universal")))
         (un (list 'UNION s1 s2)))
    ;; the union of the two exceptional sets is COUNTABLE and lies in RR.
    (fact 'countable-union-2 s1 s2)
    (pw-union-sub! s1 s2)
    (fact 'ccint-subset-rr 'a 'b)
    (fact 'subset-trans un pw-cc 'RR)
    (fact 'ooint-subset-ccint 'a 'b)
    (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
                (list 'IMPLIES (list 'NOT (list 'IN 'pat_ un))
                      (list 'IS-DIFF-AT pw-hdiff 'pat_ 0))))
      (lambda ()
        (dk-peel!)
        (let ((um (dk-fact! 'union-membership s1 s2 'pat_)))
          (dk-have! (list 'NOT (list 'IN 'pat_ s1))
            (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop)))
          (dk-have! (list 'NOT (list 'IN 'pat_ s2))
            (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop))))
        (fact 'subset-mem-fwd '(OOINT a b) pw-cc 'pat_)
        (fact 'fun-apply-type-c 'pphi_ pw-cc 'RR 'pat_)
        (dk-apply! d1 'pat_)
        (dk-apply! d2 'pat_)
        (fact 'extend-const-deriv-fwd 'a 'b 'pwf_ 'pat_ '(pphi_ pat_))
        (fact 'extend-const-deriv-fwd 'a 'b 'paw_ 'pat_ '(pphi_ pat_))
        (fact 'deriv-difference '(EXTEND-CONST pwf_ a b) '(EXTEND-CONST paw_ a b)
              'pat_ '(pphi_ pat_) '(pphi_ pat_))
        (dk-have! '(= 0 (- (pphi_ pat_) (pphi_ pat_))) (lambda () (crs)))
        (subst '(= 0 (- (pphi_ pat_) (pphi_ pat_))))
        (ass)))
    (fact 'zero-deriv-off-countable un pw-hdiff 'a 'b))
  ;; the two endpoint values of the difference
  (dk-have! (list '= (list pw-hdiff 'a) '(- (pwf_ a) (paw_ a)))
    (lambda ()
      (dk-lam-b!)
      (subst '(== ((EXTEND-CONST pwf_ a b) a) (pwf_ a)))
      (subst '(== ((EXTEND-CONST paw_ a b) a) (paw_ a)))
      (rfl)))
  (dk-have! (list '= (list pw-hdiff 'b) '(- (pwf_ b) (paw_ b)))
    (lambda ()
      (dk-lam-b!)
      (subst '(== ((EXTEND-CONST pwf_ a b) b) (pwf_ b)))
      (subst '(== ((EXTEND-CONST paw_ a b) b) (paw_ b)))
      (rfl)))
  (dk-have! '(= (- (pwf_ a) (paw_ a)) (- (pwf_ b) (paw_ b)))
    (lambda ()
      (subst (list '= '(- (pwf_ a) (paw_ a)) (list pw-hdiff 'a)))
      (subst (list '= '(- (pwf_ b) (paw_ b)) (list pw-hdiff 'b)))
      (ass))))


;;; COROLLARY 4.11 -- the uniqueness obligation of PW-INT.
;;;
;;;   "If f, g are antiderivatives of phi on the interval [a,b] then
;;;    f(b) - f(a) = g(b) - g(a)."
(sp (make-wff "forall([pwf_, paw_, pphi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   is-primitive(paw_, pphi_, a, b) implies
   pwf_(b) - pwf_(a) = paw_(b) - paw_(a))"))
(dk-peel!)
(pw-differ-block!)
(dk-have! '(= (pwf_ b) (+ (paw_ b) (- (pwf_ a) (paw_ a))))
  (lambda ()
    (subst '(= (- (pwf_ a) (paw_ a)) (- (pwf_ b) (paw_ b))))
    (crs)))
(subst '(= (pwf_ b) (+ (paw_ b) (- (pwf_ a) (paw_ a)))))
(crs)
(qed 'pw-antiderivative-endpoint-difference)
(topic! 'pw-antiderivative-endpoint-difference 'analysis)
(alias! 'pw-antiderivative-endpoint-difference
        "Corollary 4.11"
        "two piecewise antiderivatives have the same endpoint difference")

;;; =====================================================================
;;; (7) PW-INT.  THE VALUE THEOREM, UNCONDITIONAL.
;;;
;;; PW-INT is a definite description, so `iota-d' posts TWO obligations:
;;; EXISTENCE, which the given antiderivative discharges, and UNIQUENESS,
;;; which is Corollary 4.11 above.  Both are now theorems, so the only
;;; hypothesis left is the one that earns the definedness of the IOTA: that
;;; phi HAS a piecewise antiderivative.
;;; =====================================================================
(define (pw-diff f) (list '- (list f 'b) (list f 'a)))

(define (pw-obtain!)
  (let ((z (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
    (dk-landed* (lambda () (dk-split! z)))))

(define (pw-witness parts)
  (cadr (car (filter (dk-head? 'IS-PRIMITIVE) parts))))

(define (pw-int-typings!)
  (dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
  (dk-split-all!)
  (fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
  (fact 'rr-leq-reflexive 'a)
  (fact 'rr-leq-reflexive 'b)
  (fact 'rr-lt-implies-le 'a 'b)
  (pw-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
  (pw-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b)))
  (fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'a)
  (fact 'fun-apply-type-c 'pwf_ pw-cc 'RR 'b)
  (fact 'rr-sub-in-rr '(pwf_ b) '(pwf_ a)))

(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PRIMITIVE pwf_ pphi_ a b)
            (= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))))))))
(dk-peel-to! '=)
(pw-int-typings!)
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
                    (fact 'pw-antiderivative-endpoint-difference g 'pwf_ 'pphi_ 'a 'b)
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
           (fact 'pw-antiderivative-endpoint-difference g 'pwf_ 'pphi_ 'a 'b)
           (fact 'eq-trans pw-io (pw-diff g) (pw-diff 'pwf_))
           (ass)))))
 (dk-opened (lambda () (iota-d pw-io))))
(qed 'pw-int-value)
(topic! 'pw-int-value 'analysis)
(alias! 'pw-int-value
        "equation (64)"
        "the piecewise integral is F(b) - F(a) for any piecewise antiderivative F")

;;; pw-int-in-rr: the integral is a REAL wherever it is defined.  One `subst'
;;; off pw-int-value.
(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
   (IMPLIES (IS-PRIMITIVE pwf_ pphi_ a b)
            (IN (PW-INT pphi_ a b) RR))))))))
(dk-peel-to! 'IN)
(pw-int-typings!)
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(subst (list '= '(PW-INT pphi_ a b) (pw-diff 'pwf_)))
(ass)
(qed 'pw-int-in-rr)
(topic! 'pw-int-in-rr 'analysis)
(alias! 'pw-int-in-rr "the piecewise integral of an antiderivable function is a real")

;;; =====================================================================
;;; (8) CONGRUENCE.  The exceptional set makes the integrand's values on it
;;; irrelevant, and more generally a POINTWISE equality of integrands carries
;;; a piecewise antiderivative -- and therefore the integral -- across.
;;; =====================================================================
(sp (make-wff "forall([pwf_, pphi_, ppsi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   ppsi_ in fun(ccint(a,b), rr) implies
   forall([pay_ in ccint(a,b)], pphi_(pay_) == ppsi_(pay_)) implies
   is-primitive(pwf_, ppsi_, a, b))"))
(dk-peel!)
(define pw-cg-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pphi_) (dk-contains? fm 'ppsi_)))
           "the pointwise agreement"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'ooint-subset-ccint 'a 'b)
(let* ((sv (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'pwf_ 'pphi_ 'a 'b)))
       (dv (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)))
                           "the derivative universal"))))
  (mac 'IS-PRIMITIVE)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (pw-head (dk-goal)) 'FORSOME))
         (ass)
         (begin
           (ew sv)
           (dk-conj-close!
            (lambda ()
              (if (not (eq? (pw-head (dk-goal)) 'FORALL))
                  (ass)
                  (begin
                    (dk-peel!)
                    (let ((tv (caddr (dk-goal))))
                      (fact 'subset-mem-fwd '(OOINT a b) pw-cc tv)
                      (dk-apply! pw-cg-agree tv)
                      (dk-apply! dv tv)
                      (subst (list '== (list 'ppsi_ tv) (list 'pphi_ tv)))
                      (ass)))))))))))
(qed 'pw-antiderivative-integrand-congruence)
(topic! 'pw-antiderivative-integrand-congruence 'analysis)
(alias! 'pw-antiderivative-integrand-congruence
        "a piecewise antiderivative survives a pointwise change of integrand")

(sp (make-wff "forall([pwf_, pphi_, ppsi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   ppsi_ in fun(ccint(a,b), rr) implies
   forall([pay_ in ccint(a,b)], pphi_(pay_) == ppsi_(pay_)) implies
   pw-int(pphi_, a, b) = pw-int(ppsi_, a, b))"))
(dk-peel!)
(fact 'pw-antiderivative-integrand-congruence 'pwf_ 'pphi_ 'ppsi_ 'a 'b)
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-int-value 'pwf_ 'ppsi_ 'a 'b)
(subst (list '= '(PW-INT pphi_ a b) (pw-diff 'pwf_)))
(subst (list '= '(PW-INT ppsi_ a b) (pw-diff 'pwf_)))
(pw-int-typings!)
(rfl)
(qed 'pw-int-congruence)
(topic! 'pw-int-congruence 'analysis)
(alias! 'pw-int-congruence
        "the piecewise integral depends only on the pointwise values of the integrand")

;;; =====================================================================
;;; (9) THE INTRODUCTION RULE.  A function differentiable at EVERY interior
;;; point is a piecewise antiderivative -- the exceptional set is EMPTY
;;; (`countable-empty').
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pwf_, pphi_],
    pwf_ in fun(ccint(a,b), rr) implies
    pphi_ in fun(ccint(a,b), rr) implies
    is-continuous-on(pwf_, ccint(a,b)) implies
    forall([pat_ in ooint(a,b)], has-deriv-at(pwf_, pat_, pphi_(pat_))) implies
    is-primitive(pwf_, pphi_, a, b)))"))
(dk-peel!)
(define pw-ip-univ
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the interior differentiability universal"))
(fact 'countable-empty)
(fact 'empty-subset-any pw-cc)
(mac 'IS-PRIMITIVE)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (pw-head (dk-goal)) 'FORSOME))
       (ass)
       (begin
         (ew 'EMPTY-SET)
         (dk-conj-close!
          (lambda ()
            (if (not (eq? (pw-head (dk-goal)) 'FORALL))
                (ass)
                (begin
                  (dk-peel!)
                  (let ((tv (caddr (dk-goal))))
                    (dk-apply! pw-ip-univ tv)
                    (ass))))))))))
(qed 'pw-antiderivative-one-piece)
(topic! 'pw-antiderivative-one-piece 'analysis)
(alias! 'pw-antiderivative-one-piece
        "a function differentiable at every interior point is a piecewise antiderivative")

;;; =====================================================================
;;; (10) CONTINUITY ON THE INTERVAL FROM CONTINUITY ON THE LINE.  A function
;;; on [a,b] that agrees pointwise with a function continuous on the whole
;;; line is continuous on [a,b] IN THE SUBSPACE SENSE -- which is what
;;; IS-CONTINUOUS-ON means and what the witness below has to supply.
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
;;; (11) THE WITNESS.  AN AFFINE FUNCTION ON [a,b] IS A PIECEWISE
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
    is-primitive(pwf_, pphi_, a, b)))"))
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
;;; (12) THE INTEGRAL OF A CONSTANT.  The first computation the definition
;;; permits, and the one every estimate starts from.
;;; =====================================================================
(define pw-lin '(VNB-LAMBDA pkz_ (CCINT a b) (* pac_ pkz_)))

(sp (make-wff "forall([a in rr, b in rr], a < b implies
  forall([pac_ in rr, pphi_],
    pphi_ in fun(ccint(a,b), rr) implies
    forall([pay_ in ccint(a,b)], pphi_(pay_) == pac_) implies
    pw-int(pphi_, a, b) = pac_ * (b - a)))"))
(dk-peel!)
(fact 'rr-zero-in)
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(pw-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
(pw-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b)))
(dk-have! (list 'IN pw-lin (list 'FUN pw-cc 'RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pw-head (dk-goal)) 'FORALL))
           (begin (fact 'rr-is-set) (fact 'ccint-subset-rr 'a 'b)
                  (fact 'subclass-of-set-is-set pw-cc 'RR) (ass))
           (let ((z (dk-di-var!)))
             (fact 'ccint-elt-in-rr 'a 'b z)
             (have! (list 'AND '(IN pac_ RR) (list 'IN z 'RR)))
             (fact 'rr-mul-closed 'pac_ z)
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pw-cc)
            (list '== (list pw-lin 'pay_) '(+ 0 (* pac_ pay_)))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (dk-lam-b!)
      (have! (list '= (list '+ 0 (list '* 'pac_ z)) (list '* 'pac_ z))
             (lambda () (crs)))
      (subst (list '= (list '+ 0 (list '* 'pac_ z)) (list '* 'pac_ z)))
      (qrfl))))
(fact 'pw-affine-antiderivative 'a 'b 0 'pac_ pw-lin 'pphi_)
(fact 'pw-int-value pw-lin 'pphi_ 'a 'b)
(subst (list '= '(PW-INT pphi_ a b) (pw-diff pw-lin)))
(dk-lam-b!)
(crs)
(qed 'pw-int-const)
(topic! 'pw-int-const 'analysis)
(alias! 'pw-int-const "the piecewise integral of a constant is the constant times the length")

;;; =====================================================================
;;; (13) PROPOSITIONS 4.12 / 4.13 -- ADDITIVITY.
;;;
;;;   "If f, g are antiderivatives of phi, psi respectively, then f + g is an
;;;    antiderivative of phi + psi"   (4.13)
;;;
;;; The tree has no addition on FUN(A, RR), so the sum is a GIVEN function
;;; agreeing pointwise with it -- the shape every rule of
;;; interval-calculus-laws.scm section (8) uses, and the shape the caller
;;; always has in hand.  Continuity of the sum on the interval goes through the
;;; two constant EXTENSIONS and `sum-continuous-at' on the line; the derivative
;;; off the union of the two exceptional sets is `has-deriv-at-sum'.
;;; =====================================================================
(define pw-hsum
  '(VNB-LAMBDA x RR (+ ((EXTEND-CONST pwf_ a b) x) ((EXTEND-CONST paw_ a b) x))))

;;; THE BINDERS a AND b ARE GUARDED, and they come FIRST.  With EIGHT adjacent
;;; unguarded FORALLs `fact' mis-instantiates the last one (the residue reads
;;; `ccint(a, a)'), and so does `inst*!'; a guard between the binders is the
;;; shape every other statement in the library has.
(sp (make-wff "forall([a in rr, b in rr],
   forall([pwf_, paw_, pphi_, ppsi_],
     is-primitive(pwf_, pphi_, a, b) implies
     is-primitive(paw_, ppsi_, a, b) implies
     forall([pauh_ in fun(ccint(a,b), rr), pchi_ in fun(ccint(a,b), rr)],
       forall([pay_ in ccint(a,b)], pauh_(pay_) == pwf_(pay_) + paw_(pay_)) implies
       forall([pay_ in ccint(a,b)], pchi_(pay_) == pphi_(pay_) + ppsi_(pay_)) implies
       is-primitive(pauh_, pchi_, a, b) and
       pw-int(pchi_, a, b) = pw-int(pphi_, a, b) + pw-int(ppsi_, a, b))))"))
(dk-peel!)
(define pw-sum-hagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pauh_)))
           "the pointwise sum of the primitives"))
(define pw-sum-cagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)))
           "the pointwise sum of the integrands"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set pw-cc 'RR)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-in-fun 'paw_ 'ppsi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'paw_ 'ppsi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'paw_ 'ppsi_ 'a 'b)
(fact 'extend-const-in-fun 'a 'b 'pwf_)
(fact 'extend-const-in-fun 'a 'b 'paw_)
(fact 'ooint-subset-ccint 'a 'b)
;; the total sum of the two extensions, and its continuity
(dk-have! (list 'IN pw-hsum '(FUN RR RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (pw-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'fun-apply-type-c '(EXTEND-CONST pwf_ a b) 'RR 'RR z)
             (fact 'fun-apply-type-c '(EXTEND-CONST paw_ a b) 'RR 'RR z)
             (have! (list 'AND (list 'IN (list '(EXTEND-CONST pwf_ a b) z) 'RR)
                          (list 'IN (list '(EXTEND-CONST paw_ a b) z) 'RR)))
             (fact 'rr-add-closed (list '(EXTEND-CONST pwf_ a b) z)
                                  (list '(EXTEND-CONST paw_ a b) z))
             (ass))))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'FORALL 'pax_ (list 'IMPLIES '(IN pax_ RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS pw-hsum 'pax_)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'extend-const-continuous-at 'a 'b 'pwf_ z)
      (fact 'extend-const-continuous-at 'a 'b 'paw_ z)
      (fact 'sum-continuous-at '(EXTEND-CONST pwf_ a b) '(EXTEND-CONST paw_ a b) z)
      (ass))))
;; ... and it agrees with pauh_ on [a,b], so pauh_ is continuous there
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pw-cc)
            (list '== (list 'pauh_ 'pay_) (list pw-hsum 'pay_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      ;; the agreement is cited BEFORE `mac-h' consumes the membership.
      (dk-apply! pw-sum-hagree z)
      (dk-split-all! (dk-landed* (lambda ()
        (mac-h 'ccint-membership (list 'IN z pw-cc)))))
      (fact 'extend-const-fixes 'a 'b z 'pwf_)
      (fact 'extend-const-fixes 'a 'b z 'paw_)
      (dk-lam-b!)
      (subst (list '== (list '(EXTEND-CONST pwf_ a b) z) (list 'pwf_ z)))
      (subst (list '== (list '(EXTEND-CONST paw_ a b) z) (list 'paw_ z)))
      (ass))))
(fact 'pw-restrict-continuous-on 'a 'b pw-hsum 'pauh_)
;; the derivative off the union of the two exceptional sets
(let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'pwf_ 'pphi_ 'a 'b)))
       (d1 (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)
                                             (dk-contains? fm s1)))
                           "the first derivative universal")))
       (s2 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'paw_ 'ppsi_ 'a 'b)))
       (d2 (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)
                                             (dk-contains? fm s2)))
                           "the second derivative universal")))
       (un (list 'UNION s1 s2)))
  (fact 'countable-union-2 s1 s2)
  (pw-union-sub! s1 s2)
  (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
              (list 'IMPLIES (list 'NOT (list 'IN 'pat_ un))
                    '(HAS-DERIV-AT pauh_ pat_ (pchi_ pat_)))))
    (lambda ()
      (dk-peel!)
      (let ((um (dk-fact! 'union-membership s1 s2 'pat_)))
        (dk-have! (list 'NOT (list 'IN 'pat_ s1))
          (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop)))
        (dk-have! (list 'NOT (list 'IN 'pat_ s2))
          (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop))))
      (fact 'subset-mem-fwd '(OOINT a b) pw-cc 'pat_)
      (fact 'fun-apply-type-c 'pphi_ pw-cc 'RR 'pat_)
      (fact 'fun-apply-type-c 'ppsi_ pw-cc 'RR 'pat_)
      (dk-apply! d1 'pat_)
      (dk-apply! d2 'pat_)
      (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b 'pat_))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr rv)
        (fact 'rr-sub-in-rr 'pat_ rv)
        (fact 'rr-add-in-rr 'pat_ rv)
        (let ((oo (list 'OOINT (list '- 'pat_ rv) (list '+ 'pat_ rv))))
          (fact 'restrict-in-fun 'pauh_ pw-cc 'RR oo)
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ oo)
                      (list '== '(pauh_ hbx_) '(+ (pwf_ hbx_) (paw_ hbx_)))))
            (lambda ()
              (let ((y (dk-di-var!)))
                (fact 'subset-mem-fwd oo pw-cc y)
                (dk-apply! pw-sum-hagree y)
                (ass))))
          (fact 'has-deriv-at-sum rv 'pwf_ 'paw_ 'pauh_ 'pat_
                '(pphi_ pat_) '(ppsi_ pat_))
          (dk-apply! pw-sum-cagree 'pat_)
          (subst (list '== '(pchi_ pat_) '(+ (pphi_ pat_) (ppsi_ pat_))))
          (ass)))))
  (dk-have! '(IS-PRIMITIVE pauh_ pchi_ a b)
    (lambda ()
      (mac 'IS-PRIMITIVE)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (pw-head (dk-goal)) 'FORSOME))
             (ass)
             (begin
               (ew un)
               (dk-conj-close! (lambda () (ass))))))))))
;;; THE INTEGRAL IDENTITY IS A CONJUNCT OF THIS THEOREM, not a corollary.
;;; FINDING (2026-09-22): stated separately it could not be CITED -- `fact'
;;; with eight instantiation terms gives the LAST binder the FIRST term (the
;;; residue reads `ccint(a, a)'), and so does the `inst*!' behind `dk-apply!',
;;; with guards between the binders and with binder names distinct from the
;;; terms.  Everything the corollary needs is in this context already.
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-int-value 'paw_ 'ppsi_ 'a 'b)
(fact 'pw-int-value 'pauh_ 'pchi_ 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(pw-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
(pw-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b)))
(for-each (lambda (f)
            (fact 'fun-apply-type-c f pw-cc 'RR 'a)
            (fact 'fun-apply-type-c f pw-cc 'RR 'b))
          '(pwf_ paw_ pauh_))
(dk-apply! pw-sum-hagree 'a)
(dk-apply! pw-sum-hagree 'b)
(dk-conj-close!
 (lambda ()
   (if (eq? (pw-head (dk-goal)) 'IS-PRIMITIVE)
       (ass)
       (begin
         (subst '(= (PW-INT pchi_ a b) (- (pauh_ b) (pauh_ a))))
         (subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
         (subst '(= (PW-INT ppsi_ a b) (- (paw_ b) (paw_ a))))
         (subst '(== (pauh_ a) (+ (pwf_ a) (paw_ a))))
         (subst '(== (pauh_ b) (+ (pwf_ b) (paw_ b))))
         (crs)))))
(qed 'pw-antiderivative-sum)
(topic! 'pw-antiderivative-sum 'analysis)
(alias! 'pw-antiderivative-sum
        "Propositions 4.12 and 4.13"
        "the sum of two piecewise antiderivatives is one of the sum, and the integral is additive")

