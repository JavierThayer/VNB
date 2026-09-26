;;; one-sided-derivative.scm -- THE ONE-SIDED DERIVATIVES OF THE USER'S NOTES,
;;; section 2.1.  DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/one-sided-derivative-laws.scm.
;;;
;;; THE SOURCE (Supplements to Calculus, chapter 2, section 1, equations (5)
;;; and (6)):
;;;
;;;     A function f defined at a is RIGHT DIFFERENTIABLE if and only if f is
;;;     defined on some interval [a, x) for x > a and the limit
;;;
;;;   (5)          lim_{theta down a} ( f(theta) - f(a) ) / ( theta - a )
;;;
;;;     exists.  The limit is the right derivative of f at a.  Left
;;;     differentiability is defined in an analogous way:
;;;
;;;   (6)          lim_{theta up a} ( f(theta) - f(a) ) / ( theta - a ).
;;;
;;;     The right derivative at x is denoted [D+ f](x), the left derivative
;;;     [D- f](x).
;;;
;;; and then differentiability at x BY CASES: (1) if f is defined in a
;;; neighbourhood (x - r, x + r), f is differentiable at x if and only if f is
;;; both right and left differentiable and the two one-sided derivatives are
;;; identical; (2) if f is defined on [x, x + r) only, f is differentiable at x
;;; if and only if f is right differentiable at x, and on (x - r, x] likewise
;;; with the left derivative.
;;;
;;; WHAT IS DEFINED HERE
;;;
;;;     COINT(a, b)                  [a, b) = { t in RR : a <= t and t < b }
;;;     OCINT(a, b)                  (a, b] = { t in RR : a < t and t <= b }
;;;     HAS-DERIV-AT-WITHIN(f, W, x, l)
;;;                                  f has derivative l at x WITHIN the set W
;;;     HAS-RIGHT-DERIV-AT(f, x, l)  [D+ f](x) = l   -- (5)
;;;     HAS-LEFT-DERIV-AT(f, x, l)   [D- f](x) = l   -- (6)
;;;
;;; ---------------------------------------------------------------------
;;; WHY THE CARATHEODORY FORM, AND WHY A SEPARATE `WITHIN' PREDICATE.
;;;
;;; The notes' (5) is a one-sided LIMIT of the difference quotient.  Every
;;; derivative in this library is instead written in CARATHEODORY's form --
;;; there is a factor phi, continuous at the point, with phi(x) = l and
;;;
;;;     f(t) - f(x)  =  phi(t) . (t - x)      for every t of the window
;;;
;;; (IS-DIFF-AT, structure-library/derivative.scm; IS-DIFF-ON,
;;; structure-library/diff-on.scm; HAS-DERIV-AT, structure-library/interval-
;;; calculus.scm).  The form is equivalent to the limit, carries no division,
;;; and is purely equational, so the sum and scalar rules are rewriting rather
;;; than eps/delta.  Stating the one-sided derivatives in the SAME form is what
;;; lets the existing laws transport instead of being redone.
;;;
;;; IS-DIFF-ON CANNOT BE REUSED HERE: its domain U is OPEN by definition (the
;;; user's decision of 2026-09-20), and a half-window [x, x + eps) is not open.
;;; HAS-DERIV-AT cannot be reused either -- it is the local closure of
;;; IS-DIFF-ON and therefore also asks for a two-sided neighbourhood.  So the
;;; Caratheodory package is written out once, over an ARBITRARY set W, as
;;; HAS-DERIV-AT-WITHIN, and the right and left derivatives are that one
;;; predicate at W = [x, x + eps) and W = (x - eps, x].  The alternative -- two
;;; predicates each spelling the package out, with every lemma proven twice --
;;; was rejected: shrinking, uniqueness, locality, the sum rule, the scalar
;;; rule and the two sentences of Proposition 2.10 are each ONE theorem about
;;; HAS-DERIV-AT-WITHIN and two four-line corollaries.  The same predicate also
;;; carries HAS-DERIV-AT itself, over W = (x - eps, x + eps)
;;; (`has-deriv-at-iff-within-ooint'), which is what makes the notes' case (1)
;;; a statement about three instances of ONE notion.
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT CHECKS.  Each of the species CLAUDE.md lists, against these
;;; four definitions.
;;;
;;; (a) W IS NOT OPEN, and nothing below asks it to be.  The continuity of the
;;;     factor is continuity as a map off the metric SUBSPACE
;;;     SUBSPACE-MS(RR-MS, W) -- whose points are exactly W (`subspace-pts')
;;;     and whose distance is the ambient one (`subspace-dist') -- so at
;;;     x = a only the points of W are ever tested, which is precisely the
;;;     one-sided reading of (5).  No ball of RR need lie inside W.
;;;
;;; (b) THE DOMAIN OF f.  `f is defined on some interval [a, x)' is
;;;     `RESTRICT(f, W) in FUN(W, RR)'.  RESTRICT(f, W) is
;;;     (VNB-LAMBDA rsx_ W (f rsx_)); if some point of W is outside the domain
;;;     of f, that lambda is not a member of FUN(W, RR) and the conjunct is
;;;     FALSE.  So a function whose domain misses part of the window makes the
;;;     predicate FALSE, not undefined -- and nothing here is an equation
;;;     between terms that might not denote: the universal's body is guarded by
;;;     (IN ost_ W) and every term in it is then typed.  It is stated on the
;;;     RESTRICTION and not on f, exactly as HAS-DERIV-AT is, because f is a
;;;     function on a larger set (the notes' f is a function on [a, b]) and
;;;     `f in FUN(W, RR)' would be the false statement that f is defined
;;;     EXACTLY on the window.
;;;
;;; (c) THE POINT IS IN THE WINDOW.  (IN x W) is a conjunct, as (IN a U) is a
;;;     conjunct of IS-DIFF-ON.  It is not redundant decoration: phi(x) is
;;;     applied in the next conjunct, and for W = COINT(x, x + eps) it is what
;;;     ties the two one-sided definitions to a REAL x -- `x in RR' is then a
;;;     read-off (`has-right-deriv-at-pt-in-rr'), not an assumption.
;;;
;;; (d) eps IS ONLY EXISTENTIAL, as in the notes (`some interval [a, x)').  The
;;;     value of the derivative does not depend on it: `deriv-within-shrink'
;;;     says the package survives passing to any smaller window that still
;;;     contains x, and `has-right-deriv-at-unique' says l is determined.
;;;
;;; (e) l in RR is a conjunct.  Without it `phi(x) = l' would be the only thing
;;;     typing l, and a strict `=' whose right-hand side is untyped asserts the
;;;     definedness of the left-hand side -- the species `finsum-congruence'
;;;     was found under.  With it, every atom is typed.
;;;
;;; (f) THE EMPTY AND DEGENERATE CASES.  COINT(a, b) and OCINT(a, b) are SEPs
;;;     over RR: both are EMPTY when b <= a, and when a or b is not a real.
;;;     That is the fact, not a defect, and no theorem below carries an
;;;     `a < b' guard for it.  For the two one-sided predicates the window is
;;;     COINT(x, x + eps) with eps > 0, so it is inhabited exactly when x is a
;;;     real, and (IN x W) then holds -- which is (c).
;;;
;;; (g) NO FINITENESS, NO CHOICE, NO IOTA, NO succ, NO dimension: none of the
;;;     remaining species can arise here.
;;;
;;; ---------------------------------------------------------------------
;;; BINDER NAMES.  `osq_' (the separation variable), `ose_' (the radius),
;;; `osp_' (the factor), `ost_' (the running point).  None folds onto a
;;; registered constant, a class name (NN ZZ QQ RR CC ORD SET EMPTY-SET ...) or
;;; a structure accessor, and none is a name a driver instantiates at or a
;;; predicate body binds -- a functoid or predicate body whose binder is
;;; spelled like an eigenvariable gets capture-renamed by `subst-free', after
;;; which every `equal?' lookup of the rebuilt term matches nothing, silently
;;; (CLAUDE.md, "Writing proof drivers").  The parameters are f, W, x and l.
;;;
;;; Dependencies: metric-subspace.scm (SUBSPACE-MS, RESTRICT),
;;; metric-continuity.scm (IS-CONTINUOUS-AT), numeric-instances.scm (RR-MS),
;;; order-predicates.scm (POS-RR), fun.scm (FUN).  Nothing is proven here, and
;;; nothing here depends on interval-calculus.scm: this file may load anywhere
;;; after those four.

;;; -----------------------------------------------------------------------
;;; The two half-open intervals.  CCINT (extreme-value.scm) is [a, b] and
;;; OOINT (interval-calculus.scm) is (a, b); these are the remaining two.

(def-functoid 'COINT '(a b)
  '(SEP osq_ RR (AND (<= a osq_) (< osq_ b))))

(notation! 'COINT 'kind 'functoid 'arity 2
           'english "the interval from $1 included to $2 excluded")

(def-functoid 'OCINT '(a b)
  '(SEP osq_ RR (AND (< a osq_) (<= osq_ b))))

(notation! 'OCINT 'kind 'functoid 'arity 2
           'english "the interval from $1 excluded to $2 included")

;;; -----------------------------------------------------------------------
;;; The derivative at a point WITHIN a set: the Caratheodory package over an
;;; arbitrary window W.  The three derivatives of this file and HAS-DERIV-AT
;;; itself are its instances.

(def-predicate 'HAS-DERIV-AT-WITHIN '(f W x l)
  '(AND (IN (RESTRICT f W) (FUN W RR))
   (AND (IN x W)
   (AND (IN l RR)
        (FORSOME osp_
          (AND (IN osp_ (FUN W RR))
          (AND (IS-CONTINUOUS-AT (SUBSPACE-MS RR-MS W) RR-MS osp_ x)
          (AND (= (osp_ x) l)
               (FORALL ost_
                 (IMPLIES (IN ost_ W)
                   (= (- (f ost_) (f x))
                      (* (osp_ ost_) (- ost_ x)))))))))))))

(notation! 'HAS-DERIV-AT-WITHIN 'kind 'predicate 'arity 4
           'english "$1 has derivative $4 at $3 within $2")

;;; -----------------------------------------------------------------------
;;; The right derivative -- the notes' (5).  `f is defined on some interval
;;; [a, x) for x > a' is the existential radius; the limit is the Caratheodory
;;; factor.

(def-predicate 'HAS-RIGHT-DERIV-AT '(f x l)
  '(FORSOME ose_
     (AND (POS-RR ose_)
          (HAS-DERIV-AT-WITHIN f (COINT x (+ x ose_)) x l))))

(notation! 'HAS-RIGHT-DERIV-AT 'kind 'predicate 'arity 3
           'english "$1 has right derivative $3 at $2")

;;; -----------------------------------------------------------------------
;;; The left derivative -- the notes' (6).

(def-predicate 'HAS-LEFT-DERIV-AT '(f x l)
  '(FORSOME ose_
     (AND (POS-RR ose_)
          (HAS-DERIV-AT-WITHIN f (OCINT (- x ose_) x) x l))))

(notation! 'HAS-LEFT-DERIV-AT 'kind 'predicate 'arity 3
           'english "$1 has left derivative $3 at $2")
