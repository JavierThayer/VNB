;;; interval-calculus.scm -- THE VOCABULARY OF THE CALCULUS ON AN INTERVAL.
;;; DEFINITIONS ONLY; every law is PROVEN in
;;; theorem-library/interval-calculus-laws.scm and interval-mvt.scm.
;;;
;;; THE SPECIFICATION is docs/real-calculus-statements.tex, section 2.  The
;;; user's rule of 2026-09-21: a theorem is stated the way his notes state it.
;;; The notes (Supplements to Calculus, 2.11-2.13, 2.18, chapters 4 and 5) put
;;; a function ON its interval -- f is a function on [a,b], continuous on
;;; [a,b], differentiable on (a,b).  In this system a member of FUN(A,B) is
;;; defined EXACTLY on A, so `f in FUN(RR,RR) with a and b as parameters' is a
;;; DIFFERENT statement, and it is the one the library had.  These four
;;; definitions are what is needed to state the notes' version.
;;;
;;;     OOINT(a, b)             the open interval (a, b)
;;;     IS-CONTINUOUS-ON(f, D)  f, a function on D, is continuous at every
;;;                             point of D, as a map SUBSPACE-MS(RR-MS, D) -> RR-MS
;;;     HAS-DERIV-AT(f, a, L)   f has derivative L at a -- a LOCAL notion, asking
;;;                             nothing of f outside a neighbourhood of a
;;;     EXTEND-CONST(f, a, b)   f in FUN(CCINT(a,b), RR) extended to RR by the
;;;                             constants f(a) below a and f(b) above b
;;;
;;; ---------------------------------------------------------------------
;;; WHY HAS-DERIV-AT IS NOT IS-DIFF-AT, AND NOT IS-DIFF-ON EITHER.
;;;
;;; IS-DIFF-AT (structure-library/derivative.scm) asks for f in FUN(RR, RR):
;;; a function on the interval is not one.  IS-DIFF-ON (structure-library/
;;; diff-on.scm) asks for an OPEN domain U and for f in FUN(U, CARR K): a
;;; function on the CLOSED interval is not one of those either, and the notes
;;; differentiate a function on [a,b] at the interior points.  HAS-DERIV-AT is
;;; the local closure of IS-DIFF-ON: f is differentiable at a with derivative L
;;; when SOME open interval around a is inside the domain of f and the
;;; restriction of f to it is differentiable at a in the sense of IS-DIFF-ON.
;;;
;;; THE PREDICATE IS FALSE, NOT UNDEFINED, WHEN THE DOMAIN OF f MISSES A
;;; NEIGHBOURHOOD OF a.  RESTRICT(f, U) is (VNB-LAMBDA rsx_ U (f rsx_)); if
;;; some point of U is outside the domain of f, that lambda is not a member of
;;; FUN(U, RR), and `(IN f (FUN U (CARR K)))' is the third conjunct of
;;; IS-DIFF-ON.  So each disjunct of the FORSOME is FALSE and the predicate is
;;; false.  Nothing here is an undefined term: the FORSOME is over eps, and the
;;; body is a predicate application, never an equation between terms that might
;;; not denote.
;;;
;;; NO GUARDS ON f OR ON a.  The definition is self-guarding in the sense
;;; above: IS-DIFF-ON carries (IN a U) -- so a in RR follows, U being a SEP over
;;; RR -- and (IN L (CARR K)) -- so L in RR follows.  The read-offs
;;; `has-deriv-at-pt-in-rr' and `has-deriv-at-in-rr' are PROVEN, not assumed.
;;;
;;; ---------------------------------------------------------------------
;;; THE EMPTY CASES, CHECKED.
;;;
;;; OOINT(a, b) is EMPTY when b <= a (and when a or b is not a real): it is a
;;; SEP over RR, so this is not a defect, it is the fact.  `ooint-open' holds
;;; for it (vacuously) and so does `ooint-subset-ccint'.  Nothing below may
;;; acquire an `a < b' guard: HAS-DERIV-AT would then be unstatable.
;;;
;;; IS-CONTINUOUS-ON(f, D) on D = EMPTY-SET says exactly `f in FUN(EMPTY-SET,
;;; RR)', i.e. f is the empty function.  It is NOT vacuously true of an
;;; arbitrary f: that is why the FUN typing is a conjunct of its own and not
;;; left to follow from the universal.  (For an inhabited D the typing IS
;;; implied by the universal, through IS-CONTINUOUS-AT's own third conjunct and
;;; `subspace-pts'; the conjunct costs nothing there.)
;;;
;;; ---------------------------------------------------------------------
;;; EXTEND-CONST, AND WHY IT IS THE CLAMPED COMPOSITE AND NOT AN IF-TOWER.
;;;
;;; The extension of the design note -- f(a) on (-infinity, a), f on [a, b],
;;; f(b) on (b, infinity) -- is literally f composed with the RETRACTION of the
;;; line onto [a, b], and that retraction already exists:
;;;
;;;     CLAMP(a, b, x) = min(max(x, a), b)      (theorem-library/clamp.scm)
;;;
;;; with `clamp-in-rr' (unconditional), `clamp-in-ccint' (a <= b), `clamp-fixes'
;;; and `clamp-lipschitz' all proven `modulo 0'.  Written as the IF-tower
;;;
;;;     VNB-LAMBDA ecx_ RR (IF (< ecx_ a) (f a) (IF (<= ecx_ b) (f ecx_) (f b)))
;;;
;;; every law costs a three-way case analysis -- the typing, the value on
;;; [a, b], and above all the continuity, where the endpoints are the hard case
;;; (at a only a half-ball is available while the eps/delta clause quantifies
;;; over all of RR).  Written as the composite, the typing is `clamp-in-ccint'
;;; plus one application typing, the value on [a, b] is `clamp-fixes', and the
;;; continuity has NO cases at all: the clamp cannot move two points further
;;; apart than they were, so f's own delta serves unchanged.  clamp.scm's own
;;; header makes that argument for f in FUN(RR, RR); the same argument runs
;;; here for f in FUN(CCINT(a, b), RR) with f's continuity taken on the metric
;;; SUBSPACE, which is what IS-CONTINUOUS-ON gives.
;;;
;;; THE TYPING IS STILL GUARDED.  `extend-const-in-fun' carries a <= b and
;;; f in FUN(CCINT(a, b), RR), because CLAMP(a, b, x) lies in CCINT(a, b) only
;;; when a <= b (`clamp-in-ccint').  With b < a the term still denotes --
;;; CLAMP(a, b, x) = min(max(x, a), b) = b for every x -- but the interval is
;;; empty, f is the empty function and f(b) is undefined, so the lambda is not
;;; in FUN(RR, RR).  The theorem is guarded; the definition is not.
;;;
;;; LOAD ORDER.  CLAMP is a `def-functoid' that sits inside the proof file
;;; theorem-library/clamp.scm (load position 2690), so THIS file must load
;;; after it.  CLAMP is proof-free vocabulary and belongs in structure-library/
;;; by the rule of 2026-09-20; hoisting it would free this file to load with
;;; the rest of the vocabulary.

;;; BINDER NAMES.  `icx_', `icp_', `ice_', `ecx_' -- none folds onto a
;;; registered constant, a class name (NN ZZ QQ RR CC ORD SET ...) or an
;;; accessor, and none is a name a predicate body or a driver instantiates at
;;; (CLAUDE.md, "Case folding" and "Writing proof drivers": a functoid body
;;; whose binder is spelled like an eigenvariable gets capture-renamed by
;;; `subst-free' and every later lookup of the rebuilt term matches nothing).
;;;
;;; Dependencies: extreme-value.scm (CCINT), metric-subspace.scm (SUBSPACE-MS,
;;; RESTRICT), metric-continuity.scm (IS-CONTINUOUS-AT), numeric-instances.scm
;;; (RR-MS, RR-NORMED-FIELD), diff-on.scm (IS-DIFF-ON), order-predicates.scm
;;; (POS-RR).  Nothing is proven here.

;;; -----------------------------------------------------------------------
;;; The open interval.  CCINT (extreme-value.scm) is the closed one.

(def-functoid 'OOINT '(a b)
  '(SEP icx_ RR (AND (< a icx_) (< icx_ b))))

(notation! 'OOINT 'kind 'functoid 'arity 2
           'english "the open interval from $1 to $2")

;;; -----------------------------------------------------------------------
;;; Continuity on a set.  D is any subclass of RR; the intended D are
;;; CCINT(a, b) and OOINT(a, b).

(def-predicate 'IS-CONTINUOUS-ON '(f D)
  '(AND (IN f (FUN D RR))
        (FORALL icp_ (IMPLIES (IN icp_ D)
          (IS-CONTINUOUS-AT (SUBSPACE-MS RR-MS D) RR-MS f icp_)))))

(notation! 'IS-CONTINUOUS-ON 'kind 'predicate 'arity 2
           'english "$1 is continuous on $2")

;;; -----------------------------------------------------------------------
;;; The derivative at a point, as a LOCAL notion.

(def-predicate 'HAS-DERIV-AT '(f a L)
  '(FORSOME ice_
     (AND (POS-RR ice_)
          (IS-DIFF-ON RR-NORMED-FIELD
                      (OOINT (- a ice_) (+ a ice_))
                      (RESTRICT f (OOINT (- a ice_) (+ a ice_)))
                      a L))))

(notation! 'HAS-DERIV-AT 'kind 'predicate 'arity 3
           'english "$1 has derivative $3 at $2")

;;; -----------------------------------------------------------------------
;;; Extension by constants.

(def-functoid 'EXTEND-CONST '(f a b)
  '(VNB-LAMBDA ecx_ RR (f (CLAMP a b ecx_))))

(notation! 'EXTEND-CONST 'kind 'functoid 'arity 3
           'english "$1 extended to the whole line by constants outside $2 to $3")
