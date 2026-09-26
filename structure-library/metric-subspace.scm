;;; metric-subspace.scm -- the METRIC SUBSPACE of a metric space, and the
;;; RESTRICTION of a function to a subset.  DEFINITIONS ONLY; every law is
;;; PROVEN in theorem-library/metric-subspace-laws.scm.
;;;
;;;     SUBSPACE-MS(s, A) = ( A,  d_s restricted to A x A )
;;;     RESTRICT(f, A)    = x |-> f(x),  x ranging over A
;;;
;;; These are the two objects the design note docs/diff-on-open-sets-2026-09-20.md
;;; (section 3.1) asks for: without them the tree cannot say "f is continuous on
;;; the subset U", because a member of FUN(A,B) is defined EXACTLY on A, and it
;;; cannot say "the closed interval, as a space".
;;;
;;; WHY A PLAIN `def-functoid' AND NOT `def-constructed-functor'.  The latter
;;; (structures.scm:1742) takes ONE parameter: it binds `r' to `(car params)'
;;; and installs the projection macetes with left-hand sides `(ACC (NAME r))'.
;;; SUBSPACE-MS takes TWO -- the space and the subset -- so the precomputed
;;; projections would be built at the wrong arity and the object map is not a
;;; functor of METRIC-SPACE alone in any case (it is a functor of the category
;;; of PAIRS (space, subset), which the tree does not have).  The read-offs are
;;; therefore PROVEN once, as `subspace-pts' and `subspace-dist-slot', and every
;;; later proof fires those two THEOREMS by name instead of reaching for an
;;; accessor macete -- which is the discipline the accessor pin
;;; (`accessor-callsite-audit') exists to enforce.
;;;
;;; THE DISTANCE IS A VNB-LAMBDA OVER CARTESIAN(A, A), not `(DIST s)' itself.
;;; The METRIC-SPACE structure types DIST as an operation on CARTESIAN(PTS, PTS);
;;; `(DIST s)' is a member of FUN(CARTESIAN(PTS s, PTS s), RR) and so is defined
;;; exactly there, which is NOT the subspace's domain.  Cutting it down with a
;;; lambda is what makes SUBSPACE-MS(s, A) a metric space in the tree's own
;;; sense, and it is why `subspace-dist' (the value law) is stated with `==' and
;;; GUARDED on (IN u A), (IN v A): off A x A the left-hand side is an application
;;; outside its lambda's domain and nothing says what it is.
;;;
;;; THE EMPTY SUBSPACE IS INTENDED AND IS A METRIC SPACE.  A = EMPTY-SET is a
;;; subset of PTS(s); CARTESIAN(EMPTY-SET, EMPTY-SET) is empty, so the distance
;;; lambda is the empty function, `is-metric' is vacuously true, and
;;; `subspace-is-metric-space' goes through with no inhabitedness guard.  This
;;; is deliberate: the first consumer is Heine-Borel for CCINT(a, b), and
;;; CCINT(a, b) is EMPTY when b < a.  Nothing below may acquire a guard that
;;; excludes it.
;;;
;;; BINDER NAMES.  The distance lambda binds `sbu_' / `sbv_' and RESTRICT binds
;;; `rsx_' -- names no predicate body, no statement and no eigenvariable the
;;; kernel mints uses.  A functoid body whose binder is spelled like something a
;;; driver instantiates at gets capture-renamed by `subst-free', and every later
;;; `equal?' lookup of the rebuilt term then matches nothing, silently
;;; (CLAUDE.md, "Writing proof drivers").  The parameter `A' is the subset, as in
;;; IS-R-NET(s, F, A, r) (metric-topology.scm); the points are never `x', which
;;; case-folds onto nothing today but did onto the old carrier accessor `X'.
;;;
;;; Dependencies: metric-space.scm (METRIC-SPACE, PTS, DIST) and the set kernel
;;; (CARTESIAN, VNB-LAMBDA).  Nothing else -- so this file may load anywhere
;;; after metric-space.scm.

;;; -----------------------------------------------------------------------
;;; The subspace.

(def-functoid 'SUBSPACE-MS '(s A)
  '(LIST A
         (VNB-LAMBDA (LIST sbu_ sbv_) (CARTESIAN A A)
           ((DIST s) sbu_ sbv_))))

(notation! 'SUBSPACE-MS 'kind 'functoid 'arity 2
           'english "the subspace of $1 on $2")

;;; -----------------------------------------------------------------------
;;; The restriction of a function to a subset of its domain.

(def-functoid 'RESTRICT '(f A)
  '(VNB-LAMBDA rsx_ A (f rsx_)))

(notation! 'RESTRICT 'kind 'functoid 'arity 2
           'english "the restriction of $1 to $2")
