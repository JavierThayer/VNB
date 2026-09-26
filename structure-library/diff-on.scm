;;; diff-on.scm -- THE DERIVATIVE ON AN OPEN SET, OVER A NORMED FIELD.
;;; DEFINITIONS ONLY; every law is PROVEN in theorem-library/diff-on-laws.scm.
;;;
;;; The user's decision of 2026-09-20 (docs/diff-on-open-sets-2026-09-20.md,
;;; section 5): ONE derivative, over a normed field K; the domain U is OPEN by
;;; definition; the real theory (IS-DIFF-AT and the fifty theorems stated with
;;; it) is NOT touched -- it is reached by the bridge theorem `diff-at-iff-on'
;;; of theorem-library/diff-on-laws.scm.
;;;
;;;     IS-DIFF-ON(K, U, f, a, L)   f, defined on U, is differentiable at a
;;;                                 with derivative L, over the normed field K
;;;     DERIV-ON(K, U, f, a)        that L (an IOTA; unique by `diff-on-unique')
;;;     HOLOMORPHIC-ON(U, f)        f is differentiable at every point of the
;;;                                 open set U, over CC-NORMED-FIELD
;;;
;;; THE SHAPE IS CARATHEODORY'S, as in differentiation.scm: there is a factor
;;; phi, continuous at a, with phi(a) = L and
;;;
;;;     f(x) - f(a)  =  phi(x) . (x - a)        for every x in U,
;;;
;;; written in K's OWN operations -- (ADD K), (MUL K), (NEG K) -- because the
;;; numeric `+ * -' of the surface language are the operations of RR and CC and
;;; of nothing else.  The definition is purely EQUATIONAL, so the differentiation
;;; rules stay ring identities (`crs' through NORMED-FIELD-AS-COMMUTATIVE-RING)
;;; rather than eps-delta arguments on a difference quotient.
;;;
;;; WHY THE DOMAIN OF phi IS U AND NOT CARR(K).  A member of FUN(A,B) is defined
;;; EXACTLY on A, so "f is differentiable on U" cannot be said with f in
;;; FUN(CARR K, CARR K); that is the wall recorded in chain-rule.scm,
;;; inverse-function.scm and heine-borel-baby.scm.  f and phi are members of
;;; FUN(U, CARR K), and the continuity of phi at a is continuity as a map
;;;
;;;     SUBSPACE-MS(NF-METRIC-SPACE(K), U)  ->  NF-METRIC-SPACE(K),
;;;
;;; the metric subspace of structure-library/metric-subspace.scm.  Its points are
;;; U (subspace-pts) and its distance is the ambient one on U (subspace-dist), so
;;; the FUN typing of the definition and the FUN typing IS-CONTINUOUS-AT demands
;;; are the same class, one rewrite apart.
;;;
;;; WHY IS-OPEN IS A CONJUNCT.  The user's decision 2: "U is open usually when
;;; considered as domains for functions."  Openness is what makes every point of
;;; U a limit point of U (for a field whose norm is not trivial -- see
;;; `diff-on-unique', which carries that non-triviality as an antecedent and gets
;;; it for RR and CC by `rr-nf-small-elements' / `cc-nf-small-elements'), and
;;; hence what makes L unique and DERIV-ON's IOTA well-defined.  One-sided
;;; derivatives at the endpoints of a closed interval are NOT instances of this
;;; definition; they get one of their own if the fundamental theorem of calculus
;;; asks for them.
;;;
;;; NO INHABITEDNESS GUARD.  U = EMPTY-SET is open, and then `(IN a U)' is false,
;;; so IS-DIFF-ON is simply false for every a -- which is right.  Nothing below
;;; may acquire a guard that excludes it.
;;;
;;; BINDER NAMES.  The bound variables are `phi' and `x', the two
;;; differentiation.scm already uses, and the parameters are K, U, f, a, L.
;;; None folds onto a registered constant or a class name
;;; (`constant-binder-audit' is fatal and would say so).
;;;
;;; Dependencies: normed-field.scm (IS-NORMED-FIELD, CARR/ADD/MUL/NEG),
;;; normed-field-metric.scm (NF-METRIC-SPACE), metric-open-sets.scm (IS-OPEN),
;;; metric-continuity.scm (IS-CONTINUOUS-AT), metric-subspace.scm (SUBSPACE-MS),
;;; numeric-instances.scm / complex.scm (CC-NORMED-FIELD, CC).

;;; -----------------------------------------------------------------------
;;; The derivative on an open set.

(def-predicate 'IS-DIFF-ON '(K U f a L)
  '(AND (IS-NORMED-FIELD K)
   (AND (IS-OPEN (NF-METRIC-SPACE K) U)
   (AND (IN f (FUN U (CARR K)))
   (AND (IN a U)
   (AND (IN L (CARR K))
        (FORSOME phi
          (AND (IN phi (FUN U (CARR K)))
          (AND (IS-CONTINUOUS-AT (SUBSPACE-MS (NF-METRIC-SPACE K) U)
                                 (NF-METRIC-SPACE K) phi a)
          (AND (= (phi a) L)
               (FORALL x (IMPLIES (IN x U)
                 (= ((ADD K) (f x) ((NEG K) (f a)))
                    ((MUL K) (phi x) ((ADD K) x ((NEG K) a))))))))))))))))

(notation! 'IS-DIFF-ON 'kind 'predicate 'arity 5
           'english "$3, on $2, is differentiable at $4 over $1, with derivative $5")

;;; -----------------------------------------------------------------------
;;; The derivative as an operator.  Well-defined by `diff-on-unique' whenever
;;; K's norm has arbitrarily small nonzero elements (RR and CC both do).

(def-functoid 'DERIV-ON '(K U f a)
  '(IOTA L (IS-DIFF-ON K U f a L)))

(notation! 'DERIV-ON 'kind 'functoid 'arity 4
           'english "the derivative of $3 on $2 at $4 over $1")

;;; -----------------------------------------------------------------------
;;; Holomorphy.  The openness conjunct is stated on NF-METRIC-SPACE(CC-NORMED-
;;; FIELD) -- the space IS-DIFF-ON itself speaks of -- and `cc-ms-open-iff'
;;; (theorem-library/diff-on-laws.scm) turns it into openness in CC-MS in one
;;; citation, in either direction.  It is NOT implied by the last conjunct: for
;;; U = EMPTY-SET the universal is vacuous.

(def-predicate 'HOLOMORPHIC-ON '(U f)
  '(AND (IS-OPEN (NF-METRIC-SPACE CC-NORMED-FIELD) U)
   (AND (IN f (FUN U CC))
        (FORALL a (IMPLIES (IN a U)
          (FORSOME L (IS-DIFF-ON CC-NORMED-FIELD U f a L)))))))

(notation! 'HOLOMORPHIC-ON 'kind 'predicate 'arity 2
           'english "$2 is holomorphic on $1")
