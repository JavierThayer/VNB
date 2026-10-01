;;; top-continuity.scm -- COMPACTNESS of a topological space, and the SUBSPACE
;;; TOPOLOGY.  DEFINITIONS AND NOTATION ONLY; every law is proven in
;;; theorem-library/metrizable-compact-image.scm.
;;;
;;;   IS-COMPACT-T(s)        every family of opens of s covering PTS(s) has a
;;;                          finite subfamily covering PTS(s);
;;;   SUBSPACE-TOP(t, A)     the subspace topology on A: points A, opens the
;;;                          traces u ^ A of the opens u of t.
;;;
;;; CONTINUITY is not defined here.  The continuous maps between topological
;;; spaces are TOP-SPACE's generated morphisms, IS-HOM-TOP-SPACE (top-space.scm;
;;; `is-hom-top-space-def':  f in FUN(PTS s, PTS t) and forall u in OPENS(t).
;;; PREIMAGE(s, f, u) in OPENS(s)), and every theorem uses that predicate (the
;;; user's decision, 2026-10-01: a separate IS-CONTINUOUS-T would have been the
;;; same formula under a second name).
;;;
;;; IS-COMPACT-T is IS-COMPACT (compactness.scm) with "U is open in s" read as
;;; "U in OPENS(s)", and with IS-OPEN-COVER written out in place: an open cover
;;; is a family whose members are opens and whose union is, up to `==', PTS(s).
;;; The finiteness clause is the one IS-COMPACT uses, CARD(F) in NN.  Two
;;; departures, both deliberate:
;;;   - the cover hypotheses are CURRIED (members open, then union), so that
;;;     `fact' detaches them one at a time (CLAUDE.md: `fact' will not split a
;;;     conjunctive antecedent);
;;;   - the subfamily clause does not repeat "the members of F are open", which
;;;     IS-OPEN-COVER(s, F) does in the metric predicate: F is a subclass of C,
;;;     so it is a consequence, not a condition.
;;;
;;; SUBSPACE-TOP(t, A) is built the way METRIC-TOP (top-space.scm) and
;;; SUBSPACE-MS (metric-subspace.scm) build their instances: a LIST in slot
;;; order [PTS, OPENS].  The opens are a SEP over POWER(A), so they form a SET
;;; whenever A is one, and a member w is a subset of A that is the trace
;;; INTERSECTION(u, A) of some u in OPENS(t).  It is a plain `def-functoid'
;;; (two parameters, as SUBSPACE-MS: `def-constructed-functor' takes one), so
;;; its read-offs `subspace-top-pts' / `subspace-top-opens' are PROVEN, and
;;; later proofs fire those theorems by name.  No guard on A: the definition is
;;; total; A subset PTS(t) is the hypothesis of `subspace-top-is-top-space'.
;;; The empty A gives the one-point topology {EMPTY-SET} on the empty set.
;;;
;;; BINDER NAMES.  The cover binders are C, F and U, as in IS-COMPACT; the
;;; subspace binders are `stw_' / `stu_', names no predicate body and no
;;; eigenvariable uses (CLAUDE.md: a driver-instantiated functoid body whose
;;; binder is spelled like an eigenvariable is capture-renamed).
;;;
;;; Dependencies: top-space.scm (TOP-SPACE: PTS, OPENS), cardinality.scm (CARD).
;;; Loads after compactness.scm.

(def-predicate 'IS-COMPACT-T '(s)
  '(AND (IS-TOP-SPACE s)
        (FORALL C (IMPLIES (FORALL U (IMPLIES (IN U C) (IN U (OPENS s))))
                    (IMPLIES (== (BIG-UNION U C U) (PTS s))
                      (FORSOME F (AND (SUBSET F C)
                                 (AND (IN (CARD F) NN)
                                      (== (BIG-UNION U F U) (PTS s))))))))))

(notation! 'IS-COMPACT-T 'kind 'predicate 'arity 1
           'english "the topological space $1 is compact")

(def-functoid 'SUBSPACE-TOP '(t A)
  '(LIST A
         (SEP stw_ (POWER A)
           (FORSOME stu_ (AND (IN stu_ (OPENS t))
                              (= stw_ (INTERSECTION stu_ A)))))))

(notation! 'SUBSPACE-TOP 'kind 'functoid 'arity 2
           'english "the subspace topology of $1 on $2")
