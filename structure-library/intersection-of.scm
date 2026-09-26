;;; intersection-of.scm -- INTERSECTION-OF(c), the intersection of the members
;;; of a family c, as a DEFINED constructor.
;;;
;;; WHY THE FILE EXISTS.  Until 2026-09-20 the library wrote "the intersection
;;; of the members of C" as `(BIG-INTERSECTION CARR C CARR)' in exactly two
;;; formulas, HAS-FIP and compact-iff-fip (structure-library/compactness.scm).
;;; BIG-INTERSECTION was an UNINTERPRETED head: no kernel rule, no macete, no
;;; membership law, and `wff.scm' did not know it as a binder.  Worse, the
;;; binder position held `CARR', a REGISTERED structure accessor, and the fatal
;;; `constant-binder-audit' missed it because `wff-constant-binders'
;;; (macetes.scm) has no BIG-INTERSECTION case.  Both formulas therefore said
;;; something the reader could not interpret and no gate could object to.
;;; (Found by rake batch 8, entry 8-A; the user's decision: make it real.)
;;;
;;; THE DESIGN.  Both uses are the intersection of a SET OF SETS, so nothing
;;; here needs a binder or a kernel rule: the object is an ordinary SEP over an
;;; ordinary BIG-UNION.
;;;
;;;     INTERSECTION-OF(c) = { x in UNION(c) : for every u in c, x in u }
;;;
;;; THE EMPTY FAMILY.  INTERSECTION-OF(EMPTY-SET) = EMPTY-SET.  That is forced
;;; by the SEP domain (the union of the empty family is empty) and it is the
;;; convention that keeps the constructor TOTAL and keeps its value a SET:
;;; "the intersection of no sets" cannot be the universal class without leaving
;;; set theory, so it is the empty set.  The price is that a statement about
;;; "every finite subfamily" must EXCLUDE the empty subfamily explicitly --
;;; see the guard on HAS-FIP in compactness.scm, which this convention forced.
;;; The fact itself is `intersection-of-empty-family' in
;;; theorem-library/intersection-of-laws.scm, proven, not asserted.
;;;
;;; THE INDEXED FORM (the intersection of b(z) over z in A) is INTERSECTION-OF
;;; of an IMAGE.  A binder notation `big-intersection(z, A, b)' would need the
;;; expression walkers, the binder tables and a kernel rule; it is deliberately
;;; NOT built here.
;;;
;;; BINDER NAMES.  `iov_' (the element), `iow_' (the union's index), `iou_'
;;; (the member of the family).  Distinctive on purpose: a driver that rebuilds
;;; this term must not have its binders renamed out from under it by
;;; `subst-free' (CLAUDE.md, "Writing proof drivers"), and `x_' / `u_' are
;;; bound by predicate bodies all over the tree.  None of the three is a
;;; registered constant or a class name, so `functoid-binder-audit' and
;;; `constant-binder-audit' both pass.
;;;
;;; Needs only kernel vocabulary (SEP, BIG-UNION, IN, FORALL), so it may be
;;; loaded anywhere in the structure-library block; it must be loaded BEFORE
;;; structure-library/compactness.

(def-functoid 'INTERSECTION-OF '(c)
  '(SEP iov_ (BIG-UNION iow_ c iow_)
        (FORALL iou_ (IMPLIES (IN iou_ c) (IN iov_ iou_)))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'INTERSECTION-OF 'kind 'functoid 'arity 1
           'english "the intersection of the members of $1")
