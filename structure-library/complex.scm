;;; complex.scm -- CC as a metric space; completeness axiom
;;;
;;; CC-MS = [CC, lambda([x,y], magnitude(x-y))]
;;;
;;; CC-NORMED-FIELD (and its IS-RING witness) lives in basic-rings.scm alongside
;;; the other numeric ring instances; this file is now only about the
;;; metric/topological side of CC.
;;;
;;; IS-METRIC-SPACE(CC-MS) is taken as an axiom; the proof from the
;;; axioms in number-systems.scm is straightforward but requires
;;; FUN-typing infrastructure not yet developed.
;;;
;;; Completeness (every Cauchy sequence converges) is taken as an axiom.
;;; The current statement is hard-coded in terms of magnitude; a
;;; refactor through a generic IS-COMPLETE predicate on METRIC-SPACE
;;; is pending (see notes-16 endgame).

;;; -----------------------------------------------------------------------
;;; The structure CC-MS

;;; CC-MS is the list [CC, lambda([x,y], magnitude(x-y))].
;;; The lambda is a VNB functoid: a function from CARTESIAN(CC,CC) to RR.
;;; def-constant already installs cc-ms-def (definitional, citable) via
;;; theory-add-definition!; a separate theory-add-axiom! of the same equation
;;; only RE-installs it with default `asserted' provenance -- downgrading a
;;; definition to a phantom debt leaf.  One registration, kept definitional.
(def-constant 'CC-MS
  (list 'cc-ms-def
        '(= CC-MS (LIST CC (VNB-LAMBDA (LIST x y) (magnitude (- x y)))))))

;;; -----------------------------------------------------------------------
;;; CC-MS is a metric space

(theory-add-axiom! *current-theory* 'cc-is-metric-space
  '(IS-METRIC-SPACE CC-MS))

;;; -----------------------------------------------------------------------
;;; Completeness of CC-MS
;;;
;;; Every Cauchy sequence in CC-MS converges in CC-MS.  Now stated through
;;; the generic IS-COMPLETE predicate (metric-completeness.scm) instead of
;;; the magnitude-hard-coded form: IS-CAUCHY-SEQ/CONVERGES-TO read the
;;; distance off (DIST CC-MS), which is lambda([x,y], magnitude(x-y)) by
;;; cc-ms-def, so this is the same statement as before up to unfolding.

(theory-add-axiom! *current-theory* 'cc-complete
  '(IS-COMPLETE CC-MS))
