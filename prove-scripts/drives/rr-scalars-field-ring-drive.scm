;;; rr-scalars-field-ring-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23).
;;;
;;; IS-VECTOR-SPACE was UNSATISFIABLE until today: `(same-shape-as MODULE)'
;;; inherits (IS-RING (SCAL s)), pinning length(scal(s)) = 6, and the law read
;;; `is-field(scal(s))', pinning the same term to 8.  The repair states
;;; fieldhood OF A SIX-SLOT RING -- IS-FIELD-RING (structure-library/field.scm),
;;; a `(same-shape-as COMMUTATIVE-RING)' refinement with ONE /= ZERO and every
;;; nonzero element invertible.
;;;
;;; A repaired predicate is still an EMPTY predicate until something satisfies
;;; it, and this is the witness the whole normed-vector-space arc turns on: the
;;; tuple a real normed vector space's SCAL slot actually holds is
;;;
;;;     NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD)
;;;
;;; (normed-vector-space.scm:117).  Showing THAT is a FIELD-RING is what makes
;;; "the reals are a field" sayable in the shape the module machinery uses --
;;; and it is exactly the step the alternative repair (an existential over an
;;; 8-tuple FIELD) could not take, the tree having no RR FIELD instance at all,
;;; only QQ-FIELD (numeric-instances.scm:311).
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/rr-scalars-field-ring-drive.scm
;;;
;;; EVERYTHING IT NEEDS IS ALREADY PROVEN.  The six read-offs of the projected
;;; tuple are `modulo 0' in theorem-library/normed-field-ring-view.scm --
;;; rr-scalar-ring-carr/-add/-mul/-neg/-zero/-one, giving RR, binplus, bintimes,
;;; binneg, 0, 1 -- and they are live macetes, so `mac' rewrites the goal into
;;; the surface language in one step each.  The three obligations are then:
;;;
;;;   (1) IS-COMMUTATIVE-RING of the projection.  `def-functor' installed the
;;;       typing axiom NORMED-FIELD-AS-COMMUTATIVE-RING-is-COMMUTATIVE-RING
;;;       (structures.scm:1167), and `rr-is-normed-field' (numeric-instances.scm)
;;;       is its antecedent.  One `fact' each.
;;;   (2) ONE /= ZERO.  After the two read-off macetes this is `not(1 = 0)':
;;;       `arith'.
;;;   (3) INVERTIBILITY, the only one with content, and it is four citations:
;;;       after the read-offs the goal is
;;;           forall a_ in RR. not(a_ = 0) => forsome b_ in RR. bintimes(a_,b_) = 1
;;;       Witness b_ := recip(a_).  `rr-recip-closed' (number-systems.scm:390)
;;;       types it, `rr-recip-inverse' (:395) gives a_ * recip(a_) = 1, and
;;;       `bintimes-apply' (numeric-instances.scm) bridges the bridge symbol
;;;       `bintimes(a_, b_)' to the surface product `a_ * b_'.  Note the guard on
;;;       both recip axioms is `not(a_ = 0)', which the antecedent hands you --
;;;       so `fact' detaches them without a `have!'.
;;;
;;; WHAT THIS DOES NOT FIX, and it is the bigger finding of the same day.
;;; IS-NORMED-VECTOR-SPACE(m) pins length(m) = 7 (SCAL VEC VADD VZERO VNEG ACT
;;; VNRM) and IS-FINITE-DIMENSIONAL(m) pins length(m) = 6 through IS-VECTOR-SPACE
;;; (MODULE's shape).  hahn-banach, norm-as-sup, norm-attained-by-functional,
;;; vector-taylor-remainder-bound and nvs-taylor-remainder-bound all conjoin the
;;; two ON THE SAME m, so their hypotheses are unsatisfiable for a reason that
;;; has nothing to do with the scalar slot and that this repair does not touch.
;;; The statements want IS-FINITE-DIMENSIONAL(NORMED-VECTOR-SPACE-AS-MODULE(m))
;;; -- the view is already declared, normed-vector-space.scm:136 -- and that is
;;; a decision about five theorem statements, not a driver.  The satisfiability
;;; audit cannot see it: it scans one DECLARATION at a time, and this clash is
;;; between two predicates conjoined in a THEOREM.
;;;
;;; BOTH HALVES OF THAT PARAGRAPH ARE NOW DONE, LATER THE SAME DAY.  The five
;;; statements say `is-finite-dimensional(normed-vector-space-as-module(m))';
;;; `hb-good-has-maximal' (theorem-library/noetherian-maximal-proof.scm) moved
;;; with them, because `fact' detaches an antecedent only if the context holds
;;; it, and the six read-offs of the module view that its proof then needs are
;;; PROVEN modulo 0 in theorem-library/nvs-module-view.scm.  Every bill in the
;;; library came out byte-identical.  And the gate that DOES see a clash
;;; assembled by a theorem now exists: `statement-satisfiability-audit'
;;; (audit.scm), warn-only beside the per-declaration one, with its control in
;;; scratchpad/stmt-audit-control.scm and a must-not-prove entry in
;;; test-suite-negative.scm section 2e.  The leaf BELOW is still open.

(sp (make-wff '(IS-FIELD-RING (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))))

;; the projection IS a commutative ring -- the view's own typing axiom
(fact 'rr-is-normed-field)
(fact 'normed-field-as-commutative-ring-is-commutative-ring 'RR-NORMED-FIELD)

;; unfold the definition; three conjuncts open
(mac 'is-field-ring-def)

;; put the projected slots into the surface language, on every leaf
(for-each (lambda (l)
            (dk-focus! l)
            (for-each (lambda (m) (vnb-guard (lambda () (mac m))))
                      '(rr-scalar-ring-carr rr-scalar-ring-mul
                        rr-scalar-ring-one  rr-scalar-ring-zero)))
          (proof-leaves))

;; one AND goal; open the three conjuncts
(vnb-guard (lambda () (split)))

(newline)
(display "### open leaves, after the read-offs:\n")
(for-each (lambda (l)
            (dk-focus! l)
            (display "###   ") (write (dk-goal)) (newline))
          (proof-leaves))
(display "### (1) IS-COMMUTATIVE-RING(...) is already in context: (ass).\n")
(display "### (2) not(1 = 0): (arith).\n")
(display "### (3) forall a_ in RR. not(a_ = 0) => forsome b_ in RR. bintimes(a_,b_) = 1\n")
(display "###     -- (di), witness recip(a_): rr-recip-closed, rr-recip-inverse,\n")
(display "###     bintimes-apply.  This is the only leaf with content.\n")
(display "### If (split) did not fire, the single leaf is the AND of all three.\n")
