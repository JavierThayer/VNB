;;; dual-space.scm -- THE DUAL of a real normed vector space, as an OBJECT.
;;;
;;; linear-functional.scm already has the PREDICATES -- IS-LINEAR-FUNCTIONAL,
;;; IS-BOUNDED-LINEAR-FUNCTIONAL -- and the functoid DUAL-NORM(m,f), and
;;; hahn-banach-*.scm / norm-as-sup-proof.scm reason with them one functional at
;;; a time.  What was missing is the SPACE: the normed vector space whose
;;; vectors ARE the bounded linear functionals on m and whose norm is DUAL-NORM.
;;; This file builds it and states that it is one.  Vocabulary only, no proofs.
;;;
;;;   DUAL-VEC(m)   { f in FUN(VEC m, RR) : IS-BOUNDED-LINEAR-FUNCTIONAL(m,f) }
;;;   DUAL(m)       the NORMED-VECTOR-SPACE 7-tuple over that carrier
;;;
;;; NOTHING IS RESTATED.  The carrier is carved out of FUN(VEC m, RR) by the
;;; EXISTING predicate; the norm slot is the EXISTING functoid DUAL-NORM.  The
;;; only new mathematics in the file is the single claim that the seven slots fit
;;; together into a normed vector space (dual-is-normed-vector-space).
;;;
;;; THE SHAPE IS FORCED, and it is worth saying why, because it is the same rule
;;; that forces the shape of complex-inner-product.scm next door.  An accessor
;;; name lives at exactly ONE slot index library-wide (register-accessor-index!,
;;; structures.scm:245; a second claim WITHDRAWS the reduction and makes the name
;;; ambiguous for everyone).  So a tuple that is to be read with VEC / VADD /
;;; VNRM must put them where NORMED-VECTOR-SPACE put them: SCAL 1, VEC 2, VADD 3,
;;; VZERO 4, VNEG 5, ACT 6, VNRM 7.  DUAL(m) is that tuple, with the pointwise
;;; operations in slots 3-6.
;;;
;;; THE FUNCTOID TRAP (CLAUDE.md, "Where a definition lives").  DUAL-VEC is a
;;; `def-functoid', so it installs a rewrite MACETE and no theorem: `mac' unfolds
;;; it in a GOAL, and `mac-h' CANNOT unfold it in an ASSUMPTION -- it warns
;;; "unknown theorem/macete" and the driver sails on with the hypothesis intact.
;;; Every proof about the dual reads a functional OUT of the context ("let f be a
;;; vector of DUAL(m)"), so the membership law has to be stated separately:
;;; `dual-vec-membership' was that law, stamped `definitional' until 2026-10-27 --
;;; the functoid unfold composed with the SEP separation schema.  It and the three
;;; slot readouts (the DUAL unfold composed with an NTH projection) are now PROVEN
;;; in theorem-library/dual-space-readoffs.scm; see the retirement notes below.
;;;
;;; A DEFECT IT INHERITED, and no longer does (repaired 2026-08-23).  Until that
;;; date IS-NORMED-VECTOR-SPACE WAS UNSATISFIABLE, so
;;; `dual-is-normed-vector-space' below -- and every other theorem in the tree
;;; stated over that predicate -- was VACUOUSLY true.  normed-vector-space.scm
;;; declared `(substructure SCAL RING)', whose IS-RING conjunct pins
;;; length(SCAL s) = 6, and then pinned `scal(s) = rr-normed-field', where
;;; RR-NORMED-FIELD is the SEVEN-tuple [RR add mul neg 0 1 abs] (VNB-LAMBDA operations, not the bare symbols binplus ...)
;;; (numeric-instances.scm:250).  Six equals seven.  The one-line repair recorded
;;; here -- pin the scalars through the view that exists for exactly this
;;; purpose,
;;;     (law "scal(s) = normed-field-as-commutative-ring(rr-normed-field)")
;;; -- HAS NOW BEEN MADE, in normed-vector-space.scm, whose header carries the
;;; full account.  What it cost, measured rather than estimated: ZERO bills
;;; moved, every one byte-identical, because no proof in the library unfolds
;;; IS-NORMED-VECTOR-SPACE.  The blast radius this note warned about was real
;;; but empty.
;;;
;;; ONE CONSEQUENCE FOR THIS FILE, and it is not discharged.  A satisfiable
;;; predicate is not an INHABITED one: nothing in the tree exhibits a normed
;;; vector space, so `dual-is-normed-vector-space' asserts that DUAL(m) is one
;;; whenever m is, and no m is known to be.  That is an ordinary unproved
;;; hypothesis now, not a contradiction -- which is the whole difference the
;;; repair makes.
;;;
;;; Dependencies: normed-vector-space.scm (the 7-slot shape and its accessors),
;;; linear-functional.scm (IS-BOUNDED-LINEAR-FUNCTIONAL, DUAL-NORM),
;;; numeric-instances.scm is NOT needed -- RR-NORMED-FIELD is named, not unfolded.

;;; ====================================================================
;;; the carrier: the bounded linear functionals on m
;;; ====================================================================

(def-functoid 'DUAL-VEC '(m)
  '(SEP f_ (FUN (VEC m) RR) (IS-BOUNDED-LINEAR-FUNCTIONAL m f_)))

;;; The membership law -- see THE FUNCTOID TRAP above.
;;; dual-vec-membership RETIRED 2026-10-27 (a `definitional' stamp): proven modulo 0, the
;;; statement character for character, as dual-vec-membership-proven in
;;; theorem-library/dual-space-readoffs.scm (TVS-NEXT, scratchpad/dualfix2/dual-stamps.scm).

;;; ====================================================================
;;; the dual space itself
;;; ====================================================================

;;; DUAL(m) = [ NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD),
;;;                                       scalars: the reals through the RING VIEW,
;;;                                       the slot IS-NORMED-VECTOR-SPACE pins
;;;             DUAL-VEC(m),              vectors: the bounded functionals
;;;             (f,g) |-> (x |-> f x + g x),      pointwise sum
;;;             x |-> 0,                          the zero functional
;;;             f |-> (x |-> -(f x)),             pointwise negation
;;;             (r,f) |-> (x |-> r * f x),        pointwise scaling
;;;             f |-> DUAL-NORM(m,f) ]            the operator norm
;;;
;;; Every operation is POINTWISE, so each one is a VNB-LAMBDA whose body is
;;; itself a VNB-LAMBDA on VEC(m): a vector of DUAL(m) is a function, and the
;;; operations of a function space act on values.
(def-functoid 'DUAL '(m)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
         (DUAL-VEC m)
         (VNB-LAMBDA (LIST dlaf_ dlag_) (CARTESIAN (DUAL-VEC m) (DUAL-VEC m))
           (VNB-LAMBDA dlax_ (VEC m) (+ (dlaf_ dlax_) (dlag_ dlax_))))
         (VNB-LAMBDA dlzx_ (VEC m) 0)
         (VNB-LAMBDA dlnf_ (DUAL-VEC m)
           (VNB-LAMBDA dlnx_ (VEC m) (- (dlnf_ dlnx_))))
         (VNB-LAMBDA (LIST dlsr_ dlsf_) (CARTESIAN RR (DUAL-VEC m))
           (VNB-LAMBDA dlsx_ (VEC m) (* dlsr_ (dlsf_ dlsx_))))
         (VNB-LAMBDA dlvf_ (DUAL-VEC m) (DUAL-NORM m dlvf_))))

;;; ====================================================================
;;; slot readouts -- the DUAL unfold composed with an NTH projection.
;;; ====================================================================

;;; dual-scal, dual-carrier, dual-norm-value RETIRED 2026-10-27 (`definitional' stamps).
;;; Unguarded, the three are not provable under list definedness (the 2026-10-01 decision: a
;;; list denotes only when every component is a set), and dual-scal / dual-carrier are FALSE at
;;; an m whose VEC is not a set: the left side of `==' is undefined, the right side defined
;;; (TVS-NEXT F1, scratchpad/triage/TVS-NEXT-REPORT.md section 1).  They are proven modulo 0,
;;; each with the one added guard (IN (DUAL-VEC m) SET), as dual-scal-proven,
;;; dual-carrier-proven and dual-norm-value-proven in theorem-library/dual-space-readoffs.scm;
;;; every citer has the guard from dual-vec-in-set.

;;; ====================================================================
;;; ... and it is a normed vector space
;;; ====================================================================

;;; THE SCALAR SLOT (2026-10-26, carrying out the user's yes of 2026-10-12).  Until
;;; this date the scalar slot held the 7-tuple RR-NORMED-FIELD, while
;;; IS-NORMED-VECTOR-SPACE pins scal(s) = normed-field-as-commutative-ring(
;;; rr-normed-field), a 6-tuple; the statement dual-is-normed-vector-space was then
;;; FALSE (7 = 6 at m = RR-NVS) and was deleted 2026-10-12, its negation proven as
;;; rb3-dual-is-normed-vector-space-false (rake-asm-b3.scm).  The slot now holds the
;;; ring view, exactly as RR-NVS and RN(n) do; the negation is retired, and the
;;; corrected statement is PROVEN in theorem-library/dual-nvs.scm:
;;;     forall m. IS-NORMED-VECTOR-SPACE(m) => IS-NORMED-VECTOR-SPACE(DUAL(m)).
;;; The lambdas' binders were renamed at the same time (dla.._, dlz.._, ...) so that
;;; no binder of the tuple is spelled like a binder of the IS-NORMED-VECTOR-SPACE
;;; laws (r_, s_, x_, y_) or of the DUAL-NORM body (c_, d_, x_); the change is an
;;; alpha-renaming and nothing cited the old spelling.

;;; -----------------------------------------------------------------------
;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'DUAL 'kind 'functoid 'arity 1
           'english "the dual space of $1"
           'tex "{$1}^{*}")
(notation! 'DUAL-VEC 'kind 'functoid 'arity 1
           'english "the bounded linear functionals on $1")
