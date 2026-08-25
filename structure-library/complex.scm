;;; complex.scm -- CC as a metric space; completeness axiom
;;;
;;; CC-MS = [CC, vnb-lambda([x in CC, y in CC], magnitude(x-y))]
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
;;; THE COMPLEX MODULUS, DEFINED.  Added 2026-08-17.
;;;
;;; `magnitude' used to be characterised, in number-systems.scm, by five
;;; NORM-shaped axioms -- closed, nonneg, zero-iff, neg, multiplicative -- plus
;;; the triangle inequality and rr-magnitude-is-abs.  That was the `abs' defect
;;; one system up: the five say magnitude is *a* norm and never say WHICH, so
;;; nothing tied |z| to z's coordinates and no proof could compute a modulus.
;;; With real-part and imag-part now DEFINED (number-systems.scm) the standard
;;; definition is available, and every one of those axioms becomes a theorem:
;;; theorem-library/cc-magnitude.scm proves them and they are deleted there.
;;;
;;; WHY IT LIVES HERE and not beside real-part-def: `SQRT' is introduced in
;;; structure-library/real-powers.scm, which loads long AFTER number-systems.
;;; Writing this equation there would put an unregistered head in an installed
;;; formula (head-registry-sweep) -- the same constraint that made rr-abs-def
;;; state its second guard as `not (0 <= x)' rather than `x < 0'.  This file is
;;; the first place that has both SQRT and a reason to talk about the modulus.
;;;
;;; WHAT IT COSTS, stated plainly.  SQRT itself is NOT defined in this tree: it
;;; is characterised by the warranted supports sqrt-nonneg / sqrt-sq /
;;; sqrt-of-sq / sqrt-mono / sqrt-mul (real-powers.scm), which are `well-known'
;;; DEBT.  So the five magnitude facts move from `primitive' (contributing {} to
;;; every bill) to theorems billing those supports.  That is not a regression in
;;; honesty but a disclosure: the assumption was always there, in a symbol whose
;;; existence nobody had derived from order completeness, and it now shows up on
;;; the bills of exactly the facts that use it.  No other bill in the library
;;; moves, because nothing else cites a magnitude axiom by name.
;;;
;;; `==' and `definitional', for the same reasons as binary-minus-def: an
;;; unconditional equation defining a SYMBOL owes no definedness witness and is
;;; not a foundational commitment.  Not named-only: `magnitude(z)' is not a shape
;;; anything else builds by accident.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'magnitude-def
    '(FORALL z (== (magnitude z)
                   (SQRT (+ (* (real-part z) (real-part z))
                            (* (imag-part z) (imag-part z))))))))

;;; -----------------------------------------------------------------------
;;; The structure CC-MS

;;; CC-MS is the list [CC, vnb-lambda([x in CC, y in CC], magnitude(x-y))].
;;; The lambda is a VNB functoid: a function from CARTESIAN(CC,CC) to RR.
;;; def-constant already installs cc-ms-def (definitional, citable) via
;;; theory-add-definition!; a separate theory-add-axiom! of the same equation
;;; only RE-installs it with default `asserted' provenance -- downgrading a
;;; definition to a phantom debt leaf.  One registration, kept definitional.
(declare-instance! 'CC-MS 'METRIC-SPACE 'cc-ms-def
  '(CC (VNB-LAMBDA (LIST x y) (CARTESIAN CC CC) (magnitude (- x y)))))

;;; -----------------------------------------------------------------------
;;; CC-MS is a metric space

;;; cc-is-metric-space MOVED 2026-08-17 to
;;; theorem-library/cc-metric-space-proof.scm, where it is PROVEN.  It stood
;;; here as a bare `theory-add-axiom!' with no `warrant!' at all -- so it billed
;;; `trust: none', the weakest report there is, and it was one of the three such
;;; bills left in the library.  What made it provable is the same change that
;;; made this file's `magnitude' a DEFINITION rather than a family of
;;; norm-shaped axioms: the metric on CC-MS is magnitude(x - y), and its laws
;;; are now theorems (theorem-library/cc-magnitude.scm), the one with content
;;; being cc-magnitude-triangle -- two-dimensional Cauchy-Schwarz as a ring
;;; identity.  Exactly the route rr-metric-space-proof.scm took one system down.

;;; -----------------------------------------------------------------------
;;; Completeness of CC-MS
;;;
;;; cc-complete MOVED 2026-08-24 to theorem-library/cc-complete-proof.scm,
;;; where it is PROVEN.  It stood here as a bare `theory-add-axiom!' with no
;;; `warrant!' at all -- so it billed `trust: none', the weakest report there
;;; is, for a fact that is two coordinates of `rr-complete'
;;; (theorem-library/rr-complete-proof.scm), proven since 2026-08-02.  The
;;; reals' completeness was earned and the complexes' was assumed.
;;;
;;; What made it provable is the same change that made this file's `magnitude'
;;; a DEFINITION rather than a family of norm-shaped axioms: with
;;; magnitude(z) = SQRT(Re(z)^2 + Im(z)^2) the two coordinate estimates
;;; |Re z| <= |z| and |z| <= |Re z| + |Im z| are each one `sqrt-mono', and the
;;; rest is rr-complete applied twice.  Exactly the route
;;; cc-metric-space-proof.scm took for IS-METRIC-SPACE(CC-MS) one storey down.
;;;
;;; Its bill is now rr-complete's own, leaf for leaf -- the completeness of CC
;;; costs what the completeness of RR costs and nothing more.  Both read
;;; `modulo 0' since the NN-order work stamped `nn-add-succ' definitional
;;; (2026-08-24); before that both read `modulo {nn-add-succ}'.
