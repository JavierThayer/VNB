;;; zz-action.scm -- ZZ-ACT: the integer action on an abelian group.
;;;
;;; The NN-action  n.a  (MPOW under the additive monoid, monoid-power.scm) makes
;;; the underlying commutative monoid of an abelian group an NN-semimodule.
;;; EXTENDING it to a ZZ-action -- making the abelian group a ZZ-module -- is a
;;; THEOREM, not automatic: it uses the group INVERSE to define negative scalars
;;; and then re-proves the module axioms across sign boundaries.  This file
;;; carries that step.
;;;
;;;   ZZ-ACT(g, k, a) = k . a       (k in ZZ, a in CARR(g))
;;;
;;; defined by two conditional equations splitting on the sign of k:
;;;   k in NN        :  ZZ-ACT(g, k, a)     = MPOW(g-as-monoid, a, k)
;;;   k in NN, k>0   :  ZZ-ACT(g, -k, a)    = INV(g)( MPOW(g-as-monoid, a, k) )
;;; where g-as-monoid = (ABELIAN-GROUP-AS-MONOID g).  The inverse is exactly the
;;; ingredient unavailable at the monoid / NN-semimodule layer.
;;;
;;; The ZZ-module axioms (zz-act-one, zz-act-add, zz-act-distrib, zz-act-assoc,
;;; zz-act-zero) then hold.  zz-act-add is the keystone: its proof is a sign-case
;;; analysis that reduces the mixed-sign cases to the NN law mpow-add together
;;; with inverse/cancellation -- the work the slogan "every abelian group is a
;;; ZZ-module" silently elides.  Asserted with `informal' warrants in the
;;; library-build phase: each warrant string is a paper-proof SKETCH, not a
;;; machine-checked VNB proof (which would rate the stronger `proof' tier).
;;;
;;; Dependencies: abelian-group.scm (IS-ABELIAN-GROUP, OPR, E, INV),
;;; monoid-power.scm (MPOW, mpow-add), views.scm (ABELIAN-GROUP-AS-MONOID),
;;; number-systems.scm (NN, ZZ, +, *, unary -).

;;; ---- The definition (split on the sign of the integer scalar) -------------
;;; An EXPLICIT definition since 2026-09-19, not a pair of asserted equations.  Until then
;;; this was a bare `add-definition!' OUTSIDE `def-constant', which does not bind
;;; `*current-provenance*': the two equations zz-act-nonneg / zz-act-neg were `asserted'
;;; with no warrant, and every law of ZZ-ACT routed through them.  `def-functoid' installs a
;;; rewrite and no debt; the two equations are THEOREMS of it, statements unchanged
;;; (theorem-library/rake-zz-act.scm).  They overlap at k = 0, consistently:
;;; `abelian-group-inv-iden', proven in the same file, is what the overlap needs.
(def-functoid 'ZZ-ACT '(g_ k_ a_)
  '(IF (IN k_ NN)
       (MPOW (ABELIAN-GROUP-AS-MONOID g_) a_ k_)
       ((INV g_) (MPOW (ABELIAN-GROUP-AS-MONOID g_) a_ (- k_)))))

;;; ---- Endpoints ------------------------------------------------------------
;;; 0 . a = IDEN(g).
;;; zz-act-zero RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; 1 . a = a.
;;; zz-act-one RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; ---- Type ----------------------------------------------------------------
;;; k . a stays in the carrier, for every integer k.
;;; zz-act-type RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; ---- Sign law:  (-k) . a = -(k . a) --------------------------------------
;;; Holds for ALL integers k (the defining zz-act-neg is only the k in NN case).
;;; zz-act-neg-sign RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; ---- Keystone module law:  (j+k) . a = j.a + k.a -------------------------
;;; THE theorem that makes the extension a ZZ-module.  Proof is the sign-case
;;; analysis that reduces every mixed-sign combination to mpow-add plus
;;; inverse/cancellation in the group.
;;; zz-act-add RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-zz-act.scm

;;; ---- Module distributivity:  k . (a + b) = k.a + k.b ---------------------
;;; Needs the group to be ABELIAN (commutativity of OPR) to interleave factors.
;;; zz-act-distrib RAKE-ASM-2 2026-10-12: PROVEN in theorem-library/rake-asm-2.scm under this name; the assumption is retired.

;;; ---- Mixed associativity:  (j*k) . a = j . (k . a) -----------------------
;;; zz-act-assoc RAKE-ASM-2 2026-10-12: PROVEN in theorem-library/rake-asm-2.scm under this name; the assumption is retired.
