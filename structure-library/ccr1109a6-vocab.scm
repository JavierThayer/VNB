;;; ccr1109a6-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-A6), wired 2026-11-10 from scratchpad/ccr1109a6/ccr1109a6-vocab.scm.
;;; Library: complex-analysis.

;;; ccr1109a6-vocab.scm -- the extension of a character of a subgroup H of an abelian group G to H + <b>
;;; (CCR.pdf section 6.1.1: "The additive group of F_q has a non-trivial character").  DEFINITIONS ONLY.
;;; Agent CCR-1109-A6, 2026-11-09.  Destination: structure-library/ccr1109a6-vocab.scm.
;;; Library: algebra (abelian groups, ZZ-ACT, the complex exponential as a number).  Load window: after
;;; structure-library/zz-action (ZZ-ACT), abelian-group, and the file defining cc-exp.
;;;
;;;   ADJOIN-CHAR-VALUE(G, H, chi, b, t, y)   the value at y = p + k.b (p in H, k in ZZ) of the extension of the
;;;       character chi of H to H + <b> with b |-> exp(t): the unique w with w = chi(p) exp(k t) for some such
;;;       representation (an IOTA confined to CC, so that a VNB-LAMBDA over it is a set; it denotes when y lies in H + <b> and chi(m.b) = exp(m t) for the least
;;;       m >= 1 with m.b in H: theorem-library/ccr1109a6-chars, subgroup-adjoin-value).  A named functoid and
;;;       not an IOTA written inside a VNB-LAMBDA, because lam-b does not contract a lambda whose body holds an
;;;       IOTA (see the report, finding 1).
;;; Binders a6v*_.

(def-functoid 'ADJOIN-CHAR-VALUE '(a6vg_ a6vh_ a6vc_ a6vb_ a6vt_ a6vy_)
  '(IOTA a6vw_ (AND (IN a6vw_ CC) (FORSOME a6vq_ (AND (IN a6vq_ a6vh_) (FORSOME a6vl_ (AND (IN a6vl_ ZZ)
     (AND (= a6vy_ ((OPR a6vg_) a6vq_ (ZZ-ACT a6vg_ a6vl_ a6vb_)))
          (= a6vw_ (* (a6vc_ a6vq_) (cc-exp (* a6vl_ a6vt_))))))))))))
(notation! 'ADJOIN-CHAR-VALUE 'kind 'functoid 'arity 6
           'english "the value at $6 of the extension of the character $3 of $2 to $2 + <$4> with $4 |-> exp($5)")
