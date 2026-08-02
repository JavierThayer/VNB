;;; rr-ms-dist.scm -- the distance of RR-MS, on the surface.
;;;
;;;     ((DIST RR-MS) u v)  ==  abs(u - v)
;;;
;;; RR-MS is the 2-tuple (RR, lambda(x,y). |x-y|) -- numeric-instances.scm, via
;;; declare-instance!, which installs the slot equation RR-MS@DIST.  So the
;;; distance is DEFINITIONALLY |u-v| and this equation is not new mathematics.
;;; It is worth a name anyway: every proof that unfolds a metric predicate at
;;; RR-MS lands on ((DIST RR-MS) u v) and has to walk the accessor down to the
;;; surface before any RR reasoning applies.  Generalising IS-EQUICONTINUOUS to
;;; (s t fam) put that detour on the path of the whole Ascoli arc, since its
;;; consequent is now d_t(...) rather than the abs form it used to carry.
;;;
;;; PROVED, not asserted -- three steps, and the interesting part is that there
;;; are only three:
;;;   mac RR-MS@DIST   the slot equation reduces the term in OPERATOR position,
;;;                    which `subst' could not do (CLAUDE.md: a macete can).
;;;   lam-b            beta-reduces ((VNB-LAMBDA (LIST x y) body) u v) directly.
;;;                    The tupled bind-spec applied to TWO arguments needs no
;;;                    apply-tupling-2 detour; pi-lambda-beta! takes it as is.
;;;   qrfl             t == t, unconditionally.
;;;
;;; Stated with `==' and UNGUARDED on purpose.  `=' is strict, so an `=' form
;;; would need a definedness witness for abs(u-v) at every use and would carry
;;; (IN u RR) guards a rewrite does not want.  `==' holds for all u, v and makes
;;; the equation usable as a macete with no side conditions.

(sp (make-wff '(FORALL u_ (FORALL v_
      (== ((DIST RR-MS) u_ v_) (abs (- u_ v_)))))))
(di)
(mac 'RR-MS@DIST)
(lam-b)
(qrfl)
(qed 'rr-ms-dist)
(category! 'rr-ms-dist 'analysis)
