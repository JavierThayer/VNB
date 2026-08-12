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
;;; Stated with `==', and GUARDED on (IN u_ RR), (IN v_ RR).
;;;
;;; It was unguarded until 2026-08-03, on the argument that `==' holds for all
;;; u, v and so makes the equation a macete with no side conditions.  The beta
;;; guard withdrew that argument.  RR-MS@DIST's lambda has domain
;;; CARTESIAN(RR,RR), so off RR the left side is an application outside its
;;; domain -- undefined -- while NOTHING in the theory says abs(u-v) is
;;; undefined there.  `==' is quasi-equality, both-undefined-or-both-equal, and
;;; the unguarded statement claimed the first disjunct at arguments where the
;;; theory declines to say so.  The guards are not a tax on the rewrite; they
;;; are the hypothesis under which the equation was ever true.
;;;
;;; `=' would still be wrong: it is strict, and would additionally assert both
;;; sides defined at every use.  Guarded `==' says exactly what holds.

(define (rmd-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (rmd-di*)                         ; peel binders AND the two guards
  (let lp () (let* ((g (rmd-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

(sp (make-wff (forall-guarded '(u_ v_) '((IN u_ RR) (IN v_ RR))
      '(== ((DIST RR-MS) u_ v_) (abs (- u_ v_))))))
(rmd-di*)
(slot 'DIST)
(lam-b)
(qrfl)
(qed 'rr-ms-dist)
(topic! 'rr-ms-dist 'analysis)
