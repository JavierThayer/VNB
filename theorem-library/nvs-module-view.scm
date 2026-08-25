;;; nvs-module-view.scm -- THE MODULE BRIDGE OF A NORMED VECTOR SPACE, PROVEN.
;;;
;;; NORMED-VECTOR-SPACE is a SEVEN-slot shape (MODULE's six, plus VNRM at slot
;;; 7), and every module predicate pins length = 6: IS-MODULE, IS-VECTOR-SPACE,
;;; IS-NOETHERIAN and hence IS-FINITE-DIMENSIONAL.  So a normed vector space
;;; reaches the module world only through the projection
;;;
;;;     NORMED-VECTOR-SPACE-AS-MODULE(m) = [scal(m), vec(m), vadd(m),
;;;                                         vzero(m), vneg(m), act(m)]
;;;
;;; (normed-vector-space.scm:136).  Writing `is-finite-dimensional(m)' of a
;;; normed vector space m instead asserts 7 = 6: it is unsatisfiable, and the
;;; five results that did so were VACUOUSLY true (see the statement audit,
;;; audit.scm, and section 2e of test-suite-negative.scm).  The repaired
;;; statements say `is-finite-dimensional(normed-vector-space-as-module(m))'.
;;;
;;; WHAT THAT COSTS, and it is why this file exists.  `def-functor' installs a
;;; functoid and a typing axiom and NO read-off, so nothing in the tree said
;;; what `vec(normed-vector-space-as-module(m))' IS -- and the finite-dimensional
;;; Hahn-Banach argument runs the noetherian maximal-element principle over the
;;; submodules of exactly that carrier.  Six read-offs and one transfer close
;;; the gap.  NOTHING HERE IS ASSERTED: each read-off is the functoid unfold
;;; composed with an NTH projection, both trusted base, and the transfer is the
;;; def-predicate unfold rewritten by them.  All seven are `proven modulo 0'.
;;;
;;; Same recipe, same five steps, as theorem-library/normed-field-ring-view.scm
;;; -- which does this for the OTHER projection a normed vector space needs, of
;;; its scalar field into the six-slot ring world.  `==' (not `='): the
;;; projection's slot value is unconditionally that term, so no definedness
;;; obligation is owed.
;;;
;;; Dependencies: normed-vector-space.scm (the shape and the view),
;;; module.scm (IS-SUBMODULE lives in finite-dimensional.scm), interactive,
;;; proof-debt.  No structure of its own.

;;; ---- file-local driver (the `nmv-' prefix; `slot' is a tactic, not a name we
;;; ---- may bind, and single/double capitals are the case-fold danger zone).

;;; ACC read off the module view of an arbitrary m_, in five steps.  Errors if
;;; the proof does not close -- a silent no-op would install nothing and say
;;; nothing.
(define (nmv-read-off! name acc)
  (sp (make-wff (list 'FORALL 'm_
        (list '== (list acc (list 'NORMED-VECTOR-SPACE-AS-MODULE 'm_))
                  (list acc 'm_)))))
  (di)
  (slot acc)                                   ; the accessor down to (NTH k _)
  (mac 'NORMED-VECTOR-SPACE-AS-MODULE)         ; the functoid unfold
  (nth-r)                                      ; NTH k of a LIST literal
  (slot acc)                                   ; the recovered source accessor
  (qrfl)
  (if (not (proof-done? *ps*))
      (error "nmv-read-off!: proof did not close" name (dk-goal)))
  (qed name)
  (topic! name 'algebra))

;;; =====================================================================
;;; (1) the six slots of the module view
;;; =====================================================================
(nmv-read-off! 'nvs-module-view-scal  'SCAL)
(nmv-read-off! 'nvs-module-view-vec   'VEC)
(nmv-read-off! 'nvs-module-view-vadd  'VADD)
(nmv-read-off! 'nvs-module-view-vzero 'VZERO)
(nmv-read-off! 'nvs-module-view-vneg  'VNEG)
(nmv-read-off! 'nvs-module-view-act   'ACT)

;;; The read-offs, as a list, for a driver that wants to normalise a goal.
(define nvs-module-view-read-offs
  '(nvs-module-view-scal nvs-module-view-vec nvs-module-view-vadd
    nvs-module-view-vzero nvs-module-view-vneg nvs-module-view-act))

;;; =====================================================================
;;; (2) SUBMODULE TRANSFER.  IS-SUBMODULE reads only slots 1-6 of its first
;;;     argument, which is exactly what the view keeps -- so a submodule of m
;;;     is a submodule of the module view of m.  `mac' unfolds BOTH sides of
;;;     the implication at once (a macete rewrites every occurrence in the
;;;     goal); the six read-offs then turn the consequent's accessors into the
;;;     antecedent's, and the remaining goal is P => P.
;;; =====================================================================
(sp (make-wff '(FORALL m_ (FORALL t_
      (IMPLIES (IS-SUBMODULE m_ t_)
               (IS-SUBMODULE (NORMED-VECTOR-SPACE-AS-MODULE m_) t_))))))
(di)                                            ; peels m_, t_ (lands nothing:
                                                ; the antecedent is not a typing)
(mac 'IS-SUBMODULE)
(for-each (lambda (n) (mac n)) nvs-module-view-read-offs)
(di)                                            ; now the antecedent lands
(ass)
(if (not (proof-done? *ps*))
    (error "nvs-module-view: submodule transfer did not close" (dk-goal)))
(qed 'submodule-nvs-module-view)
(topic! 'submodule-nvs-module-view 'algebra)
