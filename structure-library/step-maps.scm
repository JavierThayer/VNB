;;; step-maps.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/mf/mf-mcvocab.scm.
;;; Library: measure.

;;; mf-mcvocab.scm -- step maps into a metric space (construction-of-measures.pdf ch. 2, Def 2.4): DEFINITIONS ONLY.
;;; Agent M-F (target M-C), 2026-10-29 (NEW DEFINITION, the user's to confirm).
;;; DESTINATION: structure-library/step-maps.scm.  Library: measure.
;;; Load window: after the measurable-map vocabulary (IS-MEASURABLE-MAP) and BOREL-SETS.
;;;
;;; IS-STEP-MAP(omega, ca, s, g)   g : X -> pts(s) is measurable (Borel structure on s) and assumes only countably
;;;   many values: there is a sequence of points v with every value g(x) among v(0), v(1), ...  (Def 2.4: "a
;;;   measurable function X -> Y which assumes only countably many values").

(def-predicate 'IS-STEP-MAP '(omega ca s g)
  '(AND (IS-MEASURABLE-MAP omega ca (PTS s) (BOREL-SETS s) g)
        (FORSOME stv_ (AND (IN stv_ (FUN NN (PTS s)))
                           (FORALL stx_ (IMPLIES (IN stx_ omega)
                             (FORSOME stk_ (AND (IN stk_ NN) (= (g stx_) (stv_ stk_))))))))))
(notation! 'IS-STEP-MAP 'kind 'predicate 'arity 4
           'english "$4 is a step map on $1 with $2 into the metric space $3 (measurable, with countably many values)")
