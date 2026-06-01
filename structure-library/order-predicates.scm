;;; order-predicates.scm -- derived order predicates on the kernel <=.
;;;
;;; The kernel has <= as a primitive predicate but no strict <, and the
;;; "eps > 0 for eps in RR" idiom (used pervasively in analytic axioms
;;; like cc-complete) is verbose:
;;;
;;;   (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
;;;
;;; Two named definitions so future axioms (and proofs) read cleanly:
;;;
;;;   (< x y)       <=>  (AND (<= x y) (NOT (= x y)))
;;;   (POS-RR r)    <=>  (AND (IN r RR) (<= 0 r) (NOT (= 0 r)))
;;;
;;; Existing axioms keep the verbose form (opt-in retrofit deferred).
;;; See [[feedback-no-closure-axiom-proliferation]] -- these are
;;; definitional, not closure axioms, so they pass the bar.
;;;
;;; Not extended to arith-eval: ground decisions on `<` still go through
;;; the unfold via the iff.  A future pass may dispatch arith-eval on
;;; `<` directly.

(def-predicate '< '(x y)
  '(AND (<= x y) (NOT (= x y))))

(def-predicate 'POS-RR '(r)
  '(AND (IN r RR) (<= 0 r) (NOT (= 0 r))))
