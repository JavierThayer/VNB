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

;;; --------------------------------------------------------------------
;;; The "eps can shrink" facts of the real line.  The static order axioms
;;; (rr-leq-reflexive/antisym/transitive/total/add-compat/mul-nonneg in
;;; number-systems.scm) say nothing about positive reals having no floor --
;;; yet every eps-argument in analysis (uniqueness of limits, convergent =>
;;; Cauchy, limit arithmetic) bottoms out on exactly that.  These two are the
;;; order-density / archimedean face of completeness; accepted as warranted
;;; PSS supports rather than asserted from a deeper RR axiomatisation.

;;; A real below EVERY positive real is non-positive (no smallest positive
;;; real).  The enabler: combined with metric-pos + rr-leq-antisymmetric it
;;; collapses "d(a,b) <= eps for all eps>0" to d(a,b) = 0.
(support 'rr-le-all-pos-nonpos
  '(FORALL x (IMPLIES (IN x RR)
     (IMPLIES (FORALL eps (IMPLIES (POS-RR eps) (<= x eps)))
              (<= x 0)))))
(warrant! 'rr-le-all-pos-nonpos 'well-known
  "A real number that is <= every positive real is <= 0 -- the real line has no smallest positive element.  The order-density / archimedean face of completeness; standard.")

;;; Every positive real splits into two equal positive halves.  Lets the two
;;; eps/2 convergence bounds sum back to eps (existential form avoids naming a
;;; division operator: eps = d + d with d > 0).
(support 'rr-pos-halvable
  '(FORALL eps (IMPLIES (POS-RR eps)
     (FORSOME d (AND (POS-RR d) (= (+ d d) eps))))))
(warrant! 'rr-pos-halvable 'well-known
  "Every positive real eps can be halved: there is a positive d with d + d = eps.  Standard (d = eps/2).")
