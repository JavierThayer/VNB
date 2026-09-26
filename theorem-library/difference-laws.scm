;;; difference-laws.scm -- the two DIFFERENCE laws, PROVEN.
;;;
;;; They stood as asserted supports in prod-of-sums.scm, warranted `well-known',
;;; and were the ENTIRE residue of four bills: qq-field-is-field,
;;; qq-field-recip-type, qq-line-is-module, and part of field-is-field-ring.
;;;
;;; The content is that there was nothing to assert.  DIFFERENCE is now a
;;; def-functoid for COMPLEMENT-IN (prod-of-sums.scm), whose two laws are KERNEL
;;; AXIOMS -- `complement-in-membership' (library.scm:731) and
;;; `complement-in-set-closure' (library.scm:726) -- and the supports restated
;;; them verbatim under the other spelling.  So each proof is: unfold the
;;; functoid, cite the kernel axiom, done.  `modulo 0', no oracles.
;;;
;;; The names are the ones the supports had, so every citation keeps working
;;; (field-ring-view.scm:149,165; qq-field-is-field.scm; pss-topics.scm).
;;;
;;; UNFOLD BEFORE PEELING.  `di' is greedy: on the membership statement it takes
;;; the three universals, then the IFF, then splits the AND -- and by then the
;;; focus goal is `x in u', which contains no DIFFERENCE for `mac' to rewrite
;;; ("macete not applicable", twice, and then `prop' reports a countermodel).
;;; `mac' rewrites under binders, so unfolding FIRST costs nothing and leaves a
;;; propositional tautology that `prop' closes in one move.

;;; x in (U \ B)  iff  x in U and x not in B.
;;; U, NOT X: the reader case-folds X to x, collapsing (IN x X) to (IN x x).
(sp (make-wff '(FORALL U (FORALL B (FORALL x
      (IFF (IN x (DIFFERENCE U B))
           (AND (IN x U) (NOT (IN x B)))))))))
(mac 'DIFFERENCE)                     ; ... iff x in complement-in(u,b) ...
(mac 'complement-in-membership)       ; ... a tautology ...
(let peel ((fuel 8))
  (let ((g (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
    (when (and (> fuel 0) (memq (car g) '(FORALL IMPLIES)))
      (di) (peel (- fuel 1)))))
(prop)
(qed 'difference-membership)
(topic! 'difference-membership 'plumbing)

;;; X \ B is a set whenever X is -- it is COMPLEMENT-IN's sethood closure.
(sp (make-wff '(FORALL X (IMPLIES (IN X SET)
      (FORALL B (IN (DIFFERENCE X B) SET))))))
(di) (di)
(mac 'DIFFERENCE)
(fact 'complement-in-set-closure 'X 'B)
(ass)
(qed 'difference-set)
(topic! 'difference-set 'plumbing)
