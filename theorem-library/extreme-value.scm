;;; extreme-value.scm -- the closed interval [a,b] and the Extreme Value Theorem
;;; (calculus.pdf Ch 2.5; used in Rolle's lemma): a continuous function on a
;;; closed interval attains its maximum and minimum.
;;;
;;; Stated sequentially / limit-free, so the STATEMENT needs no metric-subspace
;;; or IS-COMPACT-on-subset machinery: "f continuous on [a,b]" is just
;;;   forall x in CCINT(a,b). IS-CONTINUOUS-AT(RR-MS, RR-MS, f, x).
;;; EVT is asserted (the proof is the destination -- continuous image of the
;;; compact [a,b] attains its sup; sequentially, a maximizing sequence has a
;;; convergent subsequence by seq-compactness of [a,b], whose limit attains the
;;; max).  It is a witness-manufacturing block: the argmax c feeds Rolle's lemma
;;; by bc*, so the MVT arc assembles from it -- [[automatable-assembly]].

;;; CCINT(a, b) = the closed interval [a, b] = { x in RR : a <= x <= b }.
(def-functoid 'CCINT '(a b)
  '(SEP x RR (AND (<= a x) (<= x b))))

;;; ccint-membership MOVED 2026-08-17 to theorem-library/ccint-basics.scm, where
;;; it is PROVEN `modulo 0'.  It stood here as an `add-to-pss' support whose
;;; `proof' warrant WAS the derivation -- "Separation: x in CCINT(a,b) =
;;; SEP(x in RR | a<=x and x<=b) iff x in RR and a<=x and x<=b, by the SEP
;;; membership kernel rule" -- a proof written in prose and then not run.  One
;;; `mac CCINT' puts the separation in the goal and `sep-me' / `sep-mi' close the
;;; two directions.  The statement is reproduced verbatim there, so every citer
;;; (rolle-proof, interior-extremum-proof, deriv-constant-proof,
;;; deriv-monotone-proof, ivt-proof) is unaffected.

;;; EVT (max) MOVED 2026-08-17 to theorem-library/evt-proof.scm, where it is
;;; PROVEN `modulo 0'.  It stood here as an `add-to-pss' support with a
;;; `reference' warrant naming the sequential proof -- and it was the only
;;; asserted MATHEMATICS in the Fermat -> Rolle -> MVT -> Taylor tower, eleven
;;; bills deep.  What blocked the proof was the sentence in that warrant: it
;;; asked for sequential compactness of [a,b], which the tree does not have and
;;; which needs the whole Heine-Borel apparatus (a metric subspace structure on
;;; a SUBSET, and a continuous image of a compact set).  The supremum route
;;; needs none of it: boundedness on [a,b] and then attainment are two
;;; instances of one creeping principle (theorem-library/ccint-creep.scm), the
;;; same technique that proved IVT.  The statement is reproduced verbatim
;;; there, so every citer -- rolle-proof and through it the whole MVT arc -- is
;;; unaffected.

;;; EVT (min) MOVED 2026-08-17 to theorem-library/evt-min-proof.scm, where it
;;; is PROVEN `modulo 0'.  Its `reference' warrant here read, in full, "apply
;;; extreme-value-max to -f; the argmax of -f is the argmin of f" -- the proof
;;; written in prose and then not run, the same species of comment that hid
;;; integral-domain-cancel-zero.  What made it runnable is
;;; theorem-library/neg-continuous.scm: -f is a member of FUN(RR,RR) and is
;;; continuous wherever f is, both PROVEN, so the reduction adds no debt.  The
;;; statement is reproduced verbatim there, so rolle-proof and the whole MVT
;;; arc are unaffected.
;;;
;;; Both forms are therefore gone from this file, and what remains of it is the
;;; DEFINITION of the closed interval.
