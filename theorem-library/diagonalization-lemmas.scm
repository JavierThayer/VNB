;;; theorem-library/diagonalization-lemmas.scm
;;;
;;; Three GENERIC, reusable supports that the honest machine proof of
;;; `diagonalization' (diagonalization.scm) rests on.  None of them is
;;; the diagonal argument itself; each is a piece of ambient mathematics
;;; (a monotonicity induction, a descending-chain induction, an
;;; infinite-set fact) whose mechanical proof is a routine NN-induction
;;; with no library payoff to grind out -- exactly the intake discipline
;;; for the PSS.  diagonalization is then assembled ON TOP of these by
;;; genuine kernel steps (the dc-on-nn-pred construction, totality, the
;;; SEP/beta bookkeeping, and the f(j) in S(j) induction are all done in
;;; the proof script, not asserted).
;;;
;;; Loaded after cauchy-subsequence.scm (needs STRICTLY-MONO-NN) and
;;; inf-subsets / order-predicates, BEFORE diagonalization.scm.
;;; RETIRED 2026-09-14 (proven): inf-subset-nn-unbounded -- theorem-library/nn-infinite.scm

;;; -----------------------------------------------------------------------
;;; L1.  nn-step-strictly-mono -- consecutive-increasing => strictly monotone.
;;;
;;; A sequence g : NN -> NN that strictly increases at every single step
;;; (g(k) < g(succ k)) is strictly monotone outright (m < n => g(m) < g(n)).
;;; This is the standard "chain the consecutive gaps by transitivity"
;;; fact; mechanically it is an NN-induction on n with the succ/<
;;; case-split (m < succ n  iff  m <= n), the same ORD-SEGMENT/succ grind
;;; as scratch-succmono.  Generic over g; reused by every subsequence
;;; construction that builds its reindexing one step at a time.
;;; nn-step-strictly-mono RETIRED 2026-09-19 (rake batch 6): proven modulo 0 in theorem-library/rake-subseq-leaves.scm

;;; -----------------------------------------------------------------------
;;; L2.  nn-nested-subset-chain -- PROVEN 2026-08-03, and no longer here.
;;;
;;; It was asserted at this point, `well-known', with the note that its
;;; mechanical proof was "a routine NN-induction with no library payoff to grind
;;; out".  The shape was right and the cost estimate was wrong: it is forty
;;; lines.  See theorem-library/nn-nested-subset-chain-proof.scm, which loads
;;; before diagonalization.scm and installs the same name, so citations here and
;;; downstream are unchanged.

;;; -----------------------------------------------------------------------
;;; L3.  inf-subset-nn-unbounded -- an infinite subset of NN is unbounded.
;;;
;;; For T in INF-SUBSETS(NN) and any threshold u in NN, some element of T
;;; strictly exceeds u.  This is the one genuinely set-theoretic input to
;;; the diagonal construction: it is what makes the step set
;;; { x in T : u < x } nonempty, so the recursion never stalls.  Proof is
;;; the contrapositive cardinality fact (a bounded subset of NN is finite).
