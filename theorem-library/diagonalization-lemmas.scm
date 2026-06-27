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
(support 'nn-step-strictly-mono
  '(FORALL g
     (IMPLIES (IN g (FUN NN NN))
       (IMPLIES
         (FORALL k (IMPLIES (IN k NN) (< (g k) (g (succ k)))))
         (STRICTLY-MONO-NN g)))))
(warrant! 'nn-step-strictly-mono 'well-known
  "g:NN->NN with g(k) < g(succ k) for all k is strictly monotone.  For m < n,
   write n reached from m by succ-steps and chain g(m) < g(m+1) < ... < g(n)
   by transitivity of < (rr-lt-trans); formally NN-induction on n using
   m < succ n  iff  m <= n.  STRICTLY-MONO-NN also wants g in FUN(NN,NN),
   supplied as the hypothesis.  Textbook.")

;;; -----------------------------------------------------------------------
;;; L2.  nn-nested-subset-chain -- a descending family is a chain.
;;;
;;; If T(succ k) subset T(k) at every step, then T(j) subset T(k) whenever
;;; k <= j.  Pure SUBSET-transitivity walked along NN; NN-induction on j
;;; with the same m <= succ n case-split.  Generic over T (any NN-indexed
;;; family of classes -- T need not land in any particular codomain).
(support 'nn-nested-subset-chain
  '(FORALL T
     (IMPLIES
       (FORALL k (IMPLIES (IN k NN) (SUBSET (T (succ k)) (T k))))
       (FORALL k (IMPLIES (IN k NN)
         (FORALL j (IMPLIES (IN j NN)
           (IMPLIES (<= k j) (SUBSET (T j) (T k))))))))))
(warrant! 'nn-nested-subset-chain 'well-known
  "A descending family T(0) ⊇ T(1) ⊇ ... satisfies T(j) subset T(k) for every
   k <= j.  NN-induction on j: j=k gives T(k) subset T(k) (reflexivity); the
   step composes T(succ j) subset T(j) (hypothesis) with T(j) subset T(k) (IH)
   by transitivity of subset.  Pure order bookkeeping; generic over T.")

;;; -----------------------------------------------------------------------
;;; L3.  inf-subset-nn-unbounded -- an infinite subset of NN is unbounded.
;;;
;;; For T in INF-SUBSETS(NN) and any threshold u in NN, some element of T
;;; strictly exceeds u.  This is the one genuinely set-theoretic input to
;;; the diagonal construction: it is what makes the step set
;;; { x in T : u < x } nonempty, so the recursion never stalls.  Proof is
;;; the contrapositive cardinality fact (a bounded subset of NN is finite).
(support 'inf-subset-nn-unbounded
  '(FORALL T
     (IMPLIES (IN T (INF-SUBSETS NN))
       (FORALL u (IMPLIES (IN u NN)
         (FORSOME y (AND (IN y NN) (AND (IN y T) (< u y)))))))))
(warrant! 'inf-subset-nn-unbounded 'well-known
  "An infinite subset T of NN is unbounded: if every y in T satisfied y <= u,
   then T subset {0,...,u} = ORD-SEGMENT(succ u), a finite set, forcing CARD T
   in NN and contradicting T in INF-SUBSETS(NN).  Hence some y in T has u < y;
   and y in NN since T subset NN.  The contrapositive 'bounded subset of NN is
   finite'.")
