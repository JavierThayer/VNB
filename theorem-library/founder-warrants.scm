;;; founder-warrants.scm -- credentials for founding PSS members.
;;;
;;; Several founding entries of the Proof Support Set were admitted before
;;; warrants were standard, so they sit in the library unjustified -- a member
;;; the engine trusts and fires freely, with no comprehensible account on file
;;; of WHY we accept it.  Since these are asserted (the vnb-test authorities
;;; never re-prove them), the warrant IS the member's credentials: a plain
;;; reading of what it says plus the grounds for trusting it without a machine
;;; proof.  This file supplies those, retroactively, in one reviewable roster.
;;;
;;; Loaded last, after every result it warrants is installed.  `register-warrant!`
;;; propagates each to the auto-generated -rev companion, so only the forward
;;; needs a letter here.
;;;
;;; Voice: name the standard argument (the induction, the defining fold, the
;;; proven lemma it reduces to) -- enough that a skeptical reader sees the
;;; proof's shape without our having mechanized it.

;;; -----------------------------------------------------------------------
;;; FINSUM family -- the finite sum over an abelian group, FINSUM(ag, f, S).

(warrant! 'finsum-empty 'well-known
  "The empty sum is the group identity.  FINSUM is the SUM-AG fold over an
   enumeration of S; at cardinality 0 there are no summands and the fold
   returns its seed (E ag).  Definitional in all but name.")

(warrant! 'finsum-singleton 'well-known
  "A one-element sum is its single term.  FINSUM enumerates {x} as a length-1
   sequence and folds (E ag) with f(x); the identity law collapses
   (E ag) MUL f(x) to f(x).")

(warrant! 'finsum-type 'informal
  "Closure of the finite sum on the carrier.  Induction on card(S): the fold
   seeds at (E ag), in (A ag) by the identity law, and each step applies
   (MUL ag), which closes on (A ag) by the group's binary-operation typing.
   No inverses used -- the same argument as finsum-comm-monoid-type.")

(warrant! 'finsum-well-defined 'informal
  "FINSUM is DEFINED by picking some enumeration of S and folding; this says
   the value does not depend on WHICH enumeration.  Any two bijections from
   ord-segment(card S) onto S differ by a permutation of the index segment,
   so the claim is exactly the permutation-invariance of the abelian-group
   sum -- sum-ag-permutation-invariance, whose (archived) proof is an NN
   induction splicing one summand out and reordering the rest, using only
   associativity and commutativity.")

(warrant! 'finsum-fubini 'informal
  "Interchanging the order of a finite double sum.  Standard finite Fubini:
   induction on card(X), the step distributing the inner sum across the newly
   added outer summand via finsum additivity (finsum-add) and commutativity.
   Both sums are finite, so no convergence hypothesis is needed; holds over
   any abelian group.")

;;; -----------------------------------------------------------------------
;;; METRIC / analysis -- genuine theorems (NOT definitional unfoldings).

(warrant! 'nf-metric-space-is-metric-space 'informal
  "The norm-induced distance d(x,y) = |x - y| on a normed field satisfies the
   metric axioms, so NF-METRIC-SPACE lands in METRIC-SPACE.  Discharge the
   is-metric clauses: non-negativity and (d = 0 iff x = y) from norm
   positive-definiteness, symmetry from |-(u)| = |u|, the triangle inequality
   from subadditivity of the norm applied to (x - y) + (y - z).  A real
   theorem about the construction, not a slot-read -- hence warranted here
   rather than reclassified definitional.")
