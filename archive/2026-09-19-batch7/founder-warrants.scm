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
;;; RETIRED 2026-09-17 (proven): finsum-fubini -- theorem-library/rake-finsum-core.scm (rake batch M)
;;; RETIRED 2026-09-14 (proven): card-singleton -- theorem-library/card-singleton-proof.scm
;;; RETIRED 2026-09-14 (proven): ord-segment-nn-succ -- theorem-library/ord-segment-nn-succ-proof.scm
;;; RETIRED 2026-09-14 (proven): ord-segment-nn-subset -- theorem-library/ord-segment-nn-subset-proof.scm

;;; -----------------------------------------------------------------------
;;; FINSUM family -- the finite sum over an abelian group, FINSUM(ag, f, S).


(warrant! 'finsum-singleton 'well-known
  "A one-element sum is its single term.  FINSUM enumerates {x} as a length-1
   sequence and folds (IDEN ag) with f(x); the identity law collapses
   (IDEN ag) MUL f(x) to f(x).")


(warrant! 'finsum-well-defined 'informal
  "FINSUM is DEFINED by picking some enumeration of S and folding; this says
   the value does not depend on WHICH enumeration.  Any two bijections from
   ord-segment(card S) onto S differ by a permutation of the index segment,
   so the claim is exactly the permutation-invariance of the abelian-group
   sum -- sum-ag-permutation-invariance, whose (archived) proof is an NN
   induction splicing one summand out and reordering the rest, using only
   associativity and commutativity.")


;;; -----------------------------------------------------------------------
;;; METRIC / analysis -- genuine theorems (NOT definitional unfoldings).


;;; -----------------------------------------------------------------------
;;; ORDINAL-SEGMENT family -- foundational facts about ord-segment(n) =
;;; {k : k < n}, the von Neumann order on the naturals.


(warrant! 'union-empty-left 'well-known
  "Unioning with the empty set changes nothing.  By extensionality: y is in
   (empty-set union a) iff y is in empty-set or y is in a iff y is in a, since
   nothing is in empty-set.")





(warrant! 'ord-segment-trans 'well-known
  "Transitivity of the segment order: i in ord-segment(k) and k in
   ord-segment(m) mean i < k and k < m, hence i < m, i.e. i in ord-segment(m).
   This is transitivity of the strict ordinal order (membership on the von
   Neumann ordinals).")

(warrant! 'succ-nn-ord 'informal
  "On the naturals the arithmetic successor and the ordinal successor agree.
   NN is constructed as the ordinals below omega; for n in NN the arithmetic
   succ(n) and the ordinal succ_ord(n) = n union {n} name the same element.
   Equality by the coherence of the NN construction with the ordinals.")

;;; -----------------------------------------------------------------------
;;; COUNTING / recurrence -- finite enumeration and the counting recurrences.




(warrant! 'permutation-recurrence 'informal
  "The factorial recurrence.  A permutation of a succ(n)-element set is fixed
   by the image of the new point (succ(n) choices) together with a permutation
   of the remaining n (card(permutations(n)) each), and the two choices are
   independent: card(permutations(succ n)) = succ(n) * card(permutations(n)).
   Base case permutations-zero.")

(warrant! 'injection-extension-recurrence 'informal
  "Counting injections by extending the domain one point.  An injection from
   a union {b} into c restricts to an injection from a into c, and then sends b
   to any c-point not already in the image; card(a) points are used, leaving
   card(c) - card(a) = m choices, independent of the restriction.  Hence
   m * card(injection(a, c)).  The subtraction-free hypothesis card(c) =
   card(a) + m supplies m directly.")

(warrant! 'nn-enum-spec 'informal
  "nn-enum(s) lists an infinite set of naturals in increasing order: the order
   isomorphism NN -> s defined by recursion, each value the least element of s
   strictly above the previous.  Total because s, being infinite, is unbounded
   in NN, so a next element always exists; strictly monotone by construction.")

;;; -----------------------------------------------------------------------
;;; ANALYSIS -- subsequences, choice, continuity comparisons.



;; diagonalization was here (asserted 'informal); now PROVEN to QED in
;; theorem-library/diagonalization.scm, so its warrant lives at the proof.




;;; -----------------------------------------------------------------------
;;; SUM (algebra) -- finite sums over groups and rings.

(warrant! 'sum-ag-permutation-invariance 'informal
  "Reordering the summands of a finite abelian-group sum leaves it unchanged.
   Proof (archived, originally mechanized 2026-05-21): NN-induction on the
   number of summands; the step splices one summand out and reorders the rest
   (sum-ag-splice-out), using only associativity and commutativity -- inverses
   never appear.  The foundational fact underlying all unordered summation.")



(warrant! 'well-ordering-principle 'well-known
  "Every set is in bijection with the ordinal segment of its cardinal -- i.e.
   every set can be enumerated by an ordinal.  The classical well-ordering
   theorem, equivalent to the axiom of choice, which VNB carries as a global
   operator; too expensive to mechanize and not in active doubt.  This is the
   canonical PSS member named in the source.")

;;; cartesian-decompose -- moved here 2026-09-14 from theorem-library/finsum-fiber.scm, because
;;; theorem-library/matof-in-mat.scm (loaded ~450 entries before finsum-fiber) bills it, and a
;;; `warrant!' registered AFTER a citing qed reads as `trust: none' at load time.
