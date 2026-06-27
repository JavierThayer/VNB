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

;;; -----------------------------------------------------------------------
;;; ORDINAL-SEGMENT family -- foundational facts about ord-segment(n) =
;;; {k : k < n}, the von Neumann order on the naturals.

(warrant! 'card-singleton 'well-known
  "A singleton has cardinality one.  {x} is in bijection with ord-segment(1) =
   {0} via 0 |-> x, and card is read off that bijection: card({x}) = succ(0).")

(warrant! 'union-empty-left 'well-known
  "Unioning with the empty set changes nothing.  By extensionality: y is in
   (empty-set union a) iff y is in empty-set or y is in a iff y is in a, since
   nothing is in empty-set.")

(warrant! 'ord-segment-zero-no-members 'well-known
  "ord-segment(0) is empty.  ord-segment(n) = {k : k < n}; nothing lies below
   0, the least ordinal, so it has no members.")

(warrant! 'ord-segment-self 'well-known
  "No ordinal lies below itself.  ord-segment(n) = {k : k < n}, and k < n is
   irreflexive (the strict order is well-founded), so n is not among its own
   predecessors.")

(warrant! 'ord-segment-nn-subset 'well-known
  "Members of a finite ordinal segment are naturals.  ord-segment(m) =
   {k : k < m}; NN is an initial segment of the ordinals, closed downward, so
   every k below m in NN is itself in NN.")

(warrant! 'ord-segment-nn-succ 'well-known
  "The successor segment adds exactly its top point: ord-segment(succ n) =
   ord-segment(n) union {n}.  Immediate from succ(n) = n union {n} on the
   ordinals, so k < succ(n) iff k < n or k = n.")

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

(warrant! 'fin-enum-is-bijection 'informal
  "fin-enum(s) is the chosen enumeration of a finite set: a bijection from
   ord-segment(card s) onto s.  Existence of SOME such bijection is exactly
   card(s) in NN (the definition of finiteness); fin-enum names one, using
   VNB's choice operator to pick it.")

(warrant! 'enum-fam-in-fun 'informal
  "enum-fam(ag, f, phi, n) is a total function NN -> (A ag): on indices i < n
   it returns f(phi(i)), in the carrier since f maps into (A ag); on i >= n it
   returns the identity (E ag), in the carrier by the identity law.  Total and
   carrier-valued, hence in fun(NN, A ag).  Routine typing, no induction.")

(warrant! 'permutations-zero 'well-known
  "There is exactly one permutation of the empty set -- the empty function --
   so card(permutations(0)) = succ(0) = 1.")

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

(warrant! 'subsequence-capture 'informal
  "Every infinite set of naturals carries a strictly increasing enumeration.
   Take f = nn-enum(s); nn-enum-spec gives exactly that f is in fun(NN, s) and
   strictly order-preserving.  subsequence-capture is the existential shadow
   of nn-enum-spec.")

(warrant! 'dc-on-nn 'informal
  "The principle of dependent choice over NN.  Given a step relation in which
   every (k, u) has at least one successor y, a choice function picks each
   f(succ k) from the nonempty set of successors of (k, f(k)), starting from a;
   recursion on NN assembles f in fun(NN, x).  Derivable from VNB's global
   choice operator applied to the (hypothesis-nonempty) successor sets.")

;; diagonalization was here (asserted 'informal); now PROVEN to QED in
;; theorem-library/diagonalization.scm, so its warrant lives at the proof.

(warrant! 'pigeonhole-infinite 'informal
  "Infinite pigeonhole: an infinite set mapped to finitely many boxes fills
   some box infinitely.  Contrapositive: if every fiber pi^{-1}(c) were finite,
   s would be a union of card(f)-many finite sets, hence finite -- contra
   card(s) not in NN.  So some fiber has card not in NN.")

(warrant! 'continuous-is-continuous-at 'informal
  "A globally continuous map is continuous at every point.  IS-CONTINUOUS(f)
   is the metric IS-HOM condition stated over the whole space; specializing it
   at a fixed a in x(s) yields exactly continuity-at-a.  The pointwise notion
   is the global one localized.")

(warrant! 'uniformly-continuous-is-continuous 'informal
  "Uniform continuity implies continuity.  The uniform delta -- one delta per
   epsilon, good at every point -- serves as the pointwise delta at each point,
   so IS-UNIFORMLY-CONTINUOUS entails IS-CONTINUOUS by forgetting uniformity.")

;;; -----------------------------------------------------------------------
;;; SUM (algebra) -- finite sums over groups and rings.

(warrant! 'sum-ag-permutation-invariance 'informal
  "Reordering the summands of a finite abelian-group sum leaves it unchanged.
   Proof (archived, originally mechanized 2026-05-21): NN-induction on the
   number of summands; the step splices one summand out and reorders the rest
   (sum-ag-splice-out), using only associativity and commutativity -- inverses
   never appear.  The foundational fact underlying all unordered summation.")

(warrant! 'sum-set-left-scalar 'informal
  "Left distributivity of a ring element across a finite sum.  Induction on
   card(x): the step applies the ring's left-distributive law
   a*(u + v) = a*u + a*v over finsum-insert.  Mirror: sum-set-right-scalar.")

(warrant! 'sum-set-right-scalar 'informal
  "Right distributivity across a finite sum, the mirror of sum-set-left-scalar:
   induction on card(x) using (u + v)*b = u*b + v*b.")

(warrant! 'well-ordering-principle 'well-known
  "Every set is in bijection with the ordinal segment of its cardinal -- i.e.
   every set can be enumerated by an ordinal.  The classical well-ordering
   theorem, equivalent to the axiom of choice, which VNB carries as a global
   operator; too expensive to mechanize and not in active doubt.  This is the
   canonical PSS member named in the source.")
