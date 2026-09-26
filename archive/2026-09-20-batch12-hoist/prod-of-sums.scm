;;; MOVED 2026-09-20 (batch 12-A) from theorem-library/: this file is VOCABULARY --
;;; definitions, notation and warranted supports, not one proof -- and every theorem
;;; stated with it had to load below it.  Its load.scm slot is unchanged.
;;; RETIRED 2026-09-17 (proven, rake batch P): card-power-nn, power-insert-cover, power-insert-disjoint
;;; (modulo 0), prod-ring-empty (modulo 0), prod-ring-singleton, prod-ring-insert (modulo
;;; finsum-comm-monoid-well-defined) -- theorem-library/rake-combinatorics.scm.
;;; RETIRED 2026-09-17 (proven): prod-ring-type -- theorem-library/rake-finsum-typing.scm
;;; structure-library/prod-of-sums.scm
;;;
;;; The expansion of a finite PRODUCT OF SUMS over a commutative ring:
;;;
;;;   prod_{k in X} (a(k) + b(k))
;;;       = sum_{S subseteq X} (prod_{k in S} a(k)) * (prod_{k in X\S} b(k))
;;;
;;; -- the multilinear / "FOIL over an index set" identity.  Sum on the right
;;; ranges over POWER(X), the powerset (2^|X| terms); each term is a(k) over a
;;; subset S times b(k) over its complement X\S.  Commutativity makes the
;;; product unordered (no enumeration needed) and the regrouping valid.
;;;
;;; This file is the whole dependency tower, stated as warranted Proof Support
;;; Set entries (library-build phase: assert with a warrant, defer the formal
;;; induction).  Three layers:
;;;
;;;   (1) set-minus  -- DIFFERENCE was used in the codebase (field.scm,
;;;                     numeric-instances.scm) but never characterized; its
;;;                     membership / sethood axioms are filled in here.
;;;   (2) powerset   -- POWER(X) finiteness, subset-finiteness, and the
;;;                     insert-split that drives the induction on |X|.
;;;   (3) product    -- the finite-product recurrence (FINSUM's long-promised
;;;                     finsum-insert, finsum.scm:75) and PROD-RING's
;;;                     empty / singleton / insert / closure laws.
;;;
;;; capped by  prod-of-sums-expansion.
;;;
;;; Singletons / one-point extensions are PAIR(x,x) / UNION(X,PAIR(k,k)) to
;;; mesh with card-insert and finite-set-induction (cardinality.scm).
;;;
;;; Dependencies: finprod.scm (FINPROD/PROD-RING), views.scm (COMMUTATIVE-RING-
;;; MULTIPLICATIVE-CM, COMMUTATIVE-RING-ADDITIVE-AG), injection.scm (IMAGE),
;;; cardinality.scm (CARD), monoid.scm (COMM-MONOID), theory.scm (POWER,
;;; DIFFERENCE, UNION, INTERSECTION, PAIR, EMPTY-SET).
;;; RETIRED 2026-09-14 (proven): card-subset-nn -- theorem-library/card-subset-nn.scm (finite-set-induction)
;;; RETIRED 2026-09-14 (proven): finsum-insert -- theorem-library/finsum-insert.scm (modulo finsum-comm-monoid-well-defined)

;;; =======================================================================
;;; Layer 1 -- set difference X \ B
;;; =======================================================================

;;; DIFFERENCE IS *DEFINED*, NOT AXIOMATISED -- and the definition is that it
;;; was COMPLEMENT-IN all along.
;;;
;;; `difference-membership' and `difference-set' stood here as asserted supports
;;; warranted `well-known', and their warrants said the situation plainly:
;;; DIFFERENCE "was already in use (field.scm: NON-ZERO = A \ {ZERO};
;;; numeric-instances.scm) with no characterizing axiom; this records the
;;; standard one."  But the standard one is a KERNEL AXIOM already, under a
;;; different name:
;;;
;;;   difference-membership       x in DIFFERENCE(U,B)     iff x in U and not(x in B)
;;;   complement-in-membership    x in COMPLEMENT-IN(A,B)  iff x in A and not(x in B)   theory.scm:731
;;;   difference-set              X in SET => DIFFERENCE(X,B) in SET
;;;   complement-in-set-closure   A in SET => COMPLEMENT-IN(A,B) in SET                 theory.scm:726
;;;
;;; Verbatim, both pairs.  So DIFFERENCE was COMPLEMENT-IN under a second
;;; spelling, with two asserted laws restating trusted base -- debt for nothing.
;;; It is now a def-functoid, and both laws are PROVEN `modulo 0' in
;;; theorem-library/difference-laws.scm (the proofs need the interactive tactics,
;;; which load at 485; this file is at 395).  The NAMES are unchanged, so every
;;; citation keeps working.
;;;
;;; Same species as SINGLETON, which field-ring-view.scm found had no membership
;;; characterisation at all and defined as MAKE-SET(LIST y).
;;; The DIFFERENCE def-functoid and its notation! MOVED 2026-09-20 (batch 12-A)
;;; to structure-library/set-vocabulary.scm, which loads just after set-basics:
;;; structure-library/field.scm states IS-FIELD's defining IFF with the head and
;;; loads far above this file.  The laws keep their names and their home.

;;; =======================================================================
;;; Layer 2 -- powerset finiteness and the insert-split
;;; =======================================================================

;;; A subset of a finite set is finite.


;;; The powerset of a finite set is finite: |POWER(X)| = 2^|X| in NN.


;;; Insert-split, cover half.  For k not in X, every subset of X u {k} either
;;; avoids k (a subset of X) or is S u {k} for a unique subset S of X.  So
;;; POWER(PTS u {k}) is the union of POWER(X) and the image of POWER(X) under
;;; S |-> S u {k}.  This is the set-level heart of the induction on |X|.


;;; Insert-split, disjointness half.  k not in X, so a subset of X cannot equal
;;; one that contains k -- the two halves are disjoint, and card-union-disjoint
;;; + the injectivity of S |-> S u {k} split the FINSUM cleanly.


;;; =======================================================================
;;; Layer 3 -- the finite-product recurrence and PROD-RING's laws
;;; =======================================================================

;;; finsum-insert: the long-promised insertion recurrence for FINSUM over a
;;; finite set (finsum.scm:75 refers to it as `finsum-insert' but it was never
;;; installed; the insert-last-is-bijection groundwork is in scratch-fs3.scm).
;;; Adding one fresh point k to the index folds in one more factor f(k):
;;;
;;;   FINSUM(m, f, X u {k}) = (OPR m)(FINSUM(m, f, X), f(k))    (k not in X)
;;;
;;; Stated over a commutative monoid (the generality the unordered product
;;; needs); it is the multiplicative twin of the additive sum's recursion and
;;; the workhorse of every induction on |X| below.


;;; PROD-RING over the empty set is the multiplicative identity ONE(R).
;;; (FINSUM over EMPTY-SET is E of the structure = ONE under the mult view.)


;;; PROD-RING over a singleton {x} is f(x).


;;; PROD-RING insertion recurrence: adding a fresh index k multiplies in f(k).
;;; This is finsum-insert at m = R's multiplicative comm-monoid (MUL of the
;;; view reduces to (MUL R)); the workhorse for induction on |X|.


;;; PROD-RING stays in the carrier.


;;; =======================================================================
;;; Capstone -- the product-of-sums expansion
;;; =======================================================================

;;;   prod_{k in X} (a(k) + b(k))
;;;       = sum_{S in POWER(X)} (prod_{k in S} a(k)) * (prod_{k in X\S} b(k))
;;;
;;; LHS: PROD-RING of the pointwise sum a+b over X.
;;; RHS: FINSUM over POWER(X), in R's additive abelian group
;;;      (COMMUTATIVE-RING-ADDITIVE-AG R), of the ring product of the two
;;;      partial products PROD-RING(R,a,S) and PROD-RING(R,b,X\S).
(support 'prod-of-sums-expansion
  '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
      (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
      (FORALL a (IMPLIES (IN a (FUN X (CARR R)))
      (FORALL b (IMPLIES (IN b (FUN X (CARR R)))
        (= (PROD-RING R (VNB-LAMBDA k X ((ADD R) (a k) (b k))) X)
           (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG R)
                   (VNB-LAMBDA S (POWER X) ((MUL R) (PROD-RING R a S)
                                          (PROD-RING R b (DIFFERENCE X S))))
                   (POWER X))))))))))))

(warrant! 'prod-of-sums-expansion 'well-known
  "Expand each binomial factor and collect: choosing a(k) or b(k) at each k in
   X corresponds to a subset S (the k's where a was chosen), contributing
   prod_S a * prod_{X\\S} b; summing over all 2^|X| choices gives the result
   (commutativity makes the regrouping valid).  Formal route: induction on |X|
   via finite-set-induction.  Base |X|=0: prod-ring-empty gives 1, and POWER
   (EMPTY-SET)={EMPTY-SET} contributes ONE*ONE=1.  Step X u {k0}: prod-ring-
   insert factors out (a(k0)+b(k0)), ring-left-dist splits it, and power-
   insert-cover / power-insert-disjoint reindex POWER(PTS u {k0}) into the
   subsets containing vs avoiding k0 -- matching the two distributed sums.")
