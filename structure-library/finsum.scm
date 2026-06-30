;;; finsum.scm -- FINSUM: summation of an abelian-group-valued function
;;;               over an arbitrary finite set.
;;;
;;; FINSUM(ag, f, S) sums f over the finite set S, in the abelian group ag.
;;; It is defined by choosing an enumeration of S -- a bijection
;;; ORD-SEGMENT(CARD S) -> S -- and summing f along it with SUM-AG.
;;;
;;; sum-ag-permutation-invariance is what makes the result independent of
;;; which enumeration CHOICE returns; the theorem finsum-well-defined (in
;;; proven-theorems.scm) records that, and frees later proofs from the
;;; CHOICE in the definition.
;;;
;;; The set parameter is named S, not A: A is the carrier accessor of every
;;; algebraic structure (a registered constant), so a parameter A would
;;; shadow it.  Likewise the enumeration parameter is phi, not e: e would
;;; case-fold onto the identity accessor E.  See structures.scm header.
;;;
;;; Dependencies: sequences.scm (SUM-AG), cardinality.scm (CARD,
;;; card-finite-bij), bijection.scm (BIJECTION), ordinals.scm (ORD-SEGMENT),
;;; abelian-group.scm.

;;; -----------------------------------------------------------------------
;;; FIN-ENUM(S) -- a chosen enumeration of the finite set S: a bijection
;;; ORD-SEGMENT(CARD S) -> S.
;;;
;;; When S is finite (CARD S in NN), card-finite-bij guarantees the class
;;; BIJECTION(ORD-SEGMENT(CARD S), S) is inhabited, so by choice-axiom
;;; FIN-ENUM(S) is in that class.  Which enumeration CHOICE returns is
;;; immaterial: finsum-well-defined shows the sum does not depend on it.

(def-functoid 'FIN-ENUM '(S)
  '(CHOICE (BIJECTION (ORD-SEGMENT (CARD S)) S)))

;;; -----------------------------------------------------------------------
;;; ENUM-FAM(ag, f, phi, n) -- the family SUM-AG actually consumes.
;;;
;;;   ENUM-FAM(ag,f,phi,n)(i) = f(phi(i))   for i in ORD-SEGMENT(n)
;;;   ENUM-FAM(ag,f,phi,n)(i) = E(ag)       otherwise
;;;
;;; phi is an enumeration ORD-SEGMENT(n) -> S, so f(phi(i)) is only typed
;;; into A(ag) for i in ORD-SEGMENT(n).  The IF guard fills indices outside
;;; the segment with the identity E(ag), making ENUM-FAM total: it is in
;;; FUN(NN, A(ag)) whenever f maps into A(ag) and ag is a group.  That
;;; totality is what lets SUM-AG's lemmas (all typed FUN(NN,A(ag))) apply.
;;; The guard does not change any sum: SUM-AG(ag,_,n) only reads indices in
;;; ORD-SEGMENT(n), where the IF reduces to its then-branch.

(def-functoid 'ENUM-FAM '(ag f phi n)
  '(VNB-LAMBDA i (IF (IN i (ORD-SEGMENT n))
                     (f (phi i))
                     (ID ag))))

;;; -----------------------------------------------------------------------
;;; FINSUM(ag, f, S) -- sum of f over the finite set S, in abelian group ag.
;;;
;;;   FINSUM(ag, f, S) = SUM-AG(ag, ENUM-FAM(ag, f, FIN-ENUM(S), CARD S),
;;;                             CARD S)
;;;
;;; i.e. enumerate S as FIN-ENUM(S)(0), ..., FIN-ENUM(S)(CARD S - 1) and
;;; multiply f of those, in ag.

(def-functoid 'FINSUM '(ag f S)
  '(SUM-AG ag (ENUM-FAM ag f (FIN-ENUM S) (CARD S)) (CARD S)))

;;; -----------------------------------------------------------------------
;;; INSERT-LAST(phi, x, n) -- the append-to-enumeration construction.
;;;
;;;   INSERT-LAST(phi,x,n)(i) = phi(i)   for i in ORD-SEGMENT(n)
;;;   INSERT-LAST(phi,x,n)(i) = x         otherwise (in particular at i = n)
;;;
;;; Given an enumeration phi : ORD-SEGMENT(n) -> S and an element x not in S,
;;; INSERT-LAST(phi,x,n) is a bijection ORD-SEGMENT(succ n) -> S u {x} that
;;; agrees with phi below n and places x at index n.  This is what lets
;;; sum-ag-succ peel f(x) as the last term of FINSUM over S u {x}; see
;;; finsum-insert (proven-theorems.scm).  Sibling of DELETE-AT (bijection.scm)
;;; -- delete-at removes an index, insert-last appends one.
;;;
;;; A genuine definition (def-functoid), not an axiom: the two characterising
;;; equations are recovered by  mac INSERT-LAST + lam-b + if-true/if-false.

(def-functoid 'INSERT-LAST '(phi x n)
  '(VNB-LAMBDA i (IF (IN i (ORD-SEGMENT n))
                     (phi i)
                     x)))
