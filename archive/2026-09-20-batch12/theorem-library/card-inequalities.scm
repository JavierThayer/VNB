;;; card-inequalities.scm -- the two missing CARD inequalities.
;;; ---------------------------------------------------------------------------
;;; NOTE, 2026-09-20 (batch 9-B).  This file was written while cardinality was
;;; AXIOMATISED under the name CARD and the defined constant was its companion
;;; CARD-STAR.  On 2026-09-20 the user made the swap: CARD is the DEFINED
;;; cardinal (structure-library/cardinality.scm), the eight `primitive' axioms
;;; about it are gone, and every proof below now speaks of CARD.  The prose in
;;; this header that contrasts "the axiomatised CARD" with "the defined
;;; cardinal" is HISTORY; the surgery is docs/card-defined-2026-09-20.md.
;;; ---------------------------------------------------------------------------
;;;
;;;     card-subset-mono   B in SET, CARD(B) in NN, SUBSET(A,B)
;;;                          =>  CARD(A) <= CARD(B)
;;;
;;;     card-union-bound   A,B in SET, CARD(A) in NN, CARD(B) in NN
;;;                          =>  CARD(A u B) <= CARD(A) + CARD(B)
;;;
;;; The second is the subadditivity that a CARD-normed commutative monoid of
;;; finite sets needs (union is idempotent, so the norm is subadditive and NOT
;;; additive); the first is the monotonicity law, which does NOT follow from
;;; subadditivity -- A subset B gives A u B = B, so subadditivity yields only
;;; the vacuous CARD(B) <= CARD(A) + CARD(B).
;;;
;;; -----------------------------------------------------------------------
;;; WHY `CARD' AND NOT `CARD'.
;;;
;;; `CARD' (theorem-library/card-defined.scm) is the DEFINED cardinal -- an
;;; IOTA over "least ordinal whose segment bijects onto A" -- and is the
;;; migration target.  Neither inequality is reachable for it today, and the
;;; obstruction is recorded in structure-notes/card-basics-worklist.md:76-78:
;;; `card-insert-curried' and `card-union-disjoint-curried' are BLOCKED on `EXTEND-BY', the
;;; unbuilt second member of the finite-surgery kit (a bijection A -> S(n) has
;;; to be extended to A + {x} -> S(succ n)).  Everything the finite CARD layer
;;; has -- card-from-body, card-bij, card-empty (card-finite.scm) -- computes
;;; a cardinal from a bijection; nothing yet ADDS two cardinals.  Without a
;;; CARD form of card-union-disjoint there is no route to either inequality
;;; that does not first build EXTEND-BY and a concatenation map, which is a
;;; separate piece of work.
;;;
;;; For the axiomatised `CARD', `card-union-disjoint' is on the PRIMITIVE shelf
;;; (structure-library/cardinality.scm:87), and it is the whole engine: split B
;;; as the disjoint union A u (B \ A) and the inequality is NN arithmetic.  So
;;; these are proved for CARD.  When the CARD migration reaches
;;; card-union-disjoint-curried, both proofs below transcribe unchanged -- they touch
;;; no other CARD axiom.
;;;
;;; -----------------------------------------------------------------------
;;; THE BILL, and the one thing that is owed.
;;;
;;; Everything here is primitive except ONE leaf: `card-subset-nn'
;;; (theorem-library/prod-of-sums.scm:66, `asserted' + warrant `well-known'),
;;; "a subset of a finite set is finite".  It is cited twice in each theorem and
;;; it is unavoidable on this route: card-union-disjoint is guarded on
;;; CARD(B \ A) in NN, and nothing on the primitive shelf delivers the
;;; finiteness of a subset.  `card-image-injection' (injection.scm:157) does not
;;; help -- it gives CARD(IMAGE(phi,dm)) = CARD(dm), an EQUALITY on the image,
;;; so the inclusion A -> B returns CARD(A) = CARD(A).
;;;
;;; The fact that WOULD close the gap is card-subset-nn itself, and the worklist
;;; already names its route (card-basics-worklist.md:79-81): `finite-set-induction'
;;; (cardinality.scm:108, primitive, and never yet used in a proof anywhere in
;;; the tree).  That is a separate piece of work; see the note at the end of
;;; this file.
;;;
;;; THE MEASURED BILLS:
;;;
;;;   complement-in-subset               modulo 0
;;;   union-complement-in                modulo 0
;;;   union-as-disjoint                  modulo 0
;;;   intersection-complement-in-empty   modulo 0
;;;   card-subset-mono   modulo {card-subset-nn, nn-add-succ, nn-le-succ}
;;;                        [trust: well-known]
;;;   card-union-bound   modulo {card-subset-nn, nn-add-succ, nn-le-succ,
;;;                              nn-one-le-succ, nn-not-le-zero-pos,
;;;                              nn-le-succ-cases}
;;;                        [trust: well-known]  [oracles: arith]
;;;   card-union-nn      modulo {card-subset-nn}  [trust: well-known]
;;;
;;; card-union-nn is the cleanest of the three: it reaches the cardinal sum by
;;; the same decomposition and then closes with nn-add-closed rather than the
;;; NN ORDER lemmas, so none of the order-lemmas supports appear in its bill and
;;; card-subset-nn is its SOLE leaf.  For that one theorem -- and only that one
;;; -- proving card-subset-nn would take the bill to `modulo 0'.
;;;
;;; AND THE POINT WORTH RECORDING: card-subset-nn is NOT the sole unwarranted
;;; leaf, and it is not even the worst one.  Every other leaf above is an
;;; `asserted' NN order support -- nn-le-succ, nn-one-le-succ,
;;; nn-not-le-zero-pos, nn-le-succ-cases (structure-library/order-lemmas.scm:353,
;;; :345, :248, :241, all warranted `well-known') and nn-add-succ
;;; (structure-library/nn-arith.scm:33, `reference') -- inherited through
;;; nn-le-add-right and nn-add-le-mono, whose own bills carry them.  `well-known' is
;;; below `reference' in *pd-trust-order*, so the tier of both bills is set by
;;; the order-lemmas supports, not by card-subset-nn.
;;;
;;; Consequently PROVING card-subset-nn would move these two bills from
;;; `well-known' to `well-known': it would delete one leaf and change no tier.
;;; That is CLAUDE.md's shadowing rule ("reclassifying or proving a leaf buys
;;; nothing until it is the LAST unwarranted leaf of the bills that name it"),
;;; and it is the reason the finite-set-induction exercise is recorded at the
;;; foot of this file rather than attempted in it.  The leaf worth attacking
;;; first, for these two bills, is the NN order shelf.
;;;
;;; Everything else used is primitive or proven modulo 0:
;;;   primitive  -- class-extensionality, union-membership, union-set-closure,
;;;                 intersection-membership, complement-in-membership,
;;;                 complement-in-set-closure, empty-set-has-no-members,
;;;                 subset-def, card-union-disjoint
;;;   proven     -- subset-mem-fwd, subclass-of-set-is-set (subset-lemmas.scm),
;;;                 nn-le-add-right (nn-order-basics.scm), nn-add-le-mono
;;;                 (nn-order-proof.scm)
;;;
;;; Needs: theory (the base set axioms), structure-library/cardinality,
;;; theorem-library/prod-of-sums (card-subset-nn), theorem-library/subset-lemmas,
;;; theorem-library/nn-order-proof, interactive/proof-debt/driver-kit.

;;; --- file-local helpers (ci- prefix) ------------------------------------

;; Peel the leading FORALL/IMPLIES prefix and stop at the first other head.
;;
;; A bare `di' is NOT enough and that cost a run.  One `di' takes a GUARDED
;; universal whole, but these statements quantify UNGUARDED and then imply:
;; `(FORALL a_ (FORALL b_ (IMPLIES (SUBSET a_ b_) ...)))' loses both binders to
;; the first `di' and KEEPS the implication, so the following `bc*' saw an
;; IMPLIES goal and warned "conclusion of class-extensionality does not match
;; the goal" -- a warning, not an error, after which the rest of the script ran
;; on the unopened goal.  The loop tests the head rather than counting calls;
;; it also stops before `di' can split an AND goal into two leaves.
(define (ci-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(forall implies)))
          (begin (di) (loop))))))

;; Drop every assumption but the ones named.
;;
;; `prop' has an atom cap (*prop-atom-cap*, 12; the search is 2^n) and `fact'
;; lands its WHOLE instantiation chain -- the axiom, each partly-peeled form and
;; the instance.  Three membership citations put the union lemmas below at 16
;; distinct atoms and `prop' declined, naming the count.  Keeping the three
;; fully-instantiated iffs and nothing else brings it to five.  Same device as
;; `mcb-only!' in makeset-card-bound.scm, and for the same reason.
(define (ci-only! . keepers)
  (for-each (lambda (f) (if (not (member f keepers)) (wk f))) (dk-asms)))

;; The shared forward assembly of (6) and (7): from `a_ in SET, CARD a_ in NN,
;; b_ in SET, CARD b_ in NN' in the context, land
;;
;;    SUBSET(B \ A, B)                              [complement-in-subset]
;;    CARD(B \ A) in NN                             [card-subset-nn]
;;    UNION(A,B) = UNION(A, B \ A)                  [union-as-disjoint]
;;    CARD(UNION(A, B \ A)) = CARD A + CARD(B \ A)  [card-union-disjoint]
;;
;; It hardcodes the eigenvariable names a_ and b_, which is safe only because
;; both call sites state their theorem with those binders in that order; the
;; brief's rule is to read eigenvariables off the GOAL, and here the goal is
;; written to supply them.
(define (ci-decompose!)
  (fact 'complement-in-set-closure 'b_ 'a_)
  (fact 'complement-in-subset 'a_ 'b_)
  (have! '(AND (IN b_ SET) (IN (CARD b_) NN)))
  ;; The inclusion B \ A subset B, elementwise -- card-subset-nn spells its
  ;; subset hypothesis out rather than using SUBSET.  Routed through (1) and
  ;; subset-mem-fwd rather than unfolding complement-in-membership and calling
  ;; `prop': by this point the context is well over prop's 12-atom cap.
  (have! '(FORALL z (IMPLIES (IN z (COMPLEMENT-IN b_ a_)) (IN z b_)))
         (lambda () (ci-peel!)
                    (fact 'complement-in-subset 'a_ 'b_)
                    (fact 'subset-mem-fwd '(COMPLEMENT-IN b_ a_) 'b_ 'z)
                    (ass)))
  (have! '(AND (IN (COMPLEMENT-IN b_ a_) SET)
               (FORALL z (IMPLIES (IN z (COMPLEMENT-IN b_ a_)) (IN z b_)))))
  (fact 'card-subset-nn 'b_ '(COMPLEMENT-IN b_ a_))
  (fact 'intersection-complement-in-empty 'a_ 'b_)
  (have! '(AND (IN (COMPLEMENT-IN b_ a_) SET)
               (AND (IN (CARD (COMPLEMENT-IN b_ a_)) NN)
                    (= (INTERSECTION a_ (COMPLEMENT-IN b_ a_)) EMPTY-SET))))
  (have! '(AND (IN a_ SET) (IN (CARD a_) NN)))
  (fact 'card-union-disjoint 'a_ '(COMPLEMENT-IN b_ a_))
  (fact 'union-as-disjoint 'a_ 'b_))

;; Rewrite the goal's CARD(A u B) into CARD A + CARD(B \ A), using the two
;; equations `ci-decompose!' has just landed.
(define (ci-rewrite-union!)
  (subst '(= (UNION a_ b_) (UNION a_ (COMPLEMENT-IN b_ a_))))
  (subst '(= (CARD (UNION a_ (COMPLEMENT-IN b_ a_)))
             (+ (CARD a_) (CARD (COMPLEMENT-IN b_ a_))))))

;;; -----------------------------------------------------------------------
;;; (1) complement-in-subset:  SUBSET(B \ A, B)
;;;
;;; Unguarded: COMPLEMENT-IN and SUBSET are total over classes.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_ (SUBSET (COMPLEMENT-IN b_ a_) b_)))))
  (ci-peel!)
  (mac 'subset-def)
  (ci-peel!)
  (fact 'complement-in-membership 'b_ 'a_ 'x)
  (ci-only! '(iff (in x (complement-in b_ a_)) (and (in x b_) (not (in x a_))))
            '(in x (complement-in b_ a_)))
  (prop)))
(qed 'complement-in-subset)
(topic! 'complement-in-subset 'plumbing)

;;; -----------------------------------------------------------------------
;;; (2) union-complement-in:  SUBSET(A,B)  =>  B = A u (B \ A)
;;;
;;; Stated in THIS orientation on purpose.  The consumer's goal mentions
;;; CARD(B) and wants to rewrite it into CARD(A u (B \ A)); `subst' rewrites
;;; left-to-right in the GOAL, so the bare variable has to be the left side.
;;; That is also why it is `declare-named-only!': a live macete whose left side
;;; is a variable matches every term in every goal.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_
        (IMPLIES (SUBSET a_ b_)
                 (= b_ (UNION a_ (COMPLEMENT-IN b_ a_))))))))
  (ci-peel!)
  (bc* 'class-extensionality)
  (ci-peel!)
  (fact 'union-membership 'a_ '(COMPLEMENT-IN b_ a_) 'x)
  (fact 'complement-in-membership 'b_ 'a_ 'x)
  (have! '(IMPLIES (IN x a_) (IN x b_))
         (lambda () (ci-peel!) (fact 'subset-mem-fwd 'a_ 'b_ 'x) (ass)))
  (ci-only! '(iff (in x (union a_ (complement-in b_ a_)))
                  (or (in x a_) (in x (complement-in b_ a_))))
            '(iff (in x (complement-in b_ a_)) (and (in x b_) (not (in x a_))))
            '(implies (in x a_) (in x b_)))
  (prop)))
(qed 'union-complement-in)
(declare-named-only! 'union-complement-in
  "Its left side is a bare variable: as a live macete it would rewrite every
   term in every goal into a union with a relative complement.  Cite it by name.")
(topic! 'union-complement-in 'plumbing)

;;; -----------------------------------------------------------------------
;;; (3) union-as-disjoint:  A u B  =  A u (B \ A)
;;;
;;; The unguarded version of (2): no inclusion needed, and the point of it is
;;; that the right-hand union IS disjoint.  Purely propositional after the two
;;; membership unfolds -- (x in A or x in B) iff (x in A or (x in B and not
;;; x in A)).

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_
        (= (UNION a_ b_) (UNION a_ (COMPLEMENT-IN b_ a_)))))))
  (ci-peel!)
  (bc* 'class-extensionality)
  (ci-peel!)
  (fact 'union-membership 'a_ 'b_ 'x)
  (fact 'union-membership 'a_ '(COMPLEMENT-IN b_ a_) 'x)
  (fact 'complement-in-membership 'b_ 'a_ 'x)
  (ci-only! '(iff (in x (union a_ b_)) (or (in x a_) (in x b_)))
            '(iff (in x (union a_ (complement-in b_ a_)))
                  (or (in x a_) (in x (complement-in b_ a_))))
            '(iff (in x (complement-in b_ a_)) (and (in x b_) (not (in x a_)))))
  (prop)))
(qed 'union-as-disjoint)
(declare-named-only! 'union-as-disjoint
  "An unconditional equation whose left side matches every binary union in the
   library; as a live macete it would rewrite them all.  Cite it by name.")
(topic! 'union-as-disjoint 'plumbing)

;;; -----------------------------------------------------------------------
;;; (4) intersection-complement-in-empty:  A n (B \ A)  =  {}
;;;
;;; The disjointness card-union-disjoint is guarded on.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_
        (= (INTERSECTION a_ (COMPLEMENT-IN b_ a_)) EMPTY-SET)))))
  (ci-peel!)
  (bc* 'class-extensionality)
  (ci-peel!)
  (fact 'intersection-membership 'a_ '(COMPLEMENT-IN b_ a_) 'x)
  (fact 'complement-in-membership 'b_ 'a_ 'x)
  (fact 'empty-set-has-no-members 'x)
  (ci-only! '(iff (in x (intersection a_ (complement-in b_ a_)))
                  (and (in x a_) (in x (complement-in b_ a_))))
            '(iff (in x (complement-in b_ a_)) (and (in x b_) (not (in x a_))))
            '(not (in x empty-set)))
  (prop)))
(qed 'intersection-complement-in-empty)
(topic! 'intersection-complement-in-empty 'plumbing)

;;; -----------------------------------------------------------------------
;;; (5) card-subset-mono:  B in SET, CARD(B) in NN, SUBSET(A,B)
;;;                          =>  CARD(A) <= CARD(B)
;;;
;;; GUARDS.  Sethood of A is NOT stated: `subclass-of-set-is-set'
;;; (subset-lemmas.scm) derives it from SUBSET(A,B) and B in SET.  Finiteness of
;;; A is NOT stated either: card-subset-nn derives it.  So the guard set is the
;;; minimal one -- B is a finite set and A is contained in it.  The antecedents
;;; are CURRIED rather than conjoined, the ideal.scm:73 convention, so that
;;; `fact' can detach them one at a time at a call site.
;;;
;;; THE ARGUMENT.  B = A u (B \ A), the two pieces are disjoint and both finite,
;;; so card-union-disjoint reads CARD(B) = CARD(A) + CARD(B \ A), and
;;; nn-le-add-right is a <= a + b.

(quietly (lambda ()
  (sp (make-wff '(FORALL b_ (IMPLIES (IN b_ SET)
       (IMPLIES (IN (CARD b_) NN)
         (FORALL a_ (IMPLIES (SUBSET a_ b_)
           (<= (CARD a_) (CARD b_)))))))))
  (ci-peel!)

  ;; --- A is a set, and B \ A is a set
  (fact 'subclass-of-set-is-set 'a_ 'b_)
  (fact 'complement-in-set-closure 'b_ 'a_)

  ;; --- both are finite, by card-subset-nn off B.  Both of its antecedents are
  ;; conjunctions, which `fact' will not cross, so each wants a `have!' first.
  (have! '(AND (IN b_ SET) (IN (CARD b_) NN)))
  (have! '(FORALL z (IMPLIES (IN z a_) (IN z b_)))
         (lambda () (ci-peel!) (fact 'subset-mem-fwd 'a_ 'b_ 'z) (ass)))
  (have! '(AND (IN a_ SET) (FORALL z (IMPLIES (IN z a_) (IN z b_)))))
  (fact 'card-subset-nn 'b_ 'a_)
  ;; The inclusion B \ A subset B, elementwise -- card-subset-nn spells its
  ;; subset hypothesis out rather than using SUBSET.  Routed through (1) and
  ;; subset-mem-fwd rather than unfolding complement-in-membership and calling
  ;; `prop': by this point the context is well over prop's 12-atom cap.
  (have! '(FORALL z (IMPLIES (IN z (COMPLEMENT-IN b_ a_)) (IN z b_)))
         (lambda () (ci-peel!)
                    (fact 'complement-in-subset 'a_ 'b_)
                    (fact 'subset-mem-fwd '(COMPLEMENT-IN b_ a_) 'b_ 'z)
                    (ass)))
  (have! '(AND (IN (COMPLEMENT-IN b_ a_) SET)
               (FORALL z (IMPLIES (IN z (COMPLEMENT-IN b_ a_)) (IN z b_)))))
  (fact 'card-subset-nn 'b_ '(COMPLEMENT-IN b_ a_))

  ;; --- the disjoint decomposition
  (fact 'intersection-complement-in-empty 'a_ 'b_)
  (have! '(AND (IN (COMPLEMENT-IN b_ a_) SET)
               (AND (IN (CARD (COMPLEMENT-IN b_ a_)) NN)
                    (= (INTERSECTION a_ (COMPLEMENT-IN b_ a_)) EMPTY-SET))))
  (have! '(AND (IN a_ SET) (IN (CARD a_) NN)))
  (fact 'card-union-disjoint 'a_ '(COMPLEMENT-IN b_ a_))

  ;; --- rewrite the goal along B = A u (B\A) and then along the cardinal sum
  (fact 'union-complement-in 'a_ 'b_)
  (subst '(= b_ (UNION a_ (COMPLEMENT-IN b_ a_))))
  (subst '(= (CARD (UNION a_ (COMPLEMENT-IN b_ a_)))
             (+ (CARD a_) (CARD (COMPLEMENT-IN b_ a_)))))

  ;; --- a <= a + b.  nn-le-add-right takes the ADDEND first (nn-order-basics.scm:175).
  (fact 'nn-le-add-right '(CARD (COMPLEMENT-IN b_ a_)) '(CARD a_))
  (ass)))
(qed 'card-subset-mono)
(topic! 'card-subset-mono 'combinatorial)

;;; -----------------------------------------------------------------------
;;; (6) card-union-bound:  A,B in SET, CARD(A) in NN, CARD(B) in NN
;;;                          =>  CARD(A u B) <= CARD(A) + CARD(B)
;;;
;;; A u B = A u (B \ A), disjoint, so CARD(A u B) = CARD(A) + CARD(B \ A), and
;;; CARD(B \ A) <= CARD(B) by (5).  nn-add-le-mono adds CARD(A) to both sides.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET)
       (IMPLIES (IN (CARD a_) NN)
         (FORALL b_ (IMPLIES (IN b_ SET)
           (IMPLIES (IN (CARD b_) NN)
             (<= (CARD (UNION a_ b_)) (+ (CARD a_) (CARD b_)))))))))))
  (ci-peel!)
  (ci-decompose!)
  (ci-rewrite-union!)
  ;; --- CARD(B \ A) <= CARD(B), then add CARD(A) on the left of both sides
  (fact 'card-subset-mono 'b_ '(COMPLEMENT-IN b_ a_))
  (fact 'nn-add-le-mono '(CARD b_) '(CARD a_) '(CARD (COMPLEMENT-IN b_ a_)))
  (ass)))
(qed 'card-union-bound)
(topic! 'card-union-bound 'combinatorial)

;;; -----------------------------------------------------------------------
;;; (7) card-union-nn:  A,B in SET, CARD(A) in NN, CARD(B) in NN
;;;                       =>  CARD(A u B) in NN
;;;
;;; "The union of two finite sets is finite."  NOT a corollary of (6): `<=' is
;;; a relation on NN, and knowing CARD(A u B) <= CARD A + CARD B does not by
;;; itself put the left side in NN -- a cardinal is an ORDINAL, and nothing in
;;; the statement of (6) says which kind.  It comes from the same decomposition
;;; one step earlier: CARD(A u B) IS the sum CARD A + CARD(B \ A), and NN is
;;; closed under addition.
;;;
;;; This is the law FIN-SUBSETS needs to be closed under union at all, so it is
;;; the one of the three that the monoid cannot be built without.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET)
       (IMPLIES (IN (CARD a_) NN)
         (FORALL b_ (IMPLIES (IN b_ SET)
           (IMPLIES (IN (CARD b_) NN)
             (IN (CARD (UNION a_ b_)) NN)))))))))
  (ci-peel!)
  (ci-decompose!)
  (ci-rewrite-union!)
  (have! '(AND (IN (CARD a_) NN) (IN (CARD (COMPLEMENT-IN b_ a_)) NN)))
  (fact 'nn-add-closed '(CARD a_) '(CARD (COMPLEMENT-IN b_ a_)))
  (ass)))
(qed 'card-union-nn)
(topic! 'card-union-nn 'combinatorial)

;;; -----------------------------------------------------------------------
;;; WHAT IS LEFT OWED, precisely.
;;;
;;; One leaf: `card-subset-nn'.  Clearing it does NOT reach `modulo 0' on its own
;;; -- see the shadowing paragraph in the header; the NN order supports have to
;;; go too.  It is nonetheless the only CARDINALITY debt these proofs carry, and
;;; the statement to prove is
;;;
;;;     X in SET, CARD(X) in NN, S in SET, S subset X   =>   CARD(S) in NN
;;;
;;; by `finite-set-induction' (cardinality.scm:108, primitive) on X, with the
;;; class instantiated to
;;;
;;;     { x | forall s. s in SET and s subset x  =>  CARD(s) in NN }
;;;
;;; Base: a subclass of EMPTY-SET is EMPTY-SET (class-extensionality plus
;;; empty-set-has-no-members) and CARD({}) = 0.  Step: for s subset X u {y},
;;; write s = (s n X) u (s \ X); s n X is a subset of X so the hypothesis
;;; applies, and s \ X is either empty or {y}, so card-insert finishes.
;;;
;;; The two obstacles worth naming before anyone starts:
;;;   * finite-set-induction has never been used in a proof anywhere in the
;;;     tree.  Three files say "provable by finite-set-induction" and then
;;;     assert the result instead (prod-of-sums.scm:227, sum-set-left-scalar.scm:7,
;;;     sum-set-right-scalar.scm:7).  This would be its first firing.
;;;   * instantiating its class variable needs a COMP, and NO installed formula
;;;     in the tree contains one (CLAUDE.md).  The kernel rules exist
;;;     (pi-comp-mem-intro! / pi-comp-mem-elim!, primitive-inferences.scm:1133)
;;;     and COMP was only put into the expression walkers on 2026-08-15, so this
;;;     would be the first library exercise of that path too.
;;;
;;; Neither is a reason it cannot be done; both are reasons it is its own task.
