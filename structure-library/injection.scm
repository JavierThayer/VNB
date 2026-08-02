;;; injection.scm -- INJECTION class, IMAGE operator, and the
;;; injection-extension recurrence: the counting principle behind nPk and n!.
;;;
;;; INJECTION(X, Y) is the class of injective functions phi : X -> Y, i.e.
;;; phi in FUN(X, Y) with phi(a) = phi(b) => a = b for a, b in X.  It is
;;; BIJECTION(X, Y) minus the surjectivity clause; every bijection is an
;;; injection (bijection-is-injection below).
;;;
;;; IMAGE(phi, S) is the image set { phi(x) : x in S }.
;;;
;;; The headline result is injection-extension-recurrence: adding one fresh
;;; point to the domain multiplies the number of injections into a FIXED
;;; codomain C by the size of the unused part of C.  For b not in A and
;;; |C| = |A| + m:
;;;
;;;     |INJECTION(CARR u {b}, C)| = m * |INJECTION(A, C)|.
;;;
;;; Why: restriction  f |-> <f|A, f(b)>  is a bijection
;;;     INJECTION(CARR u {b}, C)
;;;        ~  { <g, c> : g in INJECTION(A, C), c in C \ IMAGE(g, A) },
;;; with inverse "extend g by b |-> c" (injective exactly because c is
;;; unused).  Each g is injective, so |IMAGE(g, A)| = |A| and the unused
;;; part C \ IMAGE(g, A) has size |C| - |A| = m -- the SAME constant for
;;; every g.  Summing the constant m over the |INJECTION(A, C)| fibres gives
;;; the product.  Unlike the bijection recurrence the codomain never shrinks,
;;; so no codomain-invariance lemma and no DELETE-AT/INSERT-AT index-shifting
;;; are needed; the constant-size complement does all the work.
;;;
;;; Specialising to C = ORD-SEGMENT(n) and growing A from {} to ORD-SEGMENT(n)
;;; gives |INJECTION(ORD-SEGMENT n, ORD-SEGMENT n)| = n! (an injection of a
;;; finite set into itself is a bijection), with base |INJECTION({}, C)| = 1.
;;;
;;; Dependencies: kernel (FUN, UNION, PAIR, EMPTY-SET); number-systems (NN,
;;; +, *, succ); cardinality.scm (CARD); bijection.scm (BIJECTION).
;;; All results installed as axioms for direct use; demote when proven.

;;; -----------------------------------------------------------------------
;;; INJECTION class membership
;;;
;;; Element vars a, b (not x/y): the reader case-folds, so a bound x/y would
;;; collide with the class parameters X/Y and be captured -- see bijection.scm.

;;; phi in INJECTION(X, Y) iff phi : X -> Y is injective on X.
;;; Conservative IFF definition of INJECTION-membership -> `definitional'.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'injection-membership-iff
    '(FORALL X
       (FORALL Y
         (FORALL phi
           (IFF (IN phi (INJECTION X Y))
                (AND (IN phi (FUN X Y))
                     (FORALL a
                       (IMPLIES (IN a X)
                         (FORALL b
                           (IMPLIES (IN b X)
                             (IMPLIES (= (phi a) (phi b)) (= a b)))))))))))))

;;; -----------------------------------------------------------------------
;;; INJECTIVE* -- injectivity for things that are NOT set-functions.
;;;
;;; `INJECTION(X, Y)' asks its member to BE an object: injection-membership-iff
;;; requires (IN f (FUN X Y)), membership-implies-sethood then forces f to be a
;;; set, and is-fun-def (theory.scm:388) says being a function at all means
;;; having a SET domain.  So nothing whose domain is a proper class -- a lambdoid
;;; on ORD, a def-by-ord-recursion constant -- can ever be said to be in it.
;;;
;;; INJECTIVE* says the same thing about the APPLICATION instead, so F occupies
;;; the juxtaposition slot and may be a lambdoid, a VNB-LAMBDA, or a plain
;;; function variable.
;;;
;;; NO DOMAIN ARGUMENT IS NEEDED, and that is the point.  VNB equality is
;;; PARTIAL: a strict (= s t) asserts BOTH sides defined (primitive-inferences.scm
;;; :588, "a strict (= t _)/(= _ t) asserts t defined too").  So off F's domain of
;;; definition the antecedent (F u) = (F v) is simply FALSE and the implication is
;;; vacuous.  The unguarded form therefore says exactly "F is injective on its
;;; domain of definition" -- which for a lambdoid on ORD is all of ORD -- without
;;; anyone having to name that domain as a term.
(def-predicate 'INJECTIVE* '(F)
  '(FORALL u_ (FORALL v_ (IMPLIES (= (F u_) (F v_)) (= u_ v_)))))

(notation! 'INJECTIVE* 'kind 'predicate 'arity 1 'english "$1 is injective")

;;; -----------------------------------------------------------------------
;;; Projection lemmas (each derivable from injection-membership-iff).

(theory-add-axiom! *current-theory* 'injection-in-fun
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (INJECTION X Y))
               (IN phi (FUN X Y)))))))

(theory-add-axiom! *current-theory* 'injection-injective
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (INJECTION X Y))
               (FORALL a
                 (IMPLIES (IN a X)
                   (FORALL b
                     (IMPLIES (IN b X)
                       (IMPLIES (= (phi a) (phi b)) (= a b)))))))))))

;;; INJECTION(X, Y) is a set when X and Y are sets (subclass of FUN(X, Y)).
(theory-add-axiom! *current-theory* 'injection-set-iff
  '(FORALL X (FORALL Y
      (IMPLIES (AND (IN X SET) (IN Y SET))
               (IN (INJECTION X Y) SET)))))

;;; Every bijection is an injection.
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (unfold
;;; both class memberships via the -membership-iff axioms; FUN + injective
;;; conjuncts coincide); no longer asserted here.

;;; -----------------------------------------------------------------------
;;; IMAGE: the image set of phi over S.
;;;
;;; Bound var x (domain element) / w (image value); the parameter is S, so
;;; no case-fold collision (an inner x with an outer X would capture).

;;; w in IMAGE(phi, S) iff w = phi(x) for some x in S.
(theory-add-axiom! *current-theory* 'image-membership-iff
  '(FORALL phi (FORALL S (FORALL w
      (IFF (IN w (IMAGE phi S))
           (FORSOME x (AND (IN x S) (= (phi x) w))))))))

;;; IMAGE(phi, S) is a set when S is a set.
;;;
;;; THIS IS REPLACEMENT, AND IT IS INSTALLED AS FOUNDATIONAL.  The image of a
;;; set under a class function is a set: one of the axioms of the set theory,
;;; not a fact the library owes an argument for.  Wrapped in `primitive'
;;; provenance (proof-debt.scm:12), which is the trusted-base tier -- it
;;; contributes {} to every bill, exactly like the base theory of theory.scm:613
;;; and the ordinal axioms of ordinals.scm.  User's decision, 2026-07-28.
;;;
;;; It is NOT a `warrant!'.  A warrant would move it from `none' to
;;; `well-known' -- a better tier of DEBT.  `primitive' says it is not debt.
;;; The test CLAUDE.md sets for the shelf is whether a mathematician would
;;; answer "because that is what sets are"; for replacement, they would.
;;;
;;; What it buys: `ord-no-injection-into-set' and, through it, ZORN'S LEMMA
;;; (theorem-library/zorn-route-two.scm) had this as the SOLE entry in their
;;; bills.  Both now read `modulo 0'.
(fluid-let ((*current-provenance* 'primitive))
  (theory-add-axiom! *current-theory* 'image-set
    '(FORALL phi (FORALL S
        (IMPLIES (IN S SET)
                 (IN (IMAGE phi S) SET))))))

;;; The image of phi : dm -> cod lands in cod.
(theory-add-axiom! *current-theory* 'image-subset-codomain
  '(FORALL dm (FORALL cod (FORALL phi
      (IMPLIES (IN phi (FUN dm cod))
               (FORALL w
                 (IMPLIES (IN w (IMAGE phi dm)) (IN w cod))))))))

;;; An injection preserves cardinality on its image: |IMAGE(phi, dm)| = |dm|.
;;; (phi restricted to dm is a bijection dm -> IMAGE(phi, dm).)
;; A CARD axiom, so `primitive' like the rest of them (cardinality.scm).
(fluid-let ((*current-provenance* 'primitive))
(theory-add-axiom! *current-theory* 'card-image-injection
  '(FORALL dm (FORALL cod (FORALL phi
      (IMPLIES (AND (IN phi (INJECTION dm cod)) (AND (IN dm SET) (IN (CARD dm) NN)))
               (= (CARD (IMAGE phi dm)) (CARD dm))))))))

;;; -----------------------------------------------------------------------
;;; Base case: the empty function is the unique injection out of {}.
(theory-add-axiom! *current-theory* 'injection-from-empty
  '(FORALL C
      (IMPLIES (IN C SET)
               (= (CARD (INJECTION EMPTY-SET C)) (succ 0)))))

;;; -----------------------------------------------------------------------
;;; THE TARGET THEOREM -- injection-extension recurrence.
;;;
;;; For b not in A, with |C| = |A| + m (so the unused part of C has m
;;; elements), extending the domain by b multiplies the injection count by m:
;;;
;;;     |INJECTION(CARR u {b}, C)| = m * |INJECTION(A, C)|.
;;;
;;; Boundary is automatic: if |A| = |C| then m = 0 and the right side is 0,
;;; correctly reporting that a strictly larger set has no injection into C.
;;; The singleton {b} is written (PAIR b b) to match card-insert.
;;;
;;; Recorded in the Proof Support Set (not as a raw axiom): it is the
;;; curated counting principle behind nPk / n!, believed provable but not
;;; yet mechanized.  (support ...) installs it as a macete -- usable in
;;; backchaining / rewriting -- and tags it for the PSS section of the
;;; catalog.
(support 'injection-extension-recurrence
  '(FORALL A (FORALL C (FORALL b (FORALL m
      (IMPLIES (AND (NOT (IN b A)) (AND (IN A SET) (AND (IN C SET) (AND (IN (CARD A) NN) (AND (IN m NN) (= (CARD C) (+ (CARD A) m)))))))
               (= (CARD (INJECTION (UNION A (PAIR b b)) C))
                  (* m (CARD (INJECTION A C))))))))))

;;; -----------------------------------------------------------------------
;;; PERMUTATIONS(n) := the bijections of an n-element set onto itself,
;;; realised concretely as the self-injections of ORD-SEGMENT(n).  An
;;; injection of a finite set into itself is automatically onto, so this
;;; coincides with BIJECTION(ORD-SEGMENT n, ORD-SEGMENT n); defining it as
;;; INJECTION lets |PERMUTATIONS(n)| be counted directly by
;;; injection-extension-recurrence, with no finite-pigeonhole detour.
;;;
;;; A def-functoid: (PERMUTATIONS n) unfolds (rewrites) to
;;; (INJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)).  The target counting
;;; result CARD(PERMUTATIONS(n)) = n! is then a consequence of the
;;; recurrence + nn-induction (to be proven; needs a factorial).
(def-functoid 'PERMUTATIONS '(n)
  '(INJECTION (ORD-SEGMENT n) (ORD-SEGMENT n)))

;;; -----------------------------------------------------------------------
;;; FACTORIAL via its defining recurrence:  0! = 1,  (k+1)! = (k+1) * k!.
;;;
;;; Defined as a constant with characterizing axioms (def-constant), NOT a
;;; def-functoid: the definition is recursive, so an unfolding functoid
;;; would not terminate.  Well-definedness is by NN-recursion (accepted).
;;; 1 is written (succ 0) to match the succ-based NN model of the card
;;; lemmas (card-singleton etc.).
(def-constant 'FACTORIAL
  '(factorial-zero (= (FACTORIAL 0) (succ 0)))
  '(factorial-succ (FORALL k (IMPLIES (IN k NN)
                     (= (FACTORIAL (succ k))
                        (* (succ k) (FACTORIAL k)))))))

;;; Typing: n! is a natural number.  Derivable from the recurrence by
;;; nn-induction; installed for direct use.
(theory-add-axiom! *current-theory* 'factorial-in-nn
  '(FORALL n (IMPLIES (IN n NN) (IN (FACTORIAL n) NN))))

;;; -----------------------------------------------------------------------
;;; The two "obvious lemmas" that reduce the permutation count to a short
;;; nn-induction, recorded in the PSS rather than mechanized (the falling-
;;; factorial reindexing that derives the recursion from injection-extension-
;;; recurrence is exactly the slog we choose to accept instead of grind).

;;; Base: the empty set has one self-injection (the empty function).
;;; |PERMUTATIONS(0)| = |INJECTION({}, {})| = 1, since ORD-SEGMENT(0) = {}.
(support 'permutations-zero
  '(= (CARD (PERMUTATIONS 0)) (succ 0)))

;;; Step (the n! recursion): adding one point multiplies the count by n+1.
;;; |PERMUTATIONS(n+1)| = (n+1) * |PERMUTATIONS(n)|.  This is injection-
;;; extension-recurrence specialised to the diagonal (domain = codomain
;;; grow together), via the standard falling-factorial reindexing.
(support 'permutation-recurrence
  '(FORALL n (IMPLIES (IN n NN)
     (= (CARD (PERMUTATIONS (succ n)))
        (* (succ n) (CARD (PERMUTATIONS n)))))))

;;; -----------------------------------------------------------------------
;;; TARGET (to be PROVEN -- short nn-induction off the two PSS lemmas above
;;; plus factorial-zero / factorial-succ; deliberately NOT asserted):
;;;
;;;   (FORALL n (IMPLIES (IN n NN)
;;;     (= (CARD (PERMUTATIONS n)) (FACTORIAL n))))
;;;
;;; (ni): base |PERMUTATIONS(0)| = succ 0 = 0! by permutations-zero +
;;; factorial-zero; step |PERMUTATIONS(succ n)| = (succ n)*|PERMUTATIONS(n)|
;;; = (succ n)*n! = (succ n)! by permutation-recurrence, the IH, and
;;; factorial-succ.

;;; =======================================================================
;;; BINOMIAL COEFFICIENT, defined CONCRETELY as a cardinality.
;;;
;;; CHOOSE(n,m) := the number of m-element subsets of {0,...,n-1}.  This IS the
;;; object; Pascal's rule and the falling-factorial identity below are THEOREMS
;;; about it, not its definition (the project's "define concretely, the
;;; characterising law is a theorem" discipline -- cf. quotients, completions).
;;; =======================================================================

;; CHOOSE-SET(n,m) = { A subset ORD-SEGMENT(n) : CARD(A) = m }.  A set by
;; separation over the power set of the finite segment ORD-SEGMENT(n).
(def-functoid 'CHOOSE-SET '(n m)
  '(SEP A (POWER (ORD-SEGMENT n)) (= (CARD A) m)))

;; CHOOSE(n,m) = |CHOOSE-SET(n,m)| : the binomial coefficient C(n,m).
(def-functoid 'CHOOSE '(n m)
  '(CARD (CHOOSE-SET n m)))

;; Typing: a binomial coefficient is a natural number.
(support 'choose-in-nn
  '(FORALL n (IMPLIES (IN n NN) (FORALL m (IMPLIES (IN m NN) (IN (CHOOSE n m) NN))))))
(warrant! 'choose-in-nn 'well-known
  "ORD-SEGMENT(n) is finite (card-segment: CARD = n), so POWER(ORD-SEGMENT n) is
   finite and its subset { A : CARD A = m } is finite; the cardinality lies in NN.")

;; Boundary values + Pascal's rule -- now THEOREMS of the cardinality definition,
;; kept as supports for the binomial layer (which rewrites with them).
(support 'choose-n-0
  '(FORALL n (IMPLIES (IN n NN) (= (CHOOSE n 0) (succ 0)))))
(support 'choose-0-succ
  '(FORALL k (IMPLIES (IN k NN) (= (CHOOSE 0 (succ k)) 0))))
(support 'choose-succ
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL k (IMPLIES (IN k NN)
       (= (CHOOSE (succ n) (succ k))
          (+ (CHOOSE n k) (CHOOSE n (succ k)))))))))
(warrant! 'choose-n-0 'well-known
  "The unique 0-element subset is EMPTY-SET, so CHOOSE(n,0) = 1.")
(warrant! 'choose-0-succ 'well-known
  "ORD-SEGMENT(0) = EMPTY-SET has no (k+1)-element subset, so CHOOSE(0,k+1) = 0.")
(warrant! 'choose-succ 'well-known
  "The (k+1)-subsets of ORD-SEGMENT(succ n) = {0,...,n} split disjointly on
   whether they contain the new point n: those that do not are the (k+1)-subsets
   of {0,...,n-1} (CHOOSE(n,succ k)); those that do are {n} u B with B a
   k-subset of {0,...,n-1} (CHOOSE(n,k)).  card-union-disjoint gives Pascal.")

;;; -----------------------------------------------------------------------
;;; Falling factorial  n^{(m)} = n(n-1)...(n-m+1)  (m descending factors).
;;; Single-index primitive recursion on m, via def-by-nn-recursion -- hence a
;;; CONSERVATIVE definitional extension (justified by the NN-recursion theorem),
;;; not a free postulate.  For the identity below only m <= n is used, where
;;; every factor n-k (k < m <= n) is a natural and integer subtraction is exact.
;;;   FALLING(n,0)      = 1
;;;   FALLING(n,succ k) = (n - k) * FALLING(n,k)
(def-by-nn-recursion 'FALLING '(n)
  '(succ 0)
  '(k val)
  '(* (- n k) val))

;; Typing: positive for m <= n, and 0 once a factor vanishes for m > n.
(support 'falling-in-nn
  '(FORALL n (IMPLIES (IN n NN) (FORALL m (IMPLIES (IN m NN) (IN (FALLING n m) NN))))))
(warrant! 'falling-in-nn 'well-known
  "For m <= n each factor n-k (0 <= k < m) is a positive natural; for m > n the
   factor at k = n is 0 and the product stays 0.  Either way FALLING(n,m) in NN.")

;; nPk: the number of injections of an m-set into an n-set IS the falling
;; factorial.  Generalises permutation-recurrence (the m = n diagonal gives n!).
(support 'injection-count-falling
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (AND (IN m NN) (<= m n))
       (= (CARD (INJECTION (ORD-SEGMENT m) (ORD-SEGMENT n))) (FALLING n m)))))))
(warrant! 'injection-count-falling 'well-known
  "Induction on m via injection-extension-recurrence.  Base: m = 0,
   |INJECTION(EMPTY-SET, C)| = 1 = FALLING(n,0) (injection-from-empty,
   ORD-SEGMENT 0 = EMPTY-SET).  Step: a domain of size m into a codomain of
   size n leaves n - m free targets, so extending the domain by one point
   multiplies the count by (n - m): exactly FALLING(n,succ m) = (n-m)*FALLING(n,m).")

;;; -----------------------------------------------------------------------
;;; THE THEOREM:   CHOOSE(n,m) * m!  =  n(n-1)...(n-m+1)  =  FALLING(n,m).
;;;
;;; Count injections phi : ORD-SEGMENT(m) -> ORD-SEGMENT(n) two ways:
;;;   (i)  by image + ordering: an injection is its m-element image (CHOOSE(n,m)
;;;        choices) together with a bijection of ORD-SEGMENT(m) onto that image
;;;        (m! = CARD(PERMUTATIONS m) choices) -- so CHOOSE(n,m) * m!;
;;;   (ii) directly, FALLING(n,m) by injection-count-falling.
(support 'choose-times-factorial
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL m (IMPLIES (AND (IN m NN) (<= m n))
       (= (* (CHOOSE n m) (FACTORIAL m)) (FALLING n m)))))))
(warrant! 'choose-times-factorial 'well-known
  "Both sides count the injections of an m-element set into an n-element set.
   (i) Each injection ORD-SEGMENT(m) -> ORD-SEGMENT(n) factors uniquely as a
   choice of m-element image A subset ORD-SEGMENT(n) (CHOOSE(n,m) of them, with
   card-image-injection making |A| = m) followed by a bijection ORD-SEGMENT(m)
   onto A (m! = CARD(PERMUTATIONS m) of them); so the count is CHOOSE(n,m) * m!.
   (ii) injection-count-falling gives the same count as FALLING(n,m) =
   n(n-1)...(n-m+1).  Equate the two counts.")
