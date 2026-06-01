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
;;;     |INJECTION(A u {b}, C)| = m * |INJECTION(A, C)|.
;;;
;;; Why: restriction  f |-> <f|A, f(b)>  is a bijection
;;;     INJECTION(A u {b}, C)
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
                           (IMPLIES (= (phi a) (phi b)) (= a b))))))))))))

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
(theory-add-axiom! *current-theory* 'bijection-is-injection
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y))
               (IN phi (INJECTION X Y)))))))

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

;;; IMAGE(phi, S) is a set when S is a set (replacement).
(theory-add-axiom! *current-theory* 'image-set
  '(FORALL phi (FORALL S
      (IMPLIES (IN S SET)
               (IN (IMAGE phi S) SET)))))

;;; The image of phi : dom -> cod lands in cod.
(theory-add-axiom! *current-theory* 'image-subset-codomain
  '(FORALL dom (FORALL cod (FORALL phi
      (IMPLIES (IN phi (FUN dom cod))
               (FORALL w
                 (IMPLIES (IN w (IMAGE phi dom)) (IN w cod))))))))

;;; An injection preserves cardinality on its image: |IMAGE(phi, dom)| = |dom|.
;;; (phi restricted to dom is a bijection dom -> IMAGE(phi, dom).)
(theory-add-axiom! *current-theory* 'card-image-injection
  '(FORALL dom (FORALL cod (FORALL phi
      (IMPLIES (AND (IN phi (INJECTION dom cod))
                    (IN dom SET)
                    (IN (CARD dom) NN))
               (= (CARD (IMAGE phi dom)) (CARD dom)))))))

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
;;;     |INJECTION(A u {b}, C)| = m * |INJECTION(A, C)|.
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
      (IMPLIES (AND (NOT (IN b A))
                    (IN A SET)
                    (IN C SET)
                    (IN (CARD A) NN)
                    (IN m NN)
                    (= (CARD C) (+ (CARD A) m)))
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
