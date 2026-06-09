;;; bijection.scm -- bijections between classes, and INVERSE-BIJ via CHOICE.
;;;
;;; BIJECTION(X, Y) is the class of bijections phi : X -> Y, i.e. phi in
;;; FUN(X, Y) that is injective on X and surjective onto Y.
;;;
;;; INVERSE-BIJ(phi, X, Y) is the inverse function; defined by CHOICE so we
;;; do not need to introduce a uniqueness side-condition (as IOTA would).
;;; For a bijection the chosen pre-image is unique, so the choice is
;;; immaterial; nothing in the rest of the library should depend on
;;; *which* witness CHOICE returns when the underlying set is non-singleton.
;;;
;;; Dependencies: kernel (FUN, SEP, VNB-LAMBDA, CHOICE).

;;; -----------------------------------------------------------------------
;;; BIJECTION class membership

;;; Defining iff: phi in BIJECTION(X, Y) iff phi : X -> Y is injective on X
;;; and surjective onto Y.
;; Conservative IFF definition of BIJECTION-membership -> `definitional', so
;; unfolding it (bijection-is-injection) carries no debt.
(fluid-let ((*current-provenance* 'definitional))
 (theory-add-axiom! *current-theory* 'bijection-membership-iff
  '(FORALL X
     (FORALL Y
       (FORALL phi
         (IFF (IN phi (BIJECTION X Y))
              (AND (IN phi (FUN X Y))
                   (AND
                     (FORALL a
                       (IMPLIES (IN a X)
                         (FORALL b
                           (IMPLIES (IN b X)
                             (IMPLIES (= (phi a) (phi b)) (= a b))))))
                     ;; Surjectivity.  Element vars are w (codomain) and
                     ;; z (domain) -- NOT y/x: the reader case-folds, so a
                     ;; bound y would collide with the class parameter Y
                     ;; (and x with X), capturing (IN y Y) into (IN y y).
                     (FORALL w
                       (IMPLIES (IN w Y)
                         (FORSOME z
                           (AND (IN z X) (= (phi z) w)))))))))))))

;;; BIJECTION(X, Y) is a set when both X and Y are sets.
;;; Derivable: BIJECTION(X, Y) is a subclass of FUN(X, Y), and FUN(X, Y) is
;;; a set when X, Y are sets (fun-set-iff); use class-separation.  Installed
;;; here as an axiom for direct use; demote when proven.
(theory-add-axiom! *current-theory* 'bijection-set-iff
  '(FORALL X
     (FORALL Y
       (IMPLIES (AND (IN X SET) (IN Y SET))
                (IN (BIJECTION X Y) SET)))))
(warrant! 'bijection-set-iff 'informal
  "BIJECTION(X,Y) is a subclass of FUN(X,Y), a set when X,Y are sets
   (fun-set-iff); a subclass of a set is a set by separation.  Mechanization
   needs to exhibit BIJECTION(X,Y) as a separation of FUN(X,Y); deferred.")

;;; -----------------------------------------------------------------------
;;; Projection lemmas (bijection-in-fun / bijection-injective /
;;; bijection-surjective) are each one RHS conjunct of bijection-membership-iff
;;; and are PROVEN modulo 0 in structure-library/bijection-derived.scm (loaded
;;; after the interactive tactics).  They used to be asserted here "for direct
;;; use"; that was phantom debt, now retired.

;;; -----------------------------------------------------------------------
;;; INVERSE-BIJ: inverse of a bijection, defined via CHOICE.
;;;
;;;   INVERSE-BIJ(phi, X, Y) = lambda y. CHOICE { x in X : phi(x) = y }
;;;
;;; For a bijection, this set is a singleton, so CHOICE returns the unique
;;; pre-image and the choice is canonical (in the sense that any two
;;; choices would agree -- provable from injectivity).

(def-functoid 'INVERSE-BIJ '(phi X Y)
  '(VNB-LAMBDA y (CHOICE (SEP x X (= (phi x) y)))))

;;; Typing: when phi is a bijection X -> Y, INVERSE-BIJ(phi, X, Y) is in
;;; FUN(Y, X).  Derivable from CHOICE + surjectivity.
(theory-add-axiom! *current-theory* 'inverse-bij-in-fun
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y))
               (IN (INVERSE-BIJ phi X Y) (FUN Y X)))))))

;;; Left inverse: for x in X, INVERSE-BIJ(phi)(phi(x)) = x.
;;; Derivable from CHOICE on a singleton (singleton because phi is injective).
;;; NB: bound vars are dom/cod (not X/Y) -- the reader case-folds, so an
;;; outer X and an inner x would be the same symbol and capture.
(theory-add-axiom! *current-theory* 'inverse-bij-left
  '(FORALL dom (FORALL cod (FORALL phi
      (IMPLIES (IN phi (BIJECTION dom cod))
               (FORALL x
                 (IMPLIES (IN x dom)
                          (= ((INVERSE-BIJ phi dom cod) (phi x)) x))))))))

;;; Right inverse: for y in Y, phi(INVERSE-BIJ(phi)(y)) = y.
;;; Derivable from CHOICE + surjectivity (the chosen pre-image satisfies
;;; phi(x) = y by definition of the set we are choosing from).
;;; NB: bound vars dom/cod (not X/Y) -- see inverse-bij-left note.
(theory-add-axiom! *current-theory* 'inverse-bij-right
  '(FORALL dom (FORALL cod (FORALL phi
      (IMPLIES (IN phi (BIJECTION dom cod))
               (FORALL y
                 (IMPLIES (IN y cod)
                          (= (phi ((INVERSE-BIJ phi dom cod) y)) y))))))))

;;; The inverse is itself a bijection.
;;; Derivable from inverse-bij-left, inverse-bij-right, and the iff.
(theory-add-axiom! *current-theory* 'inverse-bij-is-bijection
  '(FORALL X (FORALL Y (FORALL phi
      (IMPLIES (IN phi (BIJECTION X Y))
               (IN (INVERSE-BIJ phi X Y) (BIJECTION Y X)))))))

;;; -----------------------------------------------------------------------
;;; Composition closure.
;;;
;;; (VNB-LAMBDA x (psi (phi x))) is a bijection X -> Z whenever phi is a
;;; bijection X -> Y and psi is a bijection Y -> Z.
;;; Derivable; installed as an axiom for direct use.

(theory-add-axiom! *current-theory* 'bijection-compose
  '(FORALL X (FORALL Y (FORALL Z (FORALL phi (FORALL psi
      (IMPLIES (AND (IN phi (BIJECTION X Y))
                    (IN psi (BIJECTION Y Z)))
               (IN (VNB-LAMBDA x_ (psi (phi x_)))
                   (BIJECTION X Z)))))))))
(warrant! 'bijection-compose 'informal
  "Derivable from bijection-membership-iff in both directions plus lambda-beta:
   the composite is a function X->Z, injective (phi,psi injective) and
   surjective (phi,psi surjective).  Mechanization needs VNB-LAMBDA typing +
   beta on the nested application; deferred.")

;;; The identity on X is a bijection X -> X.
;;; Derivable trivially; useful base case in induction proofs.
(theory-add-axiom! *current-theory* 'bijection-identity
  '(FORALL X
     (IN (VNB-LAMBDA x_ x_) (BIJECTION X X))))
(warrant! 'bijection-identity 'informal
  "Backward direction of bijection-membership-iff: the identity lambda is in
   FUN(X,X), injective (lambda(a)=lambda(b) beta-reduces to a=b) and surjective
   (witness z:=w).  Mechanization needs VNB-LAMBDA typing + beta + exists-intro;
   deferred.")

;;; -----------------------------------------------------------------------
;;; DELETE-AT: restriction-and-shift on NN-indexed functions.
;;;
;;; (DELETE-AT h k) is the function on NN defined by
;;;     (DELETE-AT h k)(i) = h(i)        for i < k
;;;     (DELETE-AT h k)(i) = h(succ i)   for k <= i
;;; i.e. it deletes the entry at index k and slides later entries down.
;;;
;;; Used to reduce a bijection on ORD-SEGMENT(succ n) that sends k to n
;;; to a bijection on ORD-SEGMENT(n), in the induction step of finite
;;; permutation-invariance.
;;;
;;; The behaviour of (DELETE-AT h k) at indices i >= n is junk; only the
;;; values at i in ORD-SEGMENT(n) matter, and only those are constrained
;;; by the bijection axiom below.

;;; Below-k characterising equation: i < k.
(theory-add-axiom! *current-theory* 'delete-at-below-k
  '(FORALL h (FORALL k (FORALL i
      (IMPLIES (IN i (ORD-SEGMENT k))
               (= ((DELETE-AT h k) i) (h i)))))))

;;; At-or-above-k characterising equation: k <= i (both in NN).
(theory-add-axiom! *current-theory* 'delete-at-above-k
  '(FORALL h (FORALL k (FORALL i
      (IMPLIES (AND (IN i NN) (AND (IN k NN) (NOT (IN i (ORD-SEGMENT k)))))
               (= ((DELETE-AT h k) i) (h (succ i))))))))

;;; (DELETE-AT h k) inherits h's function typing: every value is either
;;; h(i) or h(succ i), so a function into B stays a function into B.
;;; Installed as an axiom for direct use; demote when proven.
(theory-add-axiom! *current-theory* 'delete-at-in-fun
  '(FORALL B (FORALL h (FORALL k
      (IMPLIES (IN h (FUN NN B))
               (IN (DELETE-AT h k) (FUN NN B)))))))

;;; (DELETE-AT h k) is a bijection ORD-SEGMENT(n) -> ORD-SEGMENT(n) when h
;;; is a bijection ORD-SEGMENT(succ n) -> ORD-SEGMENT(succ n) with h(k) = n
;;; and k <= n.
;;;
;;; Provable from the two characterising equations + bijection-injective +
;;; bijection-surjective, by case-split on whether the input/output is
;;; below or at-or-above k.  Installed as an axiom for direct use; demote
;;; when proven.
(theory-add-axiom! *current-theory* 'delete-at-is-bijection
  '(FORALL n (FORALL k (FORALL h
      (IMPLIES (AND (IN n NN)
               (AND (IN k (ORD-SEGMENT (succ n)))
               (AND (IN h (BIJECTION (ORD-SEGMENT (succ n)) (ORD-SEGMENT (succ n))))
                    (= (h k) n))))
               (IN (DELETE-AT h k)
                   (BIJECTION (ORD-SEGMENT n) (ORD-SEGMENT n))))))))
