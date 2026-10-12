;;; RETIRED 2026-09-17 (proven): inverse-bij-in-fun, inverse-bij-left, inverse-bij-right,
;;; inverse-bij-is-bijection -- were UNWARRANTED axioms; theorem-library/rake-inverse-bij.scm, modulo 0.
;;; RETIRED 2026-09-17 (proven): bijection-compose (was an `informal' axiom) -- theorem-library/rake-analysis2.scm,
;;; via the new fun-domain-in-set (the domain of a set-function is a set).
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
 (add-axiom! *library* 'bijection-membership-iff
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
;;; bijection-set-iff RAKE-ASM-1 2026-10-12: PROVEN in theorem-library/rake-asm-1.scm under this name; the assumption is retired.

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

;; Binders are y_ / x_ (trailing underscore): plain y/x case-fold onto the
;; parameters Y/X (functoid-binder-audit flags the shadow).  Here it happens to
;; be harmless -- the SEP domain X resolves in the outer scope before x binds --
;; but the convention keeps every functoid body collision-free.
(def-functoid 'INVERSE-BIJ '(phi X Y)
  '(VNB-LAMBDA y_ Y (CHOICE (SEP x_ X (= (phi x_) y_)))))

;;; Typing: when phi is a bijection X -> Y, INVERSE-BIJ(phi, X, Y) is in
;;; FUN(Y, X).  Derivable from CHOICE + surjectivity.

;;; Left inverse: for x in X, INVERSE-BIJ(phi)(phi(x)) = x.
;;; Derivable from CHOICE on a singleton (singleton because phi is injective).
;;; NB: bound vars are dm/cod (not X/Y) -- the reader case-folds, so an
;;; outer X and an inner x would be the same symbol and capture.

;;; Right inverse: for y in Y, phi(INVERSE-BIJ(phi)(y)) = y.
;;; Derivable from CHOICE + surjectivity (the chosen pre-image satisfies
;;; phi(x) = y by definition of the set we are choosing from).
;;; NB: bound vars dm/cod (not X/Y) -- see inverse-bij-left note.

;;; The inverse is itself a bijection.
;;; Derivable from inverse-bij-left, inverse-bij-right, and the iff.

;;; -----------------------------------------------------------------------
;;; Composition closure.
;;;
;;; (VNB-LAMBDA x (psi (phi x))) is a bijection X -> Z whenever phi is a
;;; bijection X -> Y and psi is a bijection Y -> Z.
;;; Derivable; installed as an axiom for direct use.

;;; The identity on X is a bijection X -> X.
;;; Derivable trivially; useful base case in induction proofs.
;;;
;;; GUARDED ON SETHOOD, 2026-08-05, and it must be.  Unguarded, at X := ORD this
;;; asserted that the identity LAMBDOID on a proper class is in BIJECTION(ORD,ORD)
;;; -- hence, by bijection-in-fun, in FUN(ORD,ORD).  That is exactly what
;;; pi-lambda-type!'s (IN A SET) obligation exists to prevent (the second half of
;;; the 2026-08-02 soundness repair, primitive-inferences.scm:1305): an AXIOM
;;; route around a repaired RULE.  No FALSITY was derivable from it -- the
;;; library has no unguarded "the domain of a set function is a set", `dom-of-fun'
;;; (library.scm:499) being itself guarded on (IN A SET) -- so this was an unsound
;;; ASSERTION rather than a demonstrated inconsistency.  Nothing in the tree cited
;;; it, so the guard costs no call site.
;;; bijection-identity MOVED 2026-09-15 (wave 6) to theorem-library/bijection-identity-proof.scm, where it is PROVEN modulo 0.

;;; -----------------------------------------------------------------------
;;; DELETE-AT (deleted 2026-10-12, the user's decision).  An UNDEFINED symbol that
;;; four asserted axioms characterised (delete-at-below-k, delete-at-above-k,
;;; delete-at-in-fun, delete-at-is-bijection), written for an index-shifting proof
;;; of permutation invariance that the finsum rework replaced; nothing has used it
;;; since (rake-finsum-welldef.scm, sum-ag-permutation-invariance.scm).
;;; delete-at-above-k was a strict `=' with h untyped, asserting h(succ i) DEFINED
;;; for every h -- the species of the old eplus/etimes axioms.  The originals are in
;;; archive/2026-10-12-rake-asm/bijection.scm.
