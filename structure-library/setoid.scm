;;; setoid.scm -- SETOID = (X, REL): a set with an equivalence relation,
;;; and the CONCRETE quotient X / REL together with its universal property.
;;;
;;; Design (project_setoid_quotient_design): a structure is a TERM, so facts
;;; about several objects at once -- here the setoid s, its quotient set, the
;;; projection, plus a target Z and a map f -- are a single sentence `forall
;;; s Z f. ...'.  No "theory of setoid pairs" apparatus is needed (the IMPS
;;; little-theories deficiency the user called out).
;;;
;;; We do NOT define X/REL via a universal property.  We give the CONCRETE
;;; representation -- equivalence classes as separation-subsets of X, the
;;; quotient as their IMAGE, the projection as the class map -- and then PROVE
;;; (assert, library-phase) that this concrete object satisfies the universal
;;; property of the quotient.  Descent of a relation-respecting map is by IOTA
;;; (definite description), not CHOICE-of-representative: representation-
;;; independent by construction (project_representation_independence).
;;;
;;; Accessor indices: X -> 1, REL -> 2.  REL is the relation as an extensional
;;; SET (a subset of CARTESIAN(X,X)); `a ~ b' is (IN (LIST a b) (REL s)),
;;; sugared (RELATED s a b).  The slot is named REL, not R, to avoid the
;;; ubiquitous ring variable R and its case-fold (feedback_no_case_variant_binders).
;;;
;;; Dependencies: kernel (SEP, IMAGE, VNB-LAMBDA, IOTA, FORSOME, CARTESIAN,
;;; POWER, LIST, INTERSECTION, EMPTY-SET, SUBSET, FUN), structures.scm.

;;; =======================================================================
;;; The characteristic property: REL is an equivalence relation on X.
;;; =======================================================================

;; is-equivalence(rho, crr): rho subset CARTESIAN(crr,crr) is reflexive,
;; symmetric and transitive on crr.  Param `rho' (a relation), NOT `rel' --
;; the reader case-folds and `rel' would BE the accessor REL.  Conservative
;; IFF -> `definitional', so projecting any of the three laws out of
;; IS-SETOID (as metric-laws.scm projects the metric laws) carries no debt.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'is-equivalence
    '(FORALL rho (FORALL crr
       (IFF (is-equivalence rho crr)
            (AND (IN rho (POWER (CARTESIAN crr crr)))
              (AND
                ;; reflexive
                (FORALL u (IMPLIES (IN u crr) (IN (LIST u u) rho)))
                (AND
                  ;; symmetric
                  (FORALL u (IMPLIES (IN u crr)
                    (FORALL v (IMPLIES (IN v crr)
                      (IMPLIES (IN (LIST u v) rho) (IN (LIST v u) rho))))))
                  ;; transitive
                  (FORALL u (IMPLIES (IN u crr)
                    (FORALL v (IMPLIES (IN v crr)
                      (FORALL w (IMPLIES (IN w crr)
                        (IMPLIES (AND (IN (LIST u v) rho) (IN (LIST v w) rho))
                                 (IN (LIST u w) rho)))))))))))))))

;;; =======================================================================
;;; The structure.
;;; =======================================================================

;; REL is declared as a `carriers' slot: that imposes the bare shape
;; constraint (IN (REL s) SET) -- a relation IS a set.  The tighter typing
;; (REL s) subset CARTESIAN(X,X) and the three laws come from the property.
(def-structure-from-clauses 'SETOID
  '((carriers X REL)
    (property is-equivalence REL X)))

;; The three equivalence laws (refl/sym/trans) and the typing REL subset
;; CARTESIAN(X,X) are NOT separate axioms: (property is-equivalence REL X)
;; folds is-equivalence((REL s),(X s)) into IS-SETOID, so each is PROVEN
;; modulo 0 by projecting that conjunct -- the metric-space.scm pattern.

;;; =======================================================================
;;; Sugar: the relation as an infix-ish predicate.
;;; =======================================================================

;; (RELATED s a b)  ==  a ~_s b  ==  (a,b) in REL(s).
(def-functoid 'RELATED '(s a b)
  '(IN (LIST a b) (REL s)))

;;; =======================================================================
;;; The quotient, concretely.
;;; =======================================================================

;; CLASS(s,a) = { b in X(s) : a ~ b } -- the equivalence class of a.  A
;; subset of X(s), hence a SET by separation (feedback_set_equality_not_class).
;; Param `a' (not `x'): the reader case-folds and `x' would BE the carrier
;; accessor X used in the body.
(def-functoid 'CLASS '(s a)
  '(SEP b (X s) (RELATED s a b)))

;; PROJ(s) = a |-> [a] -- the canonical projection X(s) -> X(s)/REL.
(def-functoid 'PROJ '(s)
  '(VNB-LAMBDA a (CLASS s a)))

;; QUOTIENT(s) = X(s)/REL = the IMAGE of the class map = { [a] : a in X(s) }.
;; The indexed/binder form (feedback_family_operations), not a loose POWER(X)
;; comprehension.
(def-functoid 'QUOTIENT '(s)
  '(IMAGE (PROJ s) (X s)))

;;; =======================================================================
;;; Class / partition supports (library-phase, warranted).
;;; =======================================================================

;; class-self: a in [a].  This is reflexivity of REL, projected through SEP.
(support 'class-self
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (IN a (CLASS s a)))))))
(warrant! 'class-self 'well-known
  "Unfold CLASS: a in CLASS(s,a) iff a in X(s) and RELATED(s,a,a); the latter
   is reflexivity of REL (the is-equivalence conjunct folded into IS-SETOID).")

;; class-subset-carrier: [a] subset X(s).  (CLASS is a separation OF X(s).)
(support 'class-subset-carrier
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (SUBSET (CLASS s a) (X s)))))))
(warrant! 'class-subset-carrier 'well-known
  "CLASS(s,a) = SEP(b, X(s), ...) is by construction a subset of X(s).")

;; class-is-set: [a] is a set (subclass of the set X(s), by separation).
(support 'class-is-set
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (IN (CLASS s a) SET))))))
(warrant! 'class-is-set 'well-known
  "A subclass of a set is a set (separation); CLASS(s,a) subset X(s) in SET.")

;; class-eq-iff: [a] = [b]  <=>  a ~ b.  THE fundamental fact -- equal classes
;; exactly captures the relation.  (=>) by class-self + symmetry; (<=) by
;; transitivity + symmetry, set-extensionality on the class memberships.
(support 'class-eq-iff
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (FORALL b (IMPLIES (IN b (X s))
         (IFF (= (CLASS s a) (CLASS s b))
              (RELATED s a b)))))))))
(warrant! 'class-eq-iff 'well-known
  "(<=) a~b: for any c, b~c iff a~c by transitivity+symmetry, so the two
   separations have the same members; set-extensionality gives [a]=[b].
   (=>) [a]=[b]: a in [a]=[b] (class-self) means a~b.  Uses exactly the three
   equivalence laws folded into IS-SETOID.")

;; class-disjoint: distinct classes are disjoint -- the partition property.
;; Either [a] = [b], or they share no element.
(support 'class-disjoint
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (FORALL b (IMPLIES (IN b (X s))
         (OR (= (CLASS s a) (CLASS s b))
             (= (INTERSECTION (CLASS s a) (CLASS s b)) EMPTY-SET)))))))))
(warrant! 'class-disjoint 'well-known
  "If [a],[b] share a c then a~c and b~c, so a~b (transitivity+symmetry) and
   [a]=[b] by class-eq-iff.  Contrapositive: distinct classes meet emptily.
   Together with class-self (cover) this is `QUOTIENT(s) partitions X(s)'.")

;; class-in-quotient: [a] is a member of the quotient.  (PROJ lands in QUOTIENT.)
(support 'class-in-quotient
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (X s))
       (IN (CLASS s a) (QUOTIENT s)))))))
(warrant! 'class-in-quotient 'well-known
  "QUOTIENT(s) = IMAGE(PROJ(s), X(s)); a in X(s) witnesses [a]=PROJ(s)(a) as
   a member of the image (image-membership + lambda-beta on PROJ).")

;; quotient-is-set: X(s)/REL is a set when X(s) is (IMAGE of a set is a set).
(support 'quotient-is-set
  '(FORALL s (IMPLIES (IS-SETOID s)
     (IN (QUOTIENT s) SET))))
(warrant! 'quotient-is-set 'well-known
  "X(s) is a set (carrier shape constraint); the IMAGE of a set under a
   function is a set (replacement/image-is-set).")

;; proj-in-fun: PROJ(s) : X(s) -> QUOTIENT(s).
(support 'proj-in-fun
  '(FORALL s (IMPLIES (IS-SETOID s)
     (IN (PROJ s) (FUN (X s) (QUOTIENT s))))))
(warrant! 'proj-in-fun 'well-known
  "PROJ(s) = VNB-LAMBDA a. CLASS(s,a) is total on X(s) and, by
   class-in-quotient, every value lies in QUOTIENT(s); so it is in
   FUN(X(s),QUOTIENT(s)).  It is surjective by construction (QUOTIENT is its
   image).")

;;; =======================================================================
;;; Descent and the universal property.
;;; =======================================================================

;; RESPECTS(s,f): f is constant on equivalence classes (a ~ b => f(a)=f(b)).
;; Exactly the condition under which f descends to the quotient.
(def-functoid 'RESPECTS '(s f)
  '(FORALL a (IMPLIES (IN a (X s))
     (FORALL b (IMPLIES (IN b (X s))
       (IMPLIES (RELATED s a b) (= (f a) (f b))))))))

;; DESCEND(f) : X/REL -> Z, the induced map.  On a class c it returns the
;; unique z that is f of some member of c -- IOTA, NOT a chosen representative.
;; When f RESPECTS the relation, { f(a) : a in c } is a singleton, so the
;; description is well-defined and INDEPENDENT of representative.
(def-functoid 'DESCEND '(f)
  '(VNB-LAMBDA c (IOTA z (FORSOME a (AND (IN a c) (= z (f a)))))))

;; descend-computes: the descent equation  DESCEND(f)([a]) = f(a)  -- i.e.
;; DESCEND(f) o PROJ(s) = f, the factorization, stated pointwise.
(support 'descend-computes
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (X s) Z)) (RESPECTS s f))
         (FORALL a (IMPLIES (IN a (X s))
           (= ((DESCEND f) (CLASS s a)) (f a))))))))))
(warrant! 'descend-computes 'well-known
  "Lambda-beta: DESCEND(f)([a]) = IOTA z. exists a' in [a]. z = f(a').  Since
   a in [a] (class-self), f(a) satisfies the body.  For uniqueness: any a' in
   [a] has a~a', so f(a')=f(a) by RESPECTS; the body pins z = f(a) uniquely,
   and IOTA returns it.  Representation-independent -- the value never depends
   on which member is named.")

;; descend-in-fun: DESCEND(f) : QUOTIENT(s) -> Z.
(support 'descend-in-fun
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (X s) Z)) (RESPECTS s f))
         (IN (DESCEND f) (FUN (QUOTIENT s) Z))))))))
(warrant! 'descend-in-fun 'well-known
  "Every element of QUOTIENT(s) is some [a] with a in X(s) (it is the image of
   PROJ); on it DESCEND(f) returns f(a) in Z (descend-computes), well-defined
   by RESPECTS.  So DESCEND(f) is total QUOTIENT(s) -> Z.")

;; quotient-universal (CAPSTONE): the universal property of the quotient.
;; A relation-respecting f : X(s) -> Z factors UNIQUELY through PROJ(s):
;; there is exactly one g : QUOTIENT(s) -> Z with g([a]) = f(a) for all a.
;; (VNB has no FORSOME-unique; uniqueness is spelled out as the inner FORALL.)
(support 'quotient-universal
  '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (X s) Z)) (RESPECTS s f))
         (FORSOME g
           (AND (IN g (FUN (QUOTIENT s) Z))
             (AND
               ;; g factors f through the projection
               (FORALL a (IMPLIES (IN a (X s))
                 (= (g (CLASS s a)) (f a))))
               ;; ... and is the only such map
               (FORALL g_
                 (IMPLIES (AND (IN g_ (FUN (QUOTIENT s) Z))
                               (FORALL a (IMPLIES (IN a (X s))
                                 (= (g_ (CLASS s a)) (f a)))))
                          (= g_ g)))))))))))))
(warrant! 'quotient-universal 'well-known
  "EXISTENCE: take g = DESCEND(f); descend-in-fun types it and descend-computes
   gives the factorization g([a])=f(a).  UNIQUENESS: any g' factoring f agrees
   with g on every [a] (both equal f(a)); every element of QUOTIENT(s) is such
   an [a] (image of PROJ), so g' and g agree everywhere on QUOTIENT(s) and are
   equal by function extensionality.  This is what makes X |-> X/REL a functor:
   the concrete quotient has the defining mapping property.  Capstone asserted
   with a faithful sketch over the installed CLASS/QUOTIENT/PROJ/DESCEND
   supports, in the prod-of-sums-expansion / binomial-theorem library style --
   the machinery is the deliverable, the QED induction-free factorization
   argument is the deferred tactic grind, with no missing primitive.")
