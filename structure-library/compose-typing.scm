;;; compose-typing.scm -- RAN (range) + mindless type-closure lemmas for
;;; nested function application.
;;;
;;; The point (a user design call, 2026-06-08): when you type-check a nested
;;; application g(f(a)), the intermediate space is the SOURCE of friction --
;;; written as a free variable Y it is an undetermined schema var the prover
;;; cannot infer and you must supply.  Written as RAN(f) -- a term COMPUTED
;;; from f -- it is determined by matching, so nothing is supplied.  These
;;; lemmas are deliberately mindless: cite the one of the right depth and it
;;; closes the goal in a single bc*.
;;;
;;;   RAN(f) := IMAGE(f, DOM(f))         the range (image of the whole domain)
;;;
;;; The "let*" chaining (g's domain is the range of f) is just ordinary
;;; nested typed FORALL: f is bound before g, so RAN(f) is in scope.
;;;
;;; NOTE on naming: the domain is X, NOT A -- VNB case-folds, so a bound `A'
;;; and a bound `a' are the SAME identifier (capture).  [[feedback-no-case-variant-binders]]
;;; Antecedents are CURRIED (nested IMPLIES, not one AND) so bc* spawns each
;;; hypothesis as its own subgoal, dischargeable by ass-all.
;;;
;;; Dependencies: IMAGE + image-membership-iff (injection.scm), DOM +
;;; dom-membership / dom-fun-membership (theory.scm).  Loads after injection.

(def-functoid 'RAN '(f)
  '(IMAGE f (DOM f)))

;;; range-membership: f(a) lands in RAN(f) for any a in the domain of f.
;;; The single fact every lemma below iterates.  a, f are fixed by matching
;;; the conclusion (f a) / (RAN f); nothing is undetermined.
(support 'range-membership
  '(FORALL f (FORALL a
     (IMPLIES (IN a (DOM f))
              (IN (f a) (RAN f))))))
(warrant! 'range-membership 'proof
  "Unfold RAN to IMAGE(f, DOM f); image-membership-iff says (f a) in IMAGE(f, DOM f) iff some x in DOM(f) has f(x)=(f a).  Witness x:=a: a in DOM(f) by hypothesis and (f a)=(f a) is defined there (dom-membership).")

;;; fun-range-membership: the typed convenience -- from f : X -> (anything)
;;; and a in X, get f(a) in RAN(f).  Bridges a in X to a in DOM(f) via
;;; dom-fun-membership, then range-membership.  This is the form the chain
;;; lemmas below actually compose.
(support 'fun-range-membership
  '(FORALL X (FORALL f (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN a X)
                (IN (f a) (RAN f))))))))
(warrant! 'fun-range-membership 'proof
  "dom-fun-membership: f in FUN(X) gives a in X => a in DOM(f); then range-membership gives (f a) in RAN(f).")

;;; ran-subset-codomain: RAN(f) sits inside any declared codomain.  The one
;;; bridge for cashing a RAN(.) conclusion out to a named set Y.
(support 'ran-subset-codomain
  '(FORALL X (FORALL Y (FORALL f
     (IMPLIES (IN f (FUN X Y))
              (SUBSET (RAN f) Y))))))
(warrant! 'ran-subset-codomain 'proof
  "w in RAN(f)=IMAGE(f,DOM f) means w=f(x) for some x in DOM(f)=X (dom-fun-membership); fun-codomain-iff on f in FUN(X,Y) gives f(x) in Y.  So RAN(f) subset Y.")

;;; -----------------------------------------------------------------------
;;; The mindless chain lemmas, depth 2..5.  Each says: feed a in X through a
;;; let*-chain of functions whose domains are the running ranges, and the
;;; nested value lands in the last range.  Each proof is fun-range-membership
;;; applied once per link (PTS |-> RAN f |-> RAN g |-> ...).  Cite the one of
;;; the matching depth; bc* spawns the curried hypotheses as subgoals, all
;;; closed by ass-all (supply the outer domain X, the only schema var the
;;; conclusion does not pin down).

(support 'compose-type-2
  '(FORALL X (FORALL f (FORALL g (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN a X)
                  (IN (g (f a)) (RAN g))))))))))
(warrant! 'compose-type-2 'proof
  "fun-range-membership: a in X, f in FUN(X) => (f a) in RAN(f); then (f a) in RAN(f), g in FUN(RAN f) => (g (f a)) in RAN(g).")

(support 'compose-type-3
  '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN a X)
                    (IN (h (g (f a))) (RAN h))))))))))))
(warrant! 'compose-type-3 'proof
  "fun-range-membership three times along X |-> RAN f |-> RAN g |-> RAN h.")

(support 'compose-type-4
  '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL k (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN k (FUN (RAN h)))
             (IMPLIES (IN a X)
                      (IN (k (h (g (f a)))) (RAN k))))))))))))))
(warrant! 'compose-type-4 'proof
  "fun-range-membership four times along X |-> RAN f |-> RAN g |-> RAN h |-> RAN k.")

(support 'compose-type-5
  '(FORALL X (FORALL f (FORALL g (FORALL h (FORALL k (FORALL m (FORALL a
     (IMPLIES (IN f (FUN X))
       (IMPLIES (IN g (FUN (RAN f)))
         (IMPLIES (IN h (FUN (RAN g)))
           (IMPLIES (IN k (FUN (RAN h)))
             (IMPLIES (IN m (FUN (RAN k)))
               (IMPLIES (IN a X)
                        (IN (m (k (h (g (f a))))) (RAN m))))))))))))))))
(warrant! 'compose-type-5 'proof
  "fun-range-membership five times along X |-> RAN f |-> RAN g |-> RAN h |-> RAN k |-> RAN m.")
