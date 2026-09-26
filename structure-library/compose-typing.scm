;;; RETIRED 2026-09-17 (proven): range-membership, fun-range-membership,
;;; ran-subset-codomain, compose-type-2/3/4/5 -- theorem-library/rake-compose-typing.scm,
;;; all modulo 0 from dom-membership / dom-fun-membership / fun-codomain-iff /
;;; image-membership-iff.  They had been `proof'-warranted supports here; the
;;; def-functoid RAN below is what remains of this file, and their proofs unfold it.
;;;
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

;;; fun-range-membership: the typed convenience -- from f : X -> (anything)
;;; and a in X, get f(a) in RAN(f).  Bridges a in X to a in DOM(f) via
;;; dom-fun-membership, then range-membership.  This is the form the chain
;;; lemmas below actually compose.

;;; ran-subset-codomain: RAN(f) sits inside any declared codomain.  The one
;;; bridge for cashing a RAN(.) conclusion out to a named set Y.

;;; -----------------------------------------------------------------------
;;; The mindless chain lemmas, depth 2..5.  Each says: feed a in X through a
;;; let*-chain of functions whose domains are the running ranges, and the
;;; nested value lands in the last range.  Each proof is fun-range-membership
;;; applied once per link (PTS |-> RAN f |-> RAN g |-> ...).  Cite the one of
;;; the matching depth; bc* spawns the curried hypotheses as subgoals, all
;;; closed by ass-all (supply the outer domain X, the only schema var the
;;; conclusion does not pin down).




