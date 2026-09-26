;;; compose.scm -- COMPOSE: composition of functions, f o g.
;;;
;;;   COMPOSE(f, g)        the composite "f after g": apply g, then f, so
;;;                        (COMPOSE f g)(x) = f(g(x)).
;;;
;;; DEFINITIONAL, via the VNB-LAMBDA binder (which has unconditional beta
;;; `lam-b' and typing `lam-t' rules):
;;;
;;;   COMPOSE(f, g) := VNB-LAMBDA z. f(g(z))
;;;
;;; so both characteristic laws are DERIVED, not asserted:
;;;   - compose-apply  is unfold-COMPOSE then lambda-beta (lam-b), and is now
;;;     PROVEN, in theorem-library/compose-apply-proof.scm;
;;;   - compose-type   is lambda-type (lam-t) then dom-of-fun, and is now
;;;     PROVEN too, in the same file -- GUARDED on (IN A SET), which is the
;;;     one thing the prose derivation had skipped: see the note there.
;;; (Compare RING-POWER, which wraps MPOW.)
;;;
;;; Argument order follows the mathematical o: COMPOSE(f, g) = f o g means g
;;; runs first.  In particular, for a sequence g : NN -> PTS(s) and a map
;;; f : PTS(s) -> PTS(t), COMPOSE(f, g) : NN -> PTS(t) is the sequence n |-> f(g(n))
;;; -- the term Prop 3.14 (~/docs/calculus.pdf) needs to state sequential
;;; continuity natively, with no Skolem stand-in.
;;;
;;; Dependencies: VNB-LAMBDA (library.scm / primitive-inferences.scm) and the
;;; FUN/apply axioms (fun-codomain-iff).  Nothing metric-specific -- loaded
;;; with the foundations so every later library can use it.

(def-functoid 'COMPOSE '(f g)
  '(VNB-LAMBDA z_ (DOM g) (f (g z_))))

;;; compose-apply: (COMPOSE f g)(x) = f(g(x)).  Stated against the typed form
;;; g : A -> B, f : B -> C (so both sides denote a defined point of C); the
;;; reduction itself is the beta step, on the lambda's own domain DOM(g).
;;;
;;; PROVEN modulo 0 (2026-08-23) in theorem-library/compose-apply-proof.scm --
;;; it cannot be proved HERE, `sp'/`qed' not existing this early in load.scm.
;;; It was a `support' warranted `proof' whose warrant text WAS the derivation
;;; and had never been run; the text also asserted "the beta step needs no
;;; hypotheses", which the beta guard (2026-08-03) made false: the lambda's
;;; domain is DOM(g), not A, so (IN x (DOM g)) has to be landed FIRST, off
;;; fun-codomain-iff + dom-fun-membership.  See that file's header.

;;; compose-type: g : A -> B and f : B -> C give f o g : A -> C.
;;;
;;; PROVEN modulo 0 (2026-08-23) in theorem-library/compose-apply-proof.scm,
;;; beside compose-apply -- it cannot be proved HERE, `sp'/`qed' not existing
;;; this early in load.scm.  Like its sibling it was a `support' warranted
;;; `proof' whose warrant text WAS the derivation and had never been run, and
;;; running it showed the text incomplete: `lam-t' types the unfolded lambda
;;; over DOM(g), and reaching FUN(A,C) needs `dom-of-fun', hence (IN A SET),
;;; which nothing in the tree derives from (IN g (FUN A B)).  The installed
;;; theorem therefore carries (IN A SET) as its OUTERMOST antecedent; the five
;;; citation sites were migrated the same day.  See that file's header.
