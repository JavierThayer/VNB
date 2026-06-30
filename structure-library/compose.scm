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
;;;   - compose-apply  is unfold-COMPOSE then lambda-beta (lam-b);
;;;   - compose-type   is lambda-type (lam-t) then fun-codomain-iff twice.
;;; (Compare RING-POWER, which wraps MPOW.)
;;;
;;; Argument order follows the mathematical o: COMPOSE(f, g) = f o g means g
;;; runs first.  In particular, for a sequence g : NN -> PTS(s) and a map
;;; f : PTS(s) -> PTS(t), COMPOSE(f, g) : NN -> PTS(t) is the sequence n |-> f(g(n))
;;; -- the term Prop 3.14 (~/docs/calculus.pdf) needs to state sequential
;;; continuity natively, with no Skolem stand-in.
;;;
;;; Dependencies: VNB-LAMBDA (theory.scm / primitive-inferences.scm) and the
;;; FUN/apply axioms (fun-codomain-iff).  Nothing metric-specific -- loaded
;;; with the foundations so every later library can use it.

(def-functoid 'COMPOSE '(f g)
  '(VNB-LAMBDA z_ (f (g z_))))

;;; compose-apply: (COMPOSE f g)(x) = f(g(x)).  Stated against the typed form
;;; g : A -> B, f : B -> C (so both sides denote a defined point of C); the
;;; reduction itself is the unconditional beta step.
(support 'compose-apply
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
       (FORALL x (IMPLIES (IN x A)
         (= ((COMPOSE f g) x) (f (g x))))))))))))
(warrant! 'compose-apply 'proof
  "Unfold COMPOSE to VNB-LAMBDA z. f(g(z)), then lambda-beta (lam-b): ((VNB-LAMBDA z. f(g(z))) x) reduces to f(g(x)), and reflexivity closes it.  The beta step needs no hypotheses; the typing is carried only so both sides are defined points of C.")

;;; compose-type: g : A -> B and f : B -> C give f o g : A -> C.
(support 'compose-type
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
       (IN (COMPOSE f g) (FUN A C)))))))))
(warrant! 'compose-type 'proof
  "Unfold COMPOSE, then lambda-type (lam-t): the goal becomes `for z in A, f(g(z)) in C'.  g(z) in B by fun-codomain-iff on g (z in A), then f(g(z)) in C by fun-codomain-iff on f.")
