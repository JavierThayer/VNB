;;; cr-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23).
;;;
;;; `compose-apply' (structure-library/compose.scm:32) is a `support' warranted
;;; `proof' whose warrant TEXT is the derivation -- "unfold COMPOSE to
;;; VNB-LAMBDA z. f(g(z)), then lambda-beta" -- and that derivation has never
;;; been run.  It is, with `compose-type', the WHOLE bill of
;;; `compose-continuous-at' and of `deriv-chain': prove it and half the debt of
;;; the chain rule goes away.
;;;
;;; Run:   ./prover -b -i scratchpad/cr-drive.scm      (or (load "...") in a REPL)
;;;
;;; The lines below leave you on the goal
;;;
;;;     ((VNB-LAMBDA z_ (DOM g) (f (g z_))) x)  =  f(g(x))
;;;
;;; with (IN x a), (IN g (FUN a b)), (IN f (FUN b c)), (IN (g x) b) and
;;; (IN (f (g x)) c) in context.  `(lam-b)' fires and `(rfl)' closes -- BUT
;;; `lam-b' needs its argument typed in the lambda's OWN domain FIRST, and the
;;; domain here is (DOM g), not a.  Fire it without that and the step still
;;; happens and OWES (IN x (DOM g)) at a node that cannot discharge it.
;;;
;;; So the leaf is: get (IN x (DOM g)) from (IN x a) and (IN g (FUN a b)).
;;; The two base-theory axioms that bridge it (theory.scm:459, :493, both
;;; PRIMITIVE, so free) are
;;;
;;;   fun-codomain-iff     f in FUN(A,B) iff f in FUN(A) and forall x in A. f(x) in B
;;;   dom-fun-membership   f in FUN(A)  =>  forall x. (x in DOM f  iff  x in A)
;;;
;;; `mac-h' the first at (IN g (FUN a b)) to reach (IN g (FUN a)); `fact' the
;;; second; `inst+' at x; the IFF then wants `prop' (or `ai') inside a `have!'.
;;; Then (mac 'COMPOSE) is already done below, so: (lam-b) (rfl).
;;;
;;; `compose-type' is the SIBLING and is NOT the same size -- `lam-t' types the
;;; unfolded lambda over (DOM g), and getting from FUN((DOM g), c) to FUN(a, c)
;;; wants `dom-of-fun' (theory.scm:501), hence (IN a SET), which nothing in the
;;; tree derives from (IN g (FUN a b)).  That one is a design question, not a
;;; driver.

(sp (make-wff
  '(FORALL A (FORALL B (FORALL C (FORALL f (FORALL g
     (IMPLIES (AND (IN g (FUN A B)) (IN f (FUN B C)))
       (FORALL x (IMPLIES (IN x A)
         (= ((COMPOSE f g) x) (f (g x)))))))))))))
(dk-peel-to! '=)
(ai '(AND (IN g (FUN a b)) (IN f (FUN b c))))
(fact 'fun-apply-type-c 'g 'a 'b 'x)          ; IN (g x) b
(fact 'fun-apply-type-c 'f 'b 'c '(g x))      ; IN (f (g x)) c  -- rfl's definedness
(mac 'COMPOSE)
(display "\n### your goal: ") (write (dk-goal)) (newline)
(display "### missing:   (IN x (DOM g))\n")
