;;; complement-union-case-study.scm -- b = a u (b \ a) when a is a subset of b.
;;;
;;; SAVED AS AN EXAMPLE OF WHAT CAN GO WRONG.  The theorem is a one-liner on
;;; paper.  Everything below is what the machine did with it on 2026-08-15, kept
;;; because each wrong turn was a defect in the ASSISTANT rather than in the
;;; mathematics, and because the proof that finally worked is eleven lines.
;;;
;;; Not loaded by load.scm; run it directly:  ./prover examples/complement-union-case-study.scm
;;;
;;; ---------------------------------------------------------------- THE PROOF
;;;
;;; Both sides are classes, so it is a question about members: for each x,
;;; x in b iff x in a or x in (b \ a).  Left to right needs excluded middle on
;;; `x in a'; right to left needs `a subset b' for the first disjunct and
;;; nothing at all for the second.  The whole content is propositional once the
;;; two membership laws are unfolded and the subset hypothesis is instantiated.
;;;
;;; -------------------------------------------------- WHAT WENT WRONG, IN ORDER
;;;
;;; Each of these was advice the copilot gave, and each is now fixed.  They are
;;; recorded because the SHAPE of the mistake recurs: every one of them was a
;;; lane that tested the goal's shape and never tested whether the move it named
;;; would do anything.
;;;
;;; 1. `use-em' on a proposition already in the context.  what-now offered a
;;;    case split on `x in a' when `x in a' was assumption 2.  The split is
;;;    vacuous on one branch (context-add-assumption is alpha-idempotent, so the
;;;    branch is hash-consed back onto its parent) and contradictory on the
;;;    other, and there is no undo.  The goal was already finished: (oi-l)(ass).
;;;    use-em now refuses; the lane names the two-move close.
;;;
;;; 2. `(bc* 'class-extensionality)' on a goal still under its quantifiers.  The
;;;    lane reads the prenex-normalised CONCLUSION, so it fired on a FORALL and
;;;    named a move that matches the bare equation only.  It now probes
;;;    bc*-dispatch and prefixes the (di) -- or stays quiet.
;;;
;;; 3. Rewrites that undo, reorient, duplicate, or re-fold.  `ms-eq-symm' and
;;;    its -rev (the same move twice: symmetry is its own converse) merely
;;;    reoriented an equation nested three binders down, where the top-level
;;;    churn check could not see it.  `is-set-rev' renamed `a in set' to
;;;    `is-set(a)'.  `complement-in-membership-rev' offered to undo an unfold
;;;    from two steps back.  `difference-membership-rev' folded
;;;    `x in b and not(x in a)' back inside a term.  All four are now triaged by
;;;    their RESULT, not by their name.
;;;
;;; 4. Induction, three times.  nn- / finite-set- / transfinite-induction each
;;;    quantify over a class variable occurring only as `_ in c' -- a predicate
;;;    variable in disguise -- so each concludes `... in c' and fingerprints
;;;    against EVERY membership goal in the library.  On the leaf `x in b' all
;;;    three fired and were offered.  Backchaining one replaces a single
;;;    membership with a base case and a step about ALL members.
;;;
;;; 5. `p' (prop) "doing nothing".  It declined correctly -- `a subset b' is an
;;;    opaque atom to a propositional reader, so `x in a' true with `x in b'
;;;    false is a countermodel -- and said so in the REPL, which the workspace
;;;    never showed.  No declining tactic was visible in a workspace: Emacs
;;;    watched for `;; VNB error:' and a decline is `;VNB warning:'.
;;;
;;; 6. THE EMITTED SCRIPT DID NOT REPLAY.  This is the one worth keeping.  The
;;;    proof was genuinely complete -- the workspace said so, and it was right.
;;;    But `prop' drives its branches with `dk-focus!', which moves the focus
;;;    WITHOUT recording a command, so the emitted script listed prop's
;;;    expansion (21 lines of cut/pbc/oi/ass) and replayed those steps against
;;;    whatever leaf the engine happened to focus.  Result: 9 open leaves and a
;;;    cascade of `cannot decompose' / `goal not in context'.  A complete proof
;;;    can emit a script that fails.  `prop' now records ITSELF, which is both
;;;    replayable and readable; `minimize!' and a bodied `use-em' still emit
;;;    their expansion and still have this problem.
;;;
;;; ------------------------------------------------------------- THE SHORT PROOF
;;; Verified: reaches (qed) `proven modulo 0', and replays from this file.

(sp (make-wff '(forall a (implies (in a set) (forall b (implies (in b set)
     (implies (subset a b) (= b (union a (complement-in b a))))))))))

(grind)                              ; peel the binders and the guards
(bc* 'class-extensionality)          ; two classes are equal iff same members
(di)                                 ; introduce x, split the iff
(mac 'union-membership)              ; x in a u c  ->  x in a or x in c
(mac 'complement-in-membership)      ; x in b \ a  ->  x in b and not (x in a)
(di)                                 ; the two directions of the iff

;; ->  x in b  |-  x in a or (x in b and not (x in a))
;; Excluded middle on `x in a', both branches immediate.  One move.
(prop)

;; ->  x in a or (x in b and not (x in a))  |-  x in b
;; The left disjunct needs the subset hypothesis, which is opaque to `prop'
;; until it is unfolded and instantiated at x -- exactly what prop's
;; countermodel said when it declined here.
(mac-h 'subset-def '(subset a b))
(inst+ '(forall x (implies (in x a) (in x b))) 'x)
(prop)

(qed 'union-complement-absorb)

;;; -------------------------------------------- THE SCRIPT THAT DID NOT REPLAY
;;; Emitted by write-proof-script from the very same completed proof, on a build
;;; where prop recorded its expansion.  Kept verbatim.  Loading it gives
;;; `proof-done? #f' with 9 open leaves.
;;;
;;;   (sp (make-wff (quote (forall a (implies (in a set) ...)))))
;;;   (grind)
;;;   (bc* (quote class-extensionality) ())
;;;   (di)
;;;   (mac (quote union-membership))
;;;   (mac (quote complement-in-membership))
;;;   (di)
;;;   (cut (quote (or (in x a) (not (in x a)))))     <-- prop's expansion begins
;;;   (ai (quote (or (in x a) (not (in x a)))))
;;;   (pbc)
;;;   (cut (quote (not (in x a))))
;;;   (di)
;;;   (cut (quote (or (in x a) (not (in x a)))))
;;;   (oi-l)
;;;   (ass)
;;;   (ai (quote (not (or (in x a) (not (in x a))))))
;;;   (cut (quote (or (in x a) (not (in x a)))))
;;;   (oi-r)
;;;   (ass)
;;;   (ai (quote (not (or (in x a) (not (in x a))))))
;;;   (oi-l)
;;;   (ass)
;;;   (oi-r)
;;;   (di)
;;;   (ass)
;;;   (ass)                                          <-- ... and ends
;;;   (ai 1)
;;;   (mac-h (quote subset-def) 5)
;;;   (inst 1 "x")
;;;   ... a second expansion of the same shape ...
;;;   (detach! (quote (implies (in x a) (in x b))))
;;;   (ai (quote (not (in x b))))
;;;   (ai 1)
