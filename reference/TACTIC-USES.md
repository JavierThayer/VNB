# What each proof command can reach

A proof command changes the deduction graph only by calling kernel operations.
The operations listed against a command are the bound on what it can do: every
operation recorded by any kernel procedure reachable from the command's own code,
whether or not the library exercises it.  A command listed as `none` records nothing;
those are the navigation, search and session commands.

The list is composed from the two halves of *Kernel map*: which operations each
kernel entry point records, and which entry points each command reaches.  Entries
marked [r] come from the command registry (`*tactic-kind*`) instead, because the
kernel map predates the command.

One further set is common to every command and is stated once, in *Kernel map*,
rather than repeated in every row: the hook that runs after any command which
changed the proof, to close the definedness sequents an instantiation left owed.

| command | operations it can reach |
|---|---|
| `ai` | `and-elim` `forsome-elim` `iff-elim` `not-elim` `or-elim` |
| `apply-thm` | `forall-elim` `theorem-assumption` |
| `arith` | `arith-forsome` `arith-ground` `arith-simplify` `cartesian-decompose` `eq-subst` `macete` `tuple-equality-decompose` |
| `arith--decide` | `arith-forsome` `arith-ground` `arith-simplify` |
| `ass` | `assumption` |
| `ass-all` | `assumption` |
| `backup-one` | none |
| `bc` | `backchain` |
| `bc*` | `assumption` `backchain` `cut` `forall-elim` `theorem-assumption` |
| `bc*--attempt` | `assumption` `backchain` `cut` `forall-elim` `theorem-assumption` |
| `beta` | `functoid-beta` |
| `bu-me` | `big-union-mem-elim` |
| `bu-mi` | `big-union-mem-intro` |
| `bu-set` | `big-union-sethood` |
| `calc` | *all 64 reachable operations* |
| `ce` | `cartesian-elim` |
| `choose` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `forsome-intro` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `theorem-assumption` `tuple-equality-decompose` |
| `choose-pos` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `forsome-intro` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `theorem-assumption` `tuple-equality-decompose` |
| `ci` | `cartesian-intro` |
| `comp-me` | `comp-mem-elim` |
| `comp-mi` | `comp-mem-intro` |
| `contra` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `ineq` `macete` `not-elim` `not-intro` `or-elim` `theorem-assumption` `tuple-equality-decompose` |
| `crs` | `comm-ring-simplify` |
| `cut` | `cut` |
| `detach!` | `detach` |
| `di` | `and-intro` `forall-intro` `iff-intro` `implies-intro` `not-intro` |
| `dial` | none |
| `dial-wff` | none |
| `dk-focus!` | none |
| `eps-part` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `theorem-assumption` `tuple-equality-decompose` |
| `ew` | `forsome-intro` |
| `ew-poly` | `and-intro` `comm-ring-simplify` `forsome-intro` [r] |
| `expand` | `comm-ring-simplify` `cut` `eq-subst` [r] |
| `fact` | `arith-forsome` `arith-ground` `arith-simplify` `cut` `detach` `forall-elim` `theorem-assumption` |
| `focus` | none |
| `focus-id` | none |
| `goal-status` | none |
| `grind` | `and-elim` `and-intro` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete-hyp` `not-elim` `not-intro` `or-elim` |
| `grind-and-mp` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cut` `detach` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete-hyp` `not-elim` `not-intro` `or-elim` |
| `have!` | `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `iff-intro` `implies-intro` `macete` `not-intro` `theorem-assumption` `tuple-equality-decompose` |
| `ie` | `intersection-elim` |
| `if-false` | `if-false` |
| `if-true` | `if-true` |
| `ii` | `intersection-intro` |
| `in-rr` | `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cartesian-intro` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `iff-intro` `implies-intro` `macete` `not-intro` `theorem-assumption` `tuple-equality-decompose` |
| `in-rr--refocus!` | none |
| `ineq` | `ineq` |
| `inst` | `forall-elim` |
| `inst+` | `arith-forsome` `arith-ground` `arith-simplify` `cut` `detach` `forall-elim` |
| `iota-d` | `iota-def` |
| `iota-e` | `iota-in-elim` |
| `lam-b` | `lambda-beta` |
| `lam-b-h` | `lambda-beta-hyp` |
| `lam-t` | `lambda-type` |
| `len-r` | `length-reduce` |
| `mac` | `cartesian-decompose` `macete` `tuple-equality-decompose` |
| `mac-h` | `macete-hyp` |
| `mac-h*` | `and-elim` `forsome-elim` `iff-elim` `macete-hyp` `not-elim` `or-elim` |
| `macm` | `cartesian-decompose` `macete` `tuple-equality-decompose` |
| `minimize!` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `forsome-intro` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `reflexivity` `sep-mem-elim` `sep-mem-intro` `theorem-assumption` `tuple-equality-decompose` |
| `mp` | `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cut` `detach` `forall-elim` |
| `ni` | `nn-induction` |
| `nth-r` | `nth-reduce` |
| `obtain` | *all 64 reachable operations* |
| `obtain-at` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `theorem-assumption` `tuple-equality-decompose` |
| `oi-l` | `or-intro-left` |
| `oi-r` | `or-intro-right` |
| `orelse` | none |
| `pbc` | `proof-by-contradiction` |
| `prep` | none |
| `prop` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `or-intro-left` `or-intro-right` `proof-by-contradiction` `theorem-assumption` `tuple-equality-decompose` |
| `push-not-h` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `forsome-intro` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `or-intro-left` `or-intro-right` `proof-by-contradiction` `theorem-assumption` `tuple-equality-decompose` |
| `qed` | none |
| `qrfl` | `quasi-reflexivity` |
| `quietly` | none |
| `repeat` | none |
| `replay-proof` | *all 64 reachable operations* |
| `rfl` | `reflexivity` |
| `rs` | `ring-simplify` |
| `save-proof` | none |
| `scout` | *all 64 reachable operations* |
| `scout-run` | none |
| `scout-show` | *all 64 reachable operations* |
| `sep-me` | `sep-mem-elim` |
| `sep-mi` | `sep-mem-intro` |
| `sep-set` | `sep-sethood` |
| `show` | none |
| `simp` | `comm-ring-simplify` `cut` `eq-subst` |
| `slot` | `cartesian-decompose` `macete` `tuple-equality-decompose` |
| `slot-h` | `macete-hyp` |
| `sos` | `sos` |
| `sp` | none |
| `subst` | `eq-subst` |
| `supply` | *all 64 reachable operations* |
| `ta` | `theorem-assumption` |
| `te` | `tuples-elim` |
| `tfi` | `transfinite-induction` |
| `tfi3` | `transfinite-induction-3cases` |
| `ti` | `tuples-intro` |
| `type-term` | `assumption` `comm-ring-simplify` `cut` `detach` `eq-subst` `forall-elim` `theorem-assumption` [r] |
| `ue` | `union-elim` |
| `ui` | `union-intro` |
| `undo` | none |
| `use-at` | `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `iff-intro` `implies-intro` `macete` `not-intro` `theorem-assumption` `tuple-equality-decompose` |
| `use-em` | `and-elim` `and-intro` `arith-forsome` `arith-ground` `arith-simplify` `assumption` `cartesian-decompose` `cut` `detach` `eq-subst` `forall-elim` `forall-intro` `forsome-elim` `iff-elim` `iff-intro` `implies-intro` `macete` `not-elim` `not-intro` `or-elim` `or-intro-left` `or-intro-right` `proof-by-contradiction` `theorem-assumption` `tuple-equality-decompose` |
| `vlet` | `and-elim` `cut` `forsome-elim` `iff-elim` `not-elim` `or-elim` |
| `wbc` | `and-elim` `arith-forsome` `arith-ground` `arith-simplify` `cut` `detach` `forall-elim` `forsome-elim` `iff-elim` `not-elim` `or-elim` `theorem-assumption` |
| `wk` | `weakening` |
| `zero-it` | `comm-ring-simplify` `cut` `eq-subst` [r] |

