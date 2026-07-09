;;; prove-nth-deriv-one.scm -- DUMB assembly of  f^(1) = the derivative function
;;; (calculus.pdf Def 2.2 at order 1), as a test of the automatable-assembly
;;; criterion: NO bespoke choreography.  The only moves are
;;;   (grind)        -- uniform normalization (intro foralls, unfold, split)
;;;   (scout d b n)  -- best-first search: clones the goal per branch, tries the
;;;                     tactic alphabet (grind/closers/mac/bc*/inst), discards
;;;                     dead branches.  "Many false starts", literally.
;;;   (scout-run 1)  -- adopt the first closing branch (replays it on the live
;;;                     deduction graph; a closing branch is a real kernel proof)
;;;
;;; If this reaches PROVED? #t, the blocks for f^(1) are complete by the dumb
;;; criterion -- nth-deriv-zero / nth-deriv-succ (def-by-nn-recursion), the
;;; numeral<->succ matcher bridge (so (succ n) fires on the literal 1), and the
;;; NN closure of 0 -- all assembled by search, no human/LLM in the loop.
;;;
;;; Run (RAM/swap helps -- the search + full prover image are heavy):
;;;   VNB_SKIP_PROOFS=1 mit-scheme --quiet --load load.scm \
;;;       --load prove-scripts/prove-nth-deriv-one.scm --eval '(exit)'
;;;
;;; Status when shipped: (scout 6 3 300) found 4 closing branches on the box;
;;; the adopt-and-replay step (scout-run) is what your machine runs to QED.


(sp '(FORALL f (== (NTH-DERIV f 1) (VNB-LAMBDA x (DERIV f x)))))
(grind)

(display "\n;; scouting (depth 6, fanout 3, <=600 nodes)...\n")
(let ((r (scout 6 3 600)))
  (display ";; nodes examined = ") (display (list-ref r 0))
  (display ", closing branches = ") (display (length (list-ref r 4))) (newline))

(scout-run 1)

(display "\nPROVED? ") (display (proof-done? *ps*)) (newline)
(if (proof-done? *ps*)
    (display ";; *** f^(1) assembled by a dumb scout pass -- block-complete. ***\n")
    (display ";; NOT closed by scout at these bounds -- blocks NOT yet complete.\n"))
