;;; nn-not-le-zero-pos-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-24),
;;; from the session that proved the NN order block (theorem-library/
;;; nn-order-ord.scm).
;;;
;;; Run:   ./prover -i prove-scripts/drives/nn-not-le-zero-pos-drive.scm
;;;
;;; THE STATEMENT, the last `well-known' support of the NN order block:
;;;
;;;     structure-library/order-lemmas.scm:248
;;;     nn-not-le-zero-pos :  j in NN,  1 <= j   =>   NOT (j <= 0)
;;;
;;; WHY IT IS WORTH THE TEN MINUTES.  Measured on the library as it stands, it
;;; is named in bills where it is now the SOLE unwarranted leaf -- so unlike
;;; five of the seven facts proved this session, it pays on its own with no
;;; shadowing.  It clears
;;;
;;;     nn-le-zero-is-zero          residue after the seven: (nn-not-le-zero-pos)
;;;     nn-nested-subset-chain      residue: (nn-not-le-zero-pos)
;;;     nn-nested-subset-chain-j    residue: (nn-not-le-zero-pos)
;;;
;;; and shrinks a dozen more (diagonalization, the Smith clearing chain,
;;; card-union-bound, trinum-mono, nnpair-*).
;;;
;;; THE ROUTE, and it is the file's route with no new idea in it.  Peel to
;;; FALSITY -- so `1 <= j' and `j <= 0' are both hypotheses -- and then:
;;;
;;;   1.  j ORD-LE 0        the compat bridge on (j, 0)
;;;   2.  0 ORD-LE j        ord-zero-least
;;;   3.  j = 0             ord-le-antisymm on 1 and 2
;;;   4.  1 <= 0            `subst' the equation into the hypothesis' side goal
;;;   5.  1 ORD-LE 0        the bridge again, on (1, 0)
;;;   6.  0 ORD-LE 1        ord-zero-least at 1 (nn-one-in types it)
;;;   7.  0 = 1             ord-le-antisymm on 5 and 6
;;;   8.  contradiction     nn-succ-nonzero at 0 says succ 0 /= 0, and
;;;                         `arith' says 1 = succ 0.
;;;
;;; Every citation is either PRIMITIVE (the ord-* family, nn-subset-ord) or
;;; `modulo 0' (nn-one-in, nn-succ-nonzero), so the result should print
;;; `proven modulo 0'.  If it does not, the bill names what went in sideways.
;;;
;;; WHAT NOT TO DO.  `prop' will not finish any of these: the ORD contexts run
;;; to about 30 distinct atoms and *prop-atom-cap* is 12.  Steps 3 and 7 are
;;; equality reasoning, which `prop' cannot do at any cap -- an `=' is an opaque
;;; atom to it.  `ineq' is no help either: it demands an `IN t RR' certificate
;;; for every atom and the context types in NN.
;;;
;;; When it closes, delete the support at order-lemmas.scm:248-252 (leave a
;;; MOVED comment, as its seven neighbours have) and add the proof to
;;; theorem-library/nn-order-ord.scm, after nn-le-succ-cases.

;;; ---- the kit, lifted from theorem-library/nn-order-ord.scm ---------------
;;; (nd- prefix: never name a top-level define like a tactic.)

(define (nd-and2 a b) (have! (list 'AND a b)))   ; have! defaults to from-context!

(define (nd-peel!)
  (let loop ((prev #f) (n 0))
    (let ((g (dk-goal)))
      (if (and (< n 12) (not (equal? g prev))
               (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop g (+ n 1)))))))

(define (nd-compat! a b)                 ; lands (IFF (ORD-LE a b) (<= a b))
  (nd-and2 (list 'IN a 'NN) (list 'IN b 'NN))
  (fact 'ord-le-nn-compat a b))

;; ord-le-nn-compat's IFF, consumed in the two directions.  `ai' on an IFF is
;; iff-elim (it lands BOTH implications); `detach!' takes the IMPLIES, not its
;; antecedent.
(define (nd-le->ord! a b)
  (ai (list 'IFF (list 'ORD-LE a b) (list '<= a b)))
  (detach! (list 'IMPLIES (list '<= a b) (list 'ORD-LE a b))))
(define (nd-ord->le! a b)
  (ai (list 'IFF (list 'ORD-LE a b) (list '<= a b)))
  (detach! (list 'IMPLIES (list 'ORD-LE a b) (list '<= a b))))

(define (nd-antisym! a b)                ; from ORD-LE(a,b) and ORD-LE(b,a), land a=b
  (nd-and2 (list 'ORD-LE a b) (list 'ORD-LE b a))
  (fact 'ord-le-antisymm a b))

;;; ---- the goal, set up and handed over ------------------------------------
(sp (make-wff '(FORALL j_ (IMPLIES (IN j_ NN)
                 (IMPLIES (<= 1 j_) (NOT (<= j_ 0)))))))
(nd-peel!)                               ; goal is now FALSITY

;; the typings the bridges need
(fact 'nn-zero-in)
(fact 'nn-one-in)
(fact 'nn-subset-ord 'j_)
(fact 'nn-subset-ord 0)
(fact 'nn-subset-ord 1)

;; step 2 and step 6, the two halves of "0 is least"
(fact 'ord-zero-least 'j_)
(fact 'ord-zero-least 1)

(display "\n;;; ------------------------------------------------------------\n")
(display ";;; nn-not-le-zero-pos: set up, steps 1 and 3-8 left to drive.\n")
(display ";;; goal: ") (write (dk-goal)) (newline)
(display ";;; try (what-now), or start with\n")
(display ";;;   (nd-compat! 'j_ 0)  (nd-le->ord! 'j_ 0)\n")
(display ";;; and read the route in the header from there.\n")
(display ";;; when it closes:  (qed 'nn-not-le-zero-pos)\n")
(display ";;; ------------------------------------------------------------\n")
