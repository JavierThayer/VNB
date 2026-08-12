;;; mat-basics.scm -- MAT's read-offs, PROVEN from its definition.
;;;
;;; The companion to interval-basics.scm, one constructor over: MAT is a
;;; def-functoid (matrix.scm),
;;;
;;;     MAT(m, n, X) = { P in MATRIX(X) : SIZE(P) = [m, n] }
;;;     SIZE(M)      = [ LENGTH(M), LENGTH(NTH(1, M)) ]
;;;
;;; and, like INTERVAL, it had no way to be read out of a HYPOTHESIS at all:
;;; `def-functoid' installs only a rewrite macete, so `mac' unfolds MAT in a
;;; goal but `mac-h' warns "unknown theorem/macete" and leaves the assumption
;;; untouched.  interval-basics.scm's recipe applies verbatim and is used here:
;;; prove the unfolding EQUATION once (the macete does apply to a goal that IS
;;; the equation), then every read-off `subst's its goal from the separation
;;; back to MAT, where the hypothesis matches.  No new axiom.
;;;
;;; WHY THIS FILE EXISTS.  It is step one of making CARD a definition rather
;;; than an axiom.  Before `CARD' can be defined, `interval-card-in-nn'
;;; (matrix.scm) has to be guarded -- stated unguarded it is FALSE under a
;;; defined CARD, since INTERVAL(1, +infinity) is all of NN and its cardinal is
;;; omega.  The guard it needs is `(IN b NN)' on the UPPER bound alone
;;; (INTERVAL is a separation over NN, so any natural upper bound makes it
;;; finite whatever the lower bound is).  The sites that cite it pass the
;;; literal 1 below and a matrix DIMENSION above, and the theorem statements
;;; there do not type their dimensions -- matmul-assoc quantifies `m n k l' with
;;; premises only `IN P (MAT m n (CARR A))'.  So the obligation has to come off
;;; the matrix itself, which every one of those sites has in context.  That is
;;; `mat-rows-in-nn'.
;;;
;;; STEP TWO IS DONE (2026-08-12): the guard is on, and the citing sites
;;; discharge it.  Of the 34 `fact' citations of interval-card-in-nn, 7 already
;;; had the typing in context from their own statement's premises
;;; (span-bricks2, rank-bound, and border-mult's `[1,q]' citation); 26 now land
;;; it with `mat-rows-in-nn' off a matrix in context, and border-mult's
;;; `[1, succ q]' citation lands it with `nn-succ-closed' off its premise
;;; `IN q NN'.  At every one of the 26 the dimension really is some matrix's ROW
;;; count, as surveyed above -- twice via the square elementary/unit matrix
;;; typed one line earlier (ELEM-F/G/H, MATUNIT are n-by-n), which is how the
;;; sites whose dimension is a COLUMN count of the data matrix are reached
;;; without the column read-off this file declines to prove.
;;;
;;; The control that says this is not decoration: delete the two
;;; `mat-rows-in-nn' lines from matmul-assoc-proof.scm and the library load
;;; reports `qed: proof is not complete; cannot install matmul-assoc', with the
;;; cascade behind it.  An undischarged guard is NOT silent here, because the
;;; unfired `fact' leaves the typing the finsum bricks need missing.
;;;
;;; Needs: interactive + qed/proof-debt, driver-kit (have!, dk-landed-1,
;;; dk-split!), and `length-in-nn' in its GENERALISED form (theory.scm) --
;;; `L in TUPLES(A)' for any A, not `TUPLES(SET)'.  The old guard could not be
;;; discharged here: matrix-membership gives `Q in TUPLES(TUPLES X)', and
;;; reaching TUPLES(SET) from it needs both "every member of a class is a set"
;;; and monotonicity of TUPLES, neither of which the library states.

;;; ---- the definitions, as citable equations ----------------------------
;;; `==' and separation-first, for interval-unfold's reasons: `rfl' owes a
;;; definedness witness that a bare SEP term does not syntactically have, while
;;; `==' is unconditional and `qrfl' closes it; and separation-first is the
;;; direction the read-offs `subst' in.

(sp (make-wff '(FORALL m (FORALL n (FORALL X
   (== (SEP P (MATRIX X) (= (SIZE P) (LIST m n))) (MAT m n X)))))))
(di)
(mac 'MAT)
(qrfl)
(qed 'mat-unfold)
(topic! 'mat-unfold 'plumbing)

(sp (make-wff '(FORALL M (== (LIST (LENGTH M) (LENGTH (NTH 1 M))) (SIZE M)))))
(di)
(mac 'SIZE)
(qrfl)
(qed 'size-unfold)
(topic! 'size-unfold 'plumbing)

;;; NTH on a literal pair.  `nth-r' reduces it in a GOAL; this makes the same
;;; reduction citable as an equation, which is what a `subst' chain needs.
(sp (make-wff '(FORALL a (FORALL b (== (NTH 1 (LIST a b)) a)))))
(di)
(nth-r)
(qrfl)
(qed 'nth1-pair)
(topic! 'nth1-pair 'plumbing)

;;; ---- the read-off: a matrix knows how many rows it has ----------------
;;;
;;;   IN Q (MAT m n X)  =>  IN m NN
;;;
;;; m is LENGTH(Q) -- read out of SIZE(Q) = [m, n] by taking the first
;;; component -- and the length of a tuple is a natural number.  The chain is
;;; four rewrites of the goal `LENGTH(Q) = m':
;;;
;;;   LENGTH(Q) = m
;;;     -> nth(1, [LENGTH(Q), LENGTH(nth(1,Q))]) = m      nth1-pair, backwards
;;;     -> nth(1, SIZE(Q))                       = m      size-unfold
;;;     -> nth(1, [m, n])                        = m      the separation's own equation
;;;     -> m = m                                          nth1-pair
;;;
;;; NOT PROVED HERE, and it is not an oversight: the COLUMN dimension.
;;; n is LENGTH(NTH(1, Q)), and `nth-in-range' needs 1 <= LENGTH(Q) before
;;; NTH(1, Q) is known to be a tuple at all -- out-of-range NTH is unspecified
;;; in the intended model (theory.scm's own comment on make-set-membership).
;;; So for a matrix with no rows, `n in NN' is not available and should not be:
;;; MAT(0, n, X) constrains n only through an undefined term.  A guarded
;;; `mat-cols-in-nn' (on `1 <= m') is the honest form if a site ever needs it.
;;; At the sites surveyed so far it does not -- in matmul-assoc every dimension
;;; that reaches an INTERVAL is the ROW dimension of some matrix in context
;;; (n of Q : MAT n k, k of R : MAT k l).

(define MB-SEP '(SEP P (MATRIX X) (= (SIZE P) (LIST m n))))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IN m NN))))))))
(di) (di)
(fact 'mat-unfold 'm 'n 'X)
;; pull the hypothesis across the unfolding equation into the separation
(have! (list 'IN 'Q MB-SEP)
       (lambda () (subst (list '== MB-SEP '(MAT m n X))) (ass)))
(sep-me (list 'IN 'Q MB-SEP))          ; lands (IN Q (MATRIX X)) and SIZE(Q) = [m,n]
;; Q is a tuple, so LENGTH(Q) is a natural
(dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership '(IN Q (MATRIX X))))))
(fact 'length-in-nn '(TUPLES X) 'Q)
;; m IS that length
(fact 'size-unfold 'Q)
(fact 'nth1-pair '(LENGTH Q) '(LENGTH (NTH 1 Q)))
(fact 'nth1-pair 'm 'n)
(have! '(= (LENGTH Q) m)
  (lambda ()
    (subst '(== (LENGTH Q) (NTH 1 (LIST (LENGTH Q) (LENGTH (NTH 1 Q))))))
    (subst '(== (LIST (LENGTH Q) (LENGTH (NTH 1 Q))) (SIZE Q)))
    (subst '(= (SIZE Q) (LIST m n)))
    (subst '(== (NTH 1 (LIST m n)) m))
    (rfl)))
(subst '(= m (LENGTH Q)))
(ass)

(if (proof-done? *ps*)
    (begin (qed 'mat-rows-in-nn)
           (topic! 'mat-rows-in-nn 'plumbing))
    (begin
      (display "\n*** mat-basics: mat-rows-in-nn did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (sequent-node-assertion l)))
                  (newline))
                (proof-leaves))
      (error "mat-basics: unfinished")))
