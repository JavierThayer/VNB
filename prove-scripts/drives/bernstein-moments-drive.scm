;;; DONE, 2026-08-24.  Everything below was the ROUTE, and it held: the weighted
;;; sum-expansion is `series-partial-sum-weighted-expansion'
;;; (theorem-library/series-linearity.scm) and the four identities are in
;;; theorem-library/bernstein-moments.scm.  The prediction that mattered was
;;; the negative one -- the weighted expansion never splits on the index k, so
;;; the ZZ-discreteness gap that blocks the textbook absorption identity
;;; k C(n,k) = n C(n-1,k-1) was never reached, and that identity was NOT added.
;;; Two departures from the plan below, both simplifications:
;;;   * the expansion is proved at SERIES-PARTIAL-SUM on the RR surface, not at
;;;     the ring SUM, so `crs' sees every step as ordinary real arithmetic;
;;;   * the doubling in the second moment is an ADDITION of the first moment to
;;;     itself, not a scalar multiple, which keeps the numeral 2 out entirely.
;;; The next rung is prove-scripts/drives/bernstein-density-drive.scm.
;;; -------------------------------------------------------------------------

;;; bernstein-moments-drive.scm -- IDENTITY (76), the other half of
;;; Proposition 5.4 of docs/calculus.pdf, left for the user to drive (2026-08-24).
;;;
;;;     (1/n) sum_{l=0}^{n} (l - n x)^2 B_{l,n}(x)  <=  1        (76)
;;;
;;; Identity (75) -- sum_l B_{l,n}(x) = 1 -- IS PROVEN, in
;;; theorem-library/bernstein-basis.scm.  It did fall out of `binomial-theorem'
;;; by citation, with no induction of its own -- but only after two bridges that
;;; were NOT in the tree: ONE^n = ONE in a commutative ring, and
;;; SERIES-PARTIAL-SUM = the ring SUM over RR's ring view.  (76) is the half with
;;; content.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/bernstein-moments-drive.scm
;;;
;;; -------------------------------------------------------------------------
;;; WHAT IS ALREADY THERE
;;; -------------------------------------------------------------------------
;;;   BERNSTEIN-BASIS(n,x)              = COMB-KK(RR's ring view, x, 1-x, n)
;;;   bernstein-basis-unfold            modulo 0   (so mac-h works on it)
;;;   bernstein-basis-in-fun            in FUN(ZZ,RR)
;;;   bernstein-partition               identity (75)
;;;   series-partial-sum-is-ring-sum    modulo 0 -- the SURFACE bridge
;;;   binomial-sum-value                SUM(...) = RING-POWER(...)
;;;   comb-kk-zero / comb-kk-succ       the Pascal recursion (definitional)
;;;   comb-kk-null / comb-kk-above      the two vanishing laws
;;;   sum-expansion                     multiply-and-shift (binomial-proof.scm)
;;;
;;; -------------------------------------------------------------------------
;;; THE ROUTE -- COMBINATORIAL, NOT THE NOTES' DIFFERENTIATION TRICK
;;; -------------------------------------------------------------------------
;;; Lemma 5.5 of the notes gets (78) and (79) by differentiating the binomial
;;; identity (81) twice in x.  DO NOT DO THAT HERE.  It would state the Bernstein
;;; identities in whatever polynomial-FUNCTION representation rung 1
;;; (deriv-polynomial.scm) uses, and couple this rung to that one; the
;;; combinatorial route stays inside the SUM/COMB-KK algebra that already exists
;;; and never mentions a polynomial function at all.  Only the final uniform
;;; estimate needs functions.
;;;
;;; THE ONE MECHANISM THE RUNG WANTS is a WEIGHTED sum-expansion.  binomial-proof's
;;; `sum-expansion' is its weight-1 case:
;;;
;;;   sum-expansion   SUM(R, k |-> x g(k-1) + y g(k), succ N)
;;;                     = (x+y) SUM(R,g,N) + x g(-1) + y g(N)
;;;
;;;   WANTED          SUM(R, k |-> w(k) . (x g(k-1) + y g(k)), succ N)
;;;                     =  x . ( w(0) g(-1) + SUM(R, j |-> w(succ j) g(j), N) )
;;;                     +  y . ( SUM(R, k |-> w(k) g(k), N) + w(N) g(N) )
;;;
;;; and its proof is sum-expansion's induction on N with `w' carried along --
;;; the shift is again carried by the successor recurrence of SUM, no reindex
;;; bijection and no monus.  Check the weight-1 instance against sum-expansion
;;; before going further: w = k |-> ONE(R) collapses the right-hand side to
;;; exactly sum-expansion's, and if it does not, the statement is wrong.
;;;
;;; With it, write M_w(m) = SUM(R, k |-> w(k) COMB-KK(R,x,y,m)(k), succ m).  Put
;;; g := COMB-KK(R,x,y,m), so COMB-KK(R,x,y,succ m) = k |-> x g(k-1) + y g(k) is
;;; comb-kk-succ, and N := succ m.  The two boundary terms die: g(-1) = 0 by
;;; `comb-kk-null' and g(succ m) = 0 by `comb-kk-above'.  What is left is
;;;
;;;   M_w(succ m)  =  x . SUM(j |-> w(succ j) g(j), succ m)  +  y . M_w(m)
;;;
;;; and now the three moments are three choices of w, at x + y = 1:
;;;
;;;   w = 1            M_0(succ m) = x M_0(m) + y M_0(m) = M_0(m)      -> (77)/(75)
;;;   w = k            w(succ j) = j + 1, so the first sum is M_1(m) + M_0(m):
;;;                    M_1(succ m) = x (M_1(m) + 1) + y M_1(m) = M_1(m) + x
;;;                    with M_1(0) = 0, hence M_1(n) = n x               -> (78)
;;;   w = k(k-1)       w(succ j) = (j+1) j, so the first sum is
;;;                    M_2(m) + 2 M_1(m):
;;;                    M_2(succ m) = x (M_2(m) + 2 m x) + y M_2(m)
;;;                                = M_2(m) + 2 m x^2,
;;;                    with M_2(0) = 0, hence M_2(n) = n(n-1) x^2        -> (79)
;;;
;;; and (80) is then pure algebra:
;;;   sum (l - nx)^2 B = M_2 + M_1 - 2nx M_1 + n^2x^2 M_0 = n(n-1)x^2 + nx
;;;                                                        - 2n^2x^2 + n^2x^2
;;;                    = nx(1-x),
;;; which `crs' will do in one step once the three moments are in the context.
;;; (76) is (80) divided by n, plus x(1-x) <= 1 on [0,1].
;;;
;;; -------------------------------------------------------------------------
;;; THE PIECE OF INFRASTRUCTURE THAT IS MISSING, AND WHERE TO PUT IT
;;; -------------------------------------------------------------------------
;;; Every step above splits a sum of a pointwise SUM into two sums:
;;;
;;;     SUM(j |-> (j+1) g(j), m)  =  SUM(j |-> j g(j), m)  +  SUM(g, m)
;;;
;;; and the tree has NO additivity law for `SUM' at all.  What it has is
;;; `sum-left-scalar' (structure-library/sequences.scm:192) -- and that is a bare
;;; `theory-add-axiom!' with no `warrant!', i.e. `trust: none' for anything that
;;; cites it.  DO NOT CITE IT.  Prove the two laws instead, and prove them at
;;; SERIES-PARTIAL-SUM rather than at SUM:
;;;
;;;     series-partial-sum-add    SPS(k |-> f(k) + g(k), n) = SPS(f,n) + SPS(g,n)
;;;     series-partial-sum-scale  SPS(k |-> c * f(k), n)    = c * SPS(f,n)
;;;
;;; Each is a three-line NN induction whose step is `series-partial-sum-succ'
;;; (comparison-test-proof.scm) followed by `crs' -- ordinary real arithmetic,
;;; because `series-partial-sum-is-ring-sum' put the whole Bernstein algebra on
;;; the RR surface.  Both should come out `modulo 0', and they are reusable by
;;; the entire series lane, which is the argument for proving them rather than
;;; leaning on the SUM axiom.  Watch the `lam-b' trap: type the index BEFORE
;;; reducing the summand lambda, never after (CLAUDE.md, "lam-b needs the
;;; argument TYPED, and needs it BEFORE the reduction").
;;;
;;; -------------------------------------------------------------------------
;;; THE TRAP THAT MADE ME NOT DO THIS THE OBVIOUS WAY
;;; -------------------------------------------------------------------------
;;; The obvious formulation is the POINTWISE absorption identity
;;;
;;;     k C(n,k) = n C(n-1,k-1),   i.e.
;;;     k . COMB-KK(R,x,y,succ m)(k) = succ(m) . x . COMB-KK(R,x,y,m)(k-1)
;;;
;;; by induction on m.  It is TRUE and it is the textbook route, and its BASE
;;; CASE is where the tree runs out: `comb-kk-zero' is
;;;
;;;     COMB-KK(R,x,y,0) = VNB-LAMBDA k NN. IF k = 0 THEN ONE(R) ELSE ZERO(R)
;;;
;;; so the base case is a four-way case split on a ZZ index -- k < 0, k = 0,
;;; k = 1, k > 1 -- and the middle two are separated from the outer two only by
;;; DISCRETENESS of ZZ (there is no integer strictly between 0 and 1).  The tree
;;; states no such fact: `nn-order` is the standing gap
;;; (project_unproven_basics_backlog), and `ineq' is a REAL oracle, so it cannot
;;; supply it either.  The weighted sum-expansion above never splits on k at
;;; all -- it only ever peels the top index with `sum-succ' -- which is why it is
;;; the right mechanism and not merely a tidier one.
;;;
;;; -------------------------------------------------------------------------
;;; THE LEAF
;;; -------------------------------------------------------------------------
;;; What follows states the weighted sum-expansion and opens it.  The induction
;;; is `ni' on N; the base peels one `sum-succ' onto `sum-zero'; the step is
;;; binomial-proof.scm's `sum-expansion' driver line for line with `w' threaded
;;; through.  Compare with that driver side by side -- it is 15 lines and this
;;; is the same 15.

;;; The statement is over an ARBITRARY commutative ring, as `sum-expansion' and
;;; `binomial-theorem' are; RR's ring view enters only when the moments are
;;; instantiated.  Keeping the expansion generic is what makes it reusable.

;;; the weighted summand,  k |-> w(k) . ( x g(k-1) + y g(k) )
(define bm-summand
  '(VNB-LAMBDA k NN ((MUL R) (w k) ((ADD R) ((MUL R) x (g (- k 1)))
                                            ((MUL R) y (g k))))))

;;; the two shifted sums on the right
(define bm-shifted '(SUM R (VNB-LAMBDA j NN ((MUL R) (w (succ j)) (g j))) N))
(define bm-plain   '(SUM R (VNB-LAMBDA k NN ((MUL R) (w k) (g k))) N))

(define bm-rhs
  (list '(ADD R)
        (list '(MUL R) 'x (list '(ADD R) '((MUL R) (w 0) (g (- 0 1))) bm-shifted))
        (list '(MUL R) 'y (list '(ADD R) bm-plain '((MUL R) (w N) (g N))))))

(define bm-stmt
  (list 'FORALL 'N
    (list 'IMPLIES '(IN N NN)
      (forall-guarded '(R x y g w)
        (list '(IS-COMMUTATIVE-RING R) '(IN x (CARR R)) '(IN y (CARR R))
              '(IN g (FUN ZZ (CARR R))) '(IN w (FUN ZZ (CARR R))))
        (list '= (list 'SUM 'R bm-summand '(succ N)) bm-rhs)))))

(display "\n;;; ---- weighted sum-expansion: the statement ----\n")
(display (expression->string bm-stmt))
(newline)
(display "\n;;; Sanity check FIRST: instantiate w := k |-> ONE(R) and confirm the\n")
(display ";;; right-hand side collapses to sum-expansion's.  If it does not, the\n")
(display ";;; statement above is wrong and no amount of driving will fix it.\n\n")

(sp (make-wff bm-stmt))
(ni)
(display "\n;;; Two leaves: the base (N = 0) and the step.  binomial-proof.scm's\n")
(display ";;; `sum-expansion' block is the template -- (macm 'sum-succ), (mac 'sum-zero),\n")
(display ";;; (lam-b), (crs) for the base; for the step, land the typings, (macm 'sum-succ),\n")
(display ";;; instantiate the IH, (subst) it, (lam-b), (macm 'bt-succ-minus-1), (crs).\n")
(display ";;; (what-now) on either leaf.\n")
