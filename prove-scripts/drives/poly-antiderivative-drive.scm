;;; poly-antiderivative-drive.scm -- THE LEAF LEFT FOR THE USER (2026-08-23),
;;; from the rung-1 session that proved `deriv-polynomial'.
;;;
;;; This is calculus.pdf EXAMPLE 4.7 -- "any polynomial function is
;;; antiderivable", with the antiderivative written out -- and it is the rung
;;; the integration arc actually consumes:
;;;
;;;   cf in FUN(NN,RR), n in NN, pt in RR  =>
;;;     IS-DIFF-AT( lambda x in RR. SUM_{k<succ n} (recip(succ k) . a_k) x^(succ k),
;;;                 pt,
;;;                 SUM_{k<succ n} a_k pt^k )
;;;
;;; i.e. d/dx sum_{k=0}^{n} a_k x^(k+1)/(k+1) = sum_{k=0}^{n} a_k x^k.
;;;
;;; Run:   ./prover -b -i prove-scripts/drives/poly-antiderivative-drive.scm
;;;
;;; EVERYTHING STRUCTURAL IS ALREADY PROVEN, and the driver is
;;; theorem-library/deriv-polynomial.scm's, line for line, with ONE arithmetic
;;; step changed:
;;;
;;;   poly-lam-in-fun         (deriv-polynomial.scm)  the antiderivative is a
;;;                           function RR -> RR -- but note it is stated for the
;;;                           shape SUM_k b_k x^k, and the antiderivative's
;;;                           summand is b_k x^(succ k).  Either restate it over
;;;                           the shifted shape or (cheaper) note that
;;;                           b_k x^(succ k) is the k-th term of a sequence in
;;;                           FUN(NN,RR) all the same, and re-run
;;;                           poly-term-lam-in-fun's three lines on it.
;;;   deriv-coef-monomial     (deriv-polynomial.scm)  d/dx (c x^(succ k)) =
;;;                           (succ k) c x^k -- with c := recip(succ k) . a_k
;;;   deriv-sum               (deriv-sum-product.scm)
;;;   diff-transfer-ptwise-eq (diff-transfer.scm)
;;;   series-partial-sum-succ / -zero  (comparison-test-proof.scm)
;;;
;;; THE ONE STEP THAT IS NOT deriv-polynomial's, and the reason this is worth
;;; DRIVING rather than typing.  The step's value obligation is
;;;
;;;     (succ k) . ( recip(succ k) . a_k )  =  a_k
;;;
;;; and `crs' will not do it: `crs' decides commutative-RING identities and
;;; `recip' is not a ring operation (dyadic-weights.scm makes the same point --
;;; it declines on `recip' and crashes on `power').  The step is
;;; `rr-recip-inverse' (number-systems.scm:395), whose antecedent is
;;;
;;;     NOT (= (succ k) 0)      -- as a REAL number
;;;
;;; and THAT is the leaf worth measuring.  What the tree has is
;;; `nn-one-le-succ' (structure-library/order-lemmas.scm:345), 1 <= succ n on
;;; NN -- an ASSERTED support, `warrant! 'well-known'.  So the cheap route
;;; (nn-one-le-succ + nn-in-rr + rr-one-pos + neq-sym) bills {nn-one-le-succ},
;;; and this theorem would be the first rung of the integration arc that is NOT
;;; `modulo 0'.
;;;
;;; So the question the drive is really asking is: does the tree state anywhere
;;; that a SUCCESSOR IS NONZERO, provably?  If the answer is no, the finding is
;;; the missing fact, not the missing theorem -- `nn-succ-nonzero' (or the
;;; positivity form 0 < succ n) is the sort of Peano read-off that belongs
;;; beside nn-zero-in / nn-succ-closed and is currently only reachable through
;;; an asserted ORDER support.  Check `(debt-of ...)' on whatever you cite BEFORE
;;; committing to it.
;;;
;;; ANSWERED 2026-08-24.  Yes: `nn-succ-nonzero' (theorem-library/
;;; nn-parity-proof.scm:158) states exactly `NOT (= (succ n) 0)' and it now
;;; bills `proven modulo 0'.  It always WAS a theorem; what changed is its two
;;; leaves -- nn-zero-le and nn-le-imp-neq-succ -- which are PROVEN in
;;; theorem-library/nn-order-ord.scm from the ordinal shelf.  There is no
;;; separate "as a real" form to reach for: NN <= ZZ <= QQ <= RR are genuine
;;; inclusions of sets, so that formula is already the antecedent
;;; `rr-recip-inverse' asks for.  `nn-one-le-succ' is a theorem too now, so the
;;; route this header called "cheap" costs nothing either -- but it is the
;;; longer one.
;;;
;;; AND THE OBSTACLE IS GONE.  The paragraph that stood here said Example 4.7
;;; would NOT reach `modulo 0', because `deriv-coef-monomial' -- which it must
;;; cite -- billed `modulo {nn-add-succ}' [trust: reference] through
;;; `nn-succ-plus-one'.  That was written before the same afternoon's decision:
;;; `nn-add-succ' (a + succ b = succ(a + b), structure-library/nn-arith.scm), the
;;; recursion equation DEFINING + on NN, is stamped `definitional' as of
;;; 2026-08-24, so it contributes {} to every bill.  It was named in 54 bills and
;;; was the SOLE unwarranted leaf of 19 of them -- deriv-polynomial,
;;; deriv-coef-monomial and deriv-power among them; all three now bill
;;; `modulo 0', and so does everything this drive cites.
;;;
;;; DRIVEN AND CLOSED, 2026-08-24.  The proof is
;;; theorem-library/poly-antiderivative.scm (in load.scm directly after
;;; deriv-polynomial), and it reports
;;;
;;;   qed poly-antiderivative: proven modulo 0  [oracles: crs arith ineq]
;;;
;;; What it had to add beside the headline, and why -- none of it is analysis:
;;;
;;;   anti-term-in-rr       the summand (recip(succ k) a_k) x^(succ k) is real.
;;;                         The ONE place the reciprocal's two side conditions
;;;                         are paid: (IN (succ k) RR) by nn-in-rr, and
;;;                         NOT (succ k = 0) by nn-succ-nonzero verbatim.
;;;   anti-term-lam-in-fun  that sequence is in FUN(NN,RR)
;;;   anti-lam-in-fun       the antiderivative is in FUN(RR,RR).  The header's
;;;                         guess above was right: `poly-lam-in-fun' does NOT
;;;                         cover it -- it is stated for SUM_k b_k x^k and the
;;;                         antiderivative's summand is b_k x^(succ k) -- and
;;;                         re-running poly-term-lam-in-fun's three lines on the
;;;                         shifted shape was indeed the cheap route.
;;;   rr-zero-plus          0 + t = t on RR, over a VARIABLE.  `crs' proves this
;;;                         in one move but only where it can certify its
;;;                         generators from context typings, and at the
;;;                         empty-sum end of a partial sum the term is a triple
;;;                         product whose factors are typed nowhere.
;;;   recip-succ-cancel     the cancellation itself, over variables:
;;;                         c v = ((succ m) . (recip(succ m) . c)) . v.
;;;                         ORIENTED that way round on purpose -- `subst'
;;;                         rewrites the GOAL, so the left-hand side has to be
;;;                         the shape the goal carries.
;;;   deriv-anti-monomial   d/dx ((recip(succ m) c) x^(succ m)) = c x^m, i.e.
;;;                         deriv-coef-monomial plus that one `subst'.
;;;
;;; The induction is then deriv-polynomial's, and shorter, exactly as predicted
;;; below: both sums split at succ n.
;;;
;;; The second thing to watch, and it is cheap to get wrong: the derivative slot
;;; here is the ORIGINAL polynomial, SUM_{k<succ n} a_k pt^k -- so its top term
;;; splits off at `succ n' while the ANTIDERIVATIVE's top term also splits off
;;; at `succ n'.  Both `series-partial-sum-succ' citations are at the SAME index
;;; (unlike deriv-polynomial, where the polynomial splits at succ(succ n) and
;;; the derivative sum at succ n).  That makes this induction slightly SHORTER
;;; than the one it copies.

;;; ---- the same file-local helpers deriv-polynomial.scm uses --------------
(define (pa-di-var!) (cadr (car (dk-landed* (lambda () (di))))))
(define (pa-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 10) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;; the two shapes: the ANTIDERIVATIVE's term sequence and the POLYNOMIAL's
(define (pa-anti-term cf x)                 ; k |-> (recip(succ k) a_k) x^(succ k)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list 'recip '(succ k)) (list cf 'k))
                 (list 'power x '(succ k)))))
(define (pa-poly-term cf x)                 ; k |-> a_k x^k
  (list 'VNB-LAMBDA 'k 'NN (list '* (list cf 'k) (list 'power x 'k))))
(define (pa-anti cf m)
  (list 'VNB-LAMBDA 'x 'RR (list 'SERIES-PARTIAL-SUM (pa-anti-term cf 'x) m)))

;;; ---- the goal ----------------------------------------------------------
;;; The induction variable is OUTERMOST: `ni' tests the goal's SHAPE literally,
;;; and one greedy `di' would take cf and pt with it, after which the induction
;;; is gone and there is no undo.
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
    (FORALL cf (IMPLIES (IN cf (FUN NN RR))
      (FORALL pt (IMPLIES (IN pt RR)
        (IS-DIFF-AT
          (VNB-LAMBDA x RR
            (SERIES-PARTIAL-SUM
              (VNB-LAMBDA k NN (* (* (recip (succ k)) (cf k)) (power x (succ k))))
              (succ n)))
          pt
          (SERIES-PARTIAL-SUM
            (VNB-LAMBDA k NN (* (cf k) (power pt k))) (succ n)))))))))))

(display "\n;; goal:\n  ")
(display (expression->string (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(newline)
(display "\n;; the arithmetic obligation the step will owe, and the whole point:\n")
(display ";;   (succ k) * (recip(succ k) * a_k) = a_k     -- rr-recip-inverse,\n")
(display ";;   whose antecedent is  NOT (= (succ k) 0)  in RR.\n")
(display ";; what the tree offers for it today (name, provenance, bill):\n")
(for-each (lambda (nm)
            (display ";;   ") (display nm)
            (display "  provenance: ") (display (provenance-of nm))
            (display "  bill: ") (write (debt-of nm))
            (newline))
          '(nn-one-le-succ nn-in-rr rr-recip-inverse rr-zero-lt-one))
(display "\n;; DONE 2026-08-24 -- theorem-library/poly-antiderivative.scm, modulo 0.\n")
(display ";; The route: (use-induction); base and step both close by\n")
(display ";;   deriv-anti-monomial (= deriv-coef-monomial at c := recip(succ k) * a_k,\n")
(display ";;   plus recip-succ-cancel), deriv-sum over the induction hypothesis, and\n")
(display ";;   diff-transfer-ptwise-eq onto the next partial sum.\n")
(display ";; This state is left OPEN on purpose: it is the sandbox for re-driving it.\n")
