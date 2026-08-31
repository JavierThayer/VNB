;;; deriv-polynomial.scm -- rung 1 of the integration arc: the DERIVATIVE OF A
;;; POLYNOMIAL FUNCTION, in the coefficient-lambda representation.
;;;
;;;   cf in FUN(NN,RR), n in NN, pt in RR  =>
;;;     IS-DIFF-AT( lambda x in RR. SUM_{k<succ n} cf(k) x^k,
;;;                 pt,
;;;                 SUM_{j<n} (succ j) cf(succ j) pt^j )
;;;
;;; i.e. d/dx sum_{k=0}^{n} a_k x^k = sum_{j=0}^{n-1} (j+1) a_{j+1} x^j, with
;;; every exponent and every index in NN.
;;;
;;; THE REPRESENTATION is the coefficient-lambda, which is already load-bearing
;;; in the tree: TAYLOR-POLY(f,a,n,x) (theorem-library/taylor-proof.scm:19) is
;;; exactly SERIES-PARTIAL-SUM(VNB-LAMBDA k NN ..., succ n), and taylor-lagrange
;;; is proven over it.  Nothing here touches the formal polynomial ring POLY or
;;; builds an evaluation homomorphism: that bridge is a separate, later piece of
;;; work, and the analysis must not wait on it.
;;;
;;; WHY THE DERIVATIVE IS INDEXED BY `succ j' AND NOT BY `j - 1'.  Same reason
;;; deriv-power is stated with `succ n' (see its header): k-1 at k = 0 leaves NN,
;;; and `power' at a negative exponent is governed by `power-neg', a CONDITIONAL
;;; equation needing x /= 0.  Reindexing the derivative sum by j = k-1 keeps
;;; every exponent in NN and makes the n = 0 case read "the derivative of the
;;; constant a_0 is the empty sum", which is exactly `deriv-const'.
;;;
;;; THE INDUCTION VARIABLE IS OUTERMOST.  `ni' tests the goal's SHAPE literally
;;; -- (FORALL n (IMPLIES (IN n NN) body)) at the top -- so cf and pt are
;;; quantified INSIDE n, and there is no undo if the leading `di' takes them.
;;;
;;; THE STEP is series-partial-sum-succ on BOTH sides -- on the polynomial, to
;;; split off a_{n+1} x^{n+1}, and on the derivative, to split off the
;;; corresponding (n+1) a_{n+1} x^n -- then `deriv-sum' over the induction
;;; hypothesis and `deriv-coef-monomial'.  As in deriv-power, the transfer
;;; `diff-transfer-ptwise-eq' is what makes the induction WRITABLE at all:
;;; `deriv-sum' concludes about the LITERAL lambda x. P(x) + C(x) it builds, not
;;; about the partial sum of the next rung, so rung n+1 cannot consume rung n's
;;; conclusion without carrying the conclusion across a pointwise equality.
;;;
;;; WHAT THIS FILE ADDS BESIDE THE HEADLINE, and why each was needed:
;;;   poly-term-lam-in-fun  k |-> cf(k) x^k is in FUN(NN,RR)
;;;   poly-lam-in-fun       x |-> SUM_{k<n} cf(k) x^k is in FUN(RR,RR)
;;;                         -- the transfer's (IN f (FUN RR RR)) hypothesis
;;;   poly-step-identity    (c u) v = u (c v) over RR variables -- `crs' sees
;;;                         neither `succ' nor `power', so the rearrangement is
;;;                         done once, over variables (deriv-power's
;;;                         pw-step-identity is the same device)
;;;   deriv-scalar-mult     THE CONSTANT-MULTIPLE RULE, which the tree did not
;;;                         have.  Derived from deriv-product against the
;;;                         constant lambda (deriv-const) and then reduced with
;;;                         `lam-b-h' -- NOT with the transfer: beta on the
;;;                         ASSUMPTION turns the product rule's literal lambda
;;;                         into the goal's own, so no transfer and no FUN
;;;                         typing are needed.  gmvt-aux-diff's warrant text
;;;                         already names "deriv-sum/scalar-mult" as its
;;;                         justification; this is that rule, proved.
;;;   deriv-coef-monomial   d/dx (c x^(succ m)) = (succ m) c x^m -- the scalar
;;;                         rule applied to deriv-power, `lam-b-h' again.
;;;
;;; SO THE TRANSFER IS NEEDED IN EXACTLY ONE PLACE, and it is worth saying which:
;;; the INDUCTION.  `lam-b-h' closes a gap whose two sides are beta-equal; the
;;; induction's gap is not -- SUM_{k<succ(succ n)} a_k x^k and
;;; (SUM_{k<succ n} a_k x^k) + a_{n+1} x^(n+1) are equal by
;;; series-partial-sum-succ, a THEOREM, and no reduction gets from one to the
;;; other.  That is the division of labour: beta for the redexes a citation
;;; leaves behind, `diff-transfer-ptwise-eq' for an equality that has content.
;;;
;;; Needs differentiation (IS-DIFF-AT, deriv-const), deriv-sum-product
;;; (deriv-sum, deriv-product), diff-transfer (diff-transfer-ptwise-eq),
;;; deriv-power (deriv-power), dyadic-weights (power-closed-at),
;;; comparison-test-proof (series-partial-sum-zero/-succ/-in-rr),
;;; fun-apply-type-proof (fun-apply-type-c), nn-order-basics (nn-in-rr) and
;;; driver-kit (use-induction, have!, dk-*).

;;; ---- file-local driver helpers (the `dpl-' prefix; never named like a
;;; tactic, and every assumption selected by CONTENT, not by position) ------

;; di, returning the eigenvariable of the guard it landed
(define (dpl-di-var!) (cadr (car (dk-landed* (lambda () (di))))))

;; lam-b the goal to a fixpoint; the block lambdas nest two deep, and every
;; argument reduced here is already typed (in RR or in NN) before this runs.
(define (dpl-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 10) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;; split every conjunctive / existential assumption, skolemizing the FORSOMEs
(define (dpl-split-ands!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))

;; read a conjunct of an IS-DIFF-AT hypothesis WITHOUT destroying it: `mac-h'
;; REPLACES the assumption it unfolds, so the unfold happens on a have! side
;; branch and the main branch keeps IS-DIFF-AT intact for the next citation.
(define (dpl-proj! hyp claim)
  (have! claim (lambda () (mac-h 'IS-DIFF-AT hyp) (dpl-split-ands!) (ass))))

;; the three shapes this file builds over and over
(define (dpl-term cf x)                     ; k |-> cf(k) x^k
  (list 'VNB-LAMBDA 'k 'NN (list '* (list cf 'k) (list 'power x 'k))))
(define (dpl-poly cf m)                     ; x |-> SUM_{k<m} cf(k) x^k
  (list 'VNB-LAMBDA 'x 'RR (list 'SERIES-PARTIAL-SUM (dpl-term cf 'x) m)))
(define (dpl-dseq cf pt)                    ; j |-> (succ j) cf(succ j) pt^j
  (list 'VNB-LAMBDA 'j 'NN
        (list '* (list '* '(succ j) (list cf '(succ j))) (list 'power pt 'j))))

;; (IN (* u v) RR) -- rr-mul-closed has an AND antecedent, which `fact' will
;; not split, so the conjunction goes in first.
(define (dpl-mul! u v)
  (have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

;;; =====================================================================
;;; (1) the term sequence k |-> cf(k) x^k is a function NN -> RR.
;;; `lam-t' opens TWO leaves -- the pointwise typing and the SETHOOD of the
;;; domain -- and a driver expecting one leaves the other open until `qed'.
;;; =====================================================================

(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL x (IMPLIES (IN x RR)
     (IN (VNB-LAMBDA k NN (* (cf k) (power x k))) (FUN NN RR))))))))
(dk-peel-to! 'IN)
(define ptl-bod (cadddr (cadr (dk-goal))))            ; (* (cf k) (power x k))
(define ptl-cf  (car (cadr ptl-bod)))
(define ptl-x   (cadr (caddr ptl-bod)))
(dk-lam-t!)
(let ((z (dpl-di-var!)))
  (fact 'fun-apply-type-c ptl-cf 'NN 'RR z)
  (fact 'power-closed-at z ptl-x)
  (dpl-mul! (list ptl-cf z) (list 'power ptl-x z))
  (ass))
(qed 'poly-term-lam-in-fun)
(topic! 'poly-term-lam-in-fun 'analysis)
(alias! 'poly-term-lam-in-fun
        "the term sequence k |-> a_k x^k of a polynomial is a function NN -> RR")

;;; ... and the DERIVATIVE sequence j |-> (j+1) a_{j+1} pt^j, the same way.
;;; Added 2026-08-29: `series-partial-sum-succ' is now guarded on its two
;;; arguments being real, and the step below peels the top term off exactly this
;;; sum, so its realness has to be available.  Every other sequence in this file
;;; already had such a lemma; this one did not, because the unguarded recurrence
;;; never asked.
(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL pt (IMPLIES (IN pt RR)
     (IN (VNB-LAMBDA j NN (* (* (succ j) (cf (succ j))) (power pt j)))
         (FUN NN RR))))))))
(dk-peel-to! 'IN)
(define pdl-bod (cadddr (cadr (dk-goal))))     ; (* (* (succ j) (cf (succ j))) (power pt j))
(define pdl-cf  (car (caddr (cadr pdl-bod))))
(define pdl-pt  (cadr (caddr pdl-bod)))
(dk-lam-t!)
(let ((z (dpl-di-var!)))
  (fact 'nn-succ-closed z)
  (fact 'nn-in-rr (list 'succ z))
  (fact 'fun-apply-type-c pdl-cf 'NN 'RR (list 'succ z))
  (fact 'power-closed-at z pdl-pt)
  (dpl-mul! (list 'succ z) (list pdl-cf (list 'succ z)))
  (dpl-mul! (list '* (list 'succ z) (list pdl-cf (list 'succ z)))
            (list 'power pdl-pt z))
  (ass))
(qed 'poly-dseq-lam-in-fun)
(topic! 'poly-dseq-lam-in-fun 'analysis)
(alias! 'poly-dseq-lam-in-fun
        "the derivative sequence j |-> (j+1) a_{j+1} x^j is a function NN -> RR")

;;; =====================================================================
;;; (2) the polynomial x |-> SUM_{k<n} cf(k) x^k is a function RR -> RR.
;;; This is what `diff-transfer-ptwise-eq' asks for and what IS-DIFF-AT's
;;; first conjunct is: pointwise agreement with a function does NOT establish
;;; it (see diff-transfer.scm's header).
;;; =====================================================================

(sp (make-wff '(FORALL cf (IMPLIES (IN cf (FUN NN RR))
   (FORALL n (IMPLIES (IN n NN)
     (IN (VNB-LAMBDA x RR (SERIES-PARTIAL-SUM (VNB-LAMBDA k NN (* (cf k) (power x k))) n))
         (FUN RR RR))))))))
(dk-peel-to! 'IN)
(define plf-bod (cadddr (cadr (dk-goal))))            ; (SERIES-PARTIAL-SUM T n)
(define plf-n   (caddr plf-bod))
(define plf-cf  (car (cadr (cadddr (cadr plf-bod)))))
(dk-lam-t!)
(let ((z (dpl-di-var!)))
  (fact 'poly-term-lam-in-fun plf-cf z)
  (fact 'series-partial-sum-in-rr plf-n (dpl-term plf-cf z))
  (ass))
(qed 'poly-lam-in-fun)
(topic! 'poly-lam-in-fun 'analysis)
(alias! 'poly-lam-in-fun "a polynomial function is a function RR -> RR")

;;; =====================================================================
;;; (3) the generic RR rearrangement, over VARIABLES.  `crs' decides
;;; commutative-ring identities but sees neither `succ' nor `power' (the same
;;; point deriv-power's pw-step-identity makes), so the one rearrangement this
;;; file needs is proved once here and INSTANTIATED at succ/power terms.
;;; =====================================================================

(sp (make-wff (forall-guarded '(c u v) '((IN c RR) (IN u RR) (IN v RR))
      '(= (* (* c u) v) (* u (* c v))))))
(dk-peel-to! '=)
(crs)
(qed 'poly-step-identity)
(topic! 'poly-step-identity 'inequalities)
(alias! 'poly-step-identity "(cu)v = u(cv), the polynomial rule's coefficient shuffle")

;;; =====================================================================
;;; (4) the CONSTANT-MULTIPLE rule.  The tree did not have it: `deriv-neg'
;;; (differentiation.scm) is the c = -1 case, asserted, and gmvt-aux-diff's
;;; warrant text names "deriv-sum/scalar-mult" as its justification without
;;; either rule existing.
;;;
;;; It is NOT an epsilon argument and not a second copy of the product rule's
;;; driver: it is `deriv-product' against the CONSTANT lambda K = lambda x. c,
;;; whose derivative is 0 (`deriv-const').  That gives
;;;
;;;    IS-DIFF-AT(lambda x in RR. K(x) f(x),  pt,  0.f(pt) + K(pt).dl)
;;;
;;; -- a lambda with an unreduced redex in its BODY and a value with another.
;;;
;;; AND THE WAY TO CLOSE THAT GAP IS `lam-b-h', NOT A TRANSFER.  Reducing the
;;; landed ASSUMPTION in place turns its lambda into
;;; (VNB-LAMBDA x RR (* c (f x))) -- LITERALLY the goal's lambda, same binder --
;;; and its value into 0.f(pt) + c.dl, so `diff-transfer-ptwise-eq' is not
;;; needed here at all and neither is a FUN(RR,RR) typing for the goal lambda.
;;; Both redexes are LICENSED (the body's by the enclosing VNB-LAMBDA's domain
;;; RR, the value's by (IN pt RR) in context), so the reduction owes no leaf.
;;; The first version of this proof went the other way -- cut the value
;;; equation, `lam-b' it in the have! lane, `crs' -- and the lane did not close:
;;; the goal-side beta is a different rule with a different focus discipline,
;;; and there is no reason to fight it when the hypothesis-side one lands the
;;; assumption already in the shape the goal wants.
;;;
;;; `mac-h' is DESTRUCTIVE, so the two typings read off the IS-DIFF-AT
;;; hypothesis ((IN pt RR), (IN dl RR)) are read inside `have!' lanes
;;; (dpl-proj!): unfolded in the main branch, the hypothesis would be gone
;;; before `deriv-product' could cite it.
;;; =====================================================================

(sp (make-wff '(FORALL c (IMPLIES (IN c RR)
   (FORALL f (FORALL pt (FORALL dl (IMPLIES (IS-DIFF-AT f pt dl)
     (IS-DIFF-AT (VNB-LAMBDA x RR (* c (f x))) pt (* c dl))))))))))
(dk-peel-to! 'IS-DIFF-AT)

;;; everything read off the GOAL, which names each eigenvariable in its role
(define sm-lam  (cadr (dk-goal)))                   ; lambda x in RR. c f(x)
(define sm-pt   (caddr (dk-goal)))
(define sm-bod  (cadddr sm-lam))                    ; (* c (f x))
(define sm-c    (cadr sm-bod))
(define sm-f    (car (caddr sm-bod)))
(define sm-dl   (caddr (cadddr (dk-goal))))         ; dl  (from (* c dl))
(define sm-hyp  (list 'IS-DIFF-AT sm-f sm-pt sm-dl))

;;; THREE conjuncts, not two, and the third is the one that cost a run.  `crs'
;;; certifies its generators from CONTEXT typings, and (f pt) is one of them --
;;; but `fun-apply-type-c' auto-detaches only the antecedents already in
;;; context, and (IN f (FUN RR RR)) is not: it lives INSIDE the unfolded
;;; IS-DIFF-AT.  Without it the citation lands the IMPLICATION, silently, and
;;; the `crs' four lines below fails on an uncertified generator with a message
;;; about the identity rather than about the missing typing.
(dpl-proj! sm-hyp (list 'IN sm-f '(FUN RR RR)))
(dpl-proj! sm-hyp (list 'IN sm-pt 'RR))
(dpl-proj! sm-hyp (list 'IN sm-dl 'RR))
(fact 'fun-apply-type-c sm-f 'RR 'RR sm-pt)         ; (IN (f pt) RR)

(define sm-k (list 'VNB-LAMBDA 'x 'RR sm-c))        ; K = the constant lambda
(have! (list 'AND (list 'IN sm-c 'RR) (list 'IN sm-pt 'RR)))
(fact 'deriv-const sm-c sm-pt)                      ; IS-DIFF-AT(K, pt, 0)
(have! (list 'AND (list 'IS-DIFF-AT sm-k sm-pt 0) sm-hyp))
;;; `fact' lands its whole instantiation chain, so take the landing no other
;;; landing contains -- the detached conclusion.
(define sm-pf
  (dk-deepest (lambda () (fact 'deriv-product sm-k sm-f sm-pt 0 sm-dl))))
(lam-b-h sm-pf)                                     ; both redexes, in place

;;; what is left is one RR identity between the goal's value and the reduced
;;; assumption's: c.dl = 0.f(pt) + c.dl.
(define sm-val (list '+ (list '* 0 (list sm-f sm-pt)) (list '* sm-c sm-dl)))
(have! (list '= (list '* sm-c sm-dl) sm-val) (lambda () (crs)))
(subst (list '= (list '* sm-c sm-dl) sm-val))
(ass)
(qed 'deriv-scalar-mult)
(topic! 'deriv-scalar-mult 'analysis)
(alias! 'deriv-scalar-mult "the constant-multiple rule: (cf)' = c f'")

;;; =====================================================================
;;; (5) the COEFFICIENT MONOMIAL: d/dx (c x^(succ m)) = (succ m) c x^m.
;;; The scalar rule applied to `deriv-power', closed the same two ways:
;;; `lam-b-h' on the assembled lambda, and poly-step-identity on the value
;;; (over variables, since `crs' sees neither `succ' nor `power').
;;; The value is written (succ m . c) . x^m, not c . (succ m . x^m), so that
;;; the induction step below can consume it with no further arithmetic.
;;; =====================================================================

(sp (make-wff '(FORALL c (IMPLIES (IN c RR)
   (FORALL dg (IMPLIES (IN dg NN)
     (FORALL pt (IMPLIES (IN pt RR)
       (IS-DIFF-AT (VNB-LAMBDA x RR (* c (power x (succ dg)))) pt
                   (* (* (succ dg) c) (power pt dg)))))))))))
(dk-peel-to! 'IS-DIFF-AT)

(define cm-lam (cadr (dk-goal)))
(define cm-pt  (caddr (dk-goal)))
(define cm-bod (cadddr cm-lam))                     ; (* c (power x (succ dg)))
(define cm-c   (cadr cm-bod))
(define cm-dg  (cadr (caddr (caddr cm-bod))))       ; dg, out of (succ dg)
(define cm-mono (list 'VNB-LAMBDA 'x 'RR (list 'power 'x (list 'succ cm-dg))))
(define cm-pv  (list '* (list 'succ cm-dg) (list 'power cm-pt cm-dg)))
(define cm-val (list '* cm-c cm-pv))

(fact 'nn-succ-closed cm-dg)                        ; (IN (succ dg) NN)
(fact 'nn-in-rr (list 'succ cm-dg))                 ; (IN (succ dg) RR)
(fact 'power-closed-at cm-dg cm-pt)                 ; (IN pt^dg RR)
(fact 'deriv-power cm-dg cm-pt)                     ; the monomial's derivative
(define cm-sf
  (dk-deepest (lambda () (fact 'deriv-scalar-mult cm-c cm-mono cm-pt cm-pv))))
(lam-b-h cm-sf)                                     ; lambda x. c.((lam)(x)) -> c.x^(succ dg)

;;; the value: (succ dg . c) . pt^dg = c . (succ dg . pt^dg), over variables.
(fact 'poly-step-identity (list 'succ cm-dg) cm-c (list 'power cm-pt cm-dg))
(subst (list '= (list '* (list '* (list 'succ cm-dg) cm-c) (list 'power cm-pt cm-dg))
                cm-val))
(ass)
(qed 'deriv-coef-monomial)
(topic! 'deriv-coef-monomial 'analysis)
(alias! 'deriv-coef-monomial "the derivative of c x^(m+1) is (m+1) c x^m")

;;; =====================================================================
;;; (6) THE POLYNOMIAL RULE.
;;; =====================================================================

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL cf (IMPLIES (IN cf (FUN NN RR))
     (FORALL pt (IMPLIES (IN pt RR)
       (IS-DIFF-AT
         (VNB-LAMBDA x RR
           (SERIES-PARTIAL-SUM (VNB-LAMBDA k NN (* (cf k) (power x k))) (succ n)))
         pt
         (SERIES-PARTIAL-SUM
           (VNB-LAMBDA j NN (* (* (succ j) (cf (succ j))) (power pt j))) n))))))))))
(define dp-br (use-induction))

;;; ---- base: n = 0.  SUM_{k<1} a_k x^k is the constant a_0, whose derivative
;;; is `deriv-const'; the derivative sum SUM_{j<0} is the EMPTY sum, which is 0
;;; (series-partial-sum-zero).  So the base case IS deriv-const, carried across
;;; by the transfer -- exactly as deriv-power's base case IS deriv-identity.
(dk-focus! (cdr (assq 'base dp-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define bs-goal (dk-goal))
(define bs-cf   (car (cadr (cadddr (cadr (cadddr (cadr bs-goal)))))))
(define bs-pt   (caddr bs-goal))
(define bs-poly (dpl-poly bs-cf '(succ 0)))
(define bs-const (list 'VNB-LAMBDA 'x 'RR (list bs-cf 0)))

(fact 'nn-zero-in)                                   ; (IN 0 NN)
(fact 'nn-succ-closed 0)                             ; (IN (succ 0) NN)
(fact 'fun-apply-type-c bs-cf 'NN 'RR 0)             ; (IN (cf 0) RR)
(fact 'series-partial-sum-zero (dpl-dseq bs-cf bs-pt))
(subst (list '== (list 'SERIES-PARTIAL-SUM (dpl-dseq bs-cf bs-pt) 0) 0))
(have! (list 'AND (list 'IN (list bs-cf 0) 'RR) (list 'IN bs-pt 'RR)))
(fact 'deriv-const (list bs-cf 0) bs-pt)             ; IS-DIFF-AT(const a_0, pt, 0)
(fact 'poly-lam-in-fun bs-cf '(succ 0))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
          (list '== (list bs-poly 'x_) (list bs-const 'x_))))
  (lambda ()
    (let ((z (dpl-di-var!)))
      (dpl-beta!)                                    ; SUM_{k<succ 0} a_k z^k == a_0
      ;; series-partial-sum-succ is guarded on its two arguments being real
      ;; since 2026-08-29.  poly-term-lam-in-fun (above) types the term sequence
      ;; as a real sequence, which gives both.
      (fact 'poly-term-lam-in-fun bs-cf z)
      (fact 'series-partial-sum-in-rr 0 (dpl-term bs-cf z))
      (fact 'fun-apply-type-c (dpl-term bs-cf z) 'NN 'RR 0)
      (fact 'series-partial-sum-succ (dpl-term bs-cf z) 0)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (dpl-term bs-cf z) '(succ 0))
                       (list '+ (list 'SERIES-PARTIAL-SUM (dpl-term bs-cf z) 0)
                                (list (dpl-term bs-cf z) 0))))
      (fact 'series-partial-sum-zero (dpl-term bs-cf z))
      (subst (list '== (list 'SERIES-PARTIAL-SUM (dpl-term bs-cf z) 0) 0))
      (dpl-beta!)                                    ; == 0 + a_0 z^0
      (fact 'rr-subset-cc z)
      (fact 'power-zero z)
      (subst (list '= (list 'power z 0) 1))
      (have! (list '= (list '+ 0 (list '* (list bs-cf 0) 1)) (list bs-cf 0))
             (lambda () (crs)))
      (subst (list '= (list '+ 0 (list '* (list bs-cf 0) 1)) (list bs-cf 0)))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq bs-poly bs-const bs-pt 0)
(ass)

;;; ---- step.  series-partial-sum-succ on BOTH sums:
;;;   SUM_{k<succ(succ n)} a_k x^k = SUM_{k<succ n} a_k x^k + a_{succ n} x^(succ n)
;;;   SUM_{j<succ n} (j+1)a_{j+1}pt^j = SUM_{j<n} ... + (n+1)a_{n+1}pt^n
;;; and the two right-hand summands are exactly the induction hypothesis and
;;; `deriv-coef-monomial', joined by `deriv-sum'.
(dk-focus! (cdr (assq 'step dp-br)))
(define st-n  (cdr (assq 'var dp-br)))
(define st-ih (cdr (assq 'ih  dp-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define st-goal (dk-goal))
(define st-cf   (car (cadr (cadddr (cadr (cadddr (cadr st-goal)))))))
(define st-pt   (caddr st-goal))
(define st-sn   (list 'succ st-n))

(define st-ih2 (dk-deepest (lambda () (inst+ st-ih st-cf))))
(define st-ihd (dk-deepest (lambda () (inst+ st-ih2 st-pt))))

(define st-pn   (dpl-poly st-cf st-sn))                    ; the n-th polynomial
(define st-dvn  (list 'SERIES-PARTIAL-SUM (dpl-dseq st-cf st-pt) st-n))
(define st-coef (list st-cf st-sn))                        ; a_{n+1}
(define st-mono (list 'VNB-LAMBDA 'x 'RR (list '* st-coef (list 'power 'x st-sn))))
(define st-mval (list '* (list '* st-sn st-coef) (list 'power st-pt st-n)))
(define st-sum  (list 'VNB-LAMBDA 'x 'RR (list '+ (list st-pn 'x) (list st-mono 'x))))
(define st-val  (list '+ st-dvn st-mval))
(define st-next (dpl-poly st-cf (list 'succ st-sn)))

(fact 'nn-succ-closed st-n)                                ; (IN (succ n) NN)
;;; and (IN (succ (succ n)) NN), which `poly-lam-in-fun' needs below.  Without
;;; it that citation lands the IMPLICATION, the transfer then fails to detach,
;;; and the failure surfaces four lines later as an `ass' that cannot find a
;;; goal the driver believes it just proved.
(fact 'nn-succ-closed st-sn)                               ; (IN (succ (succ n)) NN)
(fact 'fun-apply-type-c st-cf 'NN 'RR st-sn)               ; (IN a_{n+1} RR)
(fact 'deriv-coef-monomial st-coef st-n st-pt)             ; the new top term
(have! (list 'AND (list 'IS-DIFF-AT st-pn st-pt st-dvn)
                  (list 'IS-DIFF-AT st-mono st-pt st-mval)))
(fact 'deriv-sum st-pn st-mono st-pt st-dvn st-mval)

;;; the goal's derivative sum, split at its top term and beta-reduced, IS the
;;; value `deriv-sum' just concluded.
;; guarded on its two arguments being real since 2026-08-29
(fact 'poly-dseq-lam-in-fun st-cf st-pt)
(fact 'series-partial-sum-in-rr st-n (dpl-dseq st-cf st-pt))
(fact 'fun-apply-type-c (dpl-dseq st-cf st-pt) 'NN 'RR st-n)
(fact 'series-partial-sum-succ (dpl-dseq st-cf st-pt) st-n)
(subst (list '== (list 'SERIES-PARTIAL-SUM (dpl-dseq st-cf st-pt) st-sn)
                 (list '+ st-dvn (list (dpl-dseq st-cf st-pt) st-n))))
(dpl-beta!)

;;; ... and the goal's polynomial agrees pointwise with the literal sum lambda.
(fact 'poly-lam-in-fun st-cf (list 'succ st-sn))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
          (list '== (list st-next 'x_) (list st-sum 'x_))))
  (lambda ()
    (let ((z (dpl-di-var!)))
      (dpl-beta!)
      ;; guarded on its two arguments being real since 2026-08-29
      (fact 'poly-term-lam-in-fun st-cf z)
      (fact 'series-partial-sum-in-rr st-sn (dpl-term st-cf z))
      (fact 'fun-apply-type-c (dpl-term st-cf z) 'NN 'RR st-sn)
      (fact 'series-partial-sum-succ (dpl-term st-cf z) st-sn)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (dpl-term st-cf z) (list 'succ st-sn))
                       (list '+ (list 'SERIES-PARTIAL-SUM (dpl-term st-cf z) st-sn)
                                (list (dpl-term st-cf z) st-sn))))
      (dpl-beta!)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq st-next st-sum st-pt st-val)
(ass)
(qed 'deriv-polynomial)
(topic! 'deriv-polynomial 'analysis)
(alias! 'deriv-polynomial
        "the derivative of a polynomial: d/dx sum_{k<=n} a_k x^k = sum_{j<n} (j+1) a_{j+1} x^j")
