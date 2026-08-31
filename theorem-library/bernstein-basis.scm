;;; bernstein-basis.scm -- the Bernstein basis polynomials, and the first of
;;; the two identities Proposition 5.4 of docs/calculus.pdf asks for.
;;;
;;;     B_{k,n}(x)  =  C(n,k) x^k (1-x)^{n-k}          (Definition 5.1, (73))
;;;     sum_{l=0}^{n} B_{l,n}(x)  =  1                 (identity (75))
;;;
;;; RUNG 2 of the integration arc (polynomial differentiation -> BERNSTEIN
;;; DENSITY -> antiderivatives -> C-INT).  Every classical route to density
;;; other than Bernstein convolves with an approximate identity, i.e. INTEGRATES,
;;; and the integral is rung 4: the notes' route is close to forced.
;;;
;;; NOTHING HERE IS A NEW COMBINATORIAL CONSTRUCTION.  The Bernstein basis was
;;; ALREADY in the tree under another name: COMB-KK(R,x,y,m) (binomial.scm) is
;;; k |-> C(m,k) x^k y^(m-k) over an arbitrary commutative ring, defined by the
;;; Pascal recursion over a ZZ index.  So
;;;
;;;     BERNSTEIN-BASIS(n,x)  =  COMB-KK(RR-as-a-commutative-ring, x, 1-x, n)
;;;
;;; and identity (75) is `binomial-theorem' (binomial-proof.scm, PROVEN) at
;;; y := 1-x, whose left-hand side is then 1^n.  The only pieces that were
;;; missing are the bridges below.
;;;
;;; THE BRIDGES, and they are the content of this file:
;;;
;;;   (1) `ring-power-of-one' -- ONE^n = ONE in any commutative ring.
;;;       ring-power.scm has x^0, x^1, x^(j+k) and (xy)^n and NOT this one; it
;;;       is a four-line induction off `ring-power-succ'.
;;;
;;;   (2) `series-partial-sum-is-ring-sum' -- THE ONE THAT MATTERS.  The tree
;;;       has two finite sums over an initial NN-segment: SUM(r,f,n)
;;;       (sequences.scm), which the binomial theorem is stated with and which
;;;       reads its addition off a RING accessor, and SERIES-PARTIAL-SUM(f,k)
;;;       (power-series.scm), which the whole series/convergence lane is stated
;;;       with and whose recurrence was brought down to the SURFACE (`+' on RR)
;;;       in comparison-test-proof.scm.  They are equal, and proving it once --
;;;       a three-line induction, `modulo 0' -- is what lets every Bernstein
;;;       estimate downstream be ordinary real arithmetic that `crs' and `ineq'
;;;       can see, instead of (ADD r)-accessor plumbing.  This is the general
;;;       mechanism the rung wanted; without it each identity would have paid
;;;       for its own accessor descent.
;;;
;;;   (2b) `binomial-sum-value' -- the binomial theorem read left-to-right as a
;;;       SUM evaluation, and the reason it is not the auto `-rev' companion is
;;;       recorded at its own heading below.  It is a debt-reporting matter, not
;;;       a mathematical one.
;;;
;;; RR AS A RING.  RR-NORMED-FIELD is a 7-tuple, so it satisfies no 6-slot ring
;;; predicate; RR reaches the ring world only through
;;; NORMED-FIELD-AS-COMMUTATIVE-RING (views.scm), whose six slot read-offs are
;;; PROVEN in normed-field-ring-view.scm.  That projection is `bn-r' below, and
;;; it is the ring every statement here is over.
;;;
;;; WHAT IT COSTS, measured:
;;;
;;;   series-partial-sum-is-ring-sum   modulo 0
;;;   bernstein-basis-unfold           modulo 0
;;;   ring-power-of-one                modulo {bt-one-in-carr, ring-power-zero}
;;;                                      [trust: well-known]
;;;   binomial-sum-value               binomial-theorem's twelve leaves
;;;                                      [trust: well-known]
;;;   bernstein-basis-in-fun           modulo {rr-is-normed-field, comb-kk-in-fun}
;;;   bernstein-partition              those fourteen
;;;
;;; Both read `trust: well-known' since 2026-08-24.  They read `trust: none'
;;; until then, and the cause was `rr-is-normed-field' ALONE -- a bare
;;; `theory-add-axiom!' in numeric-instances.scm carrying no `warrant!' at all.
;;; EVERY statement about RR-as-a-ring in the tree inherits it (it is the only
;;; door to IS-COMMUTATIVE-RING at the reals), so it was never a defect of these
;;; proofs; warranting it re-tiered eleven bills at a stroke.
;;;
;;; THE OTHER HALF IS NOW PROVEN, in theorem-library/bernstein-moments.scm
;;; (2026-08-24): the two moments (78) and (79), the variance identity (80) and
;;; the bound (76).  The mechanism is the WEIGHTED sum-expansion the drive
;;; predicted -- `series-partial-sum-weighted-expansion' (series-linearity.scm),
;;; of which binomial-proof's `sum-expansion' is the weight-1 case.
;;;
;;; Deliberately NOT the differentiation
;;; route of the notes' Lemma 5.5: differentiating (81) would state the
;;; identities in whatever polynomial-function representation rung 1 uses and
;;; couple this rung to that one, where the combinatorial route stays inside the
;;; existing SUM/COMB-KK algebra and never mentions a polynomial function.
;;;
;;; Loads after comparison-test-proof (series-partial-sum-zero/-succ),
;;; normed-field-ring-view (the six RR slot read-offs), binomial-proof
;;; (binomial-theorem), finsum-additive (ring-power-succ) and equality-basics
;;; (eq-sym).

;;; ---- file-local driver (the `bn-' prefix) ----------------------------

;;; RR as a commutative ring: the 6-tuple projection of RR-NORMED-FIELD.
(define bn-r '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))

;;; Focus the open leaf whose goal PRINTS with the given substring.  Errors on a
;;; miss: a focus helper that returns #f and leaves focus put hides every later
;;; step's misdirection.
(define (bn-focus pred)
  (let ((l (filter (lambda (n) (pred (expression->string (dk-goal-of n))))
                   (proof-leaves))))
    (if (null? l) (error "bn-focus: no open leaf matched") (dk-focus! (car l)))))

;;; Peel the leading FORALL/IMPLIES prefix.  `di' is greedy, so a COUNT of `di's
;;; is not a way to land on a chosen goal; loop until the head changes.
(define (bn-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (bn-check name)
  (if (not (proof-done? *ps*))
      (error "bernstein-basis: proof did not close" name
             (expression->string (dk-goal)))))

;;; =====================================================================
;;; 1.  ONE^n = ONE in a commutative ring.
;;;
;;; Induction on n.  Base is ring-power-zero; the step is ring-power-succ, the
;;; induction hypothesis, and the right-identity law (which `crs' supplies).
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
       (= (RING-POWER R (ONE R) n_) (ONE R))))))))
  (ni)
  (bn-focus (lambda (s) (substring? ", 0) = " s)))
  (di) (di)
  (fact 'commutative-ring-is-ring 'r) (fact 'bt-one-in-carr 'r)
  (mac 'ring-power-zero) (crs)
  (bn-focus (lambda (s) (substring? "succ(n_)" s)))
  (di) (di) (di) (di)
  (fact 'commutative-ring-is-ring 'r) (fact 'bt-one-in-carr 'r)
  (macm 'ring-power-succ)
  (inst+ '(forall r (implies (is-commutative-ring r)
                             (= (ring-power r (one r) n_) (one r)))) 'r)
  (subst '(= (RING-POWER r (ONE r) n_) (ONE r)))
  (crs)))
(bn-check 'ring-power-of-one)
(qed 'ring-power-of-one)
(topic! 'ring-power-of-one 'algebra)

;;; =====================================================================
;;; 2.  THE BRIDGE.  A real partial sum IS the ring sum over RR's ring view.
;;;
;;;   SERIES-PARTIAL-SUM(f,n) == SUM(NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD), f, n)
;;;
;;; Both are NN recursions with the same base and the same step; the step's two
;;; additions are (OPR (NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD)) and
;;; (ADD (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)), and both come down
;;; to `binplus' and then to surface `+'.
;;;
;;; Stated `==' (quasi-equality), so no definedness obligation is owed and no
;;; typing hypothesis on f is needed -- which is what makes it usable at
;;; COMB-KK, a family indexed by ZZ rather than an element of FUN(NN,RR).
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
        (list 'FORALL 'f_
              (list '== '(SERIES-PARTIAL-SUM f_ n_) (list 'SUM bn-r 'f_ 'n_)))))))
  (ni)
  (bn-focus (lambda (s) (substring? ", 0) ==" s)))
  (di)
  (mac 'series-partial-sum-zero) (mac 'sum-zero) (mac 'rr-scalar-ring-zero)
  (qrfl)
  (bn-focus (lambda (s) (substring? "succ(n_)" s)))
  (di) (di) (di)
  ;; 2026-08-29.  This used to go SERIES-PARTIAL-SUM -> surface `+' via
  ;; series-partial-sum-succ and binplus-apply.  Neither is available now: the
  ;; recurrence is guarded on its arguments being real (and this theorem
  ;; deliberately assumes NO typing on f_, which is the whole point of it), and
  ;; the slot no longer holds `binplus'.
  ;;
  ;; It does not need the surface at all.  BOTH slots hold the SAME tupled
  ;; lambda -- OPR of RR's additive group and ADD of its commutative-ring view
  ;; are the same object -- so unfolding each side to its own recursion and
  ;; naming that lambda makes the two sides identical, with no reduction and
  ;; hence no typing obligation.  This is why the theorem can stay unguarded.
  (mac 'series-partial-sum) (mac 'sum-ag-succ) (mac 'rr-additive-ag-opr)
  (mac 'sum-succ) (mac 'rr-scalar-ring-add)
  ;; the left inner term is now SUM-AG(ag, f_, n_); put it back in
  ;; SERIES-PARTIAL-SUM language so the induction hypothesis matches it.
  (fact 'series-partial-sum-unfold 'f_ 'n_)
  (subst (list '== (list 'SUM-AG '(NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD) 'f_ 'n_)
                   '(SERIES-PARTIAL-SUM f_ n_)))
  (inst+ (list 'FORALL 'f_ (list '== '(SERIES-PARTIAL-SUM f_ n_)
                                    (list 'SUM bn-r 'f_ 'n_))) 'f_)
  (subst (list '== '(SERIES-PARTIAL-SUM f_ n_) (list 'SUM bn-r 'f_ 'n_)))
  (qrfl)))
(bn-check 'series-partial-sum-is-ring-sum)
(qed 'series-partial-sum-is-ring-sum)
(topic! 'series-partial-sum-is-ring-sum 'analysis)

;;; =====================================================================
;;; 2b. THE BINOMIAL THEOREM, READ AS A SUM EVALUATION.
;;;
;;;   SUM(R, COMB-KK(R,x,y,n), succ n)  =  RING-POWER(R, (ADD R)(x,y), n)
;;;
;;; `binomial-theorem' is this equation the other way round, and
;;; `install-theorem!' (macetes.scm) does mint an auto `binomial-theorem-rev'
;;; macete that fires in exactly this direction.  Citing THAT used to record
;;; NOTHING in the bill: the companion was stamped with the forward's
;;; provenance -- `proven' -- while nothing ever wrote a *proof-debt* entry
;;; under its name, so `debt-of' took the `proven' branch, found no entry and
;;; returned the EMPTY list.  MEASURED here, on this very proof: with
;;; `(mac 'binomial-theorem-rev)' `bernstein-partition' billed THREE leaves;
;;; with `binomial-sum-value' it bills FOURTEEN.
;;;
;;; That hole is CLOSED since 2026-08-24: install-theorem! records the
;;; parentage in *rev-companion-source* at mint time and debt-of / oracles-of /
;;; proof-citations-of resolve a companion through its forward, so the two
;;; routes now bill the same.  This file keeps the explicit flip anyway --
;;; `binomial-sum-value' is a citable theorem in its own right, and a proof
;;; reads better citing a named equation than a macete named after the
;;; direction it happens to fire in.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff (forall-guarded '(n_ R x_ y_)
                  (list '(IN n_ NN) '(IS-COMMUTATIVE-RING R)
                        '(IN x_ (CARR R)) '(IN y_ (CARR R)))
                  (list '= '(SUM R (COMB-KK R x_ y_ n_) (succ n_))
                           '(RING-POWER R ((ADD R) x_ y_) n_)))))
  (bn-peel!)
  (fact 'binomial-theorem 'n_ 'r 'x_ 'y_)
  (fact 'eq-sym '(RING-POWER r ((ADD r) x_ y_) n_)
                '(SUM r (COMB-KK r x_ y_ n_) (succ n_)))
  (ass)))
(bn-check 'binomial-sum-value)
(qed 'binomial-sum-value)
(topic! 'binomial-sum-value 'algebra)

;;; =====================================================================
;;; 3.  The Bernstein basis family (Definition 5.1).
;;;
;;;   BERNSTEIN-BASIS(n,x) : ZZ -> RR,   k |-> C(n,k) x^k (1-x)^(n-k)
;;;
;;; A `def-functoid' installs a rewrite macete and NO theorem, so `mac-h' cannot
;;; unfold it in a hypothesis by its own name.  `bernstein-basis-unfold' is the
;;; theorem that repairs that -- provable in one line and `modulo 0', which is
;;; the route CLAUDE.md records for every functoid whose values get read out of
;;; the context.
;;; =====================================================================

(def-functoid 'BERNSTEIN-BASIS '(n x)
  (list 'COMB-KK bn-r 'x '(- 1 x) 'n))

(notation! 'BERNSTEIN-BASIS 'kind 'functoid 'arity 2
  'english "the Bernstein basis family of degree $1 at $2")

(quietly (lambda ()
  (sp (make-wff (list 'FORALL 'n_ (list 'FORALL 'x_
        (list '== '(BERNSTEIN-BASIS n_ x_)
                  (list 'COMB-KK bn-r 'x_ '(- 1 x_) 'n_))))))
  (di) (di) (mac 'BERNSTEIN-BASIS) (qrfl)))
(bn-check 'bernstein-basis-unfold)
(qed 'bernstein-basis-unfold)
(topic! 'bernstein-basis-unfold 'analysis)

;;; The family is a total ZZ-indexed family of REALS.  comb-kk-in-fun at the
;;; ring view, with CARR read off by rr-scalar-ring-carr.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL x_ (IMPLIES (IN x_ RR)
       (IN (BERNSTEIN-BASIS n_ x_) (FUN ZZ RR))))))))
(quietly (lambda ()
  (di) (di)
  (fact 'rr-is-normed-field)
  (fact 'NORMED-FIELD-AS-COMMUTATIVE-RING-is-COMMUTATIVE-RING 'RR-NORMED-FIELD)
  (fact 'rr-one-in)
  (have! '(AND (IN 1 RR) (IN x_ RR)))
  (fact 'rr-sub-in-rr 1 'x_)
  (have! (list 'IN 'x_ (list 'CARR bn-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass)))
  (have! (list 'IN '(- 1 x_) (list 'CARR bn-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass)))
  (mac 'BERNSTEIN-BASIS)
  (fact 'comb-kk-in-fun bn-r 'x_ '(- 1 x_) 'n_)
  (mac-h 'rr-scalar-ring-carr
         (list 'IN (list 'COMB-KK bn-r 'x_ '(- 1 x_) 'n_)
                   (list 'FUN 'ZZ (list 'CARR bn-r))))
  (ass)))
(bn-check 'bernstein-basis-in-fun)
(qed 'bernstein-basis-in-fun)
(topic! 'bernstein-basis-in-fun 'analysis)

;;; =====================================================================
;;; 4.  IDENTITY (75) -- the Bernstein basis is a partition of unity.
;;;
;;;   sum_{l=0}^{n} B_{l,n}(x)  =  1     for every x in RR
;;;
;;; NOT restricted to [0,1]: the identity is algebraic and holds on all of RR.
;;; (Non-negativity of the basis is what needs 0 <= x <= 1; that is a separate
;;; fact, and it is not needed until the estimate.)
;;;
;;; Five rewrites, no induction of its own:
;;;   BERNSTEIN-BASIS unfold        -> COMB-KK at the ring view
;;;   the bridge (2)                -> the ring SUM the binomial theorem uses
;;;   binomial-sum-value (2b)       -> RING-POWER(R, (ADD R)(x, 1-x), n)
;;;   x + (1-x) = ONE(R)            -> RING-POWER(R, ONE(R), n)
;;;   ring-power-of-one (1)         -> ONE(R), which is 1
;;; =====================================================================

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL x_ (IMPLIES (IN x_ RR)
      (= (SERIES-PARTIAL-SUM (BERNSTEIN-BASIS n_ x_) (succ n_)) 1)))))))
(quietly (lambda ()
  (di) (di)
  (fact 'rr-is-normed-field)
  (fact 'NORMED-FIELD-AS-COMMUTATIVE-RING-is-COMMUTATIVE-RING 'RR-NORMED-FIELD)
  (fact 'rr-one-in)
  (have! '(AND (IN 1 RR) (IN x_ RR)))
  (fact 'rr-sub-in-rr 1 'x_)
  (fact 'nn-succ-closed 'n_)
  (have! (list 'IN 'x_ (list 'CARR bn-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass)))
  (have! (list 'IN '(- 1 x_) (list 'CARR bn-r))
         (lambda () (mac 'rr-scalar-ring-carr) (ass)))
  (mac 'BERNSTEIN-BASIS)
  (mac 'series-partial-sum-is-ring-sum)
  (mac 'binomial-sum-value)
  (have! (list '= (list (list 'ADD bn-r) 'x_ '(- 1 x_)) (list 'ONE bn-r))
    ;; `rr-scalar-ring-add' now names the tupled VNB-LAMBDA the ADD slot holds,
    ;; not the shared constant `binplus' -- so the surface step is the guarded
    ;; slot read-off rather than binplus-apply, and it needs both arguments typed
    ;; in RR first.  x_ and 1 - x_ are real by hypothesis; dk-saturate-slot-ops!
    ;; lands the closure facts and fires the read-off.
    (lambda () (fact 'rr-scalar-ring-carr)
               (mac 'rr-scalar-ring-add) (mac 'rr-scalar-ring-one)
               (dk-saturate-slot-ops! 'RR '((+ . rr-add-closed)
                                            (* . rr-mul-closed)
                                            (- . rr-neg-closed)))
               (crs)))
  (subst (list '= (list (list 'ADD bn-r) 'x_ '(- 1 x_)) (list 'ONE bn-r)))
  (mac 'ring-power-of-one)
  (mac 'rr-scalar-ring-one)
  (crs)))
(bn-check 'bernstein-partition)
(qed 'bernstein-partition)
(topic! 'bernstein-partition 'analysis)
(alias! 'bernstein-partition
        "the Bernstein basis is a partition of unity"
        "Proposition 5.4 (75)")
