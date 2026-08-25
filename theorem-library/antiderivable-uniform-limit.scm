;;; theorem-library/antiderivable-uniform-limit.scm -- docs/calculus.pdf
;;; PROP 4.16 and COR 4.17: THE ANTIDERIVABLE FUNCTIONS ARE CLOSED UNDER
;;; UNIFORM LIMITS.  Rung 3 of the integration arc.
;;;
;;;   rr-converges-to-abs   the abs/eps form of CONVERGES-TO, as an INTRODUCTION
;;;                         rule -- the metric packaging paid once
;;;   rr-limit-ptwise-eq    a sequence pointwise equal to a convergent one
;;;                         converges to the same limit
;;;   uniform-cauchy-limit  a UNIFORMLY CAUCHY family of maps has a pointwise
;;;                         limit which it converges to UNIFORMLY, on an
;;;                         ARBITRARY domain s_
;;;   caratheodory-witness-pair-bound
;;;                         a bound on the difference of two INTEGRANDS bounds
;;;                         the difference of their Caratheodory WITNESSES
;;;   uniform-witness-diff-at
;;;                         the analytic core: a uniformly Cauchy witness family
;;;                         differentiates the limit map
;;;   antiderivative-family-uniform-limit          Prop 4.16
;;;   antiderivable-uniform-limit                  Cor 4.17
;;;
;;; THE SHAPE OF THE PROOF.  Given antiderivatives fam(k) of phifam(k) on [a,b],
;;; NORMALISED so that fam(k)(a) = 0 (antiderivative-normalize.scm), and phifam
;;; converging uniformly on [a,b] to psi:
;;;
;;;   (1) phifam is uniformly CAUCHY on [a,b] -- the triangle inequality through
;;;       psi, with the eps/2 supplied by `rr-scale-eps' at c = 1+1;
;;;   (2) so fam is, by `antiderivative-pair-close': the normalisation makes its
;;;       f(a) = g(a) premise read 0 = 0, and `rr-scale-eps' at c = b - a turns
;;;       the M.(b-a) conclusion back into an eps;
;;;   (3) CLAMP the family.  famc(k) = z |-> fam(k)(CLAMP(a,b,z)) is uniformly
;;;       Cauchy on ALL of RR, because CLAMP puts its argument back in [a,b];
;;;   (4) `uniform-cauchy-limit' hands back the limit map fc, with pointwise
;;;       convergence and uniform convergence on all of RR, and
;;;       `uniform-limit-continuous-at' makes fc continuous at EVERY real --
;;;       ENDPOINTS INCLUDED, which is the whole reason for the clamp;
;;;   (5) at an interior t, `diff-at-witness-family' produces Caratheodory
;;;       witnesses wfam(k) for fam(k) at t; `caratheodory-witness-pair-bound'
;;;       makes THEM uniformly Cauchy on [a,b] out of (1); and
;;;       `uniform-witness-diff-at' -- `uniform-cauchy-limit' again, then
;;;       `uniform-limit-continuous-at', `rr-limit-unique' and
;;;       `diff-at-ptwise-limit' -- gives IS-DIFF-AT(fc, t, psi(t));
;;;   (6) the six conjuncts of Def 4.6 assemble.
;;;
;;; `uniform-cauchy-limit' IS THE MECHANISM, and it is used TWICE -- once for
;;; the clamped antiderivative family on the domain RR, once for the witness
;;; family on the domain CCINT(a,b).  That is why its domain is a quantified
;;; VARIABLE s_ rather than an interval: the two uses want different domains and
;;; the argument cares about neither.  It packages `rr-cauchy-converges',
;;; `seq-limit-in-rr' (unconditional, so the limit map types in one line),
;;; `seq-limit-converges-to' and `rr-limit-tail-abs-le'.
;;;
;;; `diff-at-local' DID NOT NEED TO BE CITED, and the reason is worth recording:
;;; `diff-at-ptwise-limit' (diff-at-local.scm) already absorbs it, and it is
;;; enough to feed that theorem the CLAMPED family rather than the raw one.
;;; The alternative -- differentiate the unclamped limit f and then move the
;;; conclusion to fc by `diff-at-local' -- would have to unfold IS-DIFF-AT,
;;; recover the witness and re-establish the Caratheodory identity for fc; the
;;; clamped route pays instead one `clamp-fixes' rewrite per side of an equation
;;; that was going to be written anyway.  So `diff-at-local' remains exercised
;;; only inside its own file.
;;;
;;; WHAT IT COSTS.  `trust: well-known', all of it INHERITED: `rr-le-scale-
;;; nonneg-right' and the MVT arc through `caratheodory-witness-bound', and
;;; `rr-le-all-pos-nonpos' through `seq-limit'.  Nothing here adds a leaf of its
;;; own, and the two theorems that touch neither the MVT nor SEQ-LIMIT --
;;; `rr-converges-to-abs' and `rr-limit-ptwise-eq' -- are `modulo 0'.
;;;
;;; FIVE MECHANICAL POINTS, each of which cost a run.
;;;
;;; * `di' does NOT always take the whole leading FORALL/IMPLIES prefix: it
;;;   stops at a non-typing antecedent, so ONE `di' can leave the goal in the
;;;   middle of its own prefix and a driver that reads the goal there indexes
;;;   into a variable.  `au-peel-landed!' loops until the head is neither.
;;; * A peeled typing that is ALREADY in the context does not LAND --
;;;   `context-add-assumption' is alpha-idempotent -- so reading the
;;;   eigenvariable off the landings reports "no typing landed" on a peel that
;;;   worked.  `au-peel-typed!' reads it off the GOAL by free-variable
;;;   difference instead.
;;; * POS-RR unfolds to `r in rr and 0 <= r and not(0 = r)', so `0 <= d' arrives
;;;   WITH the positivity: a driver that then claims it hits `have!'s
;;;   already-in-context error.  `au-have!' declines instead of erroring.
;;; * `dk-split!' CONSUMES the conjunction it opens.  The derivative clause of
;;;   Def 4.6 has a CONJUNCTIVE antecedent, so splitting it to read the
;;;   eigenvariable destroys the very formula the clause's own universal needs
;;;   detached; it has to be rebuilt.
;;; * `ineq' is LINEAR: a product of two variables is not something it can
;;;   compose.  `|f_k(x) - f_l(x)| <= d.(b-a)' and `(b-a).d <= eps' compose by
;;;   `crs' on the commutation plus `rr-le-trans', not by `ineq'.
;;;
;;; Loads after antiderivative-normalize (antiderivable-family-normalized),
;;; antiderivative-lipschitz (antiderivative-pair-close, caratheodory-witness-
;;; bound), witness-family-choice (diff-at-witness-family), antiderivative-
;;; transfer (antiderivative-sub), clamp, seq-limit, uniform-limit-local,
;;; diff-at-local, rr-null-scale (rr-scale-eps), rr-abs-basics, rr-order-basics,
;;; ccint-basics, fun-apply-type-proof and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `au-' prefix) --------------------

(define (au-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 30))
          (begin (di) (loop (+ n 1))) #t))))

(define (au-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "au-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (au-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (au-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (au-beta!)
  (let loop ((n 0) (g (dk-goal)))
    (if (> n 10) #t
        (begin (lam-b)
               (let ((g2 (dk-goal)))
                 (if (equal? g g2) #t (loop (+ n 1) g2)))))))

(define (au-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (au-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 6) (error "au-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (au-di-landed-1!)
  (let ((new (au-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "au-di-landed-1!: expected 1" (map expression->string new)))))

(define (au-eigen landed dom)
  (let ((f (any-pred (lambda (z) (and (pair? z) (eq? (car z) 'IN) (equal? (caddr z) dom)))
                     landed)))
    (if f (cadr f) (error "au-eigen: no typing landed" dom))))

(define (au-detach* f)
  (if (and (pair? f) (eq? (car f) 'IMPLIES)
           (any-pred (lambda (a) (alpha-equiv? a (cadr f))) (dk-asms)))
      (au-detach* (dk-deepest (lambda () (detach! f))))
      f))

(define (au-forward! f . ts)
  (let loop ((f (au-detach* f)) (ts ts))
    (if (null? ts) f
        (loop (au-detach* (dk-deepest (lambda () (inst+ f (car ts))))) (cdr ts)))))

;;; `di' until the goal is no longer a FORALL/IMPLIES, accumulating EVERY
;;; assumption the whole peel landed.  One `di' does NOT always take the whole
;;; prefix -- it stops at a non-typing antecedent -- so a single call reads the
;;; goal in the middle of its own prefix.
(define (au-peel-landed!)
  (let loop ((acc '()) (n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (loop (append acc (dk-landed* (lambda () (di)))) (+ n 1))
          acc))))

(define (au-peel-1!)
  (let ((l (au-peel-landed!)))
    (if (and (pair? l) (null? (cdr l))) (car l)
        (error "au-peel-1!: expected exactly 1 landing" (map expression->string l)))))

;;; the two family indices and the argument of a goal
;;;    |F(k)(x) - F(l)(x)| <= e      ->   (k l x)
(define (au-goal-klx)
  (let* ((d (cadr (cadr (dk-goal)))) (l (cadr d)) (r (caddr d)))
    (list (cadr (car l)) (cadr (car r)) (cadr l))))

;;; `ineq' reads ONLY the premises it is handed: a bare `(ineq)' names none and
;;; so proves nothing but a tautology, while naming an index whose atoms the
;;; oracle cannot certify in RR poisons the WHOLE call (a context full of
;;; NN-typed `n_ <= k_' does exactly that).  So the premise list has to be
;;; filtered by the oracle's own precondition.
;;;
;;; `contra--usable-indices' (contra.scm) is that filter and is UNREACHABLE
;;; here: `contra' loads at the far end of load.scm -- it probes on a scratch
;;; state and so must follow `suggest' -- and load.scm:520 says in as many words
;;; that no library proof can reach it.  This asks `ineq-oracle.scm's own
;;; predicates (structure-library, loaded long before driver-kit, so visible
;;; from a contained proof file) rather than restating the test.
(define (au-usable-indices)
  (let* ((sqn  (proof-state-focus *ps*))
         (asms (sequent-node-assumptions sqn)))
    (let loop ((as asms) (k 1) (acc '()))
      (if (null? as)
          (reverse acc)
          (let* ((f  (wff-formula (car as)))
                 (pr (formula->lin+rel f)))
            (loop (cdr as) (+ k 1)
                  (if (and pr
                           (let allok ((vs (map car (lin-coeffs (car pr)))))
                             (or (null? vs)
                                 (and (ineq-atom-rr-ok? (car vs) asms '())
                                      (allok (cdr vs))))))
                      (cons k acc)
                      acc)))))))

(define (au-ineq!) (apply ineq (au-usable-indices)))

(define (au-and2! p q)
  (au-have! (list 'AND p q) (lambda () (au-and! (lambda () (ass))))))

(define (au-pick parts pred)
  (let ((h (any-pred pred parts)))
    (if h h (error "au-pick: no part matches" (map expression->string parts)))))

(define (au-head? h) (lambda (z) (and (pair? z) (eq? (car z) h))))


;;; Peel the goal's whole FORALL/IMPLIES prefix and return the introduced
;;; variables, one per named domain, in the order of the domains.
;;;
;;; Reading them off the LANDINGS is wrong when the peeled typing is ALREADY in
;;; the context -- `context-add-assumption' is alpha-idempotent, so nothing
;;; lands and the finder reports "no typing landed" on a peel that worked.  The
;;; free-variable difference on the GOAL sees the eigenvariable either way.
(define (au-peel-typed! . doms)
  (let ((fv0 (free-vars (dk-goal))))
    (au-peel-landed!)
    (let ((new (filter (lambda (v) (not (memq v fv0))) (free-vars (dk-goal)))))
      (map (lambda (d)
             (or (any-pred (lambda (v)
                             (any-pred (lambda (f) (equal? f (list 'IN v d))) (dk-asms)))
                           new)
                 (error "au-peel-typed!: no introduced variable typed in"
                        d (map symbol->string new))))
           doms))))

(define (au-peel-typed-1! d) (car (au-peel-typed! d)))

(define (au-peel-vars!)
  (let ((fv0 (free-vars (dk-goal))))
    (au-peel-landed!)
    (filter (lambda (v) (not (memq v fv0))) (free-vars (dk-goal)))))

(define (au-var-typed vars dom)
  (or (any-pred (lambda (v)
                  (any-pred (lambda (f) (equal? f (list 'IN v dom))) (dk-asms)))
                vars)
      (error "au-var-typed: no variable typed in" dom (map symbol->string vars))))

;;; `have!' that DECLINES when the claim is already in the context up to alpha.
;;; `cut' of an in-context formula is a silent self-loop (CLAUDE.md), and
;;; `have!' errors on it -- but a driver cannot always know whether an unfold
;;; has already landed the conjunct it is about to claim (POS-RR unfolds to
;;; `0 <= r and not(0 = r)', so `0 <= d' arrives with the positivity).
(define (au-have! form . opt)
  (let ((f (->raw-formula form)))
    (if (any-pred (lambda (a) (alpha-equiv? a f)) (dk-asms))
        f
        (apply have! form opt))))

;;; =====================================================================
;;; L0.  rr-converges-to-abs -- the abs/eps form of CONVERGES-TO, as an
;;; introduction rule.  The metric packaging is paid once, here.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), lv in rr],
   (forall([eps], pos-rr(eps) implies
      forsome([n_ in nn], forall([k_ in nn], n_ <= k_ implies abs(f(k_) - lv) <= eps))))
   implies converges-to(rr-ms, f, lv))"))
(quietly (lambda () (au-peel!)))
(define AU-A0 (au-find 'h (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)))))
(quietly (lambda ()
  (fact 'rr-is-metric-space)
  (mac 'CONVERGES-TO)
  (au-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond
         ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
         ((eq? (car gl) 'IN) (slot 'PTS) (ass))
         (else
          (let* ((e  (cadr (au-peel-1!)))
                 (ix (au-forward! AU-A0 e))
                 (sk (au-skolem! ix))
                 (bn (car (cadr sk)))
                 (p2 (dk-split! (car sk)))
                 (inner (au-pick p2 (au-head? 'FORALL))))
            (ew bn)
            (au-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN) (ass)
                   (let* ((jj (au-peel-typed-1! 'NN)))
                     (fact 'fun-apply-type-c 'f 'NN 'RR jj)
                     (mac 'rr-ms-dist)
                     (au-forward! inner jj)
                     (ass)))))))))))) )
(qed 'rr-converges-to-abs)
(topic! 'rr-converges-to-abs 'analysis)


;;; =====================================================================
;;; L1.  rr-limit-ptwise-eq
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), h in fun(nn,rr), lv in rr],
     forall([j_ in nn], h(j_) = f(j_)) implies
     converges-to(rr-ms, f, lv) implies
     converges-to(rr-ms, h, lv))"))
(quietly (lambda () (au-peel!)))
(define AU-PE (au-find 'ptwise (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))))
(quietly (lambda ()
  (fact 'rr-one-in)
  (au-have! (forall-guarded 'j_ '(IN j_ NN) '(= (h j_) (* (f j_) 1)))
    (lambda ()
      (let ((v (cadr (au-peel-1!))))
        (au-forward! AU-PE v)
        (fact 'fun-apply-type-c 'f 'NN 'RR v)
        (fact 'fun-apply-type-c 'h 'NN 'RR v)
        (subst (list '= (list 'h v) (list 'f v)))
        (crs))))
  (fact 'rr-limit-scale 1 'f 'h 'lv)
  (au-have! '(= (* lv 1) lv) (lambda () (crs)))
  (subst '(= lv (* lv 1)))
  (ass)))
(qed 'rr-limit-ptwise-eq)
(topic! 'rr-limit-ptwise-eq 'analysis)

;;; =====================================================================
;;; L2.  uniform-cauchy-limit
;;; =====================================================================

(sp (make-wff "forall([g in fun(nn, fun(rr,rr))],
   forall([s_],
     (forall([eps], pos-rr(eps) implies
        forsome([n_ in nn],
          forall([k_ in nn],
            forall([l_ in nn], n_ <= k_ implies n_ <= l_ implies
              forall([x_ in rr], x_ in s_ implies
                abs((g(k_))(x_) - (g(l_))(x_)) <= eps))))))
     implies
     forsome([h in fun(rr,rr)],
       (forall([x_ in rr], x_ in s_ implies
          converges-to(rr-ms, vnb-lambda(k_, nn, (g(k_))(x_)), h(x_))))
       and
       (forall([eps], pos-rr(eps) implies
          forsome([n_ in nn],
            forall([k_ in nn], n_ <= k_ implies
              forall([x_ in rr], x_ in s_ implies
                abs(h(x_) - (g(k_))(x_)) <= eps))))))))"))
(quietly (lambda () (au-peel!)))
(define AU-HC (au-find 'cauchy (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))))

(define (au-seq v) (list 'VNB-LAMBDA 'k_ 'NN (list (list 'g 'k_) v)))
(define AU-LIM (list 'VNB-LAMBDA 'x_ 'RR (list 'SEQ-LIMIT (au-seq 'x_))))

(define (au-seqfun! v)
  (au-have! (list 'IN (au-seq v) '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((j (cadr (au-peel-1!))))
        (fact 'fun-apply-type-c 'g 'NN '(FUN RR RR) j)
        (fact 'fun-apply-type-c (list 'g j) 'RR 'RR v)
        (ass)))))

(quietly (lambda ()
  (au-have! (list 'IN AU-LIM '(FUN RR RR))
    (lambda ()
      (dk-lam-t!)
      (let ((v (cadr (au-peel-1!))))
        (fact 'seq-limit-in-rr (au-seq v))
        (ass))))))
(define AU-LIMF (car (dk-asms)))

;;; at a point of s_ the section is Cauchy, hence convergent
;;; at a point of s_ the section is uniformly Cauchy, hence convergent
(define (au-converges! v)
  (au-seqfun! v)
  (let* ((imp (dk-fact! 'rr-cauchy-converges (au-seq v)))
         (ant (cadr imp)))
    (au-have! ant
      (lambda ()
        (let* ((e  (cadr (au-peel-1!)))
               (ix (au-forward! AU-HC e))
               (sk (au-skolem! ix))
               (bn (car (cadr sk))))
          (dk-split! (car sk))
          (let ((inner (au-find 'inner
                         (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                          (dk-contains? a bn)
                                          (dk-contains? a 'abs))))))
            (ew bn)
            (au-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN) (ass)
                   (begin
                     (au-peel-landed!)
                     ;; the two indices come off the GOAL, never off the context
                     (let* ((dd (cadr (cadr (dk-goal))))
                            (mm (cadr (cadr dd)))
                            (pp (cadr (caddr dd))))
                       (au-beta!)
                       (au-forward! inner mm pp v)
                       (ass))))))))))
    (au-detach* imp)))

;;; pointwise convergence on s_
(quietly (lambda ()
  (au-have! (forall-guarded 'x_ '(IN x_ RR)
           (list 'IMPLIES '(IN x_ s_)
                 (list 'CONVERGES-TO 'RR-MS (au-seq 'x_) (list AU-LIM 'x_))))
    (lambda ()
      (let* ((v (au-peel-typed-1! 'RR)))
        (au-converges! v)
        (fact 'seq-limit-converges-to (au-seq v))
        (au-beta!)
        (ass))))))
(define AU-PT (car (dk-asms)))

(quietly (lambda ()
  (ew AU-LIM)
  (au-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond
         ((eq? (car gl) 'IN) (ass))
         ((dk-contains? gl 'CONVERGES-TO) (ass))
         (else
          (let* ((e  (cadr (au-peel-1!)))
                 (ix (au-forward! AU-HC e))
                 (sk (au-skolem! ix))
                 (bn (car (cadr sk))))
            (dk-split! (car sk))
            (let ((inner (au-find 'inner
                           (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                            (dk-contains? a bn)
                                            (dk-contains? a 'abs))))))
              (dk-split! (dk-landed-1 (lambda () (mac-h 'pos-rr (list 'POS-RR e)))))
              (ew bn)
              (au-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let* ((__p (au-peel-typed! 'NN 'RR))
                            (kk (car __p))
                            (vv (cadr __p)))
                       (au-seqfun! vv)
                       (au-forward! AU-PT vv)
                       (fact 'fun-apply-type-c AU-LIM 'RR 'RR vv)
                       (fact 'fun-apply-type-c 'g 'NN '(FUN RR RR) kk)
                       (fact 'fun-apply-type-c (list 'g kk) 'RR 'RR vv)
                       (au-have! (forall-guarded 'j_ '(IN j_ NN)
                                (list 'IMPLIES (list '<= bn 'j_)
                                  (list '<= (list 'abs
                                              (list '- (list (au-seq vv) 'j_)
                                                       (list (list 'g kk) vv))) e)))
                         (lambda ()
                           (let* ((jj (au-peel-typed-1! 'NN)))
                             (au-beta!)
                             (au-forward! inner jj kk vv)
                             (ass))))
                       (fact 'rr-limit-tail-abs-le (au-seq vv) (list AU-LIM vv)
                             (list (list 'g kk) vv) e bn)
                       (ass))))))))))))))
(qed 'uniform-cauchy-limit)
(topic! 'uniform-cauchy-limit 'analysis)


;;; =====================================================================
;;; L3.  caratheodory-witness-pair-bound -- the DIFFERENCE of two witnesses
;;; is bounded by a bound on the difference of the integrands.
;;; =====================================================================

(sp (make-wff "forall([f1 in fun(rr,rr), f2 in fun(rr,rr), p1 in fun(rr,rr), p2 in fun(rr,rr),
                       w1 in fun(rr,rr), w2 in fun(rr,rr), a in rr, b in rr, t_ in rr, m_ in rr],
   is-antiderivative(f1, p1, a, b) implies
   is-antiderivative(f2, p2, a, b) implies
   (forall([x_ in rr], x_ in ccint(a,b) implies abs(p1(x_) - p2(x_)) <= m_)) implies
   t_ in ccint(a,b) implies
   w1(t_) = p1(t_) implies
   w2(t_) = p2(t_) implies
   (forall([x_ in rr], f1(x_) - f1(t_) = w1(x_) * (x_ - t_))) implies
   (forall([x_ in rr], f2(x_) - f2(t_) = w2(x_) * (x_ - t_))) implies
   (forall([x_ in rr], x_ in ccint(a,b) implies abs(w1(x_) - w2(x_)) <= m_)))"))
(quietly (lambda () (au-peel!)))
;;; `au-peel!' takes the CONCLUSION's universal too, so the goal is already the
;;; atom and its argument is the eigenvariable.
(define AU-B-X (cadr (cadr (cadr (cadr (dk-goal))))))
(define AU-B-BD (au-find 'bd (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                              (dk-contains? z 'abs)))))
(define AU-B-I1 (au-find 'i1 (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                              (dk-contains? z 'w1)))))
(define AU-B-I2 (au-find 'i2 (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                              (dk-contains? z 'w2)))))

(define AU-B-SUB (dk-deepest (lambda () (fact 'antiderivative-sub 'f1 'f2 'p1 'p2 'a 'b))))
(define AU-B-F (cadr AU-B-SUB))
(define AU-B-P (caddr AU-B-SUB))
(define AU-B-W (cadr (dk-fact! 'sub-lam-in-fun 'w1 'w2)))

(quietly (lambda ()
  (fact 'sub-lam-in-fun 'f1 'f2)
  (fact 'sub-lam-in-fun 'p1 'p2)
  (fact 'fun-apply-type-c 'p1 'RR 'RR 't_)
  (fact 'fun-apply-type-c 'p2 'RR 'RR 't_)
  (fact 'fun-apply-type-c 'w1 'RR 'RR 't_)
  (fact 'fun-apply-type-c 'w2 'RR 'RR 't_)

  ;; (2) the bound on the difference of the integrands, as a bound on the lambda
  (au-have! (forall-guarded 'y_ '(IN y_ RR)
           (list 'IMPLIES '(IN y_ (CCINT a b))
                 (list '<= (list 'abs (list AU-B-P 'y_)) 'm_)))
    (lambda ()
      (let* ((vv (au-peel-typed-1! 'RR)))
        (au-beta!)
        (au-forward! AU-B-BD vv)
        (ass))))

  ;; (4) the witness difference agrees with the integrand difference at t_
  (au-have! (list '= (list AU-B-W 't_) (list AU-B-P 't_))
    (lambda ()
      (au-beta!)
      (subst '(= (w1 t_) (p1 t_)))
      (subst '(= (w2 t_) (p2 t_)))
      (crs)))

  ;; (5) the Caratheodory identity for the difference
  (au-have! (forall-guarded 'y_ '(IN y_ RR)
           (list '= (list '- (list AU-B-F 'y_) (list AU-B-F 't_))
                    (list '* (list AU-B-W 'y_) '(- y_ t_))))
    (lambda ()
      (let* ((vv (au-peel-typed-1! 'RR)))
        (fact 'fun-apply-type-c 'f1 'RR 'RR vv)
        (fact 'fun-apply-type-c 'f2 'RR 'RR vv)
        (fact 'fun-apply-type-c 'f1 'RR 'RR 't_)
        (fact 'fun-apply-type-c 'f2 'RR 'RR 't_)
        (fact 'fun-apply-type-c 'w1 'RR 'RR vv)
        (fact 'fun-apply-type-c 'w2 'RR 'RR vv)
        (au-beta!)
        (au-forward! AU-B-I1 vv)
        (au-forward! AU-B-I2 vv)
        (let ((split (list '= (list '- (list '- (list 'f1 vv) (list 'f2 vv))
                                            (list '- (list 'f1 't_) (list 'f2 't_)))
                              (list '- (list '- (list 'f1 vv) (list 'f1 't_))
                                            (list '- (list 'f2 vv) (list 'f2 't_))))))
          (au-have! split (lambda () (crs)))
          (subst split)
          (subst (list '= (list '- (list 'f1 vv) (list 'f1 't_))
                           (list '* (list 'w1 vv) (list '- vv 't_))))
          (subst (list '= (list '- (list 'f2 vv) (list 'f2 't_))
                           (list '* (list 'w2 vv) (list '- vv 't_))))
          (crs)))))

  (fact 'caratheodory-witness-bound AU-B-F AU-B-P AU-B-W 'a 'b 't_ 'm_)))

(define AU-B-CON (au-find 'con (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                (dk-contains? z 'CCINT)
                                                (dk-contains? z 'abs)
                                                (dk-contains? z 'VNB-LAMBDA)))))
(quietly (lambda ()
  (let* ((vv AU-B-X))
    (fact 'fun-apply-type-c 'w1 'RR 'RR vv)
    (fact 'fun-apply-type-c 'w2 'RR 'RR vv)
    (au-forward! AU-B-CON vv)
    (let ((eqn (list '= (list '- (list 'w1 vv) (list 'w2 vv)) (list AU-B-W vv))))
      (au-have! eqn (lambda () (au-beta!) (crs)))
      (subst eqn)
      (ass)))))
(qed 'caratheodory-witness-pair-bound)
(topic! 'caratheodory-witness-pair-bound 'analysis)


;;; =====================================================================
;;; L4.  uniform-witness-diff-at
;;; =====================================================================

(sp (make-wff "forall([gfam in fun(nn, fun(rr,rr)), wfam in fun(nn, fun(rr,rr)),
                       fc in fun(rr,rr), lv in rr, a in rr, b in rr, t_ in rr, rho in rr],
   0 < rho implies
   (forall([y_ in rr], abs(y_ - t_) <= rho implies y_ in ccint(a,b))) implies
   t_ in ccint(a,b) implies
   (forall([k_ in nn], is-continuous-at(rr-ms, rr-ms, wfam(k_), t_))) implies
   (forall([k_ in nn], forall([y_ in rr], y_ in ccint(a,b) implies
      (gfam(k_))(y_) - (gfam(k_))(t_) = ((wfam(k_))(y_)) * (y_ - t_)))) implies
   (forall([y_ in rr], y_ in ccint(a,b) implies
      converges-to(rr-ms, vnb-lambda(k_, nn, (gfam(k_))(y_)), fc(y_)))) implies
   (forall([eps], pos-rr(eps) implies
      forsome([n_ in nn],
        forall([k_ in nn],
          forall([l_ in nn], n_ <= k_ implies n_ <= l_ implies
            forall([x_ in rr], x_ in ccint(a,b) implies
              abs((wfam(k_))(x_) - (wfam(l_))(x_)) <= eps)))))) implies
   converges-to(rr-ms, vnb-lambda(k_, nn, (wfam(k_))(t_)), lv) implies
   is-diff-at(fc, t_, lv))"))
(quietly (lambda () (au-peel!)))
(define AU-C-BALL (au-find 'ball (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                  (dk-contains? z 'CCINT)
                                                  (dk-contains? z 'rho)))))
(define AU-C-CONT (au-find 'cont (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                  (dk-contains? z 'IS-CONTINUOUS-AT)))))
(define AU-C-ID   (au-find 'id   (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                  (dk-contains? z 'gfam)
                                                  (not (dk-contains? z 'CONVERGES-TO))))))
(define AU-C-PC   (au-find 'pc   (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                  (dk-contains? z 'gfam)
                                                  (dk-contains? z 'CONVERGES-TO)))))
(define AU-C-UC   (au-find 'uc   (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                  (dk-contains? z 'POS-RR)))))
(define AU-C-H8   (au-find 'h8   (lambda (z) (and (pair? z) (eq? (car z) 'CONVERGES-TO)))))

(define AU-C-EX  (dk-fact! 'uniform-cauchy-limit 'wfam '(CCINT a b)))
(define AU-C-SK  (au-skolem! AU-C-EX))
(define AU-C-PSI (car (cadr AU-C-SK)))
(quietly (lambda () (dk-split! (car AU-C-SK))))
(define AU-C-P1 (au-find 'p1 (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                              (dk-contains? z AU-C-PSI)
                                              (dk-contains? z 'CONVERGES-TO)))))
(define AU-C-P2 (au-find 'p2 (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                              (dk-contains? z AU-C-PSI)
                                              (dk-contains? z 'POS-RR)))))

;;; PSI is continuous at t_
(quietly (lambda ()
  (let* ((imp (dk-fact! 'uniform-limit-continuous-at 'wfam AU-C-PSI 't_ 'rho))
         (ant (cadr imp)))
    (au-have! ant
      (lambda ()
        (let* ((e  (cadr (au-peel-1!)))
               (ix (au-forward! AU-C-P2 e))
               (sk (au-skolem! ix))
               (bn (car (cadr sk))))
          (dk-split! (car sk))
          (let ((inner (au-find 'inner (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                        (dk-contains? z bn)
                                                        (dk-contains? z 'abs))))))
            (ew bn)
            (au-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN) (ass)
                   (let* ((__p (au-peel-typed! 'NN 'RR))
                          (kk (car __p))
                          (vv (cadr __p)))
                     (au-forward! AU-C-BALL vv)
                     (au-forward! inner kk vv)
                     (ass)))))))))
    (au-detach* imp))))

;;; PSI(t_) = lv
(define AU-C-TSEQ (list 'VNB-LAMBDA 'k_ 'NN (list (list 'wfam 'k_) 't_)))
(quietly (lambda ()
  (au-have! (list 'IN AU-C-TSEQ '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((j (cadr (au-peel-1!))))
        (fact 'fun-apply-type-c 'wfam 'NN '(FUN RR RR) j)
        (fact 'fun-apply-type-c (list 'wfam j) 'RR 'RR 't_)
        (ass))))
  (fact 'fun-apply-type-c AU-C-PSI 'RR 'RR 't_)
  (au-forward! AU-C-P1 't_)
  (fact 'rr-limit-unique AU-C-TSEQ (list AU-C-PSI 't_) 'lv)))

;;; and diff-at-ptwise-limit finishes
(quietly (lambda ()
  (let loop ((f (dk-fact! 'diff-at-ptwise-limit 'gfam 'wfam 'fc AU-C-PSI 't_ 'rho)))
    (if (and (pair? f) (eq? (car f) 'IMPLIES))
        (let ((ant (cadr f)))
          (au-have! ant
            (lambda ()
              (let* ((vs (au-peel-vars!))
                     (vv (au-var-typed vs 'RR)))
                (au-forward! AU-C-BALL vv)
                (cond ((dk-contains? ant 'fc)      (au-forward! AU-C-PC vv))
                      ((dk-contains? ant AU-C-PSI) (au-forward! AU-C-P1 vv))
                      (else (au-forward! AU-C-ID (au-var-typed vs 'NN) vv)))
                (ass))))
          (loop (au-detach* f)))
        (begin
          (subst (list '= 'lv (list AU-C-PSI 't_)))
          (ass))))))
(qed 'uniform-witness-diff-at)
(topic! 'uniform-witness-diff-at 'analysis)

;;; =====================================================================
;;; L5.  docs/calculus.pdf PROP 4.16
;;; =====================================================================

(sp (make-wff "forall([fam in fun(nn, fun(rr,rr)), phifam in fun(nn, fun(rr,rr)),
                       psi in fun(rr,rr), a in rr, b in rr],
   a < b implies
   (forall([k_ in nn], is-antiderivative(fam(k_), phifam(k_), a, b)
                        and (fam(k_))(a) = 0)) implies
   (forall([eps], pos-rr(eps) implies
      forsome([n_ in nn], forall([k_ in nn], n_ <= k_ implies
        forall([x_ in rr], x_ in ccint(a,b) implies
          abs(psi(x_) - (phifam(k_))(x_)) <= eps))))) implies
   forsome([f in fun(rr,rr)],
     is-antiderivative(f, psi, a, b)
     and
     (forall([eps], pos-rr(eps) implies
        forsome([n_ in nn], forall([k_ in nn], n_ <= k_ implies
          forall([x_ in rr], x_ in ccint(a,b) implies
            abs(f(x_) - (fam(k_))(x_)) <= eps)))))))"))
(quietly (lambda () (au-peel!)))
(define AU-AD (au-find 'ad (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                            (dk-contains? z 'IS-ANTIDERIVATIVE)))))
(define AU-UN (au-find 'un (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                            (dk-contains? z 'POS-RR)))))
(quietly (lambda ()
  (fact 'rr-zero-in) (fact 'rr-one-in) (fact 'rr-zero-lt-one)
  (fact 'rr-lt-implies-le 'a 'b)
  (au-and2! '(IN 1 RR) '(IN 1 RR))
  (fact 'rr-add-closed 1 1)
  (fact 'rr-sub-in-rr 'b 'a)
  (au-have! '(<= 0 (+ 1 1)) (lambda () (au-ineq!)))
  (au-have! '(<= 0 (- b a)) (lambda () (au-ineq!)))))

;;; ---- (1)  phifam is uniformly CAUCHY on [a,b] ------------------------
(define AU-IMP-PHI (dk-fact! 'uniform-cauchy-limit 'phifam '(CCINT a b)))
(define AU-CPHI (cadr AU-IMP-PHI))
(quietly (lambda ()
  (au-have! AU-CPHI
    (lambda ()
      (let ((e (cadr (au-peel-1!))))
        (au-have! (list 'IN e 'RR)
          (lambda () (dk-split! (dk-landed-1 (lambda ()
                        (mac-h 'pos-rr (list 'POS-RR e))))) (ass)))
        (let* ((ex (dk-fact! 'rr-scale-eps '(+ 1 1) e))
               (parts (dk-split! ex))
               (dd (cadr (au-pick parts (au-head? 'POS-RR))))
               (tu (au-pick parts (au-head? 'FORALL))))
          (let* ((ix (au-forward! AU-UN dd))
                 (sk (au-skolem! ix))
                 (bn (car (cadr sk)))
                 (p2 (dk-split! (car sk)))
                 (inner (au-pick p2 (au-head? 'FORALL))))
            (dk-split! (dk-landed-1 (lambda () (mac-h 'pos-rr (list 'POS-RR dd)))))
            (au-have! (list '<= 0 dd) (lambda () (au-ineq!)))
            (au-have! (list '<= dd dd) (lambda () (au-ineq!)))
            (au-forward! tu dd)
            (au-have! (list '= (list '* '(+ 1 1) dd) (list '+ dd dd)) (lambda () (crs)))
            (ew bn)
            (au-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN) (ass)
                   (begin
                     (au-peel-landed!)
                     (let* ((klx (au-goal-klx))
                            (kk (car klx)) (ll (cadr klx)) (vv (caddr klx)))
                       (au-forward! inner kk vv)
                       (au-forward! inner ll vv)
                       (fact 'fun-apply-type-c 'psi 'RR 'RR vv)
                       (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) kk)
                       (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) ll)
                       (fact 'fun-apply-type-c (list 'phifam kk) 'RR 'RR vv)
                       (fact 'fun-apply-type-c (list 'phifam ll) 'RR 'RR vv)
                       (let* ((pk (list (list 'phifam kk) vv))
                              (pl (list (list 'phifam ll) vv))
                              (ps (list 'psi vv))
                              (aa (list '- pk ps))
                              (bb (list '- ps pl)))
                         (fact 'rr-sub-in-rr pk ps)
                         (fact 'rr-sub-in-rr ps pl)
                         (fact 'rr-sub-in-rr ps pk)
                         (fact 'rr-sub-in-rr pk pl)
                         (fact 'rr-abs-closed aa)
                         (fact 'rr-abs-closed bb)
                         (fact 'rr-abs-closed (list '- ps pk))
                         (fact 'rr-abs-closed (list '- pk pl))
                         (fact 'rr-abs-triangle-c aa bb)
                         (fact 'rr-abs-sub-sym ps pk)
                         (au-have! (list '= (list '- pk pl) (list '+ aa bb))
                                (lambda () (crs)))
                         (subst (list '= (list '- pk pl) (list '+ aa bb)))
                         (fact 'rr-abs-closed (list '+ aa bb))
                         (au-ineq!))))))))))))))
(define AU-HPC AU-CPHI)

;;; ---- (2)  fam is uniformly CAUCHY on [a,b] ---------------------------
(define AU-IMP-FAM (dk-fact! 'uniform-cauchy-limit 'fam '(CCINT a b)))
(define AU-CFAM (cadr AU-IMP-FAM))
(quietly (lambda ()
  (au-have! AU-CFAM
    (lambda ()
      (let ((e (cadr (au-peel-1!))))
        (au-have! (list 'IN e 'RR)
          (lambda () (dk-split! (dk-landed-1 (lambda ()
                        (mac-h 'pos-rr (list 'POS-RR e))))) (ass)))
        (let* ((ex (dk-fact! 'rr-scale-eps '(- b a) e))
               (parts (dk-split! ex))
               (dd (cadr (au-pick parts (au-head? 'POS-RR))))
               (tu (au-pick parts (au-head? 'FORALL))))
          (let* ((ix (au-forward! AU-HPC dd))
                 (sk (au-skolem! ix))
                 (bn (car (cadr sk)))
                 (p2 (dk-split! (car sk)))
                 (inner (au-pick p2 (au-head? 'FORALL))))
            (dk-split! (dk-landed-1 (lambda () (mac-h 'pos-rr (list 'POS-RR dd)))))
            (au-have! (list '<= 0 dd) (lambda () (au-ineq!)))
            (au-have! (list '<= dd dd) (lambda () (au-ineq!)))
            (au-forward! tu dd)
            (au-and2! (list 'IN dd 'RR) '(IN (- b a) RR))
            (fact 'rr-mul-closed dd '(- b a))
            (au-have! (list '= (list '* '(- b a) dd) (list '* dd '(- b a)))
                   (lambda () (crs)))
            (ew bn)
            (au-and!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN) (ass)
                   (begin
                     (au-peel-landed!)
                     (let* ((klx (au-goal-klx))
                            (kk (car klx)) (ll (cadr klx)) (vv (caddr klx)))
                       (dk-split! (au-forward! AU-AD kk))
                       (dk-split! (au-forward! AU-AD ll))
                       (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
                       (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) ll)
                       (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) kk)
                       (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) ll)
                       (fact 'fun-apply-type-c (list 'fam kk) 'RR 'RR 'a)
                       (fact 'fun-apply-type-c (list 'fam ll) 'RR 'RR 'a)
                       (au-have! (list '= (list (list 'fam kk) 'a) (list (list 'fam ll) 'a))
                         (lambda ()
                           (subst (list '= (list (list 'fam kk) 'a) 0))
                           (subst (list '= (list (list 'fam ll) 'a) 0))
                           (crs)))
                       (au-have! (forall-guarded 'x_ '(IN x_ RR)
                                (list 'IMPLIES '(IN x_ (CCINT a b))
                                  (list '<= (list 'abs
                                     (list '- (list (list 'phifam kk) 'x_)
                                              (list (list 'phifam ll) 'x_))) dd)))
                         (lambda ()
                           (let* ((yy (au-peel-typed-1! 'RR)))
                             (au-forward! inner kk ll yy)
                             (ass))))
                       (let* ((con (dk-fact! 'antiderivative-pair-close
                                     (list 'fam kk) (list 'fam ll)
                                     (list 'phifam kk) (list 'phifam ll) 'a 'b dd))
                              (dif (list '- (list (list 'fam kk) vv)
                                            (list (list 'fam ll) vv)))
                              (bnd (list '* dd '(- b a))))
                         (au-forward! con vv)
                         (fact 'fun-apply-type-c (list 'fam kk) 'RR 'RR vv)
                         (fact 'fun-apply-type-c (list 'fam ll) 'RR 'RR vv)
                         (fact 'rr-sub-in-rr (list (list 'fam kk) vv)
                                             (list (list 'fam ll) vv))
                         (fact 'rr-abs-closed dif)
                         ;; (b-a).d <= eps commutes to d.(b-a) <= eps -- `crs',
                         ;; not `ineq': a product of two VARIABLES is not linear.
                         (au-have! (list '<= bnd e)
                           (lambda ()
                             (subst (list '= bnd (list '* '(- b a) dd)))
                             (ass)))
                         (au-and2! (list '<= (list 'abs dif) bnd)
                                   (list '<= bnd e))
                         (fact 'rr-le-trans (list 'abs dif) bnd e)
                         (ass))))))))))))))
(define AU-HFC AU-CFAM)

;;; ---- (3)  the CLAMPED family ----------------------------------------
(define (au-inner k) (list 'VNB-LAMBDA 'z_ 'RR (list (list 'fam k) '(CLAMP a b z_))))
(define AU-FAMC (list 'VNB-LAMBDA 'k_ 'NN (au-inner 'k_)))

(quietly (lambda ()
  (au-have! (list 'IN AU-FAMC '(FUN NN (FUN RR RR)))
    (lambda ()
      (dk-lam-t!)
      (let ((kk (cadr (au-peel-1!))))
        (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
        (fact 'clamp-compose-lam-in-fun (list 'fam kk) 'a 'b)
        (ass))))))

(define AU-IMP-FAMC (dk-fact! 'uniform-cauchy-limit AU-FAMC 'RR))
(define AU-CFAMC (cadr AU-IMP-FAMC))
(quietly (lambda ()
  (au-have! AU-CFAMC
    (lambda ()
      (let ((e (cadr (au-peel-1!))))
        (let* ((ix (au-forward! AU-HFC e))
               (sk (au-skolem! ix))
               (bn (car (cadr sk)))
               (p2 (dk-split! (car sk)))
               (inner (au-pick p2 (au-head? 'FORALL))))
          (ew bn)
          (au-and!
           (lambda ()
             (if (eq? (car (dk-goal)) 'IN) (ass)
                 (begin
                   (au-peel-landed!)
                   (let* ((klx (au-goal-klx))
                          (kk (car klx)) (ll (cadr klx)) (vv (caddr klx)))
                     (fact 'clamp-in-ccint 'a 'b vv)
                     (fact 'clamp-in-rr 'a 'b vv)
                     (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
                     (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) ll)
                     (au-beta!)
                     (au-forward! inner kk ll (list 'CLAMP 'a 'b vv))
                     (ass))))))))))))

;;; ---- (4)  the limit map fc, and its continuity at EVERY real --------
(define AU-EXC (au-detach* AU-IMP-FAMC))
(define AU-SKC (au-skolem! AU-EXC))
(define AU-FC  (car (cadr AU-SKC)))
(define AU-FCP (quietly (lambda () (dk-split! (car AU-SKC)))))
(define AU-FCF  (au-pick AU-FCP (au-head? 'IN)))
(define AU-FCPT (au-pick AU-FCP (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                 (dk-contains? z 'CONVERGES-TO)))))
(define AU-FCUC (au-pick AU-FCP (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                 (dk-contains? z 'POS-RR)))))

(define AU-CONTFORM (forall-guarded 't_ '(IN t_ RR)
                      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS AU-FC 't_)))
(quietly (lambda ()
  (au-have! AU-CONTFORM
    (lambda ()
      (let* ((tt (au-peel-typed-1! 'RR)))
        (au-have! (forall-guarded 'k_ '(IN k_ NN)
                 (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (list AU-FAMC 'k_) tt))
          (lambda ()
            (let* ((kk (au-peel-typed-1! 'NN)))
              (dk-split! (au-forward! AU-AD kk))
              (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
              (au-have! (forall-guarded 'x_ '(IN x_ RR)
                       (list 'IMPLIES '(IN x_ (CCINT a b))
                             (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (list 'fam kk) 'x_)))
                (lambda ()
                  (let* ((vv (au-peel-typed-1! 'RR)))
                    (let* ((cp (dk-split! (dk-landed-1 (lambda ()
                                  (mac-h 'IS-ANTIDERIVATIVE
                                    (list 'IS-ANTIDERIVATIVE (list 'fam kk)
                                          (list 'phifam kk) 'a 'b))))))
                           (cc (au-pick cp (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                     (dk-contains? z 'IS-CONTINUOUS-AT))))))
                      (au-forward! cc vv)
                      (ass)))))
              (fact 'clamp-compose-continuous-at (list 'fam kk) 'a 'b tt)
              (au-beta!)
              (ass))))
        (let* ((imp (dk-fact! 'uniform-limit-continuous-at AU-FAMC AU-FC tt 1))
               (ant (cadr imp)))
          (au-have! ant
            (lambda ()
              (let ((e (cadr (au-peel-1!))))
                (let* ((ix (au-forward! AU-FCUC e))
                       (sk (au-skolem! ix))
                       (bn (car (cadr sk)))
                       (p2 (dk-split! (car sk)))
                       (inner (au-pick p2 (au-head? 'FORALL))))
                  (ew bn)
                  (au-and!
                   (lambda ()
                     (if (eq? (car (dk-goal)) 'IN) (ass)
                         (let* ((__p (au-peel-typed! 'NN 'RR))
                                (kk (car __p))
                                (vv (cadr __p)))
                           (au-forward! inner kk vv)
                           (ass)))))))))
          (au-detach* imp)
          (ass)))))))

;;; ---- (5)  the DERIVATIVE at an interior point ------------------------
(define (au-p16-diff!)
  (let* ((l (au-peel-landed!))
         (conj (au-pick l (au-head? 'AND)))
         (parts (dk-split! conj))
         (tt (cadr (au-pick parts (lambda (z) (and (pair? z) (eq? (car z) 'IN)
                                                   (eq? (caddr z) 'RR)))))))
    (fact 'rr-lt-implies-le 'a tt)
    (fact 'rr-lt-implies-le tt 'b)
    (fact 'rr-sub-in-rr tt 'a)
    (fact 'rr-sub-in-rr 'b tt)
    (au-have! (list '< 0 (list '- tt 'a)) (lambda () (au-ineq!)))
    (au-have! (list '< 0 (list '- 'b tt)) (lambda () (au-ineq!)))
    (let* ((rx  (dk-fact! 'rr-min-pos (list '- tt 'a) (list '- 'b tt)))
           (rsk (au-skolem! rx))
           (rho (car (cadr rsk)))
           (rp  (dk-split! (car rsk))))
      (au-have! (list 'IN tt '(CCINT a b))
        (lambda () (mac 'ccint-membership)
                   (au-and! (lambda () (if (eq? (car (dk-goal)) 'IN) (ass) (au-ineq!))))))
      (au-have! (forall-guarded 'y_ '(IN y_ RR)
               (list 'IMPLIES (list '<= (list 'abs (list '- 'y_ tt)) rho)
                     '(IN y_ (CCINT a b))))
        (lambda ()
          (let* ((yy (au-peel-typed-1! 'RR)))
            (fact 'rr-sub-in-rr yy tt)
            (fact 'rr-abs-closed (list '- yy tt))
            (fact 'rr-le-abs (list '- yy tt))
            (fact 'rr-neg-abs-le (list '- yy tt))
            (mac 'ccint-membership)
            (au-and! (lambda () (if (eq? (car (dk-goal)) 'IN) (ass) (au-ineq!)))))))
      (let ((lfam (list 'VNB-LAMBDA 'k_ 'NN (list (list 'phifam 'k_) tt))))
        (au-have! (list 'IN lfam '(FUN NN RR))
          (lambda ()
            (dk-lam-t!)
            (let ((j (cadr (au-peel-1!))))
              (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) j)
              (fact 'fun-apply-type-c (list 'phifam j) 'RR 'RR tt)
              (ass))))
        (au-have! (forall-guarded 'k_ '(IN k_ NN)
                 (list 'IS-DIFF-AT (list 'fam 'k_) tt (list lfam 'k_)))
          (lambda ()
            (let* ((kk (au-peel-typed-1! 'NN)))
              (dk-split! (au-forward! AU-AD kk))
              (let* ((cp (dk-split! (dk-landed-1 (lambda ()
                            (mac-h 'IS-ANTIDERIVATIVE
                              (list 'IS-ANTIDERIVATIVE (list 'fam kk)
                                    (list 'phifam kk) 'a 'b))))))
                     (dc (au-pick cp (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                (dk-contains? z 'IS-DIFF-AT))))))
                ;; `dk-split!' CONSUMES the conjunction it opens, so the
                ;; antecedent of the derivative clause has to be rebuilt.
                (au-and2! (list 'IN tt 'RR)
                          (list 'AND (list '< 'a tt) (list '< tt 'b)))
                (au-forward! dc tt)
                (au-beta!)
                (ass)))))
        (let* ((wex   (dk-fact! 'diff-at-witness-family 'fam lfam tt))
               (wsk   (au-skolem! wex))
               (wfam  (car (cadr wsk)))
               (wp    (dk-split! (car wsk)))
               (wprop (au-pick wp (au-head? 'FORALL)))
               (wvalf (forall-guarded 'k_ '(IN k_ NN)
                        (list '= (list (list wfam 'k_) tt)
                                 (list (list 'phifam 'k_) tt)))))
          ;; h4
          (au-have! (forall-guarded 'k_ '(IN k_ NN)
                   (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (list wfam 'k_) tt))
            (lambda ()
              (let* ((kk (au-peel-typed-1! 'NN)))
                (dk-split! (au-forward! wprop kk))
                (ass))))
          ;; the witness value at tt
          (au-have! wvalf
            (lambda ()
              (let* ((kk (au-peel-typed-1! 'NN)))
                (let* ((ps (dk-split! (au-forward! wprop kk)))
                       (eqn (au-pick ps (au-head? '=))))
                  (subst eqn)
                  (au-beta!)
                  (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) kk)
                  (fact 'fun-apply-type-c (list 'phifam kk) 'RR 'RR tt)
                  (crs)))))
          ;; h5
          (au-have! (forall-guarded 'k_ '(IN k_ NN)
                   (forall-guarded 'y_ '(IN y_ RR)
                     (list 'IMPLIES '(IN y_ (CCINT a b))
                       (list '= (list '- (list (list AU-FAMC 'k_) 'y_)
                                         (list (list AU-FAMC 'k_) tt))
                                (list '* (list (list wfam 'k_) 'y_)
                                         (list '- 'y_ tt))))))
            (lambda ()
              (let* ((__p (au-peel-typed! 'NN 'RR))
                     (kk (car __p))
                     (yy (cadr __p)))
                (dk-split! (dk-landed-1 (lambda ()
                    (mac-h 'ccint-membership (list 'IN yy '(CCINT a b))))))
                (fact 'clamp-fixes 'a 'b yy)
                (fact 'clamp-fixes 'a 'b tt)
                (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
                (au-beta!)
                (subst (list '= (list 'CLAMP 'a 'b yy) yy))
                (subst (list '= (list 'CLAMP 'a 'b tt) tt))
                (let* ((ps (dk-split! (au-forward! wprop kk)))
                       (idf (au-pick ps (au-head? 'FORALL))))
                  (au-forward! idf yy)
                  (ass)))))
          ;; h6
          (au-have! (forall-guarded 'y_ '(IN y_ RR)
                   (list 'IMPLIES '(IN y_ (CCINT a b))
                     (list 'CONVERGES-TO 'RR-MS
                           (list 'VNB-LAMBDA 'k_ 'NN (list (list AU-FAMC 'k_) 'y_))
                           (list AU-FC 'y_))))
            (lambda ()
              (let* ((yy (au-peel-typed-1! 'RR)))
                (au-forward! AU-FCPT yy)
                (ass))))
          ;; h7
          (let* ((impw (dk-fact! 'uniform-cauchy-limit wfam '(CCINT a b)))
                 (cw   (cadr impw)))
            (au-have! cw
              (lambda ()
                (let ((e (cadr (au-peel-1!))))
                  (au-have! (list 'IN e 'RR)
                    (lambda () (dk-split! (dk-landed-1 (lambda ()
                        (mac-h 'pos-rr (list 'POS-RR e))))) (ass)))
                  (let* ((ix (au-forward! AU-HPC e))
                         (sk (au-skolem! ix))
                         (bn (car (cadr sk)))
                         (p2 (dk-split! (car sk)))
                         (inner (au-pick p2 (au-head? 'FORALL))))
                    (ew bn)
                    (au-and!
                     (lambda ()
                       (if (eq? (car (dk-goal)) 'IN) (ass)
                           (begin
                             (au-peel-landed!)
                             (let* ((klx (au-goal-klx))
                                    (kk (car klx)) (ll (cadr klx)) (vv (caddr klx)))
                               (dk-split! (au-forward! AU-AD kk))
                               (dk-split! (au-forward! AU-AD ll))
                               (dk-split! (au-forward! wprop kk))
                               (dk-split! (au-forward! wprop ll))
                               (au-forward! wvalf kk)
                               (au-forward! wvalf ll)
                               (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
                               (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) ll)
                               (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) kk)
                               (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) ll)
                               (fact 'fun-apply-type-c wfam 'NN '(FUN RR RR) kk)
                               (fact 'fun-apply-type-c wfam 'NN '(FUN RR RR) ll)
                               (au-have! (forall-guarded 'x_ '(IN x_ RR)
                                        (list 'IMPLIES '(IN x_ (CCINT a b))
                                          (list '<= (list 'abs
                                            (list '- (list (list 'phifam kk) 'x_)
                                                     (list (list 'phifam ll) 'x_))) e)))
                                 (lambda ()
                                   (let* ((zz (au-peel-typed-1! 'RR)))
                                     (au-forward! inner kk ll zz)
                                     (ass))))
                               (let ((con (dk-fact! 'caratheodory-witness-pair-bound
                                            (list 'fam kk) (list 'fam ll)
                                            (list 'phifam kk) (list 'phifam ll)
                                            (list wfam kk) (list wfam ll)
                                            'a 'b tt e)))
                                 (au-forward! con vv)
                                 (ass)))))))))))
            ;; h8
            ;; the binder is `j_', NOT `k_': the antecedent of rr-converges-to-abs
            ;; applies this lambda at its own `k_', and a lambda whose binder
            ;; SHADOWS the enclosing one makes `have!'/`detach!' miss the match.
            (let ((tseq (list 'VNB-LAMBDA 'j_ 'NN (list (list wfam 'j_) tt))))
              (au-have! (list 'IN tseq '(FUN NN RR))
                (lambda ()
                  (dk-lam-t!)
                  (let ((j (cadr (au-peel-1!))))
                    (fact 'fun-apply-type-c wfam 'NN '(FUN RR RR) j)
                    (fact 'fun-apply-type-c (list wfam j) 'RR 'RR tt)
                    (ass))))
              (fact 'fun-apply-type-c 'psi 'RR 'RR tt)
              (let* ((impc (dk-fact! 'rr-converges-to-abs tseq (list 'psi tt)))
                     (ac   (cadr impc)))
                (au-have! ac
                  (lambda ()
                    (let ((e (cadr (au-peel-1!))))
                      (let* ((ix (au-forward! AU-UN e))
                             (sk (au-skolem! ix))
                             (bn (car (cadr sk)))
                             (p2 (dk-split! (car sk)))
                             (inner (au-pick p2 (au-head? 'FORALL))))
                        (ew bn)
                        (au-and!
                         (lambda ()
                           (if (eq? (car (dk-goal)) 'IN) (ass)
                               (let* ((kk (au-peel-typed-1! 'NN)))
                                 (au-beta!)
                                 (au-forward! wvalf kk)
                                 (subst (list '= (list (list wfam kk) tt)
                                                 (list (list 'phifam kk) tt)))
                                 (fact 'fun-apply-type-c 'phifam 'NN '(FUN RR RR) kk)
                                 (fact 'fun-apply-type-c (list 'phifam kk) 'RR 'RR tt)
                                 (fact 'rr-abs-sub-sym (list (list 'phifam kk) tt)
                                                       (list 'psi tt))
                                 (subst (list '= (list 'abs (list '- (list (list 'phifam kk) tt)
                                                                     (list 'psi tt)))
                                                 (list 'abs (list '- (list 'psi tt)
                                                                     (list (list 'phifam kk) tt)))))
                                 (au-forward! inner kk tt)
                                 (ass)))))))))
                (au-detach* impc))
              (fact 'uniform-witness-diff-at AU-FAMC wfam AU-FC
                    (list 'psi tt) 'a 'b tt rho)
              (ass))))))))

(define (au-p16-uniform!)
  (let ((e (cadr (au-peel-1!))))
    (let* ((ix (au-forward! AU-FCUC e))
           (sk (au-skolem! ix))
           (bn (car (cadr sk)))
           (p2 (dk-split! (car sk)))
           (inner (au-pick p2 (au-head? 'FORALL))))
      (ew bn)
      (au-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN) (ass)
             (let* ((__p (au-peel-typed! 'NN 'RR))
                    (kk (car __p))
                    (vv (cadr __p)))
               (dk-split! (dk-landed-1 (lambda ()
                   (mac-h 'ccint-membership (list 'IN vv '(CCINT a b))))))
               (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) kk)
               (fact 'clamp-fixes 'a 'b vv)
               (au-forward! inner kk vv)
               (au-have! (list '= (list (list 'fam kk) vv) (list (list AU-FAMC kk) vv))
                 (lambda ()
                   (au-beta!)
                   (subst (list '= (list 'CLAMP 'a 'b vv) vv))
                   (fact 'fun-apply-type-c (list 'fam kk) 'RR 'RR vv)
                   (crs)))
               (subst (list '= (list (list 'fam kk) vv) (list (list AU-FAMC kk) vv)))
               (ass))))))))

(define (au-p16-antideriv!)
  (mac 'IS-ANTIDERIVATIVE)
  (au-and!
   (lambda ()
     (let ((g2 (dk-goal)))
       (cond
         ((memq (car g2) '(IN <)) (ass))
         ((dk-contains? g2 'IS-CONTINUOUS-AT)
          (let* ((vv (au-peel-typed-1! '(CCINT a b))))
            (au-have! (list 'IN vv 'RR)
              (lambda ()
                (dk-split! (dk-landed-1 (lambda ()
                    (mac-h 'ccint-membership (list 'IN vv '(CCINT a b))))))
                (ass)))
            (au-forward! AU-CONTFORM vv)
            (ass)))
         (else (au-p16-diff!)))))))

(quietly (lambda ()
  (ew AU-FC)
  (au-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond
         ((eq? (car gl) 'IN) (ass))
         ((eq? (car gl) 'IS-ANTIDERIVATIVE) (au-p16-antideriv!))
         (else (au-p16-uniform!))))))))
(qed 'antiderivative-family-uniform-limit)
(topic! 'antiderivative-family-uniform-limit 'analysis)

;;; =====================================================================
;;; L6.  docs/calculus.pdf COR 4.17 -- the antiderivable functions are
;;; closed under uniform limits.
;;; =====================================================================

(sp (make-wff "forall([phifam in fun(nn, fun(rr,rr)), psi in fun(rr,rr), a in rr, b in rr],
   (forall([k_ in nn], is-antiderivable(phifam(k_), a, b))) implies
   (forall([eps], pos-rr(eps) implies
      forsome([n_ in nn], forall([k_ in nn], n_ <= k_ implies
        forall([x_ in rr], x_ in ccint(a,b) implies
          abs(psi(x_) - (phifam(k_))(x_)) <= eps))))) implies
   is-antiderivable(psi, a, b))"))
(quietly (lambda () (au-peel!)))
(quietly (lambda ()
  (let* ((ex   (dk-fact! 'antiderivable-family-normalized 'phifam 'a 'b))
         (sk   (au-skolem! ex))
         (famv (car (cadr sk)))
         (ps   (dk-split! (car sk)))
         (nprp (au-pick ps (au-head? 'FORALL))))
    (fact 'nn-zero-in)
    (dk-split! (au-forward! nprp 0))
    (dk-split! (dk-deepest (lambda ()
        (fact 'antiderivative-endpoints (list famv 0) '(phifam 0) 'a 'b))))
    (let* ((exf (dk-fact! 'antiderivative-family-uniform-limit
                          famv 'phifam 'psi 'a 'b))
           (sk2 (au-skolem! exf))
           (fv  (car (cadr sk2))))
      (dk-split! (car sk2))
      (mac 'IS-ANTIDERIVABLE)
      (ew fv)
      (ass)))))
(qed 'antiderivable-uniform-limit)
(topic! 'antiderivable-uniform-limit 'analysis)
(alias! 'antiderivable-uniform-limit
        "the antiderivable functions are closed under uniform limits")
