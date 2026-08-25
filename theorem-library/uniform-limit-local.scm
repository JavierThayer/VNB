;;; theorem-library/uniform-limit-local.scm -- A UNIFORM LIMIT IS CONTINUOUS AT
;;; A POINT, from uniform convergence on a BALL about that point only.
;;;
;;; WHY, AND WHAT IS DIFFERENT FROM `uniform-limit-continuous'.  The proven
;;; theorem in theorem-library/ascoli-analytic-cores.scm concludes
;;; IS-CONTINUOUS(s, RR-MS, g) on ALL of PTS(s), from CONVERGES-UNIFORMLY(s,
;;; fam, g) -- uniformity on the whole space.  Two things make it unusable for
;;; the calculus arc:
;;;
;;;   * CONVERGES-UNIFORMLY demands a metric SPACE, and [a,b] is not one in this
;;;     tree -- there is no metric subspace structure on CCINT(a,b), and
;;;     building one is a foundational decision several proofs are waiting on.
;;;     So the uniform hypothesis is written out with `abs', as
;;;     uniform-continuity-ccint.scm, ccint-abs-bounded.scm, bernstein-density.scm
;;;     and bernstein-ccint.scm all write theirs.
;;;   * A Caratheodory witness is continuous only AT the point it witnesses, and
;;;     the estimate that makes a family of them uniformly Cauchy is available
;;;     only NEAR that point.  The conclusion therefore has to be
;;;     IS-CONTINUOUS-AT, and the hypothesis has to be local.
;;;
;;; The locality is expressed by a radius `rho' > 0: uniform convergence is
;;; assumed only for the x with |x - t| <= rho, and the delta the proof hands
;;; back is at most rho (`rr-min-pos' on delta_0 and rho), so every point the
;;; eps/delta clause ever looks at is inside the ball where the hypothesis
;;; speaks.  That last step is the only difference from the classical
;;; 3-epsilon argument, which is otherwise transcribed unchanged:
;;;
;;;   |g(t)-g(b)| <= |g(t)-f(t)| + |f(t)-f(b)| + |f(b)-g(b)| <= 3c <= eps
;;;
;;; with f = fam(cap) the single member uniformity buys, and 4c = eps.  The
;;; last inequality needs 0 <= c, which `ineq' will not supply.
;;;
;;; `modulo 0'.
;;;
;;; Loads after metric-continuity (IS-CONTINUOUS-AT), rr-halving
;;; (rr-pos-halvable), rr-order-basics (rr-min-pos, rr-le-ne-lt,
;;; rr-lt-implies-le), rr-abs-basics (rr-abs-closed, rr-abs-triangle-c,
;;; rr-abs-sub-sym, rr-abs-of-nonneg), rr-ms-dist, nn-order-basics (nn-le-refl),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `ulc-' prefix) --------------------

(define (ulc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ulc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (ulc-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

;;; skolemize a FORSOME already in the CONTEXT; returns (LANDED . (EIGENVARS)).
(define (ulc-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

;;; `di' until an ASSUMPTION lands -- never a `di' count.
(define (ulc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "ulc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (ulc-di-landed-1!)
  (let ((new (ulc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ulc-di-landed-1!: expected 1" (map expression->string new)))))

(define (ulc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ulc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (ulc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; (IN x RR) / (0 <= x) off a POS-RR on a SIDE branch -- `mac-h' is destructive
;;; and the folded POS-RR is wanted again below.
(define (ulc-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda () (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))
(define (ulc-nonneg! x)
  (have! (list '<= 0 x)
    (lambda () (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; POS-RR(d) opened into the strict form `rr-min-pos' guards on.  DESTRUCTIVE:
;;; every use of the folded predicate must already have happened.
(define (ulc-pos->lt! d)
  (mac-h 'pos-rr (list 'POS-RR d))
  (dk-split! (list 'AND (list 'IN d 'RR)
                   (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d)))))
  (have! (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))
  (fact 'rr-le-ne-lt 0 d))

;;; halve a positive real: lands POS-RR(h) and h + h = e; returns h.
(define (ulc-halve! e)
  (let ((sk (ulc-skolem! (dk-fact! 'rr-pos-halvable e))))
    (dk-split! (car sk)) (car (cadr sk))))

;;; |a - c| <= |a - b| + |b - c|, landed as a hypothesis; arguments typed first.
(define (ulc-tri! aa bb cc)
  (let ((u (list '- aa bb)) (v (list '- bb cc)) (w (list '- aa cc)))
    (fact 'rr-sub-in-rr aa bb) (fact 'rr-sub-in-rr bb cc) (fact 'rr-sub-in-rr aa cc)
    (have! (list '<= (list 'abs w) (list '+ (list 'abs u) (list 'abs v)))
      (lambda ()
        (have! (list '= w (list '+ u v)) (lambda () (crs)))
        (subst (list '= w (list '+ u v)))
        (fact 'rr-abs-triangle-c u v)
        (ass)))))

(define (ulc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ulc-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (ulc-ineq . forms) (apply ineq (map ulc-idx forms)))

;;; =====================================================================
;;; uniform-limit-continuous-at
;;; =====================================================================

(sp (make-wff "forall([fam in fun(nn, fun(rr,rr)), g in fun(rr,rr), t_ in rr, rho in rr],
     0 < rho implies
     forall([k in nn], is-continuous-at(rr-ms, rr-ms, fam(k), t_)) implies
     forall([eps], pos-rr(eps) implies
       forsome([cp_ in nn], forall([k in nn], cp_ <= k implies
         forall([x_ in rr], abs(x_ - t_) <= rho implies
           abs(g(x_) - (fam(k))(x_)) <= eps)))) implies
     is-continuous-at(rr-ms, rr-ms, g, t_))"))
(quietly (lambda () (ulc-peel!)))
(define ULC-UC (car (dk-asms)))          ; the uniform-convergence eps-clause
(define ULC-CT (cadr (dk-asms)))         ; k |-> IS-CONTINUOUS-AT (fam k) t_
(quietly (lambda ()
  (fact 'rr-is-metric-space) (fact 'rr-zero-in)
  (fact 'rr-lt-implies-le 0 'rho)))

;;; The b-branch: b within delta of t_, hence within rho, hence inside the ball
;;; where the uniform hypothesis speaks -- at BOTH t_ and b, which is where
;;; uniformity (as against pointwise convergence) is spent.
(define (ulc-inner! cp del dl c hh eps kcl du2)
  (let* ((mb (ulc-di-landed-1!)) (b (cadr mb)))
    (have! (list 'IN b 'RR) (lambda () (slot-h 'PTS (list 'IN b '(PTS RR-MS))) (ass)))
    (let ((dstb (car (ulc-di-landed!))))
      (fact 'fun-apply-type-c 'fam 'NN '(FUN RR RR) cp)
      (let ((F (list 'fam cp)))
        (fact 'fun-apply-type-c F 'RR 'RR 't_)
        (fact 'fun-apply-type-c F 'RR 'RR b)
        (fact 'fun-apply-type-c 'g 'RR 'RR 't_)
        (fact 'fun-apply-type-c 'g 'RR 'RR b)
        (fact 'rr-sub-in-rr 't_ b)
        (fact 'rr-abs-closed (list '- 't_ b))
        ;; the abs reading of d(t_,b) <= delta, on a LANE: the DIST form is what
        ;; the continuity clause below is instantiated against, and `mac-h'
        ;; would delete it.
        (have! (list '<= (list 'abs (list '- 't_ b)) dl)
          (lambda () (mac-h 'rr-ms-dist dstb) (ass)))
        (have! (list '<= (list '(DIST RR-MS) 't_ b) del)
          (lambda () (mac 'rr-ms-dist)
                     (ulc-ineq (list '<= (list 'abs (list '- 't_ b)) dl)
                               (list '<= dl del))))
        (mac-h 'rr-ms-dist (ulc-inst! du2 b))
        (fact 'nn-le-refl cp)
        (let ((kk (ulc-inst! kcl cp)))
          (have! (list '<= (list 'abs '(- t_ t_)) 'rho)
            (lambda ()
              (have! '(= (- t_ t_) 0) (lambda () (crs)))
              (subst '(= (- t_ t_) 0))
              (fact 'rr-leq-reflexive 0)
              (fact 'rr-abs-of-nonneg 0)
              (subst '(= (abs 0) 0))
              (ass)))
          (ulc-inst! kk 't_)
          (fact 'rr-abs-sub-sym 't_ b)
          (fact 'rr-sub-in-rr b 't_)
          (fact 'rr-abs-closed (list '- b 't_))
          (have! (list '<= (list 'abs (list '- b 't_)) 'rho)
            (lambda () (ulc-ineq (list '= (list 'abs (list '- 't_ b))
                                         (list 'abs (list '- b 't_)))
                                 (list '<= (list 'abs (list '- 't_ b)) dl)
                                 (list '<= dl 'rho))))
          (ulc-inst! kk b)
          (mac 'rr-ms-dist)
          (let ((gt (list 'g 't_)) (gb (list 'g b))
                (ft (list F 't_)) (fb (list F b)))
            (ulc-tri! gt ft gb)
            (ulc-tri! ft fb gb)
            (fact 'rr-abs-sub-sym fb gb)
            (let ((ab (lambda (u v) (list 'abs (list '- u v)))))
              (ulc-ineq (list '<= (ab gt gb) (list '+ (ab gt ft) (ab ft gb)))
                        (list '<= (ab ft gb) (list '+ (ab ft fb) (ab fb gb)))
                        (list '= (ab fb gb) (ab gb fb))
                        (list '<= (ab gt ft) c)
                        (list '<= (ab gb fb) c)
                        (list '<= (ab ft fb) c)
                        (list '<= 0 c)
                        (list '= (list '+ c c) hh)
                        (list '= (list '+ hh hh) eps)))))))))

(define (ulc-eps!)
  (let* ((me (ulc-di-landed-1!)) (eps (cadr me)))
    (ulc-pos-in-rr! eps) (ulc-nonneg! eps)
    (let* ((hh (ulc-halve! eps)) (c (ulc-halve! hh)))
      (ulc-pos-in-rr! hh) (ulc-nonneg! hh)
      (ulc-pos-in-rr! c) (ulc-nonneg! c)
      (let* ((sk (ulc-skolem! (ulc-inst! ULC-UC c)))
             (cp (car (cadr sk))))
        (dk-split! (car sk))
        (let ((kcl (ulc-find 'kclause
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (dk-contains? a cp) (dk-contains? a 'abs)))))
              (ct1 (ulc-inst! ULC-CT cp)))
          (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at ct1))))
          (let* ((du (ulc-find 'delta-univ
                       (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                        (dk-contains? a 'POS-RR)
                                        (dk-contains? a 'DIST)))))
                 (sk2 (ulc-skolem! (ulc-inst! du c)))
                 (del (car (cadr sk2))))
            (dk-split! (car sk2))
            (let ((du2 (ulc-find 'inner-delta
                         (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                          (dk-contains? a del)
                                          (dk-contains? a 'DIST))))))
              (ulc-pos->lt! del)
              ;; delta := a positive lower bound of delta_0 and rho -- the
              ;; "min of the two", stated existentially, so no MIN appears.
              (let* ((mp (ulc-skolem! (dk-fact! 'rr-min-pos del 'rho)))
                     (dl (car (cadr mp))))
                (dk-split! (car mp))
                (mac-h '< (list '< 0 dl))
                (dk-split! (list 'AND (list '<= 0 dl) (list 'NOT (list '= 0 dl))))
                (ew dl)
                (ulc-and!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'POS-RR)
                       (begin (mac 'pos-rr) (from-context!))
                       (ulc-inner! cp del dl c hh eps kcl du2))))))))))))

(quietly (lambda ()
  (mac 'is-continuous-at)
  (ulc-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
             ((and (eq? (car gl) 'IN) (dk-contains? gl 'PTS)) (slot 'PTS) (ass))
             (else (ulc-eps!))))))))
(qed 'uniform-limit-continuous-at)
(topic! 'uniform-limit-continuous-at 'analysis)
(alias! 'uniform-limit-continuous-at
        "a uniform limit on a ball is continuous at its centre")
(gloss! 'uniform-limit-continuous-at
  "The pointwise form of `uniform-limit-continuous': uniform convergence is
   assumed only on the ball |x - t| <= rho, and the conclusion is continuity AT
   t.  The delta handed back is at most rho, so the eps/delta clause never
   looks outside the ball.  Written with `abs' rather than CONVERGES-UNIFORMLY
   because the latter demands a metric space and [a,b] is not one here.")
