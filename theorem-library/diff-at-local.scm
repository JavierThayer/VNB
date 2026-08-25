;;; theorem-library/diff-at-local.scm -- DIFFERENTIABILITY IS LOCAL, and the
;;; Caratheodory transfer of a POINTWISE LIMIT.
;;;
;;; docs/calculus.pdf Prop 4.16 needs to differentiate a function that is a
;;; limit only on [a,b].  IS-DIFF-AT (theorem-library/differentiation.scm) is
;;; Caratheodory and its identity is GLOBAL --
;;;
;;;     forall x in RR.  f(x) - f(t) = phi(x) * (x - t)
;;;
;;; -- so a witness has to say something about every real, while the data of
;;; such a theorem says nothing outside the interval.  The two theorems here
;;; are the two halves of that gap.
;;;
;;; 1.  diff-at-local.  If psi is continuous at t, psi(t) = L, and the
;;;     Caratheodory identity holds only for |x - t| <= rho, then
;;;     IS-DIFF-AT(f, t, L).  The witness is built by TOTALISING psi with the
;;;     difference quotient:
;;;
;;;        phi(z) = IF |z - t| <= rho THEN psi(z) ELSE (f(z)-f(t)) * recip(z-t)
;;;
;;;     Outside the ball the identity then holds BY CONSTRUCTION (z /= t there,
;;;     since rho > 0, so recip(z-t) is defined and cancels), inside it is the
;;;     hypothesis, and continuity at t is psi's -- the delta is capped at rho,
;;;     so the eps/delta clause never looks outside the ball.  This is the
;;;     content of "differentiability is a local property", which the tree did
;;;     not have; note it is NOT a difference-quotient CHARACTERISATION of the
;;;     derivative (no such bridge exists here and this does not build one) --
;;;     the quotient appears only as filler where the theorem says nothing.
;;;
;;; 2.  diff-at-ptwise-limit.  The Caratheodory-native form of the analytic
;;;     core of Prop 4.16, and much shorter than the notes' route.  The notes
;;;     bound |f_k(t+h) - f_k(t) - h.psi(t)| <= eps|h| and conclude f'(t) =
;;;     psi(t): that is a difference-quotient argument and is not transcribable
;;;     here.  Caratheodory-natively there is no estimate at all.  Given
;;;
;;;        witnesses phifam(k) for fam(k) at t, valid on |x - t| <= rho,
;;;        fam(k)(x) -> f(x)        pointwise on the ball,
;;;        phifam(k)(x) -> phi(x)   pointwise on the ball,
;;;        phi continuous at t,
;;;
;;;     fix x in the ball and let D(k) = fam(k)(x) - fam(k)(t).  By
;;;     `rr-limit-sub' D -> f(x) - f(t); by `rr-limit-scale' -- D(k) being
;;;     phifam(k)(x).(x-t) -- D -> phi(x).(x-t); `rr-limit-unique' identifies
;;;     the two, which IS the Caratheodory identity for phi.  Then (1) finishes.
;;;     Three limit theorems and no epsilon.
;;;
;;; WHAT IS STILL MISSING for Prop 4.16 itself: the MVT estimate that makes the
;;; witness family phifam uniformly Cauchy on [a,b], and the endpoint problem
;;; -- IS-ANTIDERIVATIVE asks for continuity of the antiderivative AT a and AT
;;; b as a map on the LINE, and a function built as a limit on [a,b] alone is
;;; unconstrained just outside it.  Neither is here.
;;;
;;; Both theorems below need no metric subspace structure and mention no
;;; interval: the locality is carried by a radius.
;;;
;;; Loads after seq-limit (rr-limit-sub, rr-limit-scale), differentiation
;;; (IS-DIFF-AT), dominated-convergence (rr-limit-unique), metric-continuity
;;; (IS-CONTINUOUS-AT), rr-order-basics (rr-min-pos, rr-le-ne-lt,
;;; rr-lt-implies-le, rr-recip-closed/-inverse), rr-abs-basics, rr-ms-dist,
;;; fun-apply-type-proof and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `dl-' prefix) ---------------------

(define (dl-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "dl-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (dl-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

(define (dl-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (dl-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "dl-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (dl-di-landed-1!)
  (let ((new (dl-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "dl-di-landed-1!: expected 1" (map expression->string new)))))

(define (dl-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (dl-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (dl-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (dl-pos->lt! d)
  (mac-h 'pos-rr (list 'POS-RR d))
  (dk-split! (list 'AND (list 'IN d 'RR)
                   (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d)))))
  (have! (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))
  (fact 'rr-le-ne-lt 0 d))

(define (dl-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "dl-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (dl-ineq . forms) (apply ineq (map dl-idx forms)))

;;; |u - t_| <= rho for a u the context knows equals t_ up to `crs' -- i.e. the
;;; centre of the ball is in the ball, which needs 0 <= rho.
(define (dl-ball! u)
  (have! (list '<= (list 'abs (list '- u 't_)) 'rho)
    (lambda ()
      (have! (list '= (list '- u 't_) 0) (lambda () (crs)))
      (subst (list '= (list '- u 't_) 0))
      (fact 'rr-leq-reflexive 0)
      (fact 'rr-abs-of-nonneg 0)
      (subst '(= (abs 0) 0))
      (ass))))

;;; =====================================================================
;;; 1.  diff-at-local -- differentiability is a LOCAL property.
;;; =====================================================================

(define dl-phi '(VNB-LAMBDA z_ RR
                  (IF (<= (abs (- z_ t_)) rho)
                      (psi z_)
                      (* (- (f z_) (f t_)) (recip (- z_ t_))))))
(define (dl-if u)
  (list 'IF (list '<= (list 'abs (list '- u 't_)) 'rho)
        (list 'psi u)
        (list '* (list '- (list 'f u) '(f t_)) (list 'recip (list '- u 't_)))))

;;; Outside the ball the argument differs from the centre: |z - t| > rho > 0.
(define (dl-nonzero! w)
  (have! (list 'NOT (list '= w 0))
    (lambda ()
      (di)                                        ; assume (= w 0); goal FALSITY
      (have! (list '<= (list 'abs w) 'rho)
        (lambda ()
          (subst (list '= w 0))
          (fact 'rr-leq-reflexive 0)
          (fact 'rr-abs-of-nonneg 0)
          (subst '(= (abs 0) 0))
          (ass)))
      (ai (list 'NOT (list '<= (list 'abs w) 'rho))))))

;;; phi = psi INSIDE the ball -- one beta and the true branch of the IF.
(define (dl-eq-psi! u)
  (have! (list '= (list dl-phi u) (list 'psi u))
    (lambda ()
      (fact 'fun-apply-type-c 'psi 'RR 'RR u)
      (lam-b)
      (for-each (lambda (l) (dk-focus! l)
                  (if (eq? (car (dk-goal)) '<=) (ass)
                      (begin (subst (list '= (dl-if u) (list 'psi u))) (rfl))))
                (dk-opened (lambda () (if-true (dl-if u))))))))

(sp (make-wff "forall([f in fun(rr,rr), psi in fun(rr,rr), t_ in rr, lv in rr, rho in rr],
   0 < rho implies
   is-continuous-at(rr-ms, rr-ms, psi, t_) implies
   psi(t_) = lv implies
   forall([x_ in rr], abs(x_ - t_) <= rho implies
      f(x_) - f(t_) = psi(x_) * (x_ - t_)) implies
   is-diff-at(f, t_, lv))"))
(quietly (lambda () (dl-peel!)))
(define dl-hyp (dl-find 'ptwise (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                 (dk-contains? a 'psi)
                                                 (dk-contains? a 'abs)))))
(quietly (lambda () (fact 'rr-zero-in) (fact 'rr-lt-implies-le 0 'rho)))

;;; (a)  phi is a function RR -> RR.  The false branch is where `recip' has to
;;; be defined, and it is exactly where the argument is off the centre.
(quietly (lambda ()
(have! (list 'IN dl-phi '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((z (cadr (dl-di-landed-1!)))
           (w (list '- z 't_)))
      (use-em (list '<= (list 'abs w) 'rho)
        (lambda ()
          (for-each (lambda (l) (dk-focus! l)
                      (if (eq? (car (dk-goal)) '<=) (ass)
                          (begin (subst (list '= (dl-if z) (list 'psi z)))
                                 (fact 'fun-apply-type-c 'psi 'RR 'RR z)
                                 (ass))))
                    (dk-opened (lambda () (if-true (dl-if z))))))
        (lambda ()
          (for-each (lambda (l) (dk-focus! l)
                      (if (eq? (car (dk-goal)) 'NOT) (ass)
                          (begin
                            (subst (list '= (dl-if z)
                                         (list '* (list '- (list 'f z) '(f t_))
                                               (list 'recip w))))
                            (dl-nonzero! w)
                            (fact 'fun-apply-type-c 'f 'RR 'RR z)
                            (fact 'fun-apply-type-c 'f 'RR 'RR 't_)
                            (fact 'rr-sub-in-rr (list 'f z) '(f t_))
                            (fact 'rr-sub-in-rr z 't_)
                            (have! (list 'AND (list 'IN w 'RR) (list 'NOT (list '= w 0))))
                            (fact 'rr-recip-closed w)
                            (have! (list 'AND (list 'IN (list '- (list 'f z) '(f t_)) 'RR)
                                         (list 'IN (list 'recip w) 'RR)))
                            (fact 'rr-mul-closed (list '- (list 'f z) '(f t_))
                                  (list 'recip w))
                            (ass))))
                    (dk-opened (lambda () (if-false (dl-if z))))))))))
;;; (b)  phi(t) = psi(t) = L.
(dl-ball! 't_)
(dl-eq-psi! 't_)))

;;; (c)  phi is continuous at t: it AGREES with psi on the ball, and the delta
;;; is capped at rho.
(define (dl-eps! du)
  (let* ((me (dl-di-landed-1!)) (eps (cadr me)))
    (let* ((sk (dl-skolem! (dl-inst! du eps)))
           (d0 (car (cadr sk))))
      (dk-split! (car sk))
      (let ((inner (dl-find 'inner (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                    (dk-contains? a d0)
                                                    (dk-contains? a 'DIST))))))
        (dl-pos->lt! d0)
        (let* ((mp (dl-skolem! (dk-fact! 'rr-min-pos d0 'rho)))
               (dl (car (cadr mp))))
          (dk-split! (car mp))
          (mac-h '< (list '< 0 dl))
          (dk-split! (list 'AND (list '<= 0 dl) (list 'NOT (list '= 0 dl))))
          (ew dl)
          (dl-and!
           (lambda ()
             (if (eq? (car (dk-goal)) 'POS-RR)
                 (begin (mac 'pos-rr) (from-context!))
                 (let* ((mb (dl-di-landed-1!)) (b (cadr mb)))
                   (have! (list 'IN b 'RR)
                     (lambda () (slot-h 'PTS (list 'IN b '(PTS RR-MS))) (ass)))
                   (let ((dstb (car (dl-di-landed!))))
                     (fact 'rr-sub-in-rr 't_ b)
                     (fact 'rr-abs-closed (list '- 't_ b))
                     (have! (list '<= (list 'abs (list '- 't_ b)) dl)
                       (lambda () (mac-h 'rr-ms-dist dstb) (ass)))
                     (have! (list '<= (list '(DIST RR-MS) 't_ b) d0)
                       (lambda () (mac 'rr-ms-dist)
                                  (dl-ineq (list '<= (list 'abs (list '- 't_ b)) dl)
                                           (list '<= dl d0))))
                     (dl-inst! inner b)
                     (fact 'rr-abs-sub-sym 't_ b)
                     (fact 'rr-sub-in-rr b 't_)
                     (fact 'rr-abs-closed (list '- b 't_))
                     (have! (list '<= (list 'abs (list '- b 't_)) 'rho)
                       (lambda () (dl-ineq (list '= (list 'abs (list '- 't_ b))
                                                   (list 'abs (list '- b 't_)))
                                           (list '<= (list 'abs (list '- 't_ b)) dl)
                                           (list '<= dl 'rho))))
                     (dl-eq-psi! b)
                     (subst (list '= (list dl-phi 't_) '(psi t_)))
                     (subst (list '= (list dl-phi b) (list 'psi b)))
                     (ass)))))))))))

(have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS dl-phi 't_)
  (lambda ()
    (quietly (lambda ()
      (fact 'rr-is-metric-space)
      (dk-split! (dk-landed-1 (lambda ()
         (mac-h 'is-continuous-at '(IS-CONTINUOUS-AT RR-MS RR-MS psi t_)))))))
    (let ((du (dl-find 'delta-univ (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                    (dk-contains? a 'POS-RR)
                                                    (dk-contains? a 'DIST))))))
      (quietly (lambda ()
        (mac 'is-continuous-at)
        (dl-and!
         (lambda ()
           (let ((gl (dk-goal)))
             (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
                   ((and (eq? (car gl) 'IN) (dk-contains? gl 'PTS)) (slot 'PTS) (ass))
                   (else (dl-eps! du)))))))))))

;;; (d)  the Caratheodory identity, everywhere: the hypothesis inside the ball,
;;; the cancellation u.recip(w).w = u outside it.
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
        (list '= '(- (f x_) (f t_)) (list '* (list dl-phi 'x_) '(- x_ t_)))))
  (lambda ()
    (quietly (lambda ()
      (dl-di-landed-1!)
      (fact 'fun-apply-type-c 'f 'RR 'RR 'x_)
      (fact 'fun-apply-type-c 'f 'RR 'RR 't_)
      (fact 'rr-sub-in-rr '(f x_) '(f t_))
      (fact 'rr-sub-in-rr 'x_ 't_)))
    (use-em '(<= (abs (- x_ t_)) rho)
      (lambda ()
        (quietly (lambda ()
          (dl-eq-psi! 'x_)
          (subst (list '= (list dl-phi 'x_) '(psi x_)))
          (dl-inst! dl-hyp 'x_)
          (ass))))
      (lambda ()
        (quietly (lambda ()
          (lam-b)
          (for-each
           (lambda (l)
             (dk-focus! l)
             (if (eq? (car (dk-goal)) 'NOT)
                 (ass)
                 (let* ((w '(- x_ t_))
                        (u '(- (f x_) (f t_)))
                        (r '(recip (- x_ t_))))
                   (subst (list '= (dl-if 'x_) (list '* u r)))
                   (dl-nonzero! w)
                   (have! (list 'AND (list 'IN w 'RR) (list 'NOT (list '= w 0))))
                   (fact 'rr-recip-inverse w)
                   (fact 'rr-recip-closed w)
                   (have! (list '= (list '* (list '* u r) w) (list '* u (list '* w r)))
                          (lambda () (crs)))
                   (subst (list '= (list '* (list '* u r) w) (list '* u (list '* w r))))
                   (subst (list '= (list '* w r) 1))
                   (crs))))
           (dk-opened (lambda () (if-false (dl-if 'x_)))))))))))

(quietly (lambda ()
 (mac 'is-diff-at)
 (dl-and!
  (lambda ()
    (let ((gl (dk-goal)))
      (if (eq? (car gl) 'IN)
          (ass)
          (begin
            (ew dl-phi)
            (dl-and!
             (lambda ()
               (let ((g2 (dk-goal)))
                 (if (and (eq? (car g2) '=) (not (eq? (cadr g2) 'lv)))
                     (begin (subst (list '= (list dl-phi 't_) '(psi t_))) (ass))
                     (ass))))))))))))
(qed 'diff-at-local)
(topic! 'diff-at-local 'analysis)
(alias! 'diff-at-local "differentiability is a local property")
(gloss! 'diff-at-local
  "IS-DIFF-AT's Caratheodory identity quantifies over all of RR, but a witness
   is determined only near the point.  Given psi continuous at t with psi(t)=L
   and the identity for |x - t| <= rho, the witness that totalises psi by the
   difference quotient outside the ball works everywhere, so f is
   differentiable at t with derivative L.  This is what lets a function known
   only on an interval be differentiated there.")

;;; =====================================================================
;;; 2.  diff-at-ptwise-limit -- the Caratheodory core of Prop 4.16.
;;; =====================================================================

(define (dq-seq body) (list 'VNB-LAMBDA 'k_ 'NN body))
(define dq-A (dq-seq '((fam k_) x_)))
(define dq-B (dq-seq '((fam k_) t_)))
(define dq-D (dq-seq '(- ((fam k_) x_) ((fam k_) t_))))
(define dq-P (dq-seq '((phifam k_) x_)))
(define (dq-app! F k arg)
  (fact 'fun-apply-type-c F 'NN '(FUN RR RR) k)
  (fact 'fun-apply-type-c (list F k) 'RR 'RR arg))
(define (dq-type! lam thunk)
  (have! (list 'IN lam '(FUN NN RR))
    (lambda ()
      (dk-lam-t!)
      (let ((k (cadr (dl-di-landed-1!))))
        (thunk k)
        (ass)))))
(define (dq-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred dq-has-redex? e))))
(define (dq-beta!)
  (let lp ((n 0))
    (if (and (< n 6) (dq-has-redex? (dk-goal)))
        (begin (lam-b) (lp (+ n 1))))))

(sp (make-wff "forall([fam in fun(nn, fun(rr,rr)), phifam in fun(nn, fun(rr,rr)),
                       f in fun(rr,rr), phi in fun(rr,rr), t_ in rr, rho in rr],
   0 < rho implies
   is-continuous-at(rr-ms, rr-ms, phi, t_) implies
   forall([k in nn], forall([y_ in rr], abs(y_ - t_) <= rho implies
      (fam(k))(y_) - (fam(k))(t_) = ((phifam(k))(y_)) * (y_ - t_))) implies
   forall([y_ in rr], abs(y_ - t_) <= rho implies
      converges-to(rr-ms, vnb-lambda(k_, nn, (fam(k_))(y_)), f(y_))) implies
   forall([y_ in rr], abs(y_ - t_) <= rho implies
      converges-to(rr-ms, vnb-lambda(k_, nn, (phifam(k_))(y_)), phi(y_))) implies
   is-diff-at(f, t_, phi(t_)))"))
(quietly (lambda () (dl-peel!)))
(define dq-C5 (car (dk-asms)))          ; phifam converges pointwise on the ball
(define dq-C4 (cadr (dk-asms)))         ; fam converges pointwise on the ball
(define dq-C3 (caddr (dk-asms)))        ; the per-k Caratheodory identity
(quietly (lambda ()
  (fact 'rr-zero-in) (fact 'rr-lt-implies-le 0 'rho)
  (dl-ball! 't_)
  (fact 'fun-apply-type-c 'phi 'RR 'RR 't_)
  (fact 'fun-apply-type-c 'f 'RR 'RR 't_)
  (dl-inst! dq-C4 't_)
  (have! '(= (phi t_) (phi t_)) (lambda () (rfl)))))

(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
        (list 'IMPLIES '(<= (abs (- x_ t_)) rho)
              (list '= '(- (f x_) (f t_)) '(* (phi x_) (- x_ t_))))))
  (lambda ()
    (quietly (lambda ()
      (dl-di-landed-1!) (dl-di-landed-1!)
      (fact 'fun-apply-type-c 'f 'RR 'RR 'x_)
      (fact 'fun-apply-type-c 'phi 'RR 'RR 'x_)
      (fact 'rr-sub-in-rr 'x_ 't_)
      (fact 'rr-sub-in-rr '(f x_) '(f t_))
      (have! '(AND (IN (phi x_) RR) (IN (- x_ t_) RR)))
      (fact 'rr-mul-closed '(phi x_) '(- x_ t_))
      (dq-type! dq-A (lambda (k) (dq-app! 'fam k 'x_)))
      (dq-type! dq-B (lambda (k) (dq-app! 'fam k 't_)))
      (dq-type! dq-P (lambda (k) (dq-app! 'phifam k 'x_)))
      (dq-type! dq-D (lambda (k)
                       (dq-app! 'fam k 'x_) (dq-app! 'fam k 't_)
                       (fact 'rr-sub-in-rr (list (list 'fam k) 'x_)
                                           (list (list 'fam k) 't_))))
      (dl-inst! dq-C4 'x_)
      (dl-inst! dq-C5 'x_)
      ;; D(j) = A(j) - B(j): rr-limit-sub gives D -> f(x) - f(t)
      (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
               (list '= (list dq-D 'j_) (list '- (list dq-A 'j_) (list dq-B 'j_)))))
        (lambda ()
          (dl-di-landed-1!)
          (dq-app! 'fam 'j_ 'x_) (dq-app! 'fam 'j_ 't_)
          (fact 'rr-sub-in-rr '((fam j_) x_) '((fam j_) t_))
          (dq-beta!)
          (rfl)))
      (fact 'rr-limit-sub dq-A dq-B dq-D '(f x_) '(f t_))
      ;; ... and D(j) = P(j).(x-t): rr-limit-scale gives D -> phi(x).(x-t)
      (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
               (list '= (list dq-D 'j_) (list '* (list dq-P 'j_) '(- x_ t_)))))
        (lambda ()
          (dl-di-landed-1!)
          (dq-app! 'fam 'j_ 'x_) (dq-app! 'fam 'j_ 't_)
          (dq-app! 'phifam 'j_ 'x_)
          (dq-beta!)
          (dl-inst! (dl-inst! dq-C3 'j_) 'x_)
          (ass)))
      (fact 'rr-limit-scale '(- x_ t_) dq-P dq-D '(phi x_))
      (fact 'rr-limit-unique dq-D '(- (f x_) (f t_)) '(* (phi x_) (- x_ t_)))
      (ass)))))
(quietly (lambda () (fact 'diff-at-local 'f 'phi 't_ '(phi t_) 'rho) (ass)))
(qed 'diff-at-ptwise-limit)
(topic! 'diff-at-ptwise-limit 'analysis)
(alias! 'diff-at-ptwise-limit
        "the pointwise limit of maps with converging Caratheodory witnesses is differentiable")
(gloss! 'diff-at-ptwise-limit
  "Prop 4.16's analytic core, Caratheodory-natively.  If fam(k) has witness
   phifam(k) at t on a ball, fam converges pointwise to f there and phifam
   pointwise to phi with phi continuous at t, then f is differentiable at t
   with derivative phi(t).  The proof is rr-limit-sub, rr-limit-scale and
   rr-limit-unique on the single sequence k |-> fam(k)(x) - fam(k)(t), plus
   diff-at-local; there is no epsilon and no difference quotient.")
