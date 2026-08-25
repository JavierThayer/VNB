;;; rr-null-scale.scm -- a NONNEGATIVE CONSTANT MULTIPLE OF A NULL SEQUENCE IS
;;; NULL, proven, together with the eps/delta lemma that carries it.
;;;
;;;   rr-scale-eps    0 <= c, eps > 0  =>  some d > 0 has  c*t <= eps  for every
;;;                   t in [0, d].
;;;   rr-null-scale   0 <= c, f -> 0, h(j) = c*f(j) pointwise  =>  h -> 0.
;;;
;;; The tree had no scalar multiple of a limit at all: `rr-null-sum'
;;; (dominated-convergence.scm) adds two null sequences and nothing multiplies
;;; one by a constant.  It is the missing half of the linearity that the
;;; coordinatewise half of `product-convergence-coordinatewise'
;;; (structure-library/product-metric.scm) needs, where the constant is the
;;; weight w(n) and the null sequence is  j |-> rho_n(seq(j)(n), L(n)).
;;;
;;; TWO DESIGN POINTS.
;;;
;;; 1.  THE DELTA IS PACKAGED, NOT INLINED.  `rr-scale-eps' is the whole
;;;     reciprocal argument -- d = eps/(1+c) -- stated as an existential, so the
;;;     eps-branch of the convergence proof cites it once and never mentions
;;;     `recip'.  The denominator is 1+c and not c precisely so that the lemma
;;;     needs no case split at c = 0: 1+c is positive for every c >= 0, and the
;;;     estimate c*d = eps*c/(1+c) <= eps holds because c <= 1+c.
;;;
;;; 2.  THE CONCLUSION IS IN TRANSFER FORM, for the reason `rr-null-sum' is:
;;;     the theorem concludes about any h agreeing pointwise with c*f, not about
;;;     the literal term (VNB-LAMBDA j_ NN (* c (f j_))), so a caller whose
;;;     sequence arrived some other way can still use it without a
;;;     beta-reduction under a binder.
;;;
;;; NO MULTIPLICATIVE ORDER LEMMA IS CITED.  `rr-mul-le-right' /
;;; `rr-le-scale-nonneg-right' (two names for one statement, both asserted
;;; `well-known') would each have done the monotonicity step; instead it is
;;; derived in place from `rr-leq-mul-nonneg', which is PRIMITIVE
;;; (number-systems.scm): 0 <= (b-a) and 0 <= c give 0 <= (b-a)*c, `crs'
;;; rewrites that to 0 <= b*c - a*c, and `ineq' reads the two products as
;;; atoms.  Both theorems here are therefore `modulo 0'.
;;;
;;; Loads after theorem-library/dominated-convergence (rr-ms-dist,
;;; fun-apply-type-proof, rr-abs-basics, order-predicates, rr-recip-order).

;;; ---- file-local driver helpers (the `ns-' prefix) --------------------

(define (ns-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ns-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (ns-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ns-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (ns-ineq . forms) (apply ineq (map ns-idx forms)))

(define (ns-and2! a b) (have! (list 'AND a b) (lambda () (ns-and! (lambda () (ass))))))

;;; a ring identity, cut and then used to rewrite the goal
(define (ns-eq! e) (have! e (lambda () (crs))) (subst e))

;;; 0 < 1 + t  and  1 + t /= 0, from 0 <= t.  NOT by `contra': that tactic
;;; loads with the copilot, far below theorem-library, so no library proof can
;;; reach it.  The route through 0 < 1 (rr-zero-lt-one) and rr-lt-le-trans uses
;;; only what is loaded here.
(define (ns-one-plus! t)
  (let ((one+t (list '+ 1 t)))
    (have! (list '<= 1 one+t) (lambda () (ns-ineq (list '<= 0 t))))
    (ns-and2! '(< 0 1) (list '<= 1 one+t))
    (fact 'rr-lt-le-trans 0 1 one+t)
    (fact 'rr-pos-ne-zero one+t)))

;;; The two conjuncts of a context (< a b), landed WITHOUT destroying it:
;;; `mac-h' replaces the assumption it unfolds, and the strict form is still
;;; wanted (rr-mul-pos detaches against `0 < x', not against its conjuncts).
(define (ns-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (have! part (lambda ()
                     (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                (lambda (f) (eq? (car f) 'AND))))
                     (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

(define (ns-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

(define (ns-fvs forms) (apply append (map free-vars forms)))
(define (ns-skolem! ex)
  (let* ((fv0 (ns-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (ns-fvs (dk-asms)))))
      (if (null? fresh) (error "ns-skolem!: nothing appeared" ex) (car fresh)))))

(define (ns-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ns-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `di' until an ASSUMPTION lands (an unguarded universal lands nothing).
(define (ns-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "ns-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (ns-di-landed-1!)
  (let ((new (ns-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "ns-di-landed-1!: expected 1" (map expression->string new)))))

;;; =====================================================================
;;; L1.  rr-scale-eps -- the eps/delta packaging of the reciprocal.
;;;
;;;   0 <= c,  eps > 0   =>   some d > 0 with  c*t <= eps  for all t in [0,d].
;;;
;;; Witness d = eps * recip(1+c).  The estimate is
;;;   c*d = eps - eps*recip(1+c) <= eps,
;;; read off (1+c)*recip(1+c) = 1 by `crs' and closed by `ineq' over the two
;;; products as atoms.
;;; =====================================================================

(define ns-r '(recip (+ 1 c)))
(define ns-d (list '* 'eps ns-r))

(sp (make-wff "forall([c in rr, eps in rr], 0 <= c implies pos-rr(eps) implies
   forsome([d], pos-rr(d) and forall([t in rr], 0 <= t implies t <= d implies c * t <= eps)))"))
(di)(di)(di)
(dk-split! (dk-landed-find (lambda () (mac-h 'pos-rr '(POS-RR eps)))
                           (lambda (f) (eq? (car f) 'AND))))
;; 1 + c is a nonzero, positive real
(fact 'rr-one-in)
(ns-and2! '(IN 1 RR) '(IN c RR))
(fact 'rr-add-closed 1 'c)
(fact 'rr-zero-in)
(fact 'rr-zero-lt-one)
(ns-one-plus! 'c)
;; ... so recip(1+c) exists, is positive, and inverts it
(ns-and2! '(IN (+ 1 c) RR) '(NOT (= (+ 1 c) 0)))
(fact 'rr-recip-closed '(+ 1 c))
(fact 'rr-recip-inverse '(+ 1 c))
(fact 'rr-recip-pos '(+ 1 c))
(ns-from-lt! 0 ns-r)
;; ... and d = eps * recip(1+c) is a positive real
(ns-and2! (list 'IN 'eps 'RR) (list 'IN ns-r 'RR))
(fact 'rr-mul-closed 'eps ns-r)
(ns-and2! '(<= 0 eps) '(NOT (= 0 eps)))
(fact 'rr-le-ne-lt 0 'eps)
(fact 'rr-mul-pos 'eps ns-r)
(ns-from-lt! 0 ns-d)
(ew ns-d)
(ns-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'POS-RR)
            (mac 'pos-rr)
            (ns-and! (lambda () (ass))))
           (else
            (di)(di)(di)
            ;; t*c <= d*c, from 0 <= (d-t)*c
            (ns-and2! (list 'IN 't 'RR) (list 'IN 'c 'RR))
            (fact 'rr-mul-closed 't 'c)
            (ns-and2! (list 'IN ns-d 'RR) (list 'IN 'c 'RR))
            (fact 'rr-mul-closed ns-d 'c)
            (fact 'rr-sub-in-rr ns-d 't)
            (have! (list '<= 0 (list '- ns-d 't))
                   (lambda () (ns-ineq (list '<= 't ns-d))))
            (ns-and2! (list 'IN (list '- ns-d 't) 'RR) '(IN c RR))
            (ns-and2! (list '<= 0 (list '- ns-d 't)) '(<= 0 c))
            (fact 'rr-leq-mul-nonneg (list '- ns-d 't) 'c)
            (have! (list '<= 0 (list '- (list '* ns-d 'c) (list '* 't 'c)))
              (lambda ()
                (ns-eq! (list '= (list '- (list '* ns-d 'c) (list '* 't 'c))
                                 (list '* (list '- ns-d 't) 'c)))
                (ass)))
            (have! (list '<= (list '* 't 'c) (list '* ns-d 'c))
              (lambda () (ns-ineq (list '<= 0 (list '- (list '* ns-d 'c) (list '* 't 'c))))))
            ;; d + d*c = eps, which is (1+c)*recip(1+c) = 1 scaled by eps
            (have! (list '= (list '+ ns-d (list '* ns-d 'c)) 'eps)
              (lambda ()
                (ns-eq! (list '= (list '+ ns-d (list '* ns-d 'c))
                                 (list '* 'eps (list '* (list '+ 1 'c) ns-r))))
                (subst (list '= (list '* (list '+ 1 'c) ns-r) 1))
                (crs)))
            (ns-and2! '(<= 0 eps) (list '<= 0 ns-r))
            (fact 'rr-leq-mul-nonneg 'eps ns-r)
            (ns-eq! (list '= (list '* 'c 't) (list '* 't 'c)))
            (ns-ineq (list '<= (list '* 't 'c) (list '* ns-d 'c))
                     (list '= (list '+ ns-d (list '* ns-d 'c)) 'eps)
                     (list '<= 0 ns-d)))))))
(qed 'rr-scale-eps)
(topic! 'rr-scale-eps 'analysis)
(alias! 'rr-scale-eps "the eps/delta bound for a nonnegative scalar"
        "for c >= 0 and eps > 0 some d > 0 has c*t <= eps throughout [0,d]")

;;; =====================================================================
;;; L2.  rr-null-scale -- c * (null sequence) is null, in TRANSFER form.
;;; =====================================================================

(sp (make-wff "forall([c in rr, f in fun(nn,rr), h in fun(nn,rr)],
     0 <= c implies converges-to(rr-ms, f, 0) implies
     forall([j_ in nn], h(j_) = c * f(j_)) implies
     converges-to(rr-ms, h, 0))"))
(di)(di)(di)(di)
(define ns-pt (ns-find 'pointwise
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO RR-MS f 0)))
                           (lambda (a) (eq? (car a) 'AND))))
(define ns-tf (ns-find 'ftail
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'f)
                                 (dk-contains? a 'POS-RR)))))
(fact 'rr-zero-in)

;;; the index branch: n_ at or beyond the threshold the f-tail supplied
(define (ns-index! nsd inner innerf)
  (let ((n_ (cadr (ns-di-landed-1!))))
    (ns-di-landed!)                                   ; bigN <= n_
    (inst+ innerf n_)
    (inst+ ns-pt n_)
    (fact 'fun-apply-type-c 'f 'NN 'RR n_)
    (fact 'fun-apply-type-c 'h 'NN 'RR n_)
    (let* ((fn (list 'f n_)) (hn (list 'h n_)) (u (list '- fn 0)))
      ;; rr-ms-dist is GUARDED: the arguments are typed above, never below.
      (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) fn 0) nsd))
      (mac 'rr-ms-dist)
      (subst (list '= hn (list '* 'c fn)))
      ;; keep everything in `- 0' form, so the f-bound applies verbatim
      (ns-eq! (list '= (list '- (list '* 'c fn) 0) (list '* 'c u)))
      (fact 'rr-sub-in-rr fn 0)
      (ns-and2! '(IN c RR) (list 'IN u 'RR))
      (fact 'rr-abs-mult 'c u)
      (subst (list '= (list 'abs (list '* 'c u)) (list '* (list 'abs 'c) (list 'abs u))))
      (fact 'rr-abs-of-nonneg 'c)
      (subst (list '= (list 'abs 'c) 'c))
      (fact 'rr-abs-closed u)
      (fact 'rr-abs-nonneg u)
      (inst+ inner (list 'abs u))
      (ass))))

(define (ns-eps-branch!)
  (let* ((eps (cadr (ns-di-landed-1!))))
    (ns-pos-in-rr! eps)
    (let* ((dex   (dk-deepest (lambda () (fact 'rr-scale-eps 'c eps))))
           (nsd   (ns-skolem! dex))
           (inner (ns-find 'scaleinner
                    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                     (dk-contains? a nsd) (dk-contains? a '*)))))
           (nex   (dk-deepest (lambda () (inst+ ns-tf nsd))))
           (bigN  (ns-skolem! nex))
           ;; discriminate the inner eps-N clause on its THRESHOLD, not its shape
           (innerf (ns-find 'ftailinner
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (let ((b (caddr a)))
                                        (and (pair? b) (eq? (car b) 'IMPLIES)
                                             (dk-contains? (caddr b) bigN))))))))
      (ew bigN)
      (ns-and! (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (ns-index! nsd inner innerf)))))))

(mac 'converges-to)
(ns-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else (ns-eps-branch!))))))
(qed 'rr-null-scale)
(topic! 'rr-null-scale 'analysis)
(alias! 'rr-null-scale "a constant multiple of a null sequence is null")
