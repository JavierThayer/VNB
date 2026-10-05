;;; metric-connected-laws.scm -- A LOCALLY CONSTANT FUNCTION ON A CONNECTED SET IS
;;; CONSTANT.  Agent CA-5 of week 3 of the October roadmap, 2026-10-04.
;;; Definition: structure-library/metric-connected.scm (IS-CONNECTED, new this batch).
;;;
;;;  (1) connected-locally-constant   s a metric space, A connected in s, f locally
;;;      constant on A (every x of A has a ball B(x, r) on whose points of A f takes the
;;;      value f(x)): f takes one value on A.  This is the step "any continuous function
;;;      which takes only integer values is constant on connected components" of the
;;;      notes' proof of Proposition 3.27, with "continuous and integer-valued" replaced
;;;      by what it is used for, "locally constant"; the winding number is shown locally
;;;      constant directly (winding-number-components.scm).
;;;
;;; THE PROOF.  Fix p in A.  U (resp. V) is the set of points w of s lying in some ball
;;; B(z, e) with z in A, f constant on the points of A in B(z, e), and f(z) = f(p)
;;; (resp. f(z) /= f(p)).  Both are open (a ball is open, `ball-is-open'), A is covered
;;; (the ball of local constancy about each point), no point of A is in both (it would
;;; carry f(p) and not f(p)), and p is in U; connectedness says A misses V, so every q of
;;; A lies in U and f(q) = f(p).  The two sets are SEPs over PTS(s), so no union of
;;; balls (BIG-UNION over a family chosen point by point) is formed.
;;;
;;; STATEMENT CHECKS.  f is any term applied to the points of A (a function symbol or a
;;; lambda); the hypothesis states f(y) = f(x) strictly, which also makes f defined on A
;;; (the instance y = x).  A may be empty (the conclusion is then vacuous).
;;; BINDERS mca_ (the set), mcx_ mcy_ mcr_ (the hypothesis), mcp_ mcq_ (the conclusion),
;;; mcw_ mcz_ mce_ (the two SEPs); no other body binds an mc?_ name of these.
;;; Helper prefix mcn-.  NOTHING asserted; no definition here.
;;; LOAD WINDOW: lo = theorem-library/ball-is-open and rake-balls (ball-membership,
;;; ball-center-in, ball-is-set); structure-library/metric-connected before it.
;;; Tactics: the early kit only.


(define (mcn-head g) (and (pair? g) (car g)))
(define (mcn-kp! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply keep fs)
    (if (not (sequent-node-grounded? node)) (prop))))
(define (mcn-lcf y r)
  (list 'FORALL 'mcy_ (list 'IMPLIES '(IN mcy_ mca_)
    (list 'IMPLIES (list 'IN 'mcy_ (list 'BALL 's y r)) (list '= '(f mcy_) (list 'f y))))))
;;; the two sets: SIDE is (= (f mcz_) (f p)) or its negation
(define (mcn-side-u z) (list '= (list 'f z) '(f mcp_)))
(define (mcn-side-v z) (list 'NOT (list '= (list 'f z) '(f mcp_))))
(define (mcn-set side)
  (list 'SEP 'mcw_ '(PTS s)
    (list 'FORSOME 'mcz_ (list 'AND '(IN mcz_ mca_) (list 'AND (side 'mcz_)
      (list 'FORSOME 'mce_ (list 'AND '(POS-RR mce_) (list 'AND '(IN mcw_ (BALL s mcz_ mce_))
        (mcn-lcf 'mcz_ 'mce_)))))))))
(define mcn-u (mcn-set mcn-side-u))
(define mcn-v (mcn-set mcn-side-v))

;;; e > 0 as the triple ball-center-in and ball-is-open want
(define (mcn-pos3! e)
  (let ((cj (list 'AND (list 'IN e 'RR) (list 'AND (list '<= 0 e) (list 'NOT (list '= 0 e))))))
    (if (not (dk-asm? cj))
        (dk-have! cj
          (lambda ()
            (fact 'rr-pos-rr-in-rr e)
            (fact 'rr-lt-of-pos-rr e)
            (dk-conj-close!
              (lambda ()
                (let ((g (dk-goal)))
                  (cond ((dk-asm? g) (ass))
                        ((eq? (mcn-head g) '<=) (dk-ineq! (list '< 0 e)))
                        (#t (di) (dk-absurd! (list 'IN e 'RR) (list '= 0 e) (list '< 0 e))))))))))
    cj))

;;; t in PTS(s), z in A, (SIDE z), POS-RR e, t in BALL(s, z, e), LCF(z, e) in context:
;;; t is in the set of SIDE
(define (mcn-in-set! t z e side)
  (let ((st (mcn-set side)))
    (dk-have! (list 'IN t st)
      (lambda ()
        (in-sep! (lambda ()
                   (ew z)
                   (dk-conj-close!
                     (lambda ()
                       (if (eq? (mcn-head (dk-goal)) 'FORSOME)
                           (begin (ew e) (dk-conj-close! dk-ass!))
                           (dk-ass!))))))))))

;;; (IN t SET-of-SIDE), t in A in context: land (= (f t) (f z)) and (SIDE z) for the
;;; witness z, inside a lane proving CLAIM with BODY (a procedure of z)
(define (mcn-open-set! t side body)
  (let ((st (mcn-set side)))
    (sep-me (list 'IN t st))
    (dk-split-all!)
    (let* ((z (dk-skolem! (dk-pick (lambda (fm) (and (eq? (mcn-head fm) 'FORSOME) (eq? (cadr fm) 'mcz_)))
                                   "the centre witness")))
           (e (dk-skolem! (dk-pick (lambda (fm) (and (eq? (mcn-head fm) 'FORSOME) (eq? (cadr fm) 'mce_)))
                                   "the radius witness"))))
      (dk-split-all!)
      (body z e))))

(sp (make-wff '(FORALL s (FORALL mca_ (IMPLIES (IS-CONNECTED s mca_)
  (FORALL f (IMPLIES (FORALL mcx_ (IMPLIES (IN mcx_ mca_)
                       (FORSOME mcr_ (AND (POS-RR mcr_)
                         (FORALL mcy_ (IMPLIES (IN mcy_ mca_)
                           (IMPLIES (IN mcy_ (BALL s mcx_ mcr_)) (= (f mcy_) (f mcx_)))))))))
    (FORALL mcp_ (IMPLIES (IN mcp_ mca_) (FORALL mcq_ (IMPLIES (IN mcq_ mca_)
      (= (f mcp_) (f mcq_)))))))))))))
(dk-peel!)
(define mcn-lc (dk-pick (lambda (fm) (and (eq? (mcn-head fm) 'FORALL) (eq? (cadr fm) 'mcx_))) "local constancy"))
(define mcn-conn (dk-pick (lambda (fm) (eq? (mcn-head fm) 'IS-CONNECTED)) "connectedness"))
(mac-h 'IS-CONNECTED mcn-conn)
(dk-split-all!)
(define mcn-sep (dk-pick (lambda (fm) (and (eq? (mcn-head fm) 'FORALL) (eq? (cadr fm) 'cnu_))) "the separation clause"))
(fact 'ball-is-set 's)

;;; a point x of A: x in PTS(s), and its ball of local constancy, with x inside it;
;;; returns the radius
(define (mcn-local! x)
  (fact 'subset-mem-fwd 'mca_ '(PTS s) x)
  (let* ((ex (dk-apply! mcn-lc x))
         (r  (dk-skolem! ex 'top)))
    (mcn-pos3! r)
    (dk-cite! 'ball-center-in 's x r)
    r))

;;; ---- U and V are open
(define (mcn-ball-pts! w y r)
  ;; w in BALL(s, y, r) in context: land w in PTS(s)
  (let ((iff (dk-cite! 'ball-membership 's y r w)))
    (dk-have! (list 'IN w '(PTS s)) (lambda () (mcn-kp! iff (list 'IN w (list 'BALL 's y r)))))))
(define (mcn-open! side)
  (let ((st (mcn-set side)))
    (dk-have! (list 'IS-OPEN 's st)
      (lambda ()
        (mac 'IS-OPEN)
        (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond ((dk-asm? g) (ass))
                    ((eq? (mcn-head g) 'SUBSET)
                     (let ((w (subset-by-element!)))
                       (sep-me (list 'IN w st))
                       (dk-split-all!)
                       (dk-ass!)))
                    (#t
                     (let ((y (dk-di-var!)))
                       (mcn-open-set! y side
                         (lambda (z e)
                           (let* ((bl (list 'BALL 's z e)))
                             (fact 'subset-mem-fwd 'mca_ '(PTS s) z)
                             (mcn-pos3! e)
                             (dk-cite! 'ball-is-open 's z e)
                             (mac-h 'IS-OPEN (dk-ctx-form (list 'IS-OPEN 's bl)))
                             (dk-split-all!)
                             (let* ((univ (dk-pick (lambda (fm) (and (eq? (mcn-head fm) 'FORALL)
                                                                     (dk-contains? fm bl)
                                                                     (dk-contains? fm 'POS-RR)))
                                                   "the openness of the ball"))
                                    (ex (dk-apply! univ y))
                                    (r2 (dk-skolem! ex 'top)))
                               (ew r2)
                               (dk-conj-close!
                                 (lambda ()
                                   (if (not (dk-ass!))
                                       (let ((w (subset-by-element!)))
                                         (fact 'subset-mem-fwd (list 'BALL 's y r2) bl w)
                                         (mcn-ball-pts! w z e)
                                         (mcn-in-set! w z e side)))))))))))))))))))
(mcn-open! mcn-side-u)
(mcn-open! mcn-side-v)

;;; ---- A is covered by U and V
(dk-have! (list 'SUBSET 'mca_ (list 'UNION mcn-u mcn-v))
  (lambda ()
    (let* ((x (subset-by-element!))
           (r (mcn-local! x))
           (iff (dk-cite! 'union-membership mcn-u mcn-v x)))
      (use-em (list '= (list 'f x) '(f mcp_))
        (lambda () (mcn-in-set! x x r mcn-side-u) (mcn-kp! iff (list 'IN x mcn-u)))
        (lambda () (mcn-in-set! x x r mcn-side-v) (mcn-kp! iff (list 'IN x mcn-v)))))))

;;; ---- no point of A is in both
(define (mcn-value! x side)
  ;; (IN x SET-of-SIDE), x in A: land (= (f x) (f z)) and (SIDE z); return z
  (mcn-open-set! x side
    (lambda (z e)
      (dk-apply! (dk-ctx-form (mcn-lcf z e)) x)
      z)))
(dk-have! (list 'FORALL 'cnx_ (list 'IMPLIES '(IN cnx_ mca_)
            (list 'NOT (list 'AND (list 'IN 'cnx_ mcn-u) (list 'IN 'cnx_ mcn-v)))))
  (lambda ()
    (let ((x (dk-di-var!)))
      (di)
      (dk-split-all!)
      (let* ((z1 (mcn-value! x mcn-side-u))
             (z2 (mcn-value! x mcn-side-v)))
        (dk-have! (list '= (list 'f z2) '(f mcp_))
          (lambda ()
            (subst (list '= (list 'f z2) (list 'f x)))
            (subst (list '= (list 'f x) (list 'f z1)))
            (dk-ass!)))
        (ai (dk-ctx-form (mcn-side-v z2)))))))

;;; ---- p is in U
(dk-have! (list 'FORSOME 'cnx_ (list 'AND '(IN cnx_ mca_) (list 'IN 'cnx_ mcn-u)))
  (lambda ()
    (let ((r (mcn-local! 'mcp_)))
      (dk-apply! (dk-ctx-form (mcn-lcf 'mcp_ r)) 'mcp_)
      (mcn-in-set! 'mcp_ 'mcp_ r mcn-side-u)
      (ew 'mcp_)
      (dk-conj-close! dk-ass!))))

;;; ---- connectedness: A misses V; so q is in U
(define mcn-miss (dk-apply! mcn-sep mcn-u mcn-v))
(fact 'subset-mem-fwd 'mca_ (list 'UNION mcn-u mcn-v) 'mcq_)
(dk-have! (list 'NOT (list 'IN 'mcq_ mcn-v))
  (lambda ()
    (di)
    (dk-have! (list 'FORSOME 'cnx_ (list 'AND '(IN cnx_ mca_) (list 'IN 'cnx_ mcn-v)))
      (lambda () (ew 'mcq_) (dk-conj-close! dk-ass!)))
    (ai (dk-ctx-form mcn-miss))))
(let ((iff (dk-cite! 'union-membership mcn-u mcn-v 'mcq_)))
  (dk-have! (list 'IN 'mcq_ mcn-u)
    (lambda () (mcn-kp! iff (list 'IN 'mcq_ (list 'UNION mcn-u mcn-v)) (list 'NOT (list 'IN 'mcq_ mcn-v))))))
(let ((z (mcn-value! 'mcq_ mcn-side-u)))
  (subst (list '= '(f mcq_) (list 'f z)))
  (subst (list '= (list 'f z) '(f mcp_)))
  (rfl))
(qed 'connected-locally-constant)
