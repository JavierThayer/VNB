;;; clamp.scm -- CLAMP(a,b,x) = min(max(x,a),b), the retraction of the line onto
;;; the interval [a,b], and the ONE mechanism that dissolves the endpoint
;;; problem of docs/calculus.pdf Prop 4.16.
;;;
;;; THE OBSTACLE IT REMOVES.  `IS-ANTIDERIVATIVE(f,phi,a,b)'
;;; (theorem-library/antiderivative.scm) demands IS-CONTINUOUS-AT(RR-MS, RR-MS,
;;; f, x) for every x of CCINT(a,b) -- continuity as a map on the LINE,
;;; endpoints included.  A function BUILT as a limit on [a,b] -- which is what
;;; Prop 4.16 constructs -- is unconstrained just outside the interval, so it is
;;; in general DISCONTINUOUS at a and at b, and no theorem about uniform limits
;;; can repair that: at an endpoint only a half-ball is available while the
;;; eps/delta clause quantifies over all of RR.  Composing with CLAMP repairs it
;;; at the source: the composite is constant to the left of a and to the right
;;; of b, its argument never leaves [a,b], and every hypothesis stated on the
;;; interval therefore speaks at every real.
;;;
;;; THE TECHNIQUE, and it is why this file is short.  The obvious route is a
;;; three-case eps/delta at each endpoint (y <= a gives difference 0, a <= y <= b
;;; is the interval argument, y > b excluded by capping delta at b - a).  That
;;; is a bespoke argument, and it is not needed.  CLAMP is 1-LIPSCHITZ:
;;;
;;;     |CLAMP(a,b,y) - CLAMP(a,b,x)|  <=  |y - x|
;;;
;;; and with that one inequality `clamp-compose-continuous-at' is an eps/delta
;;; with NO cases at all -- take f's own delta, unchanged, since the clamp
;;; cannot move two points further apart than they were.  The interval, the
;;; endpoints and the sides never appear.  The case analysis has not been
;;; avoided; it has been spent once, in `rr-max-lipschitz' and
;;; `rr-min-lipschitz', where it is four `ineq' calls over the defining
;;; equation's own guard.
;;;
;;; WHAT IS HERE
;;;
;;;   rr-max-lipschitz   |max(u,c) - max(v,c)| <= |u - v|
;;;   rr-min-lipschitz   |min(u,c) - min(v,c)| <= |u - v|
;;;   clamp-in-rr        CLAMP(a,b,x) in RR, UNCONDITIONALLY
;;;   clamp-in-ccint     a <= b  =>  CLAMP(a,b,x) in CCINT(a,b)
;;;   clamp-fixes        a <= x <= b  =>  CLAMP(a,b,x) = x
;;;   clamp-lipschitz    the display above
;;;   clamp-compose-lam-in-fun      z |-> f(CLAMP(a,b,z))  is in FUN(RR,RR)
;;;   clamp-compose-fixes           it agrees with f on [a,b]
;;;   clamp-compose-continuous-at   f continuous at each point of [a,b]
;;;                                 =>  z |-> f(CLAMP(a,b,z)) continuous at
;;;                                 EVERY real
;;;
;;; Every one `modulo 0'.  Note in particular that `clamp-in-rr' is
;;; unconditional -- it does not ask a <= b -- so the term may sit in the body
;;; of a VNB-LAMBDA over all of RR without a side condition, which is the same
;;; design decision `seq-limit-in-rr' is made by.
;;;
;;; THE LAST THEOREM'S BILL IS ZERO AND THAT IS DELIBERATE.  Its two
;;; IS-METRIC-SPACE(RR-MS) goal conjuncts come out of the unfold of the
;;; hypothesis's own continuity at CLAMP(a,b,t), not from `rr-is-metric-space',
;;; which is still an asserted support; citing that would put it into this bill
;;; and into every bill downstream.  The same care is taken in
;;; continuity-transfer.scm and continuity-local.scm.
;;;
;;; Loads after rr-max-basics, rr-min-basics (the defining equations and the
;;; case laws), rr-abs-basics (rr-abs-bound, rr-le-abs, rr-neg-abs-le,
;;; rr-abs-nonneg), ccint-basics (ccint-membership), rr-ms-dist,
;;; metric-continuity (IS-CONTINUOUS-AT), fun-apply-type-proof
;;; (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `cm-' prefix) --------------------

(define (cm-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (cm-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cm-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cm-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (cm-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cm-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (cm-di-landed-1!)
  (let ((new (cm-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "cm-di-landed-1!: expected 1" (map expression->string new)))))

(define (cm-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cm-find: no context formula" what))
          ((pred (car l)) (car l)) (else (loop (cdr l))))))

(define (cm-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

(define (cm-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed))
         (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (cm-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cm-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (cm-ineq . forms) (apply ineq (map cm-idx forms)))

;;; Every ORDER or EQUATION hypothesis, by index: the premises `ineq' can read.
;;; Safe here because every atom of every such formula in these four proofs is
;;; certified in RR; a context carrying an equation between uncertifiable terms
;;; wants `contra--usable-indices' instead.
(define (cm-arith-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(<= < =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (else (loop (cdr l) (+ i 1) acc)))))
(define (cm-all-ineq!) (apply ineq (cm-arith-idx)))

;;; The two branches of MAX's (MIN's) defining equation, as `use-em' on its own
;;; guard.  The NOT branch lands the positive order fact by `rr-le-total' plus
;;; `prop' -- `ineq' will not negate a `<='.
(define (cm-max-case! x y k)
  (use-em (list '<= y x)
    (lambda () (detach! (list 'IMPLIES (list '<= y x) (list '= (list 'max x y) x))) (k))
    (lambda () (detach! (list 'IMPLIES (list 'NOT (list '<= y x)) (list '= (list 'max x y) y)))
               (have! (list '<= x y) (lambda () (fact 'rr-le-total x y) (prop)))
               (k))))
(define (cm-min-case! x y k)
  (use-em (list '<= x y)
    (lambda () (detach! (list 'IMPLIES (list '<= x y) (list '= (list 'min x y) x))) (k))
    (lambda () (detach! (list 'IMPLIES (list 'NOT (list '<= x y)) (list '= (list 'min x y) y)))
               (have! (list '<= y x) (lambda () (fact 'rr-le-total x y) (prop)))
               (k))))

;;; the linear reading of |p - q|: typed, bounded above and below by the
;;; difference, and nonnegative.  Everything `ineq' needs to treat it as an atom.
(define (cm-abs-setup! p q)
  (fact 'rr-sub-in-rr p q) (fact 'rr-abs-closed (list '- p q))
  (fact 'rr-le-abs (list '- p q)) (fact 'rr-neg-abs-le (list '- p q))
  (fact 'rr-abs-nonneg (list '- p q)))

;;; (IN x RR) off a POS-RR on a SIDE branch -- `mac-h' is destructive and the
;;; folded predicate is wanted again.
(define (cm-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda () (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

(define (cm-beta!)
  (let lp ((n 0))
    (if (and (< n 6) (dk-contains? (dk-goal) 'VNB-LAMBDA))
        (begin (lam-b) (lp (+ n 1))))))

;;; =====================================================================
;;; 0.  THE OPERATOR.
;;; =====================================================================

(def-functoid 'CLAMP '(a b x) '(min (max x a) b))
(notation! 'CLAMP 'kind 'functoid 'arity 3
           'english "$3 clamped to [$1, $2]"
           'noun "the clamping of $3 to [$1, $2]")

;;; =====================================================================
;;; 1.  CLAMP is real -- UNCONDITIONALLY, so the term may sit in a lambda body.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr, x in rr], clamp(a,b,x) in rr)"))
(quietly (lambda ()
  (cm-peel!) (mac 'clamp)
  (fact 'rr-max-closed 'x 'a) (fact 'rr-min-closed '(max x a) 'b) (ass)))
(qed 'clamp-in-rr)
(topic! 'clamp-in-rr 'analysis)

;;; =====================================================================
;;; 2.  CLAMP lands in [a,b].  This is the whole point of the operator: every
;;; hypothesis stated on the interval speaks at CLAMP(a,b,x) for EVERY real x.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr, x in rr],
                a <= b implies clamp(a,b,x) in ccint(a,b))"))
(quietly (lambda ()
  (cm-peel!) (mac 'clamp)
  (fact 'rr-max-closed 'x 'a) (fact 'rr-min-closed '(max x a) 'b)
  (fact 'rr-le-max-right 'x 'a)            ; a <= max(x,a)
  (fact 'rr-min-le-right '(max x a) 'b)    ; min(max(x,a),b) <= b
  (fact 'rr-le-min '(max x a) 'b 'a)       ; a <= min(max(x,a),b)
  (mac 'ccint-membership) (cm-and! (lambda () (ass)))))
(qed 'clamp-in-ccint)
(topic! 'clamp-in-ccint 'analysis)
(alias! 'clamp-in-ccint "the clamping of a real to [a,b] lies in [a,b]")

;;; =====================================================================
;;; 3.  CLAMP is the identity on [a,b] -- it is a RETRACTION.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr, x in rr],
                a <= x implies x <= b implies clamp(a,b,x) = x)"))
(quietly (lambda ()
  (cm-peel!) (mac 'clamp)
  (fact 'rr-max-def 'x 'a) (cm-split!)
  (detach! '(IMPLIES (<= a x) (= (max x a) x)))
  (subst '(= (max x a) x))
  (fact 'rr-min-def 'x 'b) (cm-split!)
  (detach! '(IMPLIES (<= x b) (= (min x b) x)))
  (subst '(= (min x b) x))
  (rfl)))
(qed 'clamp-fixes)
(topic! 'clamp-fixes 'analysis)
(alias! 'clamp-fixes "clamping fixes the points of the interval")

;;; =====================================================================
;;; 4.  MAX and MIN are 1-LIPSCHITZ in their first argument.
;;;
;;; This is where the case analysis is spent, once and for both operators.  The
;;; goal is opened by `rr-abs-bound' into a pair of LINEAR inequalities, the
;;; defining equation is landed at both argument pairs, and `use-em' on its own
;;; guard gives four branches -- in each of which the two maxima (minima) are
;;; pinned to arguments and `ineq' closes with the bounds `cm-abs-setup!' has
;;; put on |u - v|.  Nothing is substituted into the goal: the maxima stay as
;;; opaque atoms and the case equations are handed to the oracle as premises.
;;; =====================================================================
(sp (make-wff "forall([u in rr, v in rr, c in rr],
                abs(max(u,c) - max(v,c)) <= abs(u - v))"))
(quietly (lambda ()
  (cm-peel!)
  (fact 'rr-max-closed 'u 'c) (fact 'rr-max-closed 'v 'c)
  (fact 'rr-sub-in-rr '(max u c) '(max v c))
  (cm-abs-setup! 'u 'v)
  (fact 'rr-max-def 'u 'c) (cm-split!) (fact 'rr-max-def 'v 'c) (cm-split!)
  (mac 'rr-abs-bound)
  (cm-max-case! 'u 'c (lambda () (cm-max-case! 'v 'c
    (lambda () (cm-and! (lambda () (cm-all-ineq!)))))))))
(qed 'rr-max-lipschitz)
(topic! 'rr-max-lipschitz 'inequalities)
(alias! 'rr-max-lipschitz "the maximum is 1-Lipschitz in each argument")

(sp (make-wff "forall([u in rr, v in rr, c in rr],
                abs(min(u,c) - min(v,c)) <= abs(u - v))"))
(quietly (lambda ()
  (cm-peel!)
  (fact 'rr-min-closed 'u 'c) (fact 'rr-min-closed 'v 'c)
  (fact 'rr-sub-in-rr '(min u c) '(min v c))
  (cm-abs-setup! 'u 'v)
  (fact 'rr-min-def 'u 'c) (cm-split!) (fact 'rr-min-def 'v 'c) (cm-split!)
  (mac 'rr-abs-bound)
  (cm-min-case! 'u 'c (lambda () (cm-min-case! 'v 'c
    (lambda () (cm-and! (lambda () (cm-all-ineq!)))))))))
(qed 'rr-min-lipschitz)
(topic! 'rr-min-lipschitz 'inequalities)
(alias! 'rr-min-lipschitz "the minimum is 1-Lipschitz in each argument")

;;; =====================================================================
;;; 5.  ... hence CLAMP is 1-LIPSCHITZ.  Two citations and one `ineq' for the
;;; transitivity; the composition of two 1-Lipschitz maps.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr, y in rr, x in rr],
                abs(clamp(a,b,y) - clamp(a,b,x)) <= abs(y - x))"))
(quietly (lambda ()
  (cm-peel!) (mac 'clamp)
  (fact 'rr-max-closed 'y 'a) (fact 'rr-max-closed 'x 'a)
  (fact 'rr-min-closed '(max y a) 'b) (fact 'rr-min-closed '(max x a) 'b)
  (fact 'rr-sub-in-rr '(min (max y a) b) '(min (max x a) b))
  (fact 'rr-abs-closed '(- (min (max y a) b) (min (max x a) b)))
  (fact 'rr-sub-in-rr '(max y a) '(max x a))
  (fact 'rr-abs-closed '(- (max y a) (max x a)))
  (fact 'rr-sub-in-rr 'y 'x) (fact 'rr-abs-closed '(- y x))
  (fact 'rr-max-lipschitz 'y 'x 'a)
  (fact 'rr-min-lipschitz '(max y a) '(max x a) 'b)
  (cm-ineq '(<= (abs (- (min (max y a) b) (min (max x a) b)))
                (abs (- (max y a) (max x a))))
           '(<= (abs (- (max y a) (max x a))) (abs (- y x))))))
(qed 'clamp-lipschitz)
(topic! 'clamp-lipschitz 'inequalities)
(alias! 'clamp-lipschitz "clamping to an interval is 1-Lipschitz")

;;; =====================================================================
;;; 6.  THE CLAMPED COMPOSITE is a function RR -> RR.
;;; `lam-t' opens TWO leaves -- the pointwise typing and the SETHOOD of the
;;; domain -- and `clamp-in-rr' being unconditional is what makes the first a
;;; two-line citation.
;;; =====================================================================
(sp (make-wff "forall([f in fun(rr,rr), a in rr, b in rr],
                vnb-lambda(z_, rr, f(clamp(a,b,z_))) in fun(rr,rr))"))
(quietly (lambda ()
  (cm-peel!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'FORALL)
         (let ((z (cadr (car (cm-di-landed!)))))
           (fact 'clamp-in-rr 'a 'b z)
           (fact 'fun-apply-type-c 'f 'RR 'RR (list 'CLAMP 'a 'b z))
           (ass))
         (begin (fact 'rr-is-set) (ass))))
   (dk-opened (lambda () (lam-t))))))
(qed 'clamp-compose-lam-in-fun)
(topic! 'clamp-compose-lam-in-fun 'analysis)

;;; =====================================================================
;;; 7.  ... and it agrees with f on [a,b].  This is the half that makes the
;;; composite usable as a SUBSTITUTE for f: everything the interval says about
;;; f, it says about the composite.
;;; =====================================================================
(sp (make-wff "forall([f in fun(rr,rr), a in rr, b in rr, x in rr],
   a <= x implies x <= b implies
   (vnb-lambda(z_, rr, f(clamp(a,b,z_))))(x) = f(x))"))
(quietly (lambda ()
  (cm-peel!)
  (cm-beta!)
  (fact 'clamp-fixes 'a 'b 'x)
  (subst '(= (CLAMP a b x) x))
  (fact 'fun-apply-type-c 'f 'RR 'RR 'x)
  (rfl)))
(qed 'clamp-compose-fixes)
(topic! 'clamp-compose-fixes 'analysis)
(alias! 'clamp-compose-fixes
        "the clamped composite agrees with the function on the interval")

;;; =====================================================================
;;; 8.  THE PAYOFF.  f continuous at every point of [a,b] -- continuity as a map
;;; on the LINE, tested at the interval's points, which is exactly what Def 4.6
;;; asks and what every theorem of the calculus arc supplies -- makes the
;;; clamped composite continuous at EVERY real, endpoints and outside included.
;;;
;;; No cases.  The clamp cannot move two points further apart than they were
;;; (`clamp-lipschitz'), so f's own delta at CLAMP(a,b,t) serves unchanged: a
;;; point within delta of t clamps to a point within delta of CLAMP(a,b,t), and
;;; both clampings lie in [a,b], where the hypothesis speaks.
;;; =====================================================================
(sp (make-wff "forall([f in fun(rr,rr), a in rr, b in rr, t_ in rr],
   a <= b implies
   forall([x_ in rr], x_ in ccint(a,b) implies is-continuous-at(rr-ms, rr-ms, f, x_))
   implies
   is-continuous-at(rr-ms, rr-ms, vnb-lambda(z_, rr, f(clamp(a,b,z_))), t_))"))
(quietly (lambda () (cm-peel!)))
(define CC-ON (car (dk-asms)))          ; f is continuous at each point of [a,b]
(define cm-ct '(CLAMP a b t_))
(quietly (lambda ()
  (fact 'clamp-in-rr 'a 'b 't_)
  (fact 'clamp-in-ccint 'a 'b 't_)
  (let ((cc-at (cm-inst! CC-ON cm-ct)))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at cc-at)))))
  (fact 'clamp-compose-lam-in-fun 'f 'a 'b)))
(define CC-EPSU
  (cm-find 'eps (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                 (dk-contains? x 'POS-RR) (dk-contains? x 'DIST)))))

(define (cc-inner! del du2)
  (let* ((mb (cm-di-landed-1!)) (bb (cadr mb)))
    (have! (list 'IN bb 'RR)
      (lambda () (slot-h 'PTS (list 'IN bb '(PTS RR-MS))) (ass)))
    (let ((dstb (car (cm-di-landed!))))
      (fact 'rr-sub-in-rr 't_ bb)
      (fact 'rr-abs-closed (list '- 't_ bb))
      ;; the abs reading of d(t_,bb) <= del, on a LANE: `mac-h' is destructive.
      (have! (list '<= (list 'abs (list '- 't_ bb)) del)
        (lambda () (mac-h 'rr-ms-dist dstb) (ass)))
      (cm-beta!)                                     ; both arguments TYPED above
      (let ((cb (list 'CLAMP 'a 'b bb)))
        (fact 'clamp-in-rr 'a 'b bb)
        (have! (list 'IN cb '(PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
        (fact 'clamp-lipschitz 'a 'b 't_ bb)
        (fact 'rr-sub-in-rr cm-ct cb)
        (fact 'rr-abs-closed (list '- cm-ct cb))
        (have! (list '<= (list '(DIST RR-MS) cm-ct cb) del)
          (lambda () (mac 'rr-ms-dist)
             (cm-ineq (list '<= (list 'abs (list '- cm-ct cb))
                               (list 'abs (list '- 't_ bb)))
                      (list '<= (list 'abs (list '- 't_ bb)) del))))
        (cm-inst! du2 cb)
        (ass)))))

(define (cc-eps!)
  (let* ((me (cm-di-landed-1!)) (eps (cadr me)))
    (let* ((sk (cm-skolem! (cm-inst! CC-EPSU eps)))
           (del (car (cadr sk))))
      (dk-split! (car sk))
      (let ((du2 (cm-find 'inner
                   (lambda (x) (and (pair? x) (eq? (car x) 'FORALL)
                                    (dk-contains? x del) (dk-contains? x 'DIST))))))
        (cm-pos-in-rr! del)
        (ew del)
        (cm-and! (lambda ()
          (if (eq? (car (dk-goal)) 'POS-RR) (ass) (cc-inner! del du2))))))))

(quietly (lambda ()
  (mac 'is-continuous-at)
  (cm-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
             ((and (eq? (car gl) 'IN) (dk-contains? gl 'PTS)) (slot 'PTS) (ass))
             (else (cc-eps!))))))))
(qed 'clamp-compose-continuous-at)
(topic! 'clamp-compose-continuous-at 'analysis)
(alias! 'clamp-compose-continuous-at
        "clamping makes a function continuous on an interval continuous on the line")
