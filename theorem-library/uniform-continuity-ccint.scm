;;; uniform-continuity-ccint.scm -- a continuous function on a CLOSED BOUNDED
;;; INTERVAL is UNIFORMLY continuous there, PROVEN.
;;;
;;;   f in FUN(RR,RR), a <= b, f continuous at every point of [a,b], eps > 0
;;;     =>  forsome d > 0.  forall p,q in [a,b].
;;;           |p - q| <= d  ==>  |f(p) - f(q)| <= eps
;;;
;;; It is step (87) of the proof of Theorem 5.2 (Bernstein density) in
;;; docs/calculus.pdf, and the one analytic input that theorem needs which the
;;; tree did not have.  The other one -- M = sup|f| on [a,b] -- has been there
;;; since 2026-08-17 (`continuous-bounded-above-on-ccint' / `evt-max').
;;;
;;; WHY IT IS NOT STATED WITH `IS-UNIFORMLY-CONTINUOUS'.  That predicate
;;; (structure-library/metric-continuity.scm:61) requires f in
;;; FUN(PTS s, PTS t): its DOMAIN must be a metric SPACE.  CCINT(a,b) is not
;;; one in this tree -- there is no metric SUBSPACE structure, which is exactly
;;; the blocker Heine-Borel sits behind -- so the statement is written out over
;;; CCINT(a,b) with `abs', following the precedent of
;;; theorem-library/ccint-bounded.scm, which states boundedness as
;;; `forsome k. forall z in [a,b]. f(z) <= k' rather than reaching for a
;;; predicate.  Building the subspace structure for this one theorem was
;;; DECLINED: it is its own foundational decision and Heine-Borel is its real
;;; customer.  Nothing is lost -- the written-out form is what the Bernstein
;;; estimate consumes anyway, since (87) is used to bound |f(x) - f(l/n)| for
;;; plain reals x and l/n.
;;;
;;; THE MECHANISM: `ccint-creep' (theorem-library/ccint-creep.scm), whose own
;;; header names uniform continuity as the fourth instance it was written to
;;; serve.  The instance supplies only the LOCAL STEP; the lemma does all the
;;; supremum bookkeeping.  No completeness argument is written here.
;;;
;;; THE SET, with eps fixed by the outer universal:
;;;
;;;   G = { z in [a,b] : f is uniformly eps-continuous on [a,z] }
;;;
;;; i.e. ccint-bounded's set with "bounded above on [a,z]" replaced by
;;; "uniformly eps-continuous on [a,z]", and nothing else changed.
;;;
;;; THE LOCAL STEP at t in [a,b] -- the only mathematics in the file:
;;;
;;;   * `rr-pos-halvable' turns eps > 0 into a POSITIVE h with h + h = eps.
;;;     Note the shape: a WITNESS satisfying an equation, not a quotient.
;;;     There is no division anywhere in this proof.
;;;   * continuity at t at that h gives delta > 0 with
;;;       |t - z| <= delta  ==>  |f(t) - f(z)| <= h.
;;;   * halve delta the same way: rad with rad + rad = delta.  THE CREEP RADIUS
;;;     IS `rad', NOT delta.  That is the one choice in the proof, and it is
;;;     what makes the two-point case work: two points inside [t-rad, t+rad] are
;;;     at most 2*rad = delta apart, so BOTH are within delta of t.
;;;   * a w in G exceeding t - rad carries its own modulus mw > 0.  `rr-min-pos'
;;;     -- the dual of the `rr-upper-of-two' ccint-bounded merges its two bounds
;;;     with, and the reason neither proof needs a MIN operator -- gives a
;;;     positive `mod' with mod <= mw and mod <= rad.  Then rad + mod <= delta,
;;;     and the whole delta-bookkeeping is `ineq'-linear.
;;;   * then for y in [a,b] with y <= t + rad, and p,q in [a,y] with
;;;     |p-q| <= mod:
;;;       - p <= w and q <= w: both lie in [a,w], and mod <= mw, so w's own
;;;         modulus gives the bound.
;;;       - otherwise one of p,q exceeds w, hence (being within mod of each
;;;         other) both lie in (t - rad - mod, t + rad], and rad + mod <= delta,
;;;         so both are within delta of t.  Two copies of h then give
;;;         |f(p) - f(q)| <= h + h = eps.
;;;
;;; THE FOUR-WAY SPLIT IS THREE-WAY, AND THEN TWO CASES.  ccint-bounded splits
;;; ONE point against w; this splits two, and the naive nesting is four branches
;;; of which three are the same argument.  It does not have to be nested that
;;; way: `<= w p' ALONE suffices for the far case (q is dragged along by
;;; |p-q| <= mod), so the split is
;;;
;;;     p <= w  ->  ( q <= w -> NEAR-W ; w <= q -> uc-far! '(<= w q) )
;;;     w <= p  ->  uc-far! '(<= w p)
;;;
;;; -- three leaves, and `uc-far!' is ONE helper called twice, differing only in
;;; which of the two order facts it is handed.  The helper's arithmetic is
;;; identical in the two calls because it never uses the premise directly: it
;;; passes it, with eight fixed context facts, to `ineq'.  That the SAME eight
;;; premises close both calls is the content of "the roles of p and q are
;;; symmetric", discharged once by the oracle rather than three times by hand.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after ccint-creep, ccint-basics (ccint-membership), rr-halving
;;; (rr-pos-halvable), rr-order-basics (rr-min-pos, rr-le-ne-lt), rr-abs-basics
;;; (rr-abs-bound), rr-ms-dist, metric-continuity and driver-kit.

;;; ---- file-local driver helpers (the `uc-' prefix) --------------------
;;; NOTE ON NAMES: MIT Scheme folds symbols to lower case, so `uc-D' would BE
;;; `uc-d'.  The three radii are therefore spelled out -- uc-delta, uc-rad,
;;; uc-mod -- and no two differ only by case.

(define (uc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (uc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "uc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (uc-mem-in set-expr)
  (uc-find 'mem-in
    (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) set-expr)))))

(define (uc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "uc-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (uc-ineq . forms) (apply ineq (map uc-idx forms)))

(define (uc-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (uc-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (uc-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an assumption LANDS -- a guarded universal goes whole under one
;;; call, an unguarded one does not, so counting `di's reaches the wrong goal.
(define (uc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "uc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (uc-di-landed-1!)
  (let ((new (uc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "uc-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

(define (uc-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME that is ALREADY in the context.  `obtain' cannot: it
;;; recognises only an existential its own lane just landed.  The eigenvariable
;;; is read off by free-variable set difference, and a miss ERRORS.
(define (uc-skolem! ex)
  (let* ((fv0 (uc-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (uc-fvs (dk-asms)))))
      (if (null? fresh)
          (error "uc-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (uc-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "uc-obtain: nothing obtained for" what))
    v))

;;; |u - v| <= r, from linear premises.  `rr-abs-bound' turns the goal into the
;;; pair of linear bounds and the oracle closes each.  Wants (IN (- u v) RR) and
;;; (IN r RR) in context: `rr-abs-bound' is GUARDED, and a `mac' whose guard is
;;; not evident does not fire at all.
(define (uc-abs-le! u v r . prem)
  (have! (list '<= (list 'abs (list '- u v)) r)
    (lambda () (mac 'rr-abs-bound)
               (uc-goal-and! (lambda () (apply uc-ineq prem))))))

;;; d(u,v) <= r.  `rr-ms-dist' brings the accessor down to abs (it sits in
;;; OPERATOR position, where `subst' cannot reach).
(define (uc-dist! u v r . prem)
  (have! (list '<= (list '(DIST RR-MS) u v) r)
    (lambda () (mac 'rr-ms-dist) (mac 'rr-abs-bound)
               (uc-goal-and! (lambda () (apply uc-ineq prem))))))

(define (uc-unpack-abs! u v r)
  (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- u v)) r))
  (dk-split! (list 'AND (list '<= (list '- r) (list '- u v))
                       (list '<= (list '- u v) r))))

(define (uc-unpack-dist! u v r)
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) u v) r))
  (uc-unpack-abs! u v r))

(define (uc-in-pts! u)
  (have! (list 'IN u '(PTS RR-MS)) (lambda () (slot 'PTS) (ass))))

;;; POS-RR(x) -> the strict form 0 < x, with x in RR beside it.  `mac-h' is
;;; destructive, so this is done only once POS-RR(x) has served its purpose.
(define (uc-strict! x)
  (mac-h 'pos-rr (list 'POS-RR x))
  (uc-split!)
  (have! (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x))))
  (fact 'rr-le-ne-lt 0 x))

;;; ---- the statement and the set it creeps along -----------------------

;;; f is uniformly eps-continuous on [a,u].
(define (uc-unif-on u)
  (list 'FORSOME 'd_
    (list 'AND '(IN d_ RR)
      (list 'AND '(< 0 d_)
        (list 'FORALL 'p_
          (list 'IMPLIES (list 'IN 'p_ (list 'CCINT 'a u))
            (list 'FORALL 'q_
              (list 'IMPLIES (list 'IN 'q_ (list 'CCINT 'a u))
                (list 'IMPLIES (list '<= (list 'abs (list '- 'p_ 'q_)) 'd_)
                               (list '<= (list 'abs (list '- (list 'f 'p_)
                                                             (list 'f 'q_)))
                                          'eps))))))))))

(define uc-set
  (list 'SEP 'z_ 'RR
    (list 'AND (list 'AND '(<= a z_) '(<= z_ b)) (uc-unif-on 'z_))))

(define uc-stmt
  (forall-guarded '(f a b eps)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(<= a b) '(POS-RR eps)
          '(FORALL x (IMPLIES (IN x (CCINT a b))
                              (IS-CONTINUOUS-AT RR-MS RR-MS f x))))
    (uc-unif-on 'b)))

;;; The local step, in the exact shape ccint-creep's last hypothesis takes with
;;; its a, b and G instantiated here.  Built from flat lists: a formula this deep
;;; is where a miscounted parenthesis reads as a different theorem.  The radius
;;; binder is `dd_', not `d_', because `d_' is already bound INSIDE uc-set --
;;; the two are alpha-equivalent (asms-find compares up to alpha) and the
;;; unshadowed spelling is the one a reader can follow.
(define uc-local
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT a b))
      (list 'FORSOME 'dd_
        (list 'AND '(IN dd_ RR)
          (list 'AND '(< 0 dd_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ uc-set)
                                            '(< (- t_ dd_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT a b))
                                          '(<= y_ (+ t_ dd_)))
                      (list 'IN 'y_ uc-set))))))))))

;;; ---- eigenvariables set as the local step runs -----------------------
(define uc-t     #f)     ; the point of [a,b] the local step is at
(define uc-h     #f)     ; eps/2, as a witness of h + h = eps
(define uc-delta #f)     ; the continuity delta at t for that h
(define uc-rad   #f)     ; delta/2 -- THE CREEP RADIUS
(define uc-w     #f)     ; the member of G just to the left of t
(define uc-mw    #f)     ; the modulus w carries on [a,w]
(define uc-mod   #f)     ; a positive common lower bound of mw and rad
(define uc-y     #f)     ; the point of [a, t+rad] being placed in G
(define uc-p     #f)     ; the two points of [a,y] whose values must be close
(define uc-q     #f)

;;; ---- context finders -------------------------------------------------

(define (uc-forall-cont)
  ;; Discriminate on the CONSEQUENT, never on a symbol the formula contains:
  ;; once a lemma with a continuity ANTECEDENT has been cited, its own copy of
  ;; this universal sits nearer the top of the context.
  (uc-find 'cont
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body))
                            (eq? (car (caddr body)) 'IS-CONTINUOUS-AT)))))))

;;; forall eps'. POS-RR(eps') => forsome delta. ... -- the unfolded continuity
(define (uc-forall-eps)
  (uc-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))

;;; forall z in PTS(RR-MS). d(t,z) <= delta => d(f t, f z) <= h
(define (uc-forall-delta)
  (uc-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f uc-delta)
                     (not (dk-contains? f 'POS-RR))))))

;;; forall p,q in [a,w]. |p-q| <= mw => |f p - f q| <= eps -- w's own modulus
(define (uc-forall-mw)
  (uc-find 'mw
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f (list 'CCINT 'a uc-w))
                     (dk-contains? f uc-mw)))))

;;; ---- the local step, innermost outward -------------------------------

;;; THE FAR CASE, and the helper the four-way split collapses into.  One of p,q
;;; is at or beyond w -- which one is the ONLY difference between the two calls,
;;; and it enters solely as one more linear premise handed to the oracle.
;;;
;;; Given `w <= r' for either r, and |p - q| <= mod:
;;;    p, q  >  w - mod  >  t - rad - mod  >=  t - delta      (mod <= rad, rad+rad = delta)
;;;    p, q  <=  y  <=  t + rad  <=  t + delta
;;; so both are within delta of t, and continuity applies at both.
(define (uc-far! extra)
  (let ((prem (list extra
                    (list '< (list '- uc-t uc-rad) uc-w)
                    (list '<= (list '- uc-mod) (list '- uc-p uc-q))
                    (list '<= (list '- uc-p uc-q) uc-mod)
                    (list '<= uc-p uc-y)
                    (list '<= uc-q uc-y)
                    (list '<= uc-y (list '+ uc-t uc-rad))
                    (list '<= uc-mod uc-rad)
                    (list '= (list '+ uc-rad uc-rad) uc-delta))))
    (for-each
     (lambda (z)
       (fact 'rr-sub-in-rr uc-t z)
       (apply uc-dist! uc-t z uc-delta prem)
       (uc-in-pts! z)
       (inst+ (uc-forall-delta) z)
       (fact 'rr-sub-in-rr (list 'f uc-t) (list 'f z))
       (uc-unpack-dist! (list 'f uc-t) (list 'f z) uc-h))
     (list uc-p uc-q))
    ;; |f p - f q| <= (f t - f q) - (f t - f p) <= h + h = eps
    (fact 'rr-sub-in-rr (list 'f uc-p) (list 'f uc-q))
    (mac 'rr-abs-bound)
    (uc-goal-and!
     (lambda ()
       (uc-ineq (list '<= (list '- uc-h) (list '- (list 'f uc-t) (list 'f uc-p)))
                (list '<= (list '- (list 'f uc-t) (list 'f uc-p)) uc-h)
                (list '<= (list '- uc-h) (list '- (list 'f uc-t) (list 'f uc-q)))
                (list '<= (list '- (list 'f uc-t) (list 'f uc-q)) uc-h)
                (list '= (list '+ uc-h uc-h) 'eps))))))

;;; THE NEAR CASE: p and q both lie in the conquered part [a,w], where w's own
;;; modulus does the work.  mod <= mw is the whole of it.
(define (uc-near!)
  (for-each
   (lambda (z)
     (have! (list 'IN z (list 'CCINT 'a uc-w))
       (lambda () (mac 'ccint-membership) (from-context!))))
   (list uc-p uc-q))
  (uc-abs-le! uc-p uc-q uc-mw
              (list '<= (list '- uc-mod) (list '- uc-p uc-q))
              (list '<= (list '- uc-p uc-q) uc-mod)
              (list '<= uc-mod uc-mw))
  (let ((fq (dk-landed-find (lambda () (inst+ (uc-forall-mw) uc-p))
                            (dk-head? 'FORALL))))
    (inst+ fq uc-q))
  (ass))

;;; goal: |f p - f q| <= eps, with p,q in [a,y] and |p-q| <= mod in context.
(define (uc-values-close!)
  (have! (list 'AND (list 'IN uc-p 'RR) (list 'IN uc-w 'RR)))
  (have! (list 'AND (list 'IN uc-q 'RR) (list 'IN uc-w 'RR)))
  (fact 'rr-leq-total uc-p uc-w)
  (use-cases (list (list '<= uc-p uc-w) (list '<= uc-w uc-p))
    (lambda ()
      (fact 'rr-leq-total uc-q uc-w)
      (use-cases (list (list '<= uc-q uc-w) (list '<= uc-w uc-q))
        uc-near!
        (lambda () (uc-far! (list '<= uc-w uc-q)))))
    (lambda () (uc-far! (list '<= uc-w uc-p)))))

;;; goal: forsome d. d in RR and 0 < d and f is uniformly eps-continuous on
;;; [a,y].  Witness `mod'.
(define (uc-unif-on-y!)
  (ew uc-mod)
  (uc-goal-and!
   (lambda ()
     (if (memq (car (dk-goal)) '(IN <))
         (ass)
         (begin
           ;; ONE `di' takes the whole leading FORALL/IMPLIES prefix, so both
           ;; interval memberships AND the |p-q| <= mod antecedent land together.
           ;; p and q are read off THAT antecedent, which fixes their order --
           ;; the context order of the two memberships does not.
           (let loop ((acc (uc-di-landed!)) (n 0))
             (let ((le (find-first
                        (lambda (f) (and (pair? f) (eq? (car f) '<=)
                                         (pair? (cadr f)) (eq? (car (cadr f)) 'abs)))
                        acc)))
               (cond (le (let ((d (cadr (cadr le))))
                           (set! uc-p (cadr d))
                           (set! uc-q (caddr d))))
                     ((> n 4) (error "uc-unif-on-y!: the |p-q| antecedent never landed"
                                     (map expression->string acc)))
                     (else (loop (append acc (uc-di-landed!)) (+ n 1))))))
           (for-each
            (lambda (z)
              (mac-h 'ccint-membership (list 'IN z (list 'CCINT 'a uc-y)))
              (uc-split!)
              (fact 'fun-apply-type-c 'f 'RR 'RR z))
            (list uc-p uc-q))
           (fact 'rr-sub-in-rr uc-p uc-q)
           (uc-unpack-abs! uc-p uc-q uc-mod)
           (uc-values-close!))))))

;;; goal: (IN y G), with y's [a,b] membership and y <= t + rad in context.
(define (uc-y-in-set!)
  (mac-h 'ccint-membership (list 'IN uc-y '(CCINT a b)))
  (uc-split!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (ass)                                      ; (IN y RR)
         (uc-goal-and!                              ; a <= y, y <= b, UNIF(y)
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME) (uc-unif-on-y!) (ass))))))
   (dk-opened (lambda () (sep-mi)))))

;;; goal: forall y in [a,b] with y <= t + rad. y in G -- under the assumption
;;; that some member of G already exceeds t - rad.
(define (uc-reach!)
  (di)
  (set! uc-w (uc-skolem!
              (uc-find 'reach
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                 (dk-contains? f uc-set))))))
  (sep-me (uc-mem-in uc-set))
  (uc-split!)
  (set! uc-mw (uc-skolem!
               (uc-find 'inherited
                 (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                  (dk-contains? f (list 'CCINT 'a uc-w)))))))
  ;; mod: positive, below w's modulus AND below the creep radius.  `rr-min-pos'
  ;; is the dual of ccint-bounded's `rr-upper-of-two', and the reason neither
  ;; proof introduces a MIN operator.
  (set! uc-mod (uc-skolem!
                (dk-deepest (lambda () (fact 'rr-min-pos uc-mw uc-rad)))))
  (let ((and-y (uc-di-landed-1!)))
    (set! uc-y (cadr (cadr and-y)))
    (dk-split! and-y))
  (uc-y-in-set!))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff uc-stmt))
(uc-peel!)

;;; (i) G is a subset of RR.
(have! (list 'SUBSET uc-set 'RR)
  (lambda () (mac 'subset-def) (di) (sep-me (uc-mem-in uc-set)) (ass)))

;;; unpack POS-RR(eps) once -- 0 <= eps is what the degenerate case needs -- and
;;; put it back: `mac-h' REPLACES, and `rr-pos-halvable' wants POS-RR(eps).
(mac-h 'pos-rr '(POS-RR eps))
(uc-split!)
(have! '(POS-RR eps) (lambda () (mac 'pos-rr) (from-context!)))
(fact 'rr-leq-reflexive 'a)
(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
(have! '(IN 1 RR) (lambda () (arith)))

;;; (ii) a is in G.  [a,a] = {a}: any two of its points are a, by antisymmetry,
;;; so any modulus does -- take 1 -- and the conclusion is |f(a) - f(a)| <= eps,
;;; which `rr-abs-bound' plus the oracle closes off 0 <= eps alone.
(have! (uc-unif-on 'a)
  (lambda ()
    (ew 1)
    (uc-goal-and!
      (lambda ()
        (cond ((eq? (car (dk-goal)) 'IN) (ass))
              ((eq? (car (dk-goal)) '<) (arith))
              (else
               ;; ONE `di' takes BOTH guarded universals here, so both interval
               ;; memberships land together; collapse each to `= a'.
               (for-each
                 (lambda (m)
                   (let ((v (cadr m)))
                     (mac-h 'ccint-membership m) (uc-split!)
                     (have! (list 'AND (list 'IN v 'RR) '(IN a RR)))
                     (have! (list 'AND (list '<= v 'a) (list '<= 'a v)))
                     (fact 'rr-leq-antisymmetric v 'a)
                     (subst (list '= v 'a))))
                 (uc-di-landed!))
               (di)
               (fact 'rr-sub-in-rr '(f a) '(f a))
               (mac 'rr-abs-bound)
               ;; `(ineq)' with NO arguments proves nothing: name the premise.
               (uc-goal-and! (lambda () (uc-ineq '(<= 0 eps))))))))))

(have! (list 'IN 'a uc-set)
  (lambda () (for-each (lambda (k) (dk-focus! k) (from-context!))
                       (dk-opened (lambda () (sep-mi))))))

;;; (iii) b bounds G.
(have! (list 'RR-UPPER-BOUND uc-set 'b)
  (lambda ()
    (mac 'rr-upper-bound)
    (for-each (lambda (k)
                (dk-focus! k)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (di) (sep-me (uc-mem-in uc-set)) (uc-split!) (ass))))
              (dk-opened (lambda () (di))))))

;;; ---- (iv) the local step ---------------------------------------------

(have! uc-local
  (lambda ()
    (let ((mem (uc-di-landed-1!)))
      (set! uc-t (cadr mem))
      ;; instantiate continuity BEFORE unfolding the interval membership:
      ;; `mac-h' replaces the assumption it unfolds.
      (inst+ (uc-forall-cont) uc-t)
      (mac-h 'ccint-membership mem)
      (uc-split!)
      ;; f(t) in RR, and it must land HERE.  Without it `rr-ms-dist' and
      ;; `rr-abs-bound' still fire on the far case's f(t)-f(z) but SPAWN their
      ;; guard as a side-condition leaf, and `ineq' -- which certifies every
      ;; atom in RR before it will look at a premise -- silently drops the two
      ;; continuity estimates and reports the GOAL as non-linear.
      (fact 'fun-apply-type-c 'f 'RR 'RR uc-t))
    (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS 'f uc-t))
    (uc-split!)
    ;; h with h + h = eps; delta for that h; rad with rad + rad = delta.
    (set! uc-h (uc-obtain 'half (lambda () (fact 'rr-pos-halvable 'eps))))
    (uc-split!)
    (set! uc-delta (uc-obtain 'delta (lambda () (inst+ (uc-forall-eps) uc-h))))
    (uc-split!)
    (set! uc-rad (uc-obtain 'radius (lambda () (fact 'rr-pos-halvable uc-delta))))
    (uc-split!)
    (uc-strict! uc-h)
    (uc-strict! uc-delta)
    (uc-strict! uc-rad)
    (ew uc-rad)
    (uc-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IMPLIES) (uc-reach!) (ass))))))

;;; ---- creep, and read the modulus at b off the result ------------------

(let ((at-b (dk-fact! 'ccint-creep 'a 'b uc-set)))
  (sep-me at-b)
  (uc-split!)
  (ass))

(qed 'continuous-uniformly-continuous-on-ccint)
(topic! 'continuous-uniformly-continuous-on-ccint 'analysis)
(alias! 'continuous-uniformly-continuous-on-ccint
        "uniform continuity on a closed interval"
        "a continuous function on a closed bounded interval is uniformly continuous"
        "Heine-Cantor theorem on an interval")
