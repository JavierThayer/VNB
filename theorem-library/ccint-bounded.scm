;;; ccint-bounded.scm -- a continuous function on [a,b] is BOUNDED ABOVE, PROVEN.
;;;
;;;   f in FUN(RR,RR), a <= b, f continuous at every point of [a,b]
;;;     =>  forsome k in RR.  forall z in [a,b].  f(z) <= k
;;;
;;; This is the half of the Extreme Value Theorem that nothing in the tree had,
;;; and the reason EVT could not be proved: without it there is no supremum of
;;; the image for EVT to attain.  It is the first instance of `ccint-creep'.
;;;
;;; THE SET.  G = { x in [a,b] : f is bounded above on [a,x] }.  a is in G
;;; (bound f(a), since [a,a] = {a}), G is a subset of RR and b bounds it, so
;;; ccint-creep asks only for the LOCAL STEP at each t in [a,b] -- and the local
;;; step is exactly the epsilon/delta definition of continuity at t with
;;; eps = 1:
;;;
;;;   take the delta at eps = 1, so |f(z) - f(t)| <= 1 for every z within delta
;;;   of t.  If some w in G exceeds t - delta, w carries a bound k on [a,w];
;;;   let K be a common upper bound of k and f(t)+1 (`rr-upper-of-two').  Then
;;;   for any y in [a,b] with y <= t + delta and any z in [a,y], either z <= w
;;;   -- and f(z) <= k <= K -- or w <= z, in which case t - delta < z <= t +
;;;   delta, so |f(z) - f(t)| <= 1 and f(z) <= f(t) + 1 <= K.  So y is in G.
;;;
;;; THE TWO MERGED BOUNDS ARE THE POINT.  k comes from the part of the interval
;;; already conquered and f(t)+1 from the neighbourhood continuity gives; they
;;; are unrelated reals, and `rr-upper-of-two' (theorem-library/rr-order-basics)
;;; is what lets them be merged without introducing a MAX operator.
;;;
;;; eps = 1 IS ARBITRARY.  Any positive eps does; 1 is the cheapest to type
;;; (`arith' closes all three conjuncts of POS-RR(1)).
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after ccint-creep, ccint-basics, rr-order-basics (rr-upper-of-two,
;;; rr-le-ne-lt), rr-ms-dist, rr-abs-basics (rr-abs-bound), metric-continuity.

;;; ---- file-local driver helpers (the `bd-' prefix) --------------------

(define (bd-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (bd-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "bd-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (bd-mem-in set-expr)
  (bd-find 'mem-in
    (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) set-expr)))))

(define (bd-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bd-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (bd-ineq . forms) (apply ineq (map bd-idx forms)))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (bd-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (bd-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `ai' every context conjunction, to exhaustion.
(define (bd-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an ASSUMPTION lands, and return what landed.  One `di' takes a
;;; GUARDED universal whole -- binder and guard together -- but on an UNGUARDED
;;; one, (FORALL y (IMPLIES ...)), it peels the quantifier and stops, landing
;;; nothing; a second call then takes the antecedent.  Counting `di's is
;;; therefore not a way to reach a chosen goal, so this loops on the LANDING and
;;; errors if none ever appears.
(define (bd-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "bd-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (bd-di-landed-1!)
  (let ((new (bd-di-landed!)))
    (if (null? (cdr new))
        (car new)
        (error "bd-di-landed-1!: expected 1 landing, got"
               (map expression->string new)))))

(define (bd-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME that is ALREADY in the context -- what `di' lands when
;;; it peels an implication whose antecedent is existential.  `obtain' cannot do
;;; this: it recognises only an existential its own lane just landed.  The
;;; eigenvariable is read off by free-variable set difference, never guessed by
;;; shape, and a miss ERRORS.
(define (bd-skolem! ex)
  (let* ((fv0 (bd-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (bd-fvs (dk-asms)))))
      (if (null? fresh)
          (error "bd-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (bd-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "bd-obtain: nothing obtained for" what))
    v))

;;; d(u,v) <= r, and the same on a hypothesis.  `rr-ms-dist' brings the accessor
;;; down to abs (it sits in OPERATOR position, where `subst' cannot reach);
;;; `rr-abs-bound' turns the abs into the pair of linear bounds.
(define (bd-dist! u v r . prem)
  (have! (list '<= (list '(DIST RR-MS) u v) r)
    (lambda ()
      (mac 'rr-ms-dist)
      (mac 'rr-abs-bound)
      (bd-goal-and! (lambda () (apply bd-ineq prem))))))

(define (bd-unpack-dist! u v r)
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) u v) r))
  (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- u v)) r))
  (dk-split! (list 'AND (list '<= (list '- r) (list '- u v))
                       (list '<= (list '- u v) r))))

(define (bd-in-pts! t) (have! (list 'IN t '(PTS RR-MS)) (lambda () (slot 'PTS) (ass))))

;;; ---- the statement and the set it creeps along -----------------------

;;; BOUNDED(u): f is bounded above on [a,u].
(define (bd-bound-on u)
  (list 'FORSOME 'k_
    (list 'AND '(IN k_ RR)
      (list 'FORALL 'z_
        (list 'IMPLIES (list 'IN 'z_ (list 'CCINT 'a u)) '(<= (f z_) k_))))))

(define bd-set
  (list 'SEP 'x_ 'RR
    (list 'AND (list 'AND '(<= a x_) '(<= x_ b)) (bd-bound-on 'x_))))

(define bd-stmt
  (forall-guarded '(f a b)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(<= a b)
          '(FORALL x (IMPLIES (IN x (CCINT a b))
                              (IS-CONTINUOUS-AT RR-MS RR-MS f x))))
    (bd-bound-on 'b)))

;;; The local step, in the exact shape ccint-creep's last hypothesis takes when
;;; its a, b and G are instantiated here.  Built from flat lists: a formula this
;;; deep is where a miscounted parenthesis reads as a different theorem.
(define bd-local
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT a b))
      (list 'FORSOME 'd_
        (list 'AND '(IN d_ RR)
          (list 'AND '(< 0 d_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ bd-set) '(< (- t_ d_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT a b)) '(<= y_ (+ t_ d_)))
                      (list 'IN 'y_ bd-set))))))))))

;;; ---- eigenvariables set as the local step runs -----------------------
(define bd-t #f)          ; the point of [a,b] the local step is at
(define bd-d #f)          ; the continuity delta there, at eps = 1
(define bd-w #f)          ; the member of G just to the left of t
(define bd-k #f)          ; the bound w carries on [a,w]
(define bd-merged #f)     ; the merged bound: k and f(t)+1 are both below it.
                          ; NOT spelled `bd-K': MIT Scheme folds symbols to
                          ; lower case, so `bd-K' IS `bd-k' -- the merged bound
                          ; silently overwrote the inherited one, and the finder
                          ; for k's bounding universal then matched nothing.
(define bd-y #f)          ; the point of [a, t+d] being placed in G

;;; ---- context finders -------------------------------------------------

;;; forall z in [a,w]. f(z) <= k -- the bound w carries
(define (bd-forall-k)
  (bd-find 'k-bound
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) '<=)
                            (equal? (caddr (caddr body)) bd-k)))))))

;;; forall p in PTS(RR-MS). d(t,p) <= delta => d(f t, f p) <= 1
(define (bd-forall-delta)
  (bd-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f bd-d)
                     (not (dk-contains? f 'POS-RR))))))

;;; forall eps. POS-RR(eps) => forsome delta. ... -- the unfolded continuity
(define (bd-forall-eps)
  (bd-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))

(define (bd-forall-cont)
  (bd-find 'cont
    ;; Discriminate on the CONSEQUENT.  `contains IS-CONTINUOUS-AT' is not
    ;; enough: continuous-bounded-above-on-ccint carries the same continuity
    ;; universal in its own ANTECEDENT, and once that theorem has been cited
    ;; its instantiation chain sits nearer the top of the context than the
    ;; hypothesis does -- so the loose test instantiated the wrong theorem, at
    ;; b := t, and silently landed nothing usable.
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body))
                            (eq? (car (caddr body)) 'IS-CONTINUOUS-AT)))))))

;;; ---- the local step, innermost outward -------------------------------

;;; goal: (<= (f z) K), with MEM = (IN z (CCINT a y)) the assumption just landed.
(define (bd-value-le-K! z mem)
  (mac-h 'ccint-membership mem)
  (bd-split!)
  (fact 'fun-apply-type-c 'f 'RR 'RR z)
  (have! (list 'AND (list 'IN z 'RR) (list 'IN bd-w 'RR)))
  (fact 'rr-leq-total z bd-w)
  (use-cases (list (list '<= z bd-w) (list '<= bd-w z))
    ;; z lies in the conquered part [a,w]: the inherited bound k does it.
    (lambda ()
      (have! (list 'IN z (list 'CCINT 'a bd-w))
        (lambda () (mac 'ccint-membership) (from-context!)))
      (inst+ (bd-forall-k) z)
      (bd-ineq (list '<= (list 'f z) bd-k) (list '<= bd-k bd-merged)))
    ;; z lies in the delta-neighbourhood of t: continuity does it.
    (lambda ()
      (fact 'rr-sub-in-rr bd-t z)
      (bd-dist! bd-t z bd-d
                (list '< (list '- bd-t bd-d) bd-w)
                (list '<= bd-w z)
                (list '<= z bd-y)
                (list '<= bd-y (list '+ bd-t bd-d)))
      (bd-in-pts! z)
      (inst+ (bd-forall-delta) z)
      (fact 'rr-sub-in-rr (list 'f bd-t) (list 'f z))
      (bd-unpack-dist! (list 'f bd-t) (list 'f z) 1)
      (bd-ineq (list '<= '(- 1) (list '- (list 'f bd-t) (list 'f z)))
               (list '<= (list '+ (list 'f bd-t) 1) bd-merged)))))

;;; goal: forsome k. k in RR and f is bounded by k on [a,y].  Witness bd-merged.
(define (bd-bounded-on-y!)
  (ew bd-merged)
  (bd-goal-and!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IN)
         (ass)
         (let ((mem (bd-di-landed-1!)))
           (bd-value-le-K! (cadr mem) mem))))))

;;; goal: (IN y G), with the y-membership and y <= t+d already in context.
(define (bd-y-in-set!)
  (mac-h 'ccint-membership (list 'IN bd-y '(CCINT a b)))
  (bd-split!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (ass)                                     ; (IN y RR)
         (bd-goal-and!                             ; a <= y, y <= b, BOUNDED(y)
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME) (bd-bounded-on-y!) (ass))))))
   (dk-opened (lambda () (sep-mi)))))

;;; goal: forall y in [a,b] with y <= t+d. y in G -- under the assumption that
;;; some member of G already exceeds t - d.
(define (bd-reach!)
  (di)
  (set! bd-w (bd-skolem!
              (bd-find 'reach
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                 (dk-contains? f bd-set))))))
  (sep-me (bd-mem-in bd-set))
  (bd-split!)
  (set! bd-k (bd-skolem!
              (bd-find 'inherited
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                 (dk-contains? f (list 'CCINT 'a bd-w)))))))
  ;; K bounds both the inherited k and f(t) + 1
  (fact 'fun-apply-type-c 'f 'RR 'RR bd-t)
  (have! '(IN 1 RR) (lambda () (arith)))
  (have! (list 'AND (list 'IN (list 'f bd-t) 'RR) '(IN 1 RR)))
  (fact 'rr-add-closed (list 'f bd-t) 1)
  (have! (list 'AND (list 'IN bd-k 'RR)
                    (list 'IN (list '+ (list 'f bd-t) 1) 'RR)))
  (set! bd-merged (bd-skolem!
              (dk-deepest
               (lambda () (fact 'rr-upper-of-two bd-k (list '+ (list 'f bd-t) 1))))))
  (let ((and-y (bd-di-landed-1!)))
    (set! bd-y (cadr (cadr and-y)))
    (dk-split! and-y))
  (bd-y-in-set!))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff bd-stmt))
(bd-peel!)

;;; ---- G is a subset of RR, contains a, and b bounds it ----------------

(have! (list 'SUBSET bd-set 'RR)
  (lambda () (mac 'subset-def) (di) (sep-me (bd-mem-in bd-set)) (ass)))

(fact 'rr-leq-reflexive 'a)
(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
(fact 'rr-leq-reflexive '(f a))

;;; f is bounded by f(a) on [a,a]: the only member of [a,a] is a itself.
(have! (bd-bound-on 'a)
  (lambda ()
    (ew '(f a))
    (bd-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (let* ((mem (bd-di-landed-1!))
                  (z (cadr mem)))
             (mac-h 'ccint-membership mem)
             (bd-split!)
             (have! (list 'AND (list 'IN z 'RR) '(IN a RR)))
             (have! (list 'AND (list '<= z 'a) (list '<= 'a z)))
             (fact 'rr-leq-antisymmetric z 'a)
             (subst (list '= z 'a))
             (ass)))))))

(have! (list 'IN 'a bd-set)
  (lambda () (for-each (lambda (k) (dk-focus! k) (from-context!))
                       (dk-opened (lambda () (sep-mi))))))

(have! (list 'RR-UPPER-BOUND bd-set 'b)
  (lambda ()
    (mac 'rr-upper-bound)
    (for-each (lambda (k)
                (dk-focus! k)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (di) (sep-me (bd-mem-in bd-set)) (bd-split!) (ass))))
              (dk-opened (lambda () (di))))))

;;; ---- the local step --------------------------------------------------

(have! bd-local
  (lambda ()
    (let ((mem (bd-di-landed-1!)))
      (set! bd-t (cadr mem))
      ;; instantiate continuity BEFORE unfolding the interval membership:
      ;; `mac-h' replaces the assumption it unfolds.
      (inst+ (bd-forall-cont) bd-t)
      (mac-h 'ccint-membership mem)
      (bd-split!))
    (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS 'f bd-t))
    (bd-split!)
    (have! '(POS-RR 1) (lambda () (mac 'pos-rr) (bd-goal-and! (lambda () (arith)))))
    (set! bd-d (bd-obtain 'delta (lambda () (inst+ (bd-forall-eps) 1))))
    (mac-h 'pos-rr (list 'POS-RR bd-d))
    (bd-split!)
    (have! (list 'AND (list '<= 0 bd-d) (list 'NOT (list '= 0 bd-d))))
    (fact 'rr-le-ne-lt 0 bd-d)
    (ew bd-d)
    (bd-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IMPLIES) (bd-reach!) (ass))))))

;;; ---- creep, and read the bound at b off the result -------------------

(let ((at-b (dk-fact! 'ccint-creep 'a 'b bd-set)))
  (sep-me at-b)
  (bd-split!)
  (ass))

(qed 'continuous-bounded-above-on-ccint)
(topic! 'continuous-bounded-above-on-ccint 'analysis)
(alias! 'continuous-bounded-above-on-ccint
        "boundedness theorem" "a continuous function on a closed interval is bounded")
