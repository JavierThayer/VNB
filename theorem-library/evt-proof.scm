;;; evt-proof.scm -- the EXTREME VALUE THEOREM (max form), PROVEN.
;;;
;;;   f in FUN(RR,RR), a <= b, f continuous at every point of [a,b]
;;;     =>  forsome c in [a,b].  forall x in [a,b].  f(x) <= f(c)
;;;
;;; `extreme-value-max' was an ASSERTED support (theorem-library/extreme-value)
;;; carrying a `reference' warrant and appearing in ELEVEN bills -- the only
;;; asserted MATHEMATICS in the Fermat -> Rolle -> MVT -> Taylor tower, the rest
;;; of that tower's debt being glue.  It could not be proved because nothing in
;;; the tree said [a,b] was compact.  The route here does not need compactness:
;;; it is the supremum route, twice, through `ccint-creep'.
;;;
;;; THE ROUTE.
;;;
;;;   1. f is BOUNDED ABOVE on [a,b] (theorem-library/ccint-bounded), so the
;;;      image  IMG = { p in RR : p = f(q) for some q in [a,b] }  is a set of
;;;      reals, inhabited by f(a) and bounded above.  M = SUP(IMG) exists.
;;;
;;;   2. Excluded middle on "M is attained".  If it is, the witness c is the
;;;      argmax: f(x) is in IMG for every x in [a,b], so f(x) <= M = f(c).
;;;
;;;   3. If it is NOT, then f(z) < M for every z in [a,b] -- f(z) <= M because M
;;;      bounds IMG, and f(z) /= M because nothing attains it -- and a SECOND
;;;      creep contradicts that.  Creep along
;;;
;;;          T = { x in [a,b] : some k < M bounds f on [a,x] }.
;;;
;;;      a is in T (take k = f(a) < M).  At t in [a,b], continuity at
;;;      eps = (M - f(t))/2 gives a delta with f(z) <= f(t) + eps for z within
;;;      delta, and f(t) + eps = M - eps < M; merging that with the k inherited
;;;      from the left half by `rr-upper-of-two-below' keeps the merged bound
;;;      STRICTLY under M, which is what makes the creep's invariant survive.
;;;      So b is in T: some k < M bounds f on all of [a,b].  But then k is an
;;;      upper bound of IMG, so M <= k by rr-sup-least, and with k <= M
;;;      antisymmetry gives k = M against k < M.
;;;
;;; WHY THE BOUND MUST STAY BELOW M, and why `rr-upper-of-two' will not do.
;;; That lemma returns SOME common upper bound of two reals, which may overshoot
;;; M; `rr-upper-of-two-below' returns one of the two arguments, so it inherits
;;; their strict bound.  The boundedness creep did not care -- any bound would
;;; do there -- and this is the one place where the two creeps differ in
;;; substance rather than in bookkeeping.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.  Order completeness and the RR field
;;; and order axioms are primitive; ccint-creep, ccint-bounded, rr-sup-approx,
;;; ccint-membership, rr-pos-halvable and the rr-order-basics shelf are all
;;; theorems; `ineq' and `arith' add no debt.
;;;
;;; THE MIN FORM is still asserted.  It is not a copy of this file: the honest
;;; cheap route is one lemma -- z |-> -f(z) is continuous where f is -- after
;;; which extreme-value-min is extreme-value-max at that lambda, with `rr-le-neg'
;;; turning the argmax back into an argmin.  See the note at the end of
;;; theorem-library/extreme-value.scm.
;;;
;;; Loads after ccint-bounded, ccint-creep, ccint-basics, rr-halving,
;;; rr-order-basics (rr-upper-of-two-below, rr-le-ne-lt, rr-sub-ne-zero),
;;; rr-ms-dist, rr-abs-basics, metric-continuity, subset-lemmas.

;;; ---- file-local driver helpers (the `ev-' prefix) --------------------

(define (ev-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

(define (ev-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ev-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (ev-mem-in set-expr)
  (ev-find 'mem-in
    (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) set-expr)))))

(define (ev-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ev-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (ev-ineq . forms) (apply ineq (map ev-idx forms)))

(define (ev-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ev-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (ev-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `di' until an ASSUMPTION lands.  One `di' takes a GUARDED universal whole,
;;; but on an unguarded (FORALL y (IMPLIES ...)) it peels the quantifier and
;;; stops, landing nothing.  Loop on the LANDING, and error if none appears.
(define (ev-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "ev-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (ev-di-landed-1!)
  (let ((new (ev-di-landed!)))
    (if (null? (cdr new))
        (car new)
        (error "ev-di-landed-1!: expected 1 landing, got"
               (map expression->string new)))))

(define (ev-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the context.  `obtain' recognises only an
;;; existential its own lane landed, so it cannot do this one.  The
;;; eigenvariable is read off by free-variable set difference; a miss ERRORS.
(define (ev-skolem! ex)
  (let* ((fv0 (ev-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (ev-fvs (dk-asms)))))
      (if (null? fresh)
          (error "ev-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (ev-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "ev-obtain: nothing obtained for" what))
    v))

(define (ev-dist! u v r . prem)
  (have! (list '<= (list '(DIST RR-MS) u v) r)
    (lambda ()
      (mac 'rr-ms-dist)
      (mac 'rr-abs-bound)
      (ev-goal-and! (lambda () (apply ev-ineq prem))))))

(define (ev-unpack-dist! u v r)
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) u v) r))
  (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- u v)) r))
  (dk-split! (list 'AND (list '<= (list '- r) (list '- u v))
                       (list '<= (list '- u v) r))))

(define (ev-in-pts! t) (have! (list 'IN t '(PTS RR-MS)) (lambda () (slot 'PTS) (ass))))

;;; ---- the statement, the image, and the set the second creep runs on ---

;;; Reproduced VERBATIM from the `add-to-pss' support this file retires
;;; (theorem-library/extreme-value.scm), so that every citer -- rolle-proof and
;;; through it the whole MVT arc -- sees the same formula it always saw.
(define ev-stmt
  '(FORALL f (FORALL a (FORALL b
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (<= a b))))
     (IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b))
                 (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
       (FORSOME c (AND (IN c (CCINT a b))
                  (FORALL x (IMPLIES (IN x (CCINT a b))
                    (<= (f x) (f c))))))))))))

;;; IMG = f([a,b]), as a separation over RR.  Its binders are p_ and q_, not
;;; the z_ / k_ the creeping set below uses: IMG occurs INSIDE that set (in the
;;; guard k_ < SUP(IMG)), and distinct binders keep the nesting legible.
(define ev-img
  (list 'SEP 'p_ 'RR
    (list 'FORSOME 'q_ (list 'AND '(IN q_ (CCINT a b)) '(= p_ (f q_))))))

(define ev-sup (list 'SUP ev-img))

(define ev-attained
  (list 'FORSOME 'c_ (list 'AND '(IN c_ (CCINT a b)) (list '= '(f c_) ev-sup))))

;;; SBOUND(u): some k STRICTLY below M bounds f above on [a,u].
(define (ev-sbound-on u)
  (list 'FORSOME 'k_
    (list 'AND (list 'AND '(IN k_ RR) (list '< 'k_ ev-sup))
      (list 'FORALL 'z_
        (list 'IMPLIES (list 'IN 'z_ (list 'CCINT 'a u)) '(<= (f z_) k_))))))

(define ev-set
  (list 'SEP 'x_ 'RR
    (list 'AND (list 'AND '(<= a x_) '(<= x_ b)) (ev-sbound-on 'x_))))

;;; f(z) < M for every z of [a,b] -- what "M is not attained" comes to.
(define ev-strict-all
  (list 'FORALL 'z_
    (list 'IMPLIES '(IN z_ (CCINT a b)) (list '< '(f z_) ev-sup))))

;;; The local step, in the exact shape ccint-creep's last hypothesis takes when
;;; its a, b and G are instantiated here.  Built from flat lists.
(define ev-local
  (list 'FORALL 't_
    (list 'IMPLIES '(IN t_ (CCINT a b))
      (list 'FORSOME 'd_
        (list 'AND '(IN d_ RR)
          (list 'AND '(< 0 d_)
            (list 'IMPLIES
              (list 'FORSOME 'w_ (list 'AND (list 'IN 'w_ ev-set) '(< (- t_ d_) w_)))
              (list 'FORALL 'y_
                (list 'IMPLIES (list 'AND '(IN y_ (CCINT a b)) '(<= y_ (+ t_ d_)))
                      (list 'IN 'y_ ev-set))))))))))

;;; ---- eigenvariables --------------------------------------------------
(define ev-t #f)          ; the point of [a,b] the local step is at
(define ev-h #f)          ; half the gap M - f(t): the continuity eps
(define ev-d #f)          ; the continuity delta at that eps
(define ev-w #f)          ; the member of T just to the left of t
(define ev-lo #f)         ; the strict bound w carries on [a,w]      (NOT `ev-k')
(define ev-merged #f)     ; the merged strict bound, still below M
(define ev-y #f)          ; the point of [a, t+d] being placed in T

;;; MIT Scheme folds symbols to lower case, so a companion spelled `ev-K' WOULD
;;; BE `ev-k': the second assignment would silently overwrite the first and the
;;; finder for the first one's bounding universal would then match nothing.
;;; That is why these are `ev-lo' and `ev-merged'.

;;; ---- context finders -------------------------------------------------

;;; forall z in [a,u]. f(z) <= BOUND
(define (ev-forall-bounding bound)
  (ev-find 'bounding
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) '<=)
                            (equal? (caddr (caddr body)) bound)))))))

;;; forall p in IMG. p <= M -- the unfolded rr-sup-upper
(define (ev-forall-ub)
  (ev-find 'ub
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) '<=)
                            (equal? (caddr (caddr body)) ev-sup)))))))

;;; forall t. RR-UPPER-BOUND(IMG,t) => M <= t -- rr-sup-least, partly peeled
(define (ev-forall-least)
  (ev-find 'least
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (cadr body))
                            (eq? (car (cadr body)) 'RR-UPPER-BOUND)))))))

(define (ev-forall-delta)
  (ev-find 'delta
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'DIST) (dk-contains? f ev-d)
                     (not (dk-contains? f 'POS-RR))))))

(define (ev-forall-eps)
  (ev-find 'eps
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (dk-contains? f 'POS-RR) (dk-contains? f 'DIST)))))

(define (ev-forall-cont)
  (ev-find 'cont
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

(define (ev-forall-strict)
  (ev-find 'strict
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) '<)
                            (equal? (caddr (caddr body)) ev-sup)))))))

;;; ---- IMG bookkeeping -------------------------------------------------

;;; (IN (f u) IMG), for u already known to lie in [a,b] with f(u) in RR.
(define (ev-img-member! u)
  (have! (list 'IN (list 'f u) ev-img)
    (lambda ()
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (ew u)
                             (ev-goal-and!
                              (lambda () (if (eq? (car (dk-goal)) '=) (rfl) (ass)))))))
                (dk-opened (lambda () (sep-mi)))))))

;;; goal (<= p BOUND) for the eigenvariable p of IMG, with FA the universal
;;; that bounds f by BOUND on [a,b].
(define (ev-img-le! bound)
  (let ((p (cadr (dk-goal))))
    (sep-me (ev-mem-in ev-img))
    (let ((q (ev-skolem!
              (ev-find 'img-witness
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                 (dk-contains? f p)))))))
      (inst+ (ev-forall-bounding bound) q)
      (subst (list '= p (list 'f q)))
      (ass))))

;;; RR-UPPER-BOUND(IMG, BOUND), from a universal bounding f by BOUND on [a,b].
(define (ev-img-upper! bound)
  (have! (list 'RR-UPPER-BOUND ev-img bound)
    (lambda ()
      (mac 'rr-upper-bound)
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (di) (ev-img-le! bound))))
                (dk-opened (lambda () (di)))))))

;;; ---- the second creep's local step, innermost outward ----------------

;;; goal: (<= (f z) merged), with MEM = (IN z (CCINT a y)) just landed.
(define (ev-value-le-merged! z mem)
  (mac-h 'ccint-membership mem)
  (ev-split!)
  (fact 'fun-apply-type-c 'f 'RR 'RR z)
  (have! (list 'AND (list 'IN z 'RR) (list 'IN ev-w 'RR)))
  (fact 'rr-leq-total z ev-w)
  (use-cases (list (list '<= z ev-w) (list '<= ev-w z))
    (lambda ()
      (have! (list 'IN z (list 'CCINT 'a ev-w))
        (lambda () (mac 'ccint-membership) (from-context!)))
      (inst+ (ev-forall-bounding ev-lo) z)
      (ev-ineq (list '<= (list 'f z) ev-lo) (list '<= ev-lo ev-merged)))
    (lambda ()
      (fact 'rr-sub-in-rr ev-t z)
      (ev-dist! ev-t z ev-d
                (list '< (list '- ev-t ev-d) ev-w)
                (list '<= ev-w z)
                (list '<= z ev-y)
                (list '<= ev-y (list '+ ev-t ev-d)))
      (ev-in-pts! z)
      (inst+ (ev-forall-delta) z)
      (fact 'rr-sub-in-rr (list 'f ev-t) (list 'f z))
      (ev-unpack-dist! (list 'f ev-t) (list 'f z) ev-h)
      (ev-ineq (list '<= (list '- ev-h) (list '- (list 'f ev-t) (list 'f z)))
               (list '<= (list '+ (list 'f ev-t) ev-h) ev-merged)))))

;;; goal: forsome k. k in RR, k < M, and k bounds f on [a,y].  Witness ev-merged.
(define (ev-sbounded-on-y!)
  (ew ev-merged)
  (ev-goal-and!
   (lambda ()
     (let ((g (dk-goal)))
       (if (eq? (car g) 'FORALL)
           (let ((mem (ev-di-landed-1!)))
             (ev-value-le-merged! (cadr mem) mem))
           (ass))))))

;;; goal: (IN y T)
(define (ev-y-in-set!)
  (mac-h 'ccint-membership (list 'IN ev-y '(CCINT a b)))
  (ev-split!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (car (dk-goal)) 'IN)
         (ass)
         (ev-goal-and!
          (lambda ()
            (if (eq? (car (dk-goal)) 'FORSOME) (ev-sbounded-on-y!) (ass))))))
   (dk-opened (lambda () (sep-mi)))))

;;; goal: forall y in [a,b] with y <= t+d. y in T, under "some member of T
;;; already exceeds t - d".
(define (ev-reach!)
  (di)
  (set! ev-w (ev-skolem!
              (ev-find 'reach
                (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                 (dk-contains? f ev-set))))))
  (sep-me (ev-mem-in ev-set))
  (ev-split!)
  (set! ev-lo (ev-skolem!
               (ev-find 'inherited
                 (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                  (dk-contains? f (list 'CCINT 'a ev-w)))))))
  ;; f(t) + h is below M, and so is the inherited bound; merge them BELOW M.
  ;; `rr-add-closed' has an AND antecedent, which `fact' will not split, so the
  ;; conjunction is landed first -- without it the citation lands the
  ;; implication and every later step runs on an undetached chain.
  (have! (list 'AND (list 'IN (list 'f ev-t) 'RR) (list 'IN ev-h 'RR)))
  (fact 'rr-add-closed (list 'f ev-t) ev-h)
  (have! (list '< (list '+ (list 'f ev-t) ev-h) ev-sup)
    (lambda ()
      (mac '<)
      (ev-goal-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'NOT)
             (begin (di)
                    (have! (list '= 0 ev-h)
                      (lambda () (ev-ineq (list '= (list '+ (list 'f ev-t) ev-h) ev-sup)
                                          (list '= (list '+ ev-h ev-h)
                                                (list '- ev-sup (list 'f ev-t))))))
                    (ai (list 'NOT (list '= 0 ev-h))))
             (ev-ineq (list '= (list '+ ev-h ev-h)
                            (list '- ev-sup (list 'f ev-t)))
                      (list '<= 0 ev-h)))))))
  (set! ev-merged
        (ev-skolem!
         (dk-deepest
          (lambda () (fact 'rr-upper-of-two-below ev-lo
                           (list '+ (list 'f ev-t) ev-h) ev-sup)))))
  (let ((and-y (ev-di-landed-1!)))
    (set! ev-y (cadr (cadr and-y)))
    (dk-split! and-y))
  (ev-y-in-set!))

;;; ---- the two branches of "is M attained?" ----------------------------

(define (ev-hit!)
  (let ((c (ev-skolem! ev-attained)))
    (ew c)
    (ev-goal-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'FORALL)
           (let* ((mem (ev-di-landed-1!))
                  (x (cadr mem)))
             (subst (list '= (list 'f c) ev-sup))
             (fact 'subset-mem-fwd '(CCINT a b) 'RR x)
             (fact 'fun-apply-type-c 'f 'RR 'RR x)
             (ev-img-member! x)
             (inst+ (ev-forall-ub) (list 'f x))
             (ass))
           (ass))))))

(define (ev-miss!)
  ;; every value is STRICTLY below M
  (have! ev-strict-all
    (lambda ()
      (let* ((mem (ev-di-landed-1!))
             (z (cadr mem)))
        (fact 'subset-mem-fwd '(CCINT a b) 'RR z)
        (fact 'fun-apply-type-c 'f 'RR 'RR z)
        (ev-img-member! z)
        (inst+ (ev-forall-ub) (list 'f z))
        (have! (list 'NOT (list '= (list 'f z) ev-sup))
          (lambda ()
            (di)
            (have! ev-attained (lambda () (ew z) (from-context!)))
            (ai (list 'NOT ev-attained))))
        (have! (list 'AND (list 'IN (list 'f z) 'RR) (list 'IN ev-sup 'RR)))
        (have! (list 'AND (list '<= (list 'f z) ev-sup)
                          (list 'NOT (list '= (list 'f z) ev-sup))))
        (fact 'rr-le-ne-lt (list 'f z) ev-sup)
        (ass))))

  ;; T is a subset of RR, contains a, and b bounds it
  (have! (list 'SUBSET ev-set 'RR)
    (lambda () (mac 'subset-def) (di) (sep-me (ev-mem-in ev-set)) (ass)))
  (inst+ (ev-forall-strict) 'a)                      ; f(a) < M
  (have! (ev-sbound-on 'a)
    (lambda ()
      (ew '(f a))
      (ev-goal-and!
       (lambda ()
         (let ((g (dk-goal)))
           (if (eq? (car g) 'FORALL)
               (let* ((mem (ev-di-landed-1!))
                      (z (cadr mem)))
                 (mac-h 'ccint-membership mem)
                 (ev-split!)
                 (have! (list 'AND (list 'IN z 'RR) '(IN a RR)))
                 (have! (list 'AND (list '<= z 'a) (list '<= 'a z)))
                 (fact 'rr-leq-antisymmetric z 'a)
                 (subst (list '= z 'a))
                 (ass))
               (ass)))))))
  (have! (list 'IN 'a ev-set)
    (lambda () (for-each (lambda (k) (dk-focus! k) (from-context!))
                         (dk-opened (lambda () (sep-mi))))))
  (have! (list 'RR-UPPER-BOUND ev-set 'b)
    (lambda ()
      (mac 'rr-upper-bound)
      (for-each (lambda (k)
                  (dk-focus! k)
                  (if (eq? (car (dk-goal)) 'IN)
                      (ass)
                      (begin (di) (sep-me (ev-mem-in ev-set)) (ev-split!) (ass))))
                (dk-opened (lambda () (di))))))

  ;; the local step
  (have! ev-local
    (lambda ()
      (let ((mem (ev-di-landed-1!)))
        (set! ev-t (cadr mem))
        (inst+ (ev-forall-cont) ev-t)
        (inst+ (ev-forall-strict) ev-t)
        (mac-h 'ccint-membership mem)
        (ev-split!))
      (fact 'fun-apply-type-c 'f 'RR 'RR ev-t)
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS 'f ev-t))
      (ev-split!)
      ;; eps = half the gap M - f(t), which is positive because f(t) < M
      (fact 'rr-sub-in-rr ev-sup (list 'f ev-t))
      (mac-h '< (list '< (list 'f ev-t) ev-sup))
      (ev-split!)
      (fact 'neq-sym (list 'f ev-t) ev-sup)
      (fact 'rr-sub-ne-zero ev-sup (list 'f ev-t))
      (fact 'neq-sym (list '- ev-sup (list 'f ev-t)) 0)
      (have! (list 'POS-RR (list '- ev-sup (list 'f ev-t)))
        (lambda ()
          (mac 'pos-rr)
          (ev-goal-and!
           (lambda ()
             (if (equal? (dk-goal) (list '<= 0 (list '- ev-sup (list 'f ev-t))))
                 (ev-ineq (list '<= (list 'f ev-t) ev-sup))
                 (ass))))))
      (set! ev-h (ev-obtain 'half
                   (lambda () (fact 'rr-pos-halvable
                                    (list '- ev-sup (list 'f ev-t))))))
      ;; the continuity delta at eps = h, taken BEFORE POS-RR(h) is unfolded
      (set! ev-d (ev-obtain 'delta (lambda () (inst+ (ev-forall-eps) ev-h))))
      (mac-h 'pos-rr (list 'POS-RR ev-h))
      (ev-split!)
      (have! (list 'AND (list '<= 0 ev-h) (list 'NOT (list '= 0 ev-h))))
      (fact 'rr-le-ne-lt 0 ev-h)
      (mac-h 'pos-rr (list 'POS-RR ev-d))
      (ev-split!)
      (have! (list 'AND (list '<= 0 ev-d) (list 'NOT (list '= 0 ev-d))))
      (fact 'rr-le-ne-lt 0 ev-d)
      (ew ev-d)
      (ev-goal-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IMPLIES) (ev-reach!) (ass))))))

  ;; creep to b, and contradict the leastness of M
  (let ((at-b (dk-fact! 'ccint-creep 'a 'b ev-set)))
    (sep-me at-b)
    (ev-split!)
    (let ((kb (ev-skolem!
               (ev-find 'at-b
                 (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                  (dk-contains? f '(CCINT a b))
                                  (dk-contains? f ev-sup)))))))
      (ev-img-upper! kb)
      (inst+ (ev-forall-least) kb)                   ; M <= kb
      (mac-h '< (list '< kb ev-sup))
      (ev-split!)
      (have! (list 'AND (list 'IN kb 'RR) (list 'IN ev-sup 'RR)))
      (have! (list 'AND (list '<= kb ev-sup) (list '<= ev-sup kb)))
      (fact 'rr-leq-antisymmetric kb ev-sup)
      (ai (list 'NOT (list '= kb ev-sup))))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff ev-stmt))
(ev-peel!)
(ev-split!)

(have! '(SUBSET (CCINT a b) RR)
  (lambda ()
    (mac 'subset-def)
    (let ((mem (ev-di-landed-1!)))
      (mac-h 'ccint-membership mem)
      (ev-split!)
      (ass))))

(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(have! '(IN a (CCINT a b)) (lambda () (mac 'ccint-membership) (from-context!)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
;; f(a) <= f(a): what the [a,a] base case of the second creep closes on, after
;; antisymmetry has collapsed its z to a.
(fact 'rr-leq-reflexive '(f a))

;;; IMG is a set of reals, inhabited, and bounded above -- so M = SUP(IMG) exists
(have! (list 'SUBSET ev-img 'RR)
  (lambda () (mac 'subset-def) (di) (sep-me (ev-mem-in ev-img)) (ass)))
(ev-img-member! 'a)
(have! (list 'FORSOME 'x_ (list 'IN 'x_ ev-img)) (lambda () (ew '(f a)) (ass)))

(define ev-bound
  (ev-skolem! (dk-fact! 'continuous-bounded-above-on-ccint 'f 'a 'b)))
(ev-img-upper! ev-bound)
(have! (list 'RR-BOUNDED-ABOVE ev-img)
  (lambda () (mac 'rr-bounded-above) (ew ev-bound) (ass)))

(fact 'rr-sup-in ev-img)
(fact 'rr-sup-upper ev-img)
(mac-h 'rr-upper-bound (list 'RR-UPPER-BOUND ev-img ev-sup))
(ev-split!)
(fact 'rr-sup-least ev-img)

;;; is the supremum attained?
(use-em ev-attained ev-hit! ev-miss!)

(qed 'extreme-value-max)
(topic! 'extreme-value-max 'analysis)
(alias! 'extreme-value-max "Extreme Value Theorem" "EVT"
                           "Weierstrass extreme value theorem")
