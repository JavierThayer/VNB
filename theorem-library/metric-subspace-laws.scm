;;; metric-subspace-laws.scm -- the laws of SUBSPACE-MS and RESTRICT
;;; (structure-library/metric-subspace.scm).  Everything here is PROVEN; the
;;; definition file asserts nothing.
;;;
;;; PROVEN below, all `modulo 0':
;;;   subspace-pts              PTS(SUBSPACE-MS(s,A)) == A               (read-off)
;;;   subspace-dist-slot        DIST(SUBSPACE-MS(s,A)) == the lambda     (read-off)
;;;   subspace-dist             the distance VALUE on points of A
;;;   subspace-is-metric-space  a subset of a metric space is a metric space
;;;   restrict-apply            RESTRICT(f,A)(x) == f(x)  for x in A
;;;   restrict-in-fun           f in FUN(D,B), A subset D => RESTRICT(f,A) in FUN(A,B)
;;;   subspace-whole            SUBSPACE-MS(s, PTS s) has the points and the
;;;                             distance of s (the bridge of the design note, s.3.3)
;;;   subspace-ball-membership  y in BALL(sub,c,r) iff y in BALL(s,c,r) and y in A
;;;   subspace-ball             BALL(sub,c,r) = BALL(s,c,r) ^ A
;;;   subspace-open-trace       U open in s  =>  U ^ A open in the subspace
;;;   subspace-open-is-trace    V open in the subspace => V = U ^ A, U open in s
;;;   restrict-continuous-at    continuity at a point of A restricts
;;;   subspace-converges-to     convergence in the subspace vs in s
;;;   closed-limit-in           a limit of a sequence in a closed set is in it
;;;   subspace-is-cauchy-seq    Cauchy in the subspace vs in s
;;;   subspace-complete         a closed subspace of a complete space is complete
;;;
;;; THE TWO READ-OFFS ARE THE DOOR.  SUBSPACE-MS is a two-parameter
;;; `def-functoid', so it has no precomputed functor projections and `slot' falls
;;; back to the accessor's own macete -- which rewrites EVERY occurrence, the one
;;; inside the constructed tuple included.  That fallback is used ONCE, here, in
;;; the two read-off proofs (the recipe of theorem-library/bdd-metric-carrier.scm:
;;; unfold the functoid, `slot', `nth-r', `qrfl').  Every later proof fires
;;; `subspace-pts' / `subspace-dist-slot' -- THEOREMS -- by name, so no file below
;;; goes near an accessor macete.
;;;
;;; NO INHABITEDNESS GUARD ANYWHERE.  A = EMPTY-SET is a legal subset and
;;; SUBSPACE-MS(s, EMPTY-SET) is a metric space: `is-metric' quantifies over the
;;; points, of which there are none, and the distance lambda over
;;; CARTESIAN(EMPTY-SET, EMPTY-SET) = EMPTY-SET is the empty function, which is a
;;; member of FUN(EMPTY-SET, RR).  Heine-Borel for CCINT(a,b) with b < a needs
;;; exactly this, so the guard must stay out.
;;;
;;; WHAT EACH BILL LEANS ON.  metric-dist-real, metric-pos, metric-self-zero,
;;; metric-zero-eq, metric-sym, metric-triangle -- all PROVEN (op-typing.scm,
;;; metric-laws.scm) -- plus subset-mem-fwd, subclass-of-set-is-set,
;;; cartesian-set-iff, fun-apply-type, fun-domain-in-set.  Nothing asserted.
;;;
;;; WINDOW (scratchpad/window.py).  lo = 1348, forced by theorem-library/rake-balls
;;; (ball-membership, ball-is-set, ball-center-in, ball-mem-from-le); metric-laws
;;; (1328) and pos-rr-bridges / rr-halving (744, 805, reached through dk-halve!)
;;; are above it.  hi = none: nothing cites these yet.  The load.scm slot is
;;; immediately after "theorem-library/rake-balls".  structure-library/metric-subspace
;;; must load before it and may sit anywhere after metric-space.scm -- the slot
;;; proposed is right after "structure-library/metric-topology" (line 149).
;;;
;;; Helper prefix: msub-.

;;; ---- file-local driver helpers --------------------------------------

(define (msub-open) (dk-open-leaves))
(define (msub-head g) (and (pair? g) (car g)))

;;; Split an AND goal to its atoms and run CLOSER on each.
(define (msub-and! closer)
  (if (eq? (msub-head (dk-goal)) 'AND)
      (for-each (lambda (k) (dk-focus! k) (msub-and! closer))
                (dk-opened (lambda () (di))))
      (closer)))

;;; Is there a beta redex anywhere in E?
(define (msub-has-lam? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (msub-has-lam? (car g)) (msub-has-lam? (cdr g))))
        (#t #f)))

;;; Beta to a fixpoint, guarded on PROGRESS (`lam-b' only warns when there is
;;; nothing to do, so "while there is a redex" would spin).  Run BEFORE the `di'
;;; that lands the point memberships: the enclosing guarded universal is what
;;; licenses the reduction (trunc-metric-proof.scm makes the same point).
(define (msub-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (msub-has-lam? (dk-goal)))
        (let ((before (dk-goal))) (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; Decompose every open leaf whose goal is a FORALL/IMPLIES/AND, beta-reducing
;;; first so that what an IMPLIES lands is already in DIST form.
(define (msub-drive!)
  (let loop ((fuel 200))
    (let ((k (find-first (lambda (n) (memq (msub-head (dk-goal-of n))
                                           '(FORALL IMPLIES AND)))
                         (msub-open))))
      (if (and k (> fuel 0))
          (begin (dk-focus! k) (msub-beta!)
                 (if (memq (msub-head (dk-goal)) '(FORALL IMPLIES AND)) (di) #t)
                 (loop (- fuel 1)))
          #t))))

;;; (IN x A) + SUBSET A (PTS s)  ==>  (IN x (PTS s)).
(define (msub-pt! x) (fact 'subset-mem-fwd 'A '(PTS s) x))

;;; (IN A SET), from SUBSET A (PTS s) and the sethood conjunct of
;;; IS-METRIC-SPACE(s).  `mac-h' CONSUMES the hypothesis, but every leaf is its
;;; own sequent node, so the folded IS-METRIC-SPACE(s) the siblings cite is
;;; untouched.
(define (msub-a-set!)
  (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s))
  (dk-split-all!)
  (fact 'subclass-of-set-is-set 'A '(PTS s))
  (ass))

;;; =====================================================================
;;; (1) THE POINT SET.  SUBSPACE-MS(s,A) = (A, lambda), so its carrier slot is
;;; `A' verbatim -- an unguarded read-off, true for every s and every A.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL A (== (PTS (SUBSPACE-MS s A)) A)))))
(di)
(mac 'SUBSPACE-MS)        ; (== (PTS (LIST A (VNB-LAMBDA ...))) A)
(slot 'PTS)               ; (== (nth 1 (LIST A ...)) A)
(nth-r)                   ; (== A A)
(qrfl)
(qed 'subspace-pts)
(topic! 'subspace-pts 'constructions)
(alias! 'subspace-pts "the points of a subspace are the subset")

;;; =====================================================================
;;; (2) THE DISTANCE SLOT.  Also unguarded: the second component of the tuple,
;;; verbatim.  This is the theorem every later proof fires instead of `slot'.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL A
     (== (DIST (SUBSPACE-MS s A))
         (VNB-LAMBDA (LIST sbu_ sbv_) (CARTESIAN A A) ((DIST s) sbu_ sbv_)))))))
(di)
(mac 'SUBSPACE-MS)
(slot 'DIST)              ; the OUTER (DIST (LIST ...)) and the RIGHT side's (DIST s);
(nth-r)                   ; the accessor macete does not re-descend into what it
(slot 'DIST)              ; rewrote, so the left body's (DIST s) needs a second call
(qrfl)                    ; (bdd-metric-carrier.scm does the same for PTS)
(qed 'subspace-dist-slot)
(topic! 'subspace-dist-slot 'constructions)
(alias! 'subspace-dist-slot "the distance of a subspace is the restricted distance")

;;; =====================================================================
;;; (3) THE DISTANCE VALUE, on points of A.  Stated with `==' and guarded: off
;;; A x A the left side is an application outside its lambda's domain.
;;; =====================================================================
(sp (make-wff (list 'FORALL 's (list 'FORALL 'A
     (forall-guarded '(u_ v_) '((IN u_ A) (IN v_ A))
       '(== ((DIST (SUBSPACE-MS s A)) u_ v_) ((DIST s) u_ v_)))))))
(dk-peel!)
(mac 'SUBSPACE-MS)
(slot 'DIST)
(nth-r)
(lam-b)                   ; u_, v_ are typed in A above the redex
(slot 'DIST)              ; normalise the left body's (DIST s) too
(qrfl)
(qed 'subspace-dist)
(topic! 'subspace-dist 'constructions)
(alias! 'subspace-dist "the subspace distance is the ambient distance")

;;; =====================================================================
;;; (4) A SUBSET OF A METRIC SPACE IS A METRIC SPACE.
;;;
;;; The four conjuncts of IS-METRIC-SPACE: the tuple length, the sethood of the
;;; carrier, the FUN typing of the distance, and the five metric laws.  Only the
;;; sethood has content of its own (a subclass of a set is a set); each metric
;;; law is the ambient law at points transported through `subset-mem-fwd'.
;;; =====================================================================

;;; The two leaves `lam-t' opens for the distance: the pointwise typing of the
;;; body, and the SETHOOD of CARTESIAN(A,A).
(define (msub-dist-fun-leaf!)
  (let ((g (dk-goal)))
    (cond
      ((equal? g '(IN (CARTESIAN A A) SET))
       (mac 'cartesian-set-iff)
       (for-each (lambda (k) (dk-focus! k) (msub-a-set!)) (dk-opened (lambda () (di)))))
      ((and (eq? (msub-head g) 'IN) (pair? (cadr g)) (equal? (car (cadr g)) '(DIST s)))
       (let* ((d (cadr g)) (a (cadr d)) (b (caddr d)))
         (msub-pt! a) (msub-pt! b)
         (fact 'metric-dist-real 's a b)
         (ass)))
      (#t (error "msub-dist-fun-leaf!: unexpected leaf" g)))))

;;; The five metric laws, dispatched on the shape of the leaf.  Each is one
;;; citation of the ambient law after the points are placed in PTS(s).
(define (msub-law!)
  (let ((g (dk-goal)))
    (cond
      ;; d(u,u) = 0
      ((and (eq? (msub-head g) '=) (pair? (cadr g)) (equal? (car (cadr g)) '(DIST s))
            (equal? (caddr g) 0))
       (let ((a (cadr (cadr g))))
         (msub-pt! a) (fact 'metric-self-zero 's a) (ass)))
      ;; 0 <= d(u,v)
      ((and (eq? (msub-head g) '<=) (equal? (cadr g) 0))
       (let* ((d (caddr g)) (a (cadr d)) (b (caddr d)))
         (msub-pt! a) (msub-pt! b) (fact 'metric-pos 's a b) (ass)))
      ;; d(u,v) = 0  =>  u = v   (the equation is already in context)
      ((and (eq? (msub-head g) '=) (symbol? (cadr g)))
       (let ((a (cadr g)) (b (caddr g)))
         (msub-pt! a) (msub-pt! b) (fact 'metric-zero-eq 's a b) (ass)))
      ;; d(u,v) = d(v,u)
      ((eq? (msub-head g) '=)
       (let* ((d (cadr g)) (a (cadr d)) (b (caddr d)))
         (msub-pt! a) (msub-pt! b) (fact 'metric-sym 's a b) (ass)))
      ;; d(u,w) <= d(u,v) + d(v,w)
      ((eq? (msub-head g) '<=)
       (let* ((d (cadr g)) (a (cadr d)) (c (caddr d))
              (b (caddr (cadr (caddr g)))))
         (msub-pt! a) (msub-pt! b) (msub-pt! c)
         (fact 'metric-triangle 's a b c) (ass)))
      (#t (error "msub-law!: unexpected leaf" g)))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (IS-METRIC-SPACE (SUBSPACE-MS s A))))))))
(dk-peel!)
(mac 'IS-METRIC-SPACE)      ; the GOAL only; the hypothesis stays folded
(mac 'subspace-pts)         ; PTS(SUBSPACE-MS s A) -> A
(mac 'subspace-dist-slot)   ; DIST(SUBSPACE-MS s A) -> the lambda
(msub-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((and (eq? (msub-head g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
        (mac 'SUBSPACE-MS) (len-r) (arith))
       ((equal? g '(IN A SET)) (msub-a-set!))
       ((eq? (msub-head g) 'IN)
        (for-each (lambda (k) (dk-focus! k) (msub-drive!) (msub-dist-fun-leaf!))
                  (dk-opened (lambda () (lam-t)))))
       ;; `msub-open' is GLOBAL, so the law leaves are the ones this branch
       ;; ADDED -- a bare (msub-open) here picked up a sibling's still-open
       ;; typing leaf and msub-law! died on it.
       (#t (let ((before (msub-open)))
             (mac 'is-metric) (msub-drive!)
             (for-each (lambda (k) (dk-focus! k) (msub-law!))
                       (filter (lambda (n) (not (memq n before))) (msub-open)))))))))
(qed 'subspace-is-metric-space)
(topic! 'subspace-is-metric-space 'constructions)
(alias! 'subspace-is-metric-space
        "a subset of a metric space is a metric space")

;;; =====================================================================
;;; (5) RESTRICT: the value law.
;;; =====================================================================
(sp (make-wff (list 'FORALL 'f (list 'FORALL 'A
     (forall-guarded '(u_) '((IN u_ A)) '(== ((RESTRICT f A) u_) (f u_)))))))
(dk-peel!)
(mac 'RESTRICT)
(lam-b)
(qrfl)
(qed 'restrict-apply)
(topic! 'restrict-apply 'functions)
(alias! 'restrict-apply "a restriction takes the same values")

;;; =====================================================================
;;; (6) RESTRICT: the typing.  A subset of the domain, and the codomain is
;;; unchanged.  `lam-t' owes the sethood of A, which is subclass-of-set-is-set
;;; against fun-domain-in-set.
;;; =====================================================================
(sp (make-wff '(FORALL f (FORALL dm_ (FORALL cd_ (FORALL A
     (IMPLIES (IN f (FUN dm_ cd_))
       (IMPLIES (SUBSET A dm_)
         (IN (RESTRICT f A) (FUN A cd_))))))))))
(dk-peel!)
(mac 'RESTRICT)
(for-each
 (lambda (k)
   (dk-focus! k)
   (let ((g (dk-goal)))
     (cond
       ((equal? g '(IN A SET))
        (fact 'fun-domain-in-set 'dm_ 'cd_ 'f)
        (fact 'subclass-of-set-is-set 'A 'dm_)
        (ass))
       (#t (di)
           (let ((x (cadr (cadr (dk-goal)))))
             (fact 'subset-mem-fwd 'A 'dm_ x)
             ;; the CURRIED form: `fact' will not split fun-apply-type's
             ;; conjunctive antecedent, and lands the implication silently
             (fact 'fun-apply-type-c 'f 'dm_ 'cd_ x)
             (ass))))))
 (dk-opened (lambda () (lam-t))))
(qed 'restrict-in-fun)
(topic! 'restrict-in-fun 'functions)
(alias! 'restrict-in-fun "a restriction to a subset of the domain is a function on it")

;;; =====================================================================
;;; (7) THE WHOLE SPACE.  SUBSPACE-MS(s, PTS s) has the points of s and its
;;; distance on them.  Unguarded -- IS-METRIC-SPACE(s) is not needed for either
;;; half -- so the bridge theorem of the design note (s.3.3) can cite it
;;; wherever it lands.
;;; =====================================================================
(sp (make-wff (list 'FORALL 's
     (list 'AND
       '(== (PTS (SUBSPACE-MS s (PTS s))) (PTS s))
       (forall-guarded '(u_ v_) '((IN u_ (PTS s)) (IN v_ (PTS s)))
         '(== ((DIST (SUBSPACE-MS s (PTS s))) u_ v_) ((DIST s) u_ v_)))))))
(di)
(msub-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((and (eq? (msub-head g) '==) (pair? (cadr g)) (eq? (car (cadr g)) 'PTS))
        (mac 'subspace-pts) (qrfl))
       (#t (dk-peel!)
           (fact 'subspace-dist 's '(PTS s) 'u_ 'v_)
           (ass))))))
(qed 'subspace-whole)
(topic! 'subspace-whole 'constructions)
(alias! 'subspace-whole "the subspace on all the points is the space itself")

;;; =====================================================================
;;; (8) THE BALLS OF THE SUBSPACE ARE THE TRACES OF THE BALLS.  Membership
;;; form first: it is what the open-set argument below reads.
;;;
;;; The case split on (IN y A) is the whole proof.  Inside A the two distances
;;; agree (subspace-dist) and the subset inclusion supplies (IN y (PTS s)), so
;;; the two sides are the same conjunction; outside A both sides are FALSE --
;;; each carries (IN y A) as a conjunct, the left through PTS(SUBSPACE-MS(s,A)).
;;; `prop' finishes each branch and adds no trust.
;;; =====================================================================
(define msub-space '(SUBSPACE-MS s A))
(define msub-dsub (list (list 'DIST msub-space) 'c 'y))
(define msub-damb '((DIST s) c y))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'FORALL 'A (list 'IMPLIES '(SUBSET A (PTS s))
     (list 'FORALL 'c (list 'IMPLIES '(IN c A)
       (list 'FORALL 'r (list 'FORALL 'y
         (list 'IFF (list 'IN 'y (list 'BALL msub-space 'c 'r))
                    (list 'AND (list 'IN 'y '(BALL s c r)) (list 'IN 'y 'A)))))))))))))
(dk-peel!)
(mac 'ball-membership)        ; both ball atoms at once
(mac 'subspace-pts)           ; (IN y (PTS (SUBSPACE-MS s A))) -> (IN y A)
(use-em '(IN y A)
  (lambda ()
    (fact 'subset-mem-fwd 'A '(PTS s) 'y)
    (fact 'subspace-dist 's 'A 'c 'y)
    (subst (list '== msub-dsub msub-damb))
    (prop))
  (lambda () (prop)))
(qed 'subspace-ball-membership)
(topic! 'subspace-ball-membership 'constructions)
(alias! 'subspace-ball-membership "a subspace ball is the ambient ball met with the subset")

;;; =====================================================================
;;; (9) The same, as a SET equation.  `class-extensionality' is unconditional
;;; (no sethood premise), so the pointwise iff of (8) is the whole proof.
;;; =====================================================================
(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'FORALL 'A (list 'IMPLIES '(SUBSET A (PTS s))
     (list 'FORALL 'c (list 'IMPLIES '(IN c A)
       (list 'FORALL 'r
         (list '= (list 'BALL msub-space 'c 'r)
                  '(INTERSECTION (BALL s c r) A)))))))))))
(dk-peel!)
;; The sethood of the two classes, BEFORE the citation: `forall-elim' posts the
;; side sequent  t = t  unless `pi--defined?' certifies t, and a BALL is a SEP
;; over PTS(SUBSPACE-MS(s,A)), which it does not certify.  With (IN ball SET) in
;; context the term is typed and the obligation does not arise.
(fact 'subspace-is-metric-space 's 'A)
(fact 'ball-is-set msub-space 'c 'r)
(have! (list 'FORALL 'z_
         (list 'IFF (list 'IN 'z_ (list 'BALL msub-space 'c 'r))
                    '(IN z_ (INTERSECTION (BALL s c r) A))))
  (lambda ()
    (di)
    (mac 'intersection-membership)
    (fact 'subspace-ball-membership 's 'A 'c 'r 'z_)
    (ass)))
(fact 'class-extensionality (list 'BALL msub-space 'c 'r)
                            '(INTERSECTION (BALL s c r) A))
(ass)
(qed 'subspace-ball)
(topic! 'subspace-ball 'constructions)
(alias! 'subspace-ball "the balls of a subspace are the traces of the balls")

;;; =====================================================================
;;; (10) THE TRACE OF AN OPEN SET IS OPEN IN THE SUBSPACE -- the easy half of
;;; "the open sets of the subspace are the traces of the open sets".
;;;
;;; The SAME radius serves: BALL(SUBSPACE-MS(s,A), y, r) is BALL(s,y,r) met
;;; with A (theorem 9), and a ball inside U has its trace inside U meet A.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (FORALL U (IMPLIES (IS-OPEN s U)
         (IS-OPEN (SUBSPACE-MS s A) (INTERSECTION U A))))))))))
(dk-peel!)
(fact 'subspace-is-metric-space 's 'A)
(mac 'IS-OPEN)              ; the GOAL only
(mac 'subspace-pts)         ; PTS(SUBSPACE-MS s A) -> A
(msub-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (msub-head g) 'IS-METRIC-SPACE) (ass))
       ;; U ^ A subset A
       ((eq? (msub-head g) 'SUBSET)
        (mac 'subset-def) (di)
        (let ((z (cadr (dk-goal))))
          (mac-h 'intersection-membership (list 'IN z '(INTERSECTION U A)))
          (dk-split-all!)
          (ass)))
       ;; every point of U ^ A has a subspace ball inside U ^ A
       (#t
        (let ((y (dk-di-var!)))
          (mac-h 'intersection-membership (list 'IN y '(INTERSECTION U A)))
          (dk-split-all!)                        ; y in U, y in A
          (mac-h 'IS-OPEN '(IS-OPEN s U))
          (dk-split-all!)                        ; ... and the ball-witness universal
          (let* ((univ (dk-pick (lambda (f)
                                  (and (pair? f) (eq? (car f) 'FORALL)
                                       (dk-contains? f 'POS-RR)))
                                "the open-set ball witness"))
                 (ex   (dk-apply! univ y))
                 (r    (dk-skolem! ex)))         ; POS-RR r, BALL(s,y,r) subset U
            (ew r)
            (dk-conj-close!
             (lambda ()
               (let ((g2 (dk-goal)))
                 (if (eq? (msub-head g2) 'POS-RR)
                     (ass)
                     (begin
                       (mac 'subset-def) (di)
                       (let ((z (cadr (dk-goal))))
                         (mac 'intersection-membership)
                         (have! (list 'AND (list 'IN z (list 'BALL 's y r))
                                           (list 'IN z 'A))
                           (lambda ()
                             (fact 'subspace-ball-membership 's 'A y r z)
                             (prop)))
                         (dk-split-all!)
                         (fact 'subset-mem-fwd (list 'BALL 's y r) 'U z)
                         (dk-conj-close! (lambda () (ass)))))))))))))))) 
(qed 'subspace-open-trace)
(topic! 'subspace-open-trace 'topology)
(alias! 'subspace-open-trace "the trace of an open set is open in the subspace")

;;; =====================================================================
;;; (11) CONTINUITY RESTRICTS.  f continuous at a point a of A, as a map
;;; s -> t, gives RESTRICT(f,A) continuous at a as a map SUBSPACE-MS(s,A) -> t.
;;;
;;; The SAME delta serves.  The two transports are the only real steps and both
;;; go through `subst' on the GOAL, never on a hypothesis: the subspace distance
;;; is rewritten to the ambient one inside a `have!' lane (the hypothesis holds
;;; the subspace form, so the claim is cut in the ambient form and `subst' turns
;;; the claim into what the context has), and the two RESTRICT applications are
;;; rewritten away by `restrict-apply' just before the citation lands.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (FORALL tt_ (FORALL f (FORALL pa_ (IMPLIES (IN pa_ A)
         (IMPLIES (IS-CONTINUOUS-AT s tt_ f pa_)
           (IS-CONTINUOUS-AT (SUBSPACE-MS s A) tt_ (RESTRICT f A) pa_))))))))))))
(dk-peel!)
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT s tt_ f pa_))
(dk-split-all!)
(fact 'subspace-is-metric-space 's 'A)
(fact 'subset-mem-fwd 'A '(PTS s) 'pa_)
(mac 'IS-CONTINUOUS-AT)
(mac 'subspace-pts)
(msub-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (msub-head g) 'IS-METRIC-SPACE) (ass))
       ((and (eq? (msub-head g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'RESTRICT))
        (fact 'restrict-in-fun 'f '(PTS s) '(PTS tt_) 'A) (ass))
       ((eq? (msub-head g) 'IN) (ass))          ; pa_ in A
       (#t
        (let* ((landed (dk-peel!))              ; FORALL eps, then POS-RR eps
               (eps (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)))
                                   "POS-RR eps")))
               (univ (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (dk-contains? f 'POS-RR)
                                               (dk-contains? f 'FORSOME)))
                              "the eps universal"))
               (ex  (dk-apply! univ eps))
               (del (dk-skolem! ex)))
          (ew del)
          (dk-conj-close!
           (lambda ()
             (if (eq? (msub-head (dk-goal)) 'POS-RR)
                 (ass)
                 (begin
                   (dk-peel!)                   ; b, (IN b A), the delta bound
                   (let* ((g2 (dk-goal))
                          (b  (cadr (caddr (cadr g2)))))
                     (fact 'subset-mem-fwd 'A '(PTS s) b)
                     (fact 'subspace-dist 's 'A 'pa_ b)
                     (have! (list '<= (list '(DIST s) 'pa_ b) del)
                       (lambda ()
                         (subst (list '== (list '(DIST s) 'pa_ b)
                                           (list (list 'DIST msub-space) 'pa_ b)))
                         (ass)))
                     (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                          (dk-contains? f del)))
                                         "the delta universal")
                                b)
                     (fact 'restrict-apply 'f 'A 'pa_)
                     (fact 'restrict-apply 'f 'A b)
                     (subst (list '== (list '(RESTRICT f A) 'pa_) '(f pa_)))
                     (subst (list '== (list '(RESTRICT f A) b) (list 'f b)))
                     (ass)))))))))))) 
(qed 'restrict-continuous-at)
(topic! 'restrict-continuous-at 'analysis)
(alias! 'restrict-continuous-at
        "a map continuous at a point of a subset restricts to one on the subspace")

;;; =====================================================================
;;; (12) CONVERGENCE IN THE SUBSPACE IS CONVERGENCE IN THE SPACE, for a
;;; sequence IN A with its limit IN A.  Both halves of the iff are the same
;;; eps-argument with the distance rewritten by `subspace-dist' at the typed
;;; index; the typing halves differ (fun-codomain-superset one way,
;;; `subspace-pts' the other).
;;;
;;; The guard "L in A" is not cosmetic: a sequence in A may well converge in s
;;; to a point OUTSIDE A (1/n in the subspace (0,1]), and then it converges to
;;; nothing in the subspace.  That is exactly why the Heine-Borel argument has
;;; to place the limit in the interval before it can use this theorem.
;;; =====================================================================

;;; The eps-lane, shared by the two directions.  GOAL-D and CTX-D build the
;;; distance term as the GOAL and as the CONTEXT spell it, at the sequence value.
(define (msub-conv-eps! goal-d ctx-d)
  (dk-peel!)                                   ; FORALL eps ; POS-RR eps
  (let* ((eps  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)))
                              "POS-RR eps")))
         (univ (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (dk-contains? f 'POS-RR)
                                         (dk-contains? f 'FORSOME)))
                        "the eps universal"))
         (ex   (dk-apply! univ eps))
         (cap  (dk-skolem! ex)))               ; (IN cap NN) and the tail universal
    (ew cap)
    (dk-conj-close!
     (lambda ()
       (if (eq? (msub-head (dk-goal)) 'IN)
           (ass)
           (begin
             (dk-peel!)                        ; n_, (IN n_ NN), (<= cap n_)
             (let* ((g2 (dk-goal))
                    (gn (cadr (cadr g2)))
                    (n_ (cadr gn)))
               (fact 'fun-apply-type-c 'g 'NN 'A n_)
               (fact 'subspace-dist 's 'A gn 'L)
               (dk-apply! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f cap)))
                                   "the tail universal")
                          n_)
               (subst (list '== (goal-d gn) (ctx-d gn)))
               (ass))))))))

(define (msub-dsub-at x) (list (list 'DIST msub-space) x 'L))
(define (msub-damb-at x) (list '(DIST s) x 'L))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (FORALL g (IMPLIES (IN g (FUN NN A))
         (FORALL L (IMPLIES (IN L A)
           (IFF (CONVERGES-TO (SUBSPACE-MS s A) g L)
                (CONVERGES-TO s g L))))))))))))
(dk-peel!)
(fact 'subspace-is-metric-space 's 'A)
(fact 'subset-mem-fwd 'A '(PTS s) 'L)
(fact 'fun-codomain-superset 'g 'NN 'A '(PTS s))
(dk-iff!
 (lambda (g) (dk-contains? (if (eq? (car g) 'IMPLIES) (caddr g) g) 'SUBSPACE-MS))
 ;; s  ==>  subspace
 (lambda ()
   (dk-peel!)
   (mac-h 'CONVERGES-TO '(CONVERGES-TO s g L))
   (dk-split-all!)
   (mac 'CONVERGES-TO)
   (mac 'subspace-pts)
   (msub-and!
    (lambda ()
      (if (memq (msub-head (dk-goal)) '(IS-METRIC-SPACE IN))
          (ass)
          (msub-conv-eps! msub-dsub-at msub-damb-at)))))
 ;; subspace  ==>  s
 (lambda ()
   (dk-peel!)
   (mac-h 'CONVERGES-TO (list 'CONVERGES-TO msub-space 'g 'L))
   (dk-split-all!)
   (mac 'CONVERGES-TO)
   (msub-and!
    (lambda ()
      (if (memq (msub-head (dk-goal)) '(IS-METRIC-SPACE IN))
          (ass)
          (msub-conv-eps! msub-damb-at msub-dsub-at))))))
(qed 'subspace-converges-to)
(topic! 'subspace-converges-to 'analysis)
(alias! 'subspace-converges-to
        "a sequence in a subset converges in the subspace iff it converges in the space to a point of the subset")

;;; =====================================================================
;;; (13) EVERY OPEN SET OF THE SUBSPACE IS A TRACE -- the other half.
;;;
;;; The witness is built, not chosen: no radius function is selected, so no
;;; CHOICE and no dependent recurrence.  With V open in the subspace, put
;;;
;;;   U = { z in PTS(s) : some y in V and some r > 0 have
;;;                       BALL(SUBSPACE-MS(s,A), y, r) subset V and z in BALL(s,y,r) }
;;;
;;; -- the union of the ambient balls that witness V's openness, written as ONE
;;; separation with the witnesses existentially quantified INSIDE the condition.
;;; U is open because a point z of U, witnessed by (y, r), carries the ambient
;;; ball of radius r - d(y,z) > 0, every point w of which is still within r of y
;;; (the triangle inequality) and so keeps the SAME witnesses; and U meet A = V
;;; because a point of V witnesses its own membership (`ball-center-in') while a
;;; point of U in A lies in a subspace ball that V contains (theorem 8).
;;; =====================================================================

;;; (IN r RR), (<= 0 r), (NOT (= 0 r)) from (POS-RR r) -- without consuming it.
(define (msub-pos-parts! rr_)
  (have! (list 'AND (list 'IN rr_ 'RR)
                    (list 'AND (list '<= 0 rr_) (list 'NOT (list '= 0 rr_))))
    (lambda () (fact 'pos-rr rr_) (prop)))
  (dk-split-all!))

;;; the three conjuncts of (IN z (BALL s c r)) -- again without consuming it.
(define (msub-ball-parts! c rr_ z)
  (let ((d (list '(DIST s) c z)))
    (have! (list 'AND (list 'IN z '(PTS s))
                      (list 'AND (list '<= d rr_) (list 'NOT (list '= d rr_))))
      (lambda () (fact 'ball-membership 's c rr_ z) (prop)))
    (dk-split-all!)
    d))

;;; (< a b) from (<= a b) and (NOT (= a b)), both in context.
(define (msub-lt! a b)
  (have! (list '< a b) (lambda () (mac '<) (dk-conj-close! (lambda () (ass))))))

(define msub-trace-set
  '(SEP zu_ (PTS s)
     (FORSOME yu_ (AND (IN yu_ vs_)
       (FORSOME ru_ (AND (POS-RR ru_)
         (AND (SUBSET (BALL (SUBSPACE-MS s A) yu_ ru_) vs_)
              (IN zu_ (BALL s yu_ ru_)))))))))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-METRIC-SPACE s)
     (list 'FORALL 'A (list 'IMPLIES '(SUBSET A (PTS s))
     (list 'FORALL 'vs_ (list 'IMPLIES (list 'IS-OPEN msub-space 'vs_)
       (list 'FORSOME 'us_
         (list 'AND '(IS-OPEN s us_)
                    '(= vs_ (INTERSECTION us_ A))))))))))))
(dk-peel!)
(fact 'subspace-is-metric-space 's 'A)
(mac-h 'IS-OPEN (list 'IS-OPEN msub-space 'vs_))
(dk-split-all!)                              ; ... SUBSET vs_ (PTS sub), the witness universal
(mac-h 'subspace-pts (list 'SUBSET 'vs_ (list 'PTS msub-space)))   ; -> SUBSET vs_ A
(ew msub-trace-set)
(both!
 ;; ---------- U is open in s ----------
 (lambda ()
   (mac 'IS-OPEN)
   (msub-and!
    (lambda ()
      (let ((g (dk-goal)))
        (cond
          ((eq? (msub-head g) 'IS-METRIC-SPACE) (ass))
          ((eq? (msub-head g) 'SUBSET)
           (mac 'subset-def) (di)
           (let ((z (cadr (dk-goal))))
             (sep-me (list 'IN z msub-trace-set))
             (ass)))
          (#t
           (let* ((z  (dk-di-var!)))
             (sep-me (list 'IN z msub-trace-set))
             (let* ((y  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the trace witness y")))
                    (r  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the trace witness r"))))
               (fact 'subset-mem-fwd 'vs_ 'A y)
               (fact 'subset-mem-fwd 'A '(PTS s) y)
               (msub-pos-parts! r)
               (let ((dyz (msub-ball-parts! y r z)))
                 (msub-lt! dyz r)
                 (fact 'metric-dist-real 's y z)
                 (let ((rho (list '- r dyz)))
                   (fact 'rr-sub-in-rr r dyz)
                   (fact 'rr-lt-diff-pos dyz r)         ; 0 < r - d(y,z)
                   (fact 'rr-pos-rr-of-lt rho)          ; POS-RR (r - d(y,z))
                   (ew rho)
                   (dk-conj-close!
                    (lambda ()
                      (if (eq? (msub-head (dk-goal)) 'POS-RR)
                          (ass)
                          (begin
                            (mac 'subset-def) (di)
                            (let ((w (cadr (dk-goal))))
                              (let ((dzw (msub-ball-parts! z rho w)))
                                (msub-lt! dzw rho)
                                (fact 'metric-dist-real 's z w)
                                (fact 'metric-dist-real 's y w)
                                (fact 'metric-triangle 's y z w)
                                (let ((dsum (list '+ dyz dzw)))
                                  (have! (list 'AND (list 'IN dyz 'RR) (list 'IN dzw 'RR)))
                                  (fact 'rr-add-closed dyz dzw)
                                  (in-sep!
                                   (lambda () (ass))
                                   (lambda ()
                                     (ew y)
                                     (both!
                                      (lambda () (ass))
                                      (lambda ()
                                        (ew r)
                                        (dk-conj-close!
                                         (lambda ()
                                           (let ((g2 (dk-goal)))
                                             (cond
                                               ((eq? (msub-head g2) 'POS-RR) (ass))
                                               ((eq? (msub-head g2) 'SUBSET) (ass))
                                               (#t
                                                (have!
                                                 (list 'AND (list 'IN w '(PTS s))
                                                  (list 'AND (list 'IN dsum 'RR)
                                                   (list 'AND (list 'IN r 'RR)
                                                    (list 'AND (list '<= (list '(DIST s) y w) dsum)
                                                               (list '< dsum r)))))
                                                 (lambda ()
                                                   (dk-conj-close!
                                                    (lambda ()
                                                      (if (eq? (msub-head (dk-goal)) '<)
                                                          (dk-ineq! (list '< dzw rho)
                                                                    (list 'IN dyz 'RR)
                                                                    (list 'IN dzw 'RR)
                                                                    (list 'IN r 'RR))
                                                          (ass))))))
                                                (fact 'ball-mem-from-le 's y w dsum r)
                                                (ass)))))))))))))))))))))))))))
 ;; ---------- V = U meet A ----------
 (lambda ()
   (have! (list 'FORALL 'zc_
            (list 'IFF '(IN zc_ vs_)
                       (list 'IN 'zc_ (list 'INTERSECTION msub-trace-set 'A))))
     (lambda ()
       (di)
       (dk-iff!
        (lambda (g) (dk-contains? (if (eq? (car g) 'IMPLIES) (caddr g) g) 'INTERSECTION))
        ;; V ==> U meet A
        (lambda ()
          (dk-peel!)
          (fact 'subset-mem-fwd 'vs_ 'A 'zc_)
          (fact 'subset-mem-fwd 'A '(PTS s) 'zc_)
          (mac 'intersection-membership)
          (both!
           (lambda ()
             (let* ((univ (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                    (dk-contains? f 'POS-RR)
                                                    (dk-contains? f 'FORSOME)))
                                   "the subspace ball witness"))
                    (ex  (dk-apply! univ 'zc_))
                    (r   (dk-skolem! ex)))
               (msub-pos-parts! r)
               (in-sep!
                (lambda () (ass))
                (lambda ()
                  (ew 'zc_)
                  (both!
                   (lambda () (ass))
                   (lambda ()
                     (ew r)
                     (dk-conj-close!
                      (lambda ()
                        (let ((g2 (dk-goal)))
                          (cond
                            ((eq? (msub-head g2) 'POS-RR) (ass))
                            ((eq? (msub-head g2) 'SUBSET) (ass))
                            (#t
                             (have! (list 'AND (list 'IN r 'RR)
                                     (list 'AND (list '<= 0 r) (list 'NOT (list '= 0 r)))))
                             (fact 'ball-center-in 's 'zc_ r)
                             (ass))))))))))))
           (lambda () (ass))))
        ;; U meet A ==> V
        (lambda ()
          (dk-peel!)
          (mac-h 'intersection-membership
                 (list 'IN 'zc_ (list 'INTERSECTION msub-trace-set 'A)))
          (dk-split-all!)
          (sep-me (list 'IN 'zc_ msub-trace-set))
          (let* ((y (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the trace witness y")))
                 (r (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the trace witness r"))))
            (fact 'subset-mem-fwd 'vs_ 'A y)
            (have! (list 'IN 'zc_ (list 'BALL msub-space y r))
              (lambda ()
                (fact 'subspace-ball-membership 's 'A y r 'zc_)
                (prop)))
            (fact 'subset-mem-fwd (list 'BALL msub-space y r) 'vs_ 'zc_)
            (ass))))))
   (fact 'class-extensionality 'vs_ (list 'INTERSECTION msub-trace-set 'A))
   (ass)))
(qed 'subspace-open-is-trace)
(topic! 'subspace-open-is-trace 'topology)
(alias! 'subspace-open-is-trace
        "an open set of the subspace is the trace of an open set")

;;; =====================================================================
;;; (14) A LIMIT OF A SEQUENCE IN A CLOSED SET LIES IN THE SET.
;;;
;;; Stated for the AMBIENT space (it is a fact about closed sets, not about
;;; subspaces) because that is the form the completeness theorem below and any
;;; closure argument want.  The proof is the excluded-middle split on the
;;; conclusion: if L were outside A it would sit in the OPEN complement, some
;;; ball around it would miss A, and a tail term of the sequence -- which is in
;;; A -- would be in that ball.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (IS-CLOSED s A)
       (FORALL f (IMPLIES (IN f (FUN NN A))
         (FORALL L (IMPLIES (CONVERGES-TO s f L)
                            (IN L A)))))))))))
(dk-peel!)
(mac-h 'IS-CLOSED '(IS-CLOSED s A))
(dk-split-all!)                                ; SUBSET A (PTS s), IS-OPEN s (comp)
(mac-h 'CONVERGES-TO '(CONVERGES-TO s f L))
(dk-split-all!)                                ; ... (IN L (PTS s)), the eps universal
(use-em '(IN L A)
  (lambda () (ass))
  (lambda ()
    ;; L is in the open complement, so some ball around it misses A
    (have! '(IN L (COMPLEMENT-IN (PTS s) A))
      (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
    (mac-h 'IS-OPEN '(IS-OPEN s (COMPLEMENT-IN (PTS s) A)))
    (dk-split-all!)
    (let* ((univ (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                           (dk-contains? h 'POS-RR)
                                           (dk-contains? h 'FORSOME)
                                           (dk-contains? h 'COMPLEMENT-IN)))
                          "the complement ball witness"))
           (ex   (dk-apply! univ 'L))
           (r    (dk-skolem! ex)))            ; POS-RR r, BALL(s,L,r) subset comp
      (msub-pos-parts! r)
      (let* ((hf  (dk-halve! r))              ; hf + hf = r, POS-RR hf
             ;; `DIST' is what tells it apart from rr-pos-halvable's universal,
             ;; which dk-halve! has just landed and which also matches
             ;; "a FORALL with a POS-RR and a FORSOME in it".
             (ueps (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                             (dk-contains? h 'POS-RR)
                                             (dk-contains? h 'FORSOME)
                                             (dk-contains? h 'DIST)))
                            "the convergence eps universal"))
             (ex2 (dk-apply! ueps hf))
             (cap (dk-skolem! ex2)))          ; (IN cap NN) and the tail universal
        (fact 'nn-in-rr cap)
        (fact 'rr-leq-reflexive cap)          ; the tail universal is read AT cap
        (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                             (dk-contains? h cap)
                                             (dk-contains? h 'DIST)))
                            "the tail universal")
                   cap)                       ; d(f(cap), L) <= hf
        (let ((fc (list 'f cap)))
          (fact 'fun-apply-type-c 'f 'NN 'A cap)      ; (IN fc A)
          (fact 'subset-mem-fwd 'A '(PTS s) fc)
          (fact 'metric-dist-real 's fc 'L)
          (fact 'metric-sym 's fc 'L)
          (fact 'rr-pos-rr-in-rr hf)
          (have! (list 'AND (list 'IN fc '(PTS s))
                  (list 'AND (list 'IN hf 'RR)
                   (list 'AND (list 'IN r 'RR)
                    (list 'AND (list '<= (list '(DIST s) 'L fc) hf)
                               (list '< hf r)))))
            (lambda ()
              (dk-conj-close!
               (lambda ()
                 (let ((g (dk-goal)))
                   (cond
                     ((and (eq? (msub-head g) '<=) (pair? (cadr g)))
                      (subst (list '= (list '(DIST s) 'L fc) (list '(DIST s) fc 'L)))
                      (ass))
                     ((eq? (msub-head g) '<)
                      (dk-ineq! (list '= (list '+ hf hf) r)
                                (list 'IN hf 'RR) (list 'IN r 'RR)
                                (list '< 0 hf)))
                     (#t (ass))))))))
          (fact 'ball-mem-from-le 's 'L fc hf r)       ; fc in BALL(s,L,r)
          (fact 'subset-mem-fwd (list 'BALL 's 'L r) '(COMPLEMENT-IN (PTS s) A) fc)
          (mac-h 'complement-in-membership (list 'IN fc '(COMPLEMENT-IN (PTS s) A)))
          (dk-split-all!)
          ;; NOT-ELIM, not `prop': the context here is far over prop's atom cap
          ;; and it drops the very pair that closes the branch.
          (ai (list 'NOT (list 'IN fc 'A))))))))
(qed 'closed-limit-in)
(topic! 'closed-limit-in 'analysis)
(alias! 'closed-limit-in "the limit of a sequence in a closed set lies in the set")

;;; =====================================================================
;;; (15) CAUCHY IN THE SUBSPACE IS CAUCHY IN THE SPACE, for a sequence in A.
;;; The twin of (12); the only difference is that the tail condition has TWO
;;; indices and a CONJUNCTIVE antecedent, which `dk-apply!' detaches whole
;;; because the peel landed it whole.
;;; =====================================================================
(define (msub-cauchy-eps! goal-d ctx-d)
  (dk-peel!)
  (let* ((eps  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'POS-RR)))
                              "POS-RR eps")))
         (univ (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (dk-contains? f 'POS-RR)
                                         (dk-contains? f 'FORSOME)
                                         (dk-contains? f 'DIST)))
                        "the eps universal"))
         (ex   (dk-apply! univ eps))
         (cap  (dk-skolem! ex)))
    (ew cap)
    (dk-conj-close!
     (lambda ()
       (if (eq? (msub-head (dk-goal)) 'IN)
           (ass)
           (begin
             (dk-peel!)
             (let* ((g2 (dk-goal))
                    (fm (cadr (cadr g2)))
                    (fn (caddr (cadr g2))))
               (fact 'fun-apply-type-c 'f 'NN 'A (cadr fm))
               (fact 'fun-apply-type-c 'f 'NN 'A (cadr fn))
               (fact 'subspace-dist 's 'A fm fn)
               (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                    (dk-contains? h cap)
                                                    (dk-contains? h 'DIST)))
                                   "the tail universal")
                          (cadr fm) (cadr fn))
               (subst (list '== (goal-d fm fn) (ctx-d fm fn)))
               (ass))))))))

(define (msub-dsub-2 a b) (list (list 'DIST msub-space) a b))
(define (msub-damb-2 a b) (list '(DIST s) a b))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (FORALL f (IMPLIES (IN f (FUN NN A))
         (IFF (IS-CAUCHY-SEQ (SUBSPACE-MS s A) f)
              (IS-CAUCHY-SEQ s f))))))))))
(dk-peel!)
(fact 'subspace-is-metric-space 's 'A)
(fact 'fun-codomain-superset 'f 'NN 'A '(PTS s))
(dk-iff!
 (lambda (g) (dk-contains? (if (eq? (car g) 'IMPLIES) (caddr g) g) 'SUBSPACE-MS))
 (lambda ()                                   ; s ==> subspace
   (dk-peel!)
   (mac-h 'IS-CAUCHY-SEQ '(IS-CAUCHY-SEQ s f))
   (dk-split-all!)
   (mac 'IS-CAUCHY-SEQ)
   (mac 'subspace-pts)
   (msub-and!
    (lambda ()
      (if (memq (msub-head (dk-goal)) '(IS-METRIC-SPACE IN))
          (ass)
          (msub-cauchy-eps! msub-dsub-2 msub-damb-2)))))
 (lambda ()                                   ; subspace ==> s
   (dk-peel!)
   (mac-h 'IS-CAUCHY-SEQ (list 'IS-CAUCHY-SEQ msub-space 'f))
   (dk-split-all!)
   (mac 'IS-CAUCHY-SEQ)
   (msub-and!
    (lambda ()
      (if (memq (msub-head (dk-goal)) '(IS-METRIC-SPACE IN))
          (ass)
          (msub-cauchy-eps! msub-damb-2 msub-dsub-2))))))
(qed 'subspace-is-cauchy-seq)
(topic! 'subspace-is-cauchy-seq 'analysis)
(alias! 'subspace-is-cauchy-seq
        "a sequence in a subset is Cauchy in the subspace iff it is Cauchy in the space")

;;; =====================================================================
;;; (16) A CLOSED SUBSPACE OF A COMPLETE SPACE IS COMPLETE.
;;; Cauchy in the subspace -> Cauchy in s (15) -> converges in s -> the limit
;;; is in A because A is closed (14) -> converges in the subspace (12).
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-COMPLETE s)
     (FORALL A (IMPLIES (IS-CLOSED s A)
       (IS-COMPLETE (SUBSPACE-MS s A))))))))
(dk-peel!)
;; The two conjuncts of IS-CLOSED are taken in LANES: `mac-h' CONSUMES the
;; hypothesis it unfolds, and `closed-limit-in' below is guarded on the FOLDED
;; IS-CLOSED(s, A) -- unfolding it in the main context left that citation
;; undetached and silent.
(have! '(IS-METRIC-SPACE s)
  (lambda () (mac-h 'IS-CLOSED '(IS-CLOSED s A)) (dk-split-all!) (ass)))
(have! '(SUBSET A (PTS s))
  (lambda () (mac-h 'IS-CLOSED '(IS-CLOSED s A)) (dk-split-all!) (ass)))
(mac-h 'IS-COMPLETE '(IS-COMPLETE s))
(dk-split-all!)                                ; ... the Cauchy universal of s
(fact 'subspace-is-metric-space 's 'A)
(mac 'IS-COMPLETE)
(msub-and!
 (lambda ()
   (if (eq? (msub-head (dk-goal)) 'IS-METRIC-SPACE)
       (ass)
       (begin
         (dk-peel!)                            ; f, and IS-CAUCHY-SEQ(sub, f)
         (have! (list 'IN 'f (list 'FUN 'NN (list 'PTS msub-space)))
           (lambda ()
             (mac-h 'IS-CAUCHY-SEQ (list 'IS-CAUCHY-SEQ msub-space 'f))
             (dk-split-all!)
             (ass)))
         (mac-h 'subspace-pts (list 'IN 'f (list 'FUN 'NN (list 'PTS msub-space))))
         (have! '(IS-CAUCHY-SEQ s f)
           (lambda () (fact 'subspace-is-cauchy-seq 's 'A 'f) (prop)))
         (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                              (dk-contains? h 'IS-CAUCHY-SEQ)))
                             "the completeness universal")
                    'f)                        ; (CONVERGES s f)
         (mac-h 'CONVERGES '(CONVERGES s f))
         (let ((lim (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the limit in s"))))
           (fact 'closed-limit-in 's 'A 'f lim)
           (have! (list 'CONVERGES-TO msub-space 'f lim)
             (lambda () (fact 'subspace-converges-to 's 'A 'f lim) (prop)))
           (mac 'CONVERGES)
           (ew lim)
           (ass))))))
(qed 'subspace-complete)
(topic! 'subspace-complete 'analysis)
(alias! 'subspace-complete "a closed subspace of a complete space is complete")
