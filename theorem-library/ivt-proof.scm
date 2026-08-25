;;; ivt-proof.scm -- the INTERMEDIATE VALUE THEOREM, PROVEN.
;;;
;;;   f in FUN(RR,RR), a,b,c in RR, a <= b,
;;;   f continuous at every point of [a,b],  f(a) <= c <= f(b)
;;;     =>  forsome x.  x in RR  and  x in CCINT(a,b)  and  f(x) = c
;;;
;;; THE WITNESS IS TYPED.  The conclusion carries (IN x RR) beside the interval
;;; membership, and that is not decoration.  When rolle / mvt / generalized-mvt
;;; dropped the typing of their interior witness, the gap was papered over by
;;; `rr-strict-between-real' -- "u,v in RR, u<x<v => x in RR" -- which is an
;;; extra AXIOM about the primitive <=, not a consequence of one: the RR order
;;; axioms constrain <= on reals without forbidding it to relate a real to a
;;; non-real.  Those statements were repaired at the source on 2026-08-16 (see
;;; the note at the head of theorem-library/deriv-constant-proof.scm) and this
;;; one is written the repaired way from the start.
;;;
;;; THE ROUTE -- Bolzano's, and every ingredient is `primitive'.  Let
;;;
;;;     S = { x in RR : a <= x <= b  and  f(x) <= c },      s = SUP(S).
;;;
;;;   1. S is a set (separation), inhabited (a is in it, since f(a) <= c), a
;;;      subset of RR, and bounded above by b.
;;;   2. rr-sup-in / rr-sup-upper / rr-sup-least (number-systems.scm, primitive:
;;;      order completeness) give s in RR, s an upper bound, s below every upper
;;;      bound.  Hence a <= s (a is in S) and s <= b (b is an upper bound), so s
;;;      lies in [a,b] and f is continuous there.
;;;   3. Trichotomy on f(s) versus c.  The equal case IS the theorem, with
;;;      witness s.  The other two die -- with one exception, which is the
;;;      interesting part of the proof:
;;;
;;;      f(s) < c.  Continuity at eps = c - f(s) gives delta > 0 with
;;;        f(y) <= c for every y within delta of s.  Split on s + delta vs b:
;;;          * s + delta <= b.  Then s + delta is in S, so s + delta <= s, so
;;;            delta <= 0 -- contradiction.
;;;          * b <= s + delta.  Then |s - b| <= delta already, so f(b) <= c;
;;;            with c <= f(b) that gives f(b) = c, and **b is the root**.  No
;;;            contradiction is available here and none is needed: this is the
;;;            case s = b, where the textbook argument silently uses f(s) = f(b).
;;;            Choosing the witness per branch avoids that congruence step
;;;            entirely.
;;;
;;;      c < f(s).  Halve the gap (rr-pos-halvable, PROVEN in
;;;        theorem-library/rr-halving.scm) to h and take the continuity delta dd
;;;        at h.  Then every y within dd of s has f(y) >= c + h > c, so no such
;;;        y is in S: s - dd is an upper bound of S, whence s <= s - dd and
;;;        dd <= 0 -- contradiction.  The halving is what makes the separation
;;;        STRICT; with eps = f(s) - c itself one gets only f(y) >= c, which is
;;;        consistent with membership in S.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.  Order completeness and the RR field
;;; and order axioms are primitive (number-systems.scm is in *primitive-files*),
;;; ccint-membership and rr-pos-halvable are theorems, and the two oracles used
;;; -- `ineq' for the linear arithmetic, `crs' nowhere here -- add no debt.
;;;
;;; WHAT IT DOES NOT USE.  Neither `continuous-nonpos-right' nor
;;; `continuous-nonneg-left' (theorem-library/mean-value.scm), the two asserted
;;; sign-preservation supports an IVT proof might be expected to want.  They are
;;; one-sided statements about a punctured neighbourhood; the sup argument needs
;;; the two-sided eps/delta bound directly, and takes it from the definition.
;;;
;;; Loads after extreme-value (CCINT), ccint-basics (the membership law),
;;; rr-halving (rr-pos-halvable), rr-ms-dist, rr-abs-basics (rr-abs-bound),
;;; rr-order-basics (rr-lt-trichotomy, rr-sub-ne-zero, rr-pos-ne-zero),
;;; metric-continuity (IS-CONTINUOUS-AT), driver-kit and sketch (`obtain').

;;; =====================================================================
;;; The statement, and the set the proof turns on.
;;; =====================================================================
(define ivt-set '(SEP x_ RR (AND (AND (<= a x_) (<= x_ b)) (<= (f x_) c))))
(define ivt-sup (list 'SUP ivt-set))
(define ivt-fs  (list 'f ivt-sup))
(define ivt-eps (list '- 'c ivt-fs))            ; the case f(s) < c
(define ivt-gap (list '- ivt-fs 'c))            ; the case c < f(s)

(define ivt-stmt
  (forall-guarded '(f a b c)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(IN c RR) '(<= a b))
    '(IMPLIES (FORALL x (IMPLIES (IN x (CCINT a b)) (IS-CONTINUOUS-AT RR-MS RR-MS f x)))
      (IMPLIES (AND (<= (f a) c) (<= c (f b)))
        (FORSOME p_ (AND (IN p_ RR) (AND (IN p_ (CCINT a b)) (= (f p_) c))))))))

;;; =====================================================================
;;; File-local driver helpers (the `ivt-' prefix -- never named like a tactic).
;;; =====================================================================

;;; `di' is greedy WITHIN a binder level and stops at the next, so the guarded
;;; prefix takes several calls.  Guarded on the head AND on fuel: `di' only
;;; WARNS when it cannot decompose, so a head test alone spins on a no-op.
(define (ivt-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 15))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `ai' every context conjunction, to exhaustion.  Neither `fact' nor `di'
;;; splits a conjunctive hypothesis, and `from-context!' closes an AND goal
;;; conjunct by conjunct, so an unsplit AND matches nothing.
(define (ivt-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 14)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (ivt-has? tree sub)
  (or (equal? tree sub)
      (and (pair? tree) (or (ivt-has? (car tree) sub) (ivt-has? (cdr tree) sub)))))

;;; Select a hypothesis by CONTENT, and ERROR on a miss: a driver that
;;; reconstructs a formula to cite it addresses the wrong assumption silently.
(define (ivt-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "ivt-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (ivt-mem-in set-expr)
  (ivt-find 'mem-in
    (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (caddr a) set-expr)))))

(define (ivt-and-with sub)
  (ivt-find 'and-with
    (lambda (a) (and (pair? a) (eq? (car a) 'AND) (ivt-has? a sub)))))

;;; forall x. x in S => x <= SUP(S)   -- the upper-bound half of rr-sup-upper.
;;; Discriminated on the CONSEQUENT being an inequality with SUP(S) on the
;;; right: the two generic sup axioms in context also mention SUP, and
;;; rr-sup-least's universal has an RR-UPPER-BOUND antecedent.
(define (ivt-forall-ub)
  (ivt-find 'ub
    (lambda (a)
      (and (pair? a) (eq? (car a) 'FORALL)
           (let ((body (caddr a)))
             (and (pair? body) (eq? (car body) 'IMPLIES)
                  (let ((con (caddr body)))
                    (and (pair? con) (eq? (car con) '<=)
                         (equal? (caddr con) ivt-sup)))))))))

;;; forall t. RR-UPPER-BOUND(S,t) => SUP(S) <= t
(define (ivt-forall-least)
  (ivt-find 'least
    (lambda (a)
      (and (pair? a) (eq? (car a) 'FORALL)
           (let ((body (caddr a)))
             (and (pair? body) (eq? (car body) 'IMPLIES)
                  (pair? (cadr body)) (eq? (car (cadr body)) 'RR-UPPER-BOUND)))))))

(define (ivt-forall-cont)
  (ivt-find 'cont
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (ivt-has? a 'IS-CONTINUOUS-AT)))))

;;; forall eps. POS-RR(eps) => forsome delta. ... -- the unfolded continuity.
(define (ivt-forall-eps)
  (ivt-find 'eps
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (ivt-has? a 'POS-RR) (ivt-has? a 'DIST)))))

;;; forall y in PTS. d(s,y) <= DELTA => d(f s, f y) <= eps -- the instance the
;;; chosen DELTA came with.  It is the DIST-universal that is NOT the eps one.
(define (ivt-forall-delta delta)
  (ivt-find 'delta
    (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                     (ivt-has? a 'DIST) (ivt-has? a delta)
                     (not (ivt-has? a 'POS-RR))))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE rather than swept up by shape: the context here carries distance and
;;; membership formulas whose atoms can never be certified in RR, and a single
;;; such premise poisons the whole call.
(define (ivt-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ivt-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (ivt-ineq . forms) (apply ineq (map ivt-idx forms)))

;;; `obtain' returns #f when nothing landed, and a #f eigenvariable propagates
;;; into every later formula as a term nobody can read.  Make it error.
(define (ivt-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "ivt-obtain: nothing obtained for" what))
    v))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (ivt-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (ivt-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (ivt-ass!) (ivt-goal-and! (lambda () (ass))))

;;; POS-RR(t): the typing and the disequality are in context, the sign is linear.
(define (ivt-pos! t . prem)
  (have! (list 'POS-RR t)
    (lambda ()
      (mac 'pos-rr)
      (ivt-goal-and!
       (lambda ()
         (if (equal? (dk-goal) (list '<= 0 t)) (apply ivt-ineq prem) (ass)))))))

;;; d(u,v) <= r.  `rr-ms-dist' brings the accessor down to abs (it sits in
;;; OPERATOR position, where `subst' cannot reach); `rr-abs-bound' turns the one
;;; abs goal into two linear ones, which the oracle decides from PREM.
(define (ivt-dist! u v r . prem)
  (have! (list '<= (list '(DIST RR-MS) u v) r)
    (lambda ()
      (mac 'rr-ms-dist)
      (mac 'rr-abs-bound)
      (ivt-goal-and! (lambda () (apply ivt-ineq prem))))))

;;; The same two macetes on a HYPOTHESIS d(u,v) <= r, leaving the pair of linear
;;; bounds.  Both rewrites want (IN (- u v) RR) already in context, or their
;;; guard opens a side goal the caller was not expecting.
(define (ivt-unpack-dist! u v r)
  (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) u v) r))
  (mac-h 'rr-abs-bound (list '<= (list 'abs (list '- u v)) r))
  (dk-split! (list 'AND (list '<= (list '- r) (list '- u v))
                       (list '<= (list '- u v) r))))

(define (ivt-in-pts! t)
  (have! (list 'IN t '(PTS RR-MS)) (lambda () (slot 'PTS) (ass))))

;;; y in S, by separation: the typing and the three bounds are all in context.
(define (ivt-in-set! y)
  (have! (list 'IN y ivt-set)
    (lambda () (for-each (lambda (k) (dk-focus! k) (from-context!))
                         (dk-opened (lambda () (sep-mi)))))))

;;; ---- eigenvariables, set by the case procedures ----------------------
(define ivt-d  #f)          ; f(s) < c: the continuity delta
(define ivt-h  #f)          ; c < f(s): half the gap
(define ivt-dd #f)          ; c < f(s): the continuity delta
(define ivt-y  #f)          ; c < f(s): the arbitrary member of S

;;; =====================================================================
;;; CASE  c < f(s).  s - dd is an upper bound of S, and it is below s.
;;; =====================================================================

;;; goal (<= y (- s dd)) with (IN y S) in context, y the eigenvariable
(define (ivt-gt-member!)
  (set! ivt-y (cadr (dk-goal)))
  (inst+ (ivt-forall-ub) ivt-y)                       ; y <= s, BEFORE sep-me
  (sep-me (ivt-mem-in ivt-set))                       ; ... which consumes (IN y S)
  (ivt-split!)                                        ; a <= y, y <= b, f(y) <= c
  (have! (list 'AND (list 'IN ivt-y 'RR)
                    (list 'IN (list '- ivt-sup ivt-dd) 'RR)))
  (fact 'rr-leq-total ivt-y (list '- ivt-sup ivt-dd))
  (use-cases (list (list '<= ivt-y (list '- ivt-sup ivt-dd))
                   (list '<= (list '- ivt-sup ivt-dd) ivt-y))
             ivt-gt-member-easy!
             ivt-gt-member-hard!))

(define (ivt-gt-member-easy!) (ass))

;;; s - dd <= y <= s, so |s - y| <= dd, so f(y) >= f(s) - h = c + h > c, against
;;; f(y) <= c.  The contradiction is read out as h = 0 by the oracle and closed
;;; by NOT-elim on (POS-RR h)'s disequality.
(define (ivt-gt-member-hard!)
  (fact 'rr-sub-in-rr ivt-sup ivt-y)
  (ivt-dist! ivt-sup ivt-y ivt-dd
             (list '<= ivt-y ivt-sup)
             (list '<= 0 ivt-dd)
             (list '<= (list '- ivt-sup ivt-dd) ivt-y))
  (ivt-in-pts! ivt-y)
  (inst+ (ivt-forall-delta ivt-dd) ivt-y)
  (fact 'fun-apply-type-c 'f 'RR 'RR ivt-y)
  (fact 'rr-sub-in-rr ivt-fs (list 'f ivt-y))
  (ivt-unpack-dist! ivt-fs (list 'f ivt-y) ivt-h)
  (have! (list '= 0 ivt-h)
         (lambda ()
           (ivt-ineq (list '<= (list '- ivt-fs (list 'f ivt-y)) ivt-h)
                     (list '<= (list 'f ivt-y) 'c)
                     (list '= (list '+ ivt-h ivt-h) ivt-gap)
                     (list '<= 0 ivt-h))))
  (ai (list 'NOT (list '= 0 ivt-h))))

(define (ivt-case-gt)
  (fact 'rr-sub-in-rr ivt-fs 'c)                      ; f(s) - c in RR
  (mac-h '< (list '< 'c ivt-fs))
  (dk-split! (list 'AND (list '<= 'c ivt-fs) (list 'NOT (list '= 'c ivt-fs))))
  (fact 'neq-sym 'c ivt-fs)
  (fact 'rr-sub-ne-zero ivt-fs 'c)
  (fact 'neq-sym ivt-gap 0)
  (ivt-pos! ivt-gap (list '<= 'c ivt-fs))
  (set! ivt-h (ivt-obtain 'half (lambda () (fact 'rr-pos-halvable ivt-gap))))
  ;; The continuity instance at h is taken BEFORE (POS-RR h) is unfolded:
  ;; `mac-h' REPLACES the assumption it unfolds, and `inst+' needs (POS-RR h)
  ;; verbatim in context to detach the instance.  Unfolding first leaves the
  ;; implication undetached, `obtain' finds no existential, and the eigenvariable
  ;; comes back #f -- which is how this was found.
  (set! ivt-dd (ivt-obtain 'delta (lambda () (inst+ (ivt-forall-eps) ivt-h))))
  (mac-h 'pos-rr (list 'POS-RR ivt-h))
  (dk-split! (list 'AND (list 'IN ivt-h 'RR)
                        (list 'AND (list '<= 0 ivt-h) (list 'NOT (list '= 0 ivt-h)))))
  (mac-h 'pos-rr (list 'POS-RR ivt-dd))
  (dk-split! (list 'AND (list 'IN ivt-dd 'RR)
                        (list 'AND (list '<= 0 ivt-dd) (list 'NOT (list '= 0 ivt-dd)))))
  (fact 'rr-sub-in-rr ivt-sup ivt-dd)
  (have! (list 'RR-UPPER-BOUND ivt-set (list '- ivt-sup ivt-dd))
    (lambda ()
      (mac 'rr-upper-bound)
      (for-each (lambda (k)
                  (dk-focus! k)
                  (if (eq? (car (dk-goal)) 'IN) (ass) (begin (di) (ivt-gt-member!))))
                (dk-opened (lambda () (di))))))
  (inst+ (ivt-forall-least) (list '- ivt-sup ivt-dd))  ; s <= s - dd
  (have! (list '= 0 ivt-dd)
         (lambda () (ivt-ineq (list '<= ivt-sup (list '- ivt-sup ivt-dd))
                              (list '<= 0 ivt-dd))))
  (ai (list 'NOT (list '= 0 ivt-dd))))

;;; =====================================================================
;;; CASE  f(s) < c.
;;; =====================================================================

;;; s + d <= b: the point s + d lands in S, so s + d <= s and d <= 0.
(define (ivt-lt-inside!)
  (let ((y (list '+ ivt-sup ivt-d)))
    (fact 'rr-sub-in-rr ivt-sup y)
    (ivt-dist! ivt-sup y ivt-d (list '<= 0 ivt-d))
    (ivt-in-pts! y)
    (inst+ (ivt-forall-delta ivt-d) y)
    (fact 'fun-apply-type-c 'f 'RR 'RR y)
    (fact 'rr-sub-in-rr ivt-fs (list 'f y))
    (ivt-unpack-dist! ivt-fs (list 'f y) ivt-eps)
    (have! (list '<= (list 'f y) 'c)
           (lambda () (ivt-ineq (list '<= (list '- ivt-eps)
                                          (list '- ivt-fs (list 'f y))))))
    (have! (list '<= 'a y)
           (lambda () (ivt-ineq (list '<= 'a ivt-sup) (list '<= 0 ivt-d))))
    (ivt-in-set! y)
    (inst+ (ivt-forall-ub) y)
    (have! (list '= 0 ivt-d)
           (lambda () (ivt-ineq (list '<= y ivt-sup) (list '<= 0 ivt-d))))
    (ai (list 'NOT (list '= 0 ivt-d)))))

;;; b <= s + d: then |s - b| <= d already, so f(b) <= c; with c <= f(b) the
;;; endpoint b IS the root.  This is the s = b case, and it is why the witness
;;; is chosen per branch rather than fixed as s before the split.
(define (ivt-lt-atend!)
  (fact 'rr-sub-in-rr ivt-sup 'b)
  (ivt-dist! ivt-sup 'b ivt-d
             (list '<= 'b (list '+ ivt-sup ivt-d))
             (list '<= ivt-sup 'b)
             (list '<= 0 ivt-d))
  (ivt-in-pts! 'b)
  (inst+ (ivt-forall-delta ivt-d) 'b)
  (fact 'rr-sub-in-rr ivt-fs '(f b))
  (ivt-unpack-dist! ivt-fs '(f b) ivt-eps)
  (have! '(= (f b) c)
         (lambda () (ivt-ineq (list '<= (list '- ivt-eps) (list '- ivt-fs '(f b)))
                              '(<= c (f b)))))
  (ew 'b)
  (ivt-ass!))

(define (ivt-case-lt)
  (fact 'rr-sub-in-rr 'c ivt-fs)                      ; c - f(s) in RR
  (mac-h '< (list '< ivt-fs 'c))
  (dk-split! (list 'AND (list '<= ivt-fs 'c) (list 'NOT (list '= ivt-fs 'c))))
  (fact 'neq-sym ivt-fs 'c)
  (fact 'rr-sub-ne-zero 'c ivt-fs)
  (fact 'neq-sym ivt-eps 0)
  (ivt-pos! ivt-eps (list '<= ivt-fs 'c))
  (set! ivt-d (ivt-obtain 'delta (lambda () (inst+ (ivt-forall-eps) ivt-eps))))
  (mac-h 'pos-rr (list 'POS-RR ivt-d))
  (dk-split! (list 'AND (list 'IN ivt-d 'RR)
                        (list 'AND (list '<= 0 ivt-d) (list 'NOT (list '= 0 ivt-d)))))
  (have! (list 'AND (list 'IN ivt-sup 'RR) (list 'IN ivt-d 'RR)))
  (fact 'rr-add-closed ivt-sup ivt-d)
  (have! (list 'AND (list 'IN (list '+ ivt-sup ivt-d) 'RR) '(IN b RR)))
  (fact 'rr-leq-total (list '+ ivt-sup ivt-d) 'b)
  (use-cases (list (list '<= (list '+ ivt-sup ivt-d) 'b)
                   (list '<= 'b (list '+ ivt-sup ivt-d)))
             ivt-lt-inside!
             ivt-lt-atend!))

;;; =====================================================================
;;; CASE  f(s) = c.  s is the root.
;;; =====================================================================
(define (ivt-case-eq)
  (ew ivt-sup)
  (ivt-ass!))

;;; =====================================================================
;;; The proof.
;;; =====================================================================
(sp (make-wff ivt-stmt))
(ivt-peel!)
(ivt-split!)

(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
(fact 'fun-apply-type-c 'f 'RR 'RR 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(have! '(IN b (CCINT a b)) (lambda () (mac 'ccint-membership) (from-context!)))

;;; S is a set, a is in it, it is a subset of RR, and b is an upper bound.
(have! (list 'IN ivt-set 'SET) (lambda () (sep-set) (fact 'rr-is-set) (ass)))
(ivt-in-set! 'a)
(have! (list 'FORSOME 'x_ (list 'IN 'x_ ivt-set)) (lambda () (ew 'a) (ass)))
(have! (list 'SUBSET ivt-set 'RR)
  (lambda () (mac 'subset-def) (di) (sep-me (ivt-mem-in ivt-set)) (ass)))
(have! (list 'RR-UPPER-BOUND ivt-set 'b)
  (lambda ()
    (mac 'rr-upper-bound)
    (for-each (lambda (k)
                (dk-focus! k)
                (if (eq? (car (dk-goal)) 'IN)
                    (ass)
                    (begin (di) (sep-me (ivt-mem-in ivt-set)) (ivt-split!) (ass))))
              (dk-opened (lambda () (di))))))
(have! (list 'RR-BOUNDED-ABOVE ivt-set)
  (lambda () (mac 'rr-bounded-above) (ew 'b) (ass)))

;;; s = SUP(S) exists, lies in [a,b], and f is continuous there.
(fact 'rr-sup-in ivt-set)
(fact 'rr-sup-upper ivt-set)
(fact 'rr-sup-least ivt-set)
(mac-h 'rr-upper-bound (list 'RR-UPPER-BOUND ivt-set ivt-sup))
(dk-split! (ivt-and-with 'SUP))
(inst+ (ivt-forall-ub) 'a)                 ; a <= s   (a is in S)
(inst+ (ivt-forall-least) 'b)              ; s <= b   (b is an upper bound)
(have! (list 'IN ivt-sup '(CCINT a b)) (lambda () (mac 'ccint-membership) (from-context!)))
(inst+ (ivt-forall-cont) ivt-sup)
(fact 'fun-apply-type-c 'f 'RR 'RR ivt-sup)
(mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS 'f ivt-sup))
(dk-split! (ivt-and-with 'IS-METRIC-SPACE))

;;; Trichotomy on f(s) versus c.
(fact 'rr-lt-trichotomy ivt-fs 'c)
(use-cases (list (list '< ivt-fs 'c)
                 (list '= ivt-fs 'c)
                 (list '< 'c ivt-fs))
           ivt-case-lt
           ivt-case-eq
           ivt-case-gt)

(qed 'ivt)
(topic! 'ivt 'analysis)
(alias! 'ivt "Intermediate Value Theorem" "IVT" "Bolzano's theorem"
             "intermediate value theorem (interval form)")
