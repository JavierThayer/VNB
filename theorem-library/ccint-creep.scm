;;; ccint-creep.scm -- the CREEPING PRINCIPLE on a closed interval, PROVEN.
;;;
;;;   G subset RR,  a in G,  b an upper bound of G,  a <= b,  and
;;;   for every t in [a,b] there is d > 0 such that
;;;       (some member of G exceeds t - d)  =>  every y in [a,b] with y <= t+d is in G
;;;     =>  b in G.
;;;
;;; WHAT IT IS FOR.  Every "creeping along the interval" argument in freshman
;;; analysis has this shape: a property that holds at `a', that continuity
;;; propagates a little to the right of wherever it already holds, therefore
;;; holds at `b'.  Boundedness of a continuous function on [a,b] is one
;;; instance; the attainment half of the Extreme Value Theorem is a second;
;;; Heine-Borel (a finite subcover of [a,x]) is a third, and uniform continuity
;;; a fourth.  Each of those would otherwise mean writing the whole supremum
;;; argument out again.  Here it is written ONCE: the instance supplies only
;;; the local step -- the `d' at each t -- and this lemma does the completeness
;;; bookkeeping.
;;;
;;; This is the mechanism the working brief asks for in place of N bespoke
;;; lemmas: the caller's obligation is exactly the mathematics of its own case,
;;; and none of the supremum plumbing.
;;;
;;; THE PROOF.  s = SUP(G) exists (G is inhabited by a, bounded above by b, and
;;; a subset of RR), lies in [a,b], and the hypothesis gives a d > 0 at s.
;;; `rr-sup-approx' (theorem-library/rr-sup-approx.scm) produces a member of G
;;; above s - d, which is precisely the antecedent of the local step, so every
;;; y in [a,b] below s + d is in G.  Two cases on s + d versus b:
;;;
;;;   * s + d <= b.  Then s + d itself is such a y, so s + d is in G, so
;;;     s + d <= s (s is an upper bound), so d <= 0 -- against d > 0.
;;;   * b <= s + d.  Then b is such a y, and b in G IS the conclusion.
;;;
;;; The second case is the whole point of stating the local step as "every y up
;;; to t + d" rather than "t + d itself": at the right-hand end the interval
;;; runs out before the step does, and the conclusion is collected there.  It
;;; is the same two-branch shape as the f(s) < c case of ivt-proof.scm, and for
;;; the same reason.
;;;
;;; NO DOWNWARD-CLOSURE HYPOTHESIS.  G is not required to be an initial segment
;;; of [a,b].  Every instance so far happens to be one, but the proof never
;;; uses it: what it needs is a member of G near s, and rr-sup-approx supplies
;;; that from completeness alone.
;;;
;;; WHY THE LOCAL STEP'S EXISTENTIAL BINDS `w_'.  It is written with the same
;;; bound variable rr-sup-approx's conclusion uses, so the formula that lemma
;;; lands IS the antecedent of the local step and `detach!' fires on it
;;; directly.  Nothing deeper -- an alpha-variant would want a bridging step
;;; this proof does not need.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after rr-sup-approx, ccint-basics (ccint-membership), extreme-value
;;; (CCINT), rr-order-basics and driver-kit.

;;; ---- file-local driver helpers (the `cc-' prefix) --------------------

(define (cc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; Select a hypothesis by CONTENT and ERROR on a miss -- a driver that
;;; reconstructs a formula to cite it addresses the wrong assumption silently.
(define (cc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cc-and-with sub)
  (cc-find 'and-with
    (lambda (f) (and (pair? f) (eq? (car f) 'AND) (dk-contains? f sub)))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE: the context carries membership formulas whose atoms can never be
;;; certified in RR, and one such premise poisons the whole call.
(define (cc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cc-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (cc-ineq . forms) (apply ineq (map cc-idx forms)))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (cc-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cc-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `obtain' returns #f on a miss and a #f eigenvariable propagates into every
;;; later formula as a term nobody can read.  Make it error.
(define (cc-obtain what lane)
  (let ((v (obtain lane)))
    (if (not v) (error "cc-obtain: nothing obtained for" what))
    v))

;;; ---- the statement ---------------------------------------------------

(define cc-sup '(SUP g_))

;;; Built from flat lists rather than hand-nested: a formula this deep is where
;;; a miscounted parenthesis reads as a different theorem.
(define cc-ante
  (list 'FORSOME 'w_ (list 'AND '(IN w_ g_) '(< (- t_ d_) w_))))

(define cc-cons
  (list 'FORALL 'y_
        (list 'IMPLIES '(AND (IN y_ (CCINT a b)) (<= y_ (+ t_ d_)))
                       '(IN y_ g_))))

(define cc-local
  (list 'FORALL 't_
        (list 'IMPLIES '(IN t_ (CCINT a b))
              (list 'FORSOME 'd_
                    (list 'AND '(IN d_ RR)
                          (list 'AND '(< 0 d_)
                                (list 'IMPLIES cc-ante cc-cons)))))))

(define cc-stmt
  (forall-guarded '(a b g_)
    (list '(IN a RR) '(IN b RR) '(<= a b)
          '(SUBSET g_ RR) '(IN a g_) '(RR-UPPER-BOUND g_ b)
          cc-local)
    '(IN b g_)))

;;; ---- eigenvariables --------------------------------------------------
(define cc-d #f)                        ; the local step's radius at s

;;; ---- hypothesis finders ----------------------------------------------

;;; forall y in [a,b] with y <= s + d.  y in G -- what the local step delivered.
(define (cc-forall-y)
  (cc-find 'reach
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) 'IN)
                            (eq? (caddr (caddr body)) 'g_)))))))

;;; forall x in G. x <= SUP(G) -- the unfolded rr-sup-upper.
(define (cc-forall-ub)
  (cc-find 'ub
    (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                     (let ((body (caddr f)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body)) (eq? (car (caddr body)) '<=)
                            (equal? (caddr (caddr body)) cc-sup)))))))

;;; ---- the two branches ------------------------------------------------

;;; s + d <= b: the point s + d lands in G, so s + d <= s and d <= 0.
(define (cc-inside!)
  (let ((y (list '+ cc-sup cc-d)))
    (fact 'rr-leq-reflexive y)
    (have! (list 'IN y '(CCINT a b))
      (lambda ()
        (mac 'ccint-membership)
        (cc-goal-and!
         (lambda ()
           (if (equal? (dk-goal) (list '<= 'a y))
               (cc-ineq (list '<= 'a cc-sup) (list '<= 0 cc-d))
               (ass))))))
    (have! (list 'AND (list 'IN y '(CCINT a b)) (list '<= y y)))
    (inst+ (cc-forall-y) y)                       ; IN (s + d) G
    (inst+ (cc-forall-ub) y)                      ; s + d <= s
    (have! (list '= 0 cc-d)
      (lambda () (cc-ineq (list '<= y cc-sup) (list '<= 0 cc-d))))
    (ai (list 'NOT (list '= 0 cc-d)))))

;;; b <= s + d: b itself is one of the y's, and IN b G is the conclusion.
(define (cc-atend!)
  (fact 'rr-leq-reflexive 'b)
  (have! '(IN b (CCINT a b))
    (lambda () (mac 'ccint-membership) (from-context!)))
  (have! (list 'AND '(IN b (CCINT a b)) (list '<= 'b (list '+ cc-sup cc-d))))
  (inst+ (cc-forall-y) 'b)
  (ass))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff cc-stmt))
(cc-peel!)

(define cc-hyp (cc-find 'local (dk-head? 'FORALL)))

;;; G is inhabited and bounded above, so SUP(G) exists.
(have! '(FORSOME x_ (IN x_ g_)) (lambda () (ew 'a) (ass)))
(have! '(RR-BOUNDED-ABOVE g_) (lambda () (mac 'rr-bounded-above) (ew 'b) (ass)))
(fact 'rr-sup-in 'g_)                             ; SUP(G) in RR
(fact 'rr-sup-upper 'g_)                          ; RR-UPPER-BOUND(G, SUP(G))
(mac-h 'rr-upper-bound (list 'RR-UPPER-BOUND 'g_ cc-sup))
(dk-split! (cc-and-with cc-sup))
(inst+ (cc-forall-ub) 'a)                         ; a <= SUP(G)   (a is in G)
(fact 'rr-sup-least 'g_ 'b)                       ; SUP(G) <= b   (b is an upper bound)
(have! (list 'IN cc-sup '(CCINT a b))
  (lambda () (mac 'ccint-membership) (from-context!)))

;;; The local step at s, and the member of G its antecedent asks for.  The
;;; `<'-unfolding of 0 < d comes AFTER the rr-sup-approx citation: `mac-h'
;;; REPLACES the assumption it unfolds, and (< 0 d) is one of that lemma's
;;; guards.
(set! cc-d (cc-obtain 'radius (lambda () (inst+ cc-hyp cc-sup))))
(fact 'rr-sup-approx 'g_ cc-d)                    ; forsome w in G. s - d < w
;; Discriminate the local step on its CONSEQUENT as well: `fact' lands its
;; whole instantiation chain, and rr-sup-approx's own partly-peeled forms are
;; implications with a FORSOME antecedent too (its inhabitedness guard).  On
;; the antecedent alone this picked one of those and `detach!' no-opped
;; silently -- so the landing is checked, not assumed.
(dk-landed
 (lambda ()
   (detach! (cc-find 'step
              (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                               (pair? (cadr f)) (eq? (car (cadr f)) 'FORSOME)
                               (pair? (caddr f)) (eq? (car (caddr f)) 'FORALL)))))))
(mac-h '< (list '< 0 cc-d))
(dk-split! (list 'AND (list '<= 0 cc-d) (list 'NOT (list '= 0 cc-d))))

;;; s + d versus b
(have! (list 'AND (list 'IN cc-sup 'RR) (list 'IN cc-d 'RR)))
(fact 'rr-add-closed cc-sup cc-d)
(have! (list 'AND (list 'IN (list '+ cc-sup cc-d) 'RR) '(IN b RR)))
(fact 'rr-leq-total (list '+ cc-sup cc-d) 'b)
(use-cases (list (list '<= (list '+ cc-sup cc-d) 'b)
                 (list '<= 'b (list '+ cc-sup cc-d)))
           cc-inside!
           cc-atend!)

(qed 'ccint-creep)
(topic! 'ccint-creep 'analysis)
(alias! 'ccint-creep "creeping principle" "creeping along a closed interval"
                     "connectedness of a closed interval")
