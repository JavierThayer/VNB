;;; ccint-abs-bounded.scm -- a continuous function on a CLOSED BOUNDED INTERVAL
;;; is bounded in ABSOLUTE VALUE there, PROVEN modulo 0.
;;;
;;;   f in FUN(RR,RR), a <= b, f continuous at every point of [a,b]
;;;     =>  forsome m in RR.  0 <= m  and  forall z in [a,b].  |f(z)| <= m
;;;
;;; "M = sup |f| on [a,b]" -- the second analytic input Theorem 5.2 (Bernstein
;;; density, docs/calculus.pdf) needs, beside step (87).  (87) is
;;; `continuous-uniformly-continuous-on-ccint'
;;; (theorem-library/uniform-continuity-ccint.scm), also `modulo 0'.
;;;
;;; WHY IT WAS NOT ALREADY THERE, WHICH IS THE FINDING THE DRIVE RECORDED.
;;; The tree looks like it has this and did not.  What it had is the two
;;; ATTAINMENT theorems, and they are ONE-SIDED:
;;;
;;;   extreme-value-max (theorem-library/evt-proof.scm)
;;;      forsome c in [a,b]. forall x in [a,b].  f(x) <= f(c)
;;;   extreme-value-min (theorem-library/evt-min-proof.scm)
;;;      forsome c in [a,b]. forall x in [a,b].  f(c) <= f(x)
;;;
;;; and `continuous-bounded-above-on-ccint' (theorem-library/ccint-bounded.scm)
;;; is bounded ABOVE only.  Nothing bounded |f|.  Bernstein's estimate splits
;;; the sum at |l/n - x| <= delta and bounds the FAR block by 2M -- an
;;; absolute-value bound, both sides at once -- so the gap was real, however
;;; small.  It is small: both EVTs are in hand, so this file is a MERGE and
;;; contains no analysis.  No supremum, no completeness, no creeping argument:
;;; every one of those was paid for by evt-proof and evt-min-proof.
;;;
;;; WHY IT IS NOT STATED WITH A PREDICATE.  Same reason as
;;; uniform-continuity-ccint: `IS-UNIFORMLY-CONTINUOUS' and the boundedness
;;; predicates want the domain to be a metric SPACE, and CCINT(a,b) is not one
;;; in this tree -- there is no metric SUBSPACE structure, which is exactly the
;;; blocker Heine-Borel sits behind.  The statement is therefore written out
;;; over CCINT(a,b) with `abs', following ccint-bounded.scm's precedent.  It is
;;; also the form the Bernstein estimate consumes, which bounds |f(x)| and
;;; |f(l/n)| for plain reals.
;;;
;;; THE ROUTE.  Let cx attain the max and cn the min.  For every z in [a,b],
;;;
;;;     f(cn)  <=  f(z)  <=  f(cx).
;;;
;;; `rr-upper-of-two' (theorem-library/rr-order-basics.scm) -- the same lemma
;;; ccint-bounded merges its two unrelated bounds with, and the reason neither
;;; proof needs a MAX operator -- gives an m above BOTH |f(cx)| and |f(cn)|.
;;; With `rr-le-abs' (y <= |y|) at f(cx) and `rr-neg-abs-le' (-|y| <= y) at
;;; f(cn),
;;;
;;;     -m  <=  -|f(cn)|  <=  f(cn)  <=  f(z)  <=  f(cx)  <=  |f(cx)|  <=  m
;;;
;;; is linear, and `rr-abs-bound' turns the goal |f(z)| <= m into exactly that
;;; pair of bounds.  0 <= m is `rr-abs-nonneg' at cx plus the same merge.
;;; Every leaf below the merge is one `ineq' call.
;;;
;;; THE TRAP, AND IT WAS PREDICTED BEFORE THE FIRST RUN AND MEASURED AFTER.
;;; `rr-abs-bound' is GUARDED on (IN x RR), so the `mac' on the goal
;;; |f(z)| <= m needs (IN (f z) RR) ALREADY in context: a `mac' whose guard is
;;; not evident does not fire at ALL -- it warns `macete not applicable' and
;;; leaves the goal untouched.  Deleting the one line
;;;
;;;     (fact 'fun-apply-type-c 'f 'RR 'RR z)
;;;
;;; from cab-bound! reproduces it exactly, and it fails TWICE over:
;;;
;;;     ;VNB warning: apply-macete: macete not applicable: rr-abs-bound
;;;     ;VNB warning: ineq: goal not a linear-RR consequence of the named
;;;                   assumptions: abs(f(z_)) <= w__2003
;;;
;;; -- the second message blames the GOAL, which is linear and true.  `ineq'
;;; certifies every atom of every named premise as `IN _ RR' before it will
;;; accept the premise, so the missing typing makes it drop premises silently
;;; and then report the goal.  Same failure, same one-line cure, as
;;; uniform-continuity-ccint's f(t).  The rule: when `ineq' calls an obviously
;;; linear goal non-linear, look for an uncertifiable ATOM, not a bad goal.
;;;
;;; ORDER OF THE THREE MOVES AT z, which is the only other thing that can go
;;; wrong: `mac-h' REPLACES the assumption it unfolds, so the two `inst+' of the
;;; attainment universals -- which need (IN z (CCINT a b)) to detach -- must run
;;; BEFORE the `mac-h' of `ccint-membership' that destroys it.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; Loads after evt-proof and evt-min-proof (both EVTs), ccint-basics
;;; (ccint-membership), rr-abs-basics (rr-abs-closed, rr-abs-nonneg, rr-le-abs,
;;; rr-neg-abs-le, rr-abs-bound), rr-order-basics (rr-upper-of-two),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.

;;; ---- file-local driver helpers (the `cab-' prefix) -------------------

(define (cab-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (cab-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cab-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (cab-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cab-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
;;; `(ineq)' with NO arguments proves nothing; name the premises by looking
;;; each one up in the context.
(define (cab-ineq . forms) (apply ineq (map cab-idx forms)))

(define (cab-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 16)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (cab-goal-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cab-goal-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an assumption LANDS -- a guarded universal goes whole under one
;;; call, an unguarded one does not, so counting `di's reaches the wrong goal.
(define (cab-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "cab-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (cab-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME that is ALREADY in the context.  `obtain' cannot: it
;;; recognises only an existential its own lane just landed, and it swallows
;;; errors raised inside that lane.  The eigenvariable is read off by
;;; free-variable set difference, and a miss ERRORS.
(define (cab-skolem! ex)
  (let* ((fv0 (cab-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (cab-fvs (dk-asms)))))
      (if (null? fresh)
          (error "cab-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; ---- eigenvariables --------------------------------------------------
(define cab-cx #f)      ; the point where f attains its maximum on [a,b]
(define cab-cn #f)      ; the point where f attains its minimum
(define cab-m  #f)      ; a common upper bound of |f(cx)| and |f(cn)|
(define cab-absx #f)
(define cab-absn #f)

;;; The attainment universal naming `c'.  Discriminate on the EIGENVARIABLE and
;;; on the CONSEQUENT's head, never on a symbol the formula merely contains:
;;; both EVT citations leave their whole instantiation chain in the context, and
;;; `forall([x in rr], x <= abs(x))' is FORALL/IMPLIES/<= as well.
(define (cab-forall-at c)
  (cab-find 'attain
    (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                     (dk-contains? h c)
                     (let ((body (caddr h)))
                       (and (pair? body) (eq? (car body) 'IMPLIES)
                            (pair? (caddr body))
                            (eq? (car (caddr body)) '<=)))))))

;;; ---- the statement ---------------------------------------------------

(define cab-stmt
  (forall-guarded '(f a b)
    (list '(IN f (FUN RR RR)) '(IN a RR) '(IN b RR) '(<= a b)
          '(FORALL x (IMPLIES (IN x (CCINT a b))
                              (IS-CONTINUOUS-AT RR-MS RR-MS f x))))
    (list 'FORSOME 'm_
      (list 'AND '(IN m_ RR)
        (list 'AND '(<= 0 m_)
          (list 'FORALL 'z_
            (list 'IMPLIES '(IN z_ (CCINT a b))
                  '(<= (abs (f z_)) m_))))))))

;;; goal: |f(z)| <= m, for the z the outer `di' just landed in [a,b].
(define (cab-bound! z)
  ;; BEFORE the mac-h below, which destroys (IN z [a,b]) that these detach on.
  (inst+ (cab-forall-at cab-cx) z)
  (inst+ (cab-forall-at cab-cn) z)
  (mac-h 'ccint-membership (list 'IN z '(CCINT a b)))
  (cab-split!)
  ;; f(z) in RR, and it must land HERE: `rr-abs-bound' is guarded, and a `mac'
  ;; whose guard is not evident does not fire at all.  See the header.
  (fact 'fun-apply-type-c 'f 'RR 'RR z)
  (mac 'rr-abs-bound)
  (cab-goal-and!
   (lambda ()
     (cab-ineq (list '<= (list 'f z) (list 'f cab-cx))
               (list '<= cab-absx cab-m)
               (list '<= (list 'f cab-cx) cab-absx)
               (list '<= (list 'f cab-cn) (list 'f z))
               (list '<= cab-absn cab-m)
               (list '<= (list '- cab-absn) (list 'f cab-cn))))))

;;; ---- the proof -------------------------------------------------------

(sp (make-wff cab-stmt))
(cab-peel!)

;;; Both EVTs carry a CONJUNCTIVE antecedent, and `fact' will not split one:
;;; without this `have!' the citation lands the IMPLICATION, silently, and the
;;; skolemizer below dies on it.  (The continuity universal is the SECOND
;;; antecedent and is already in context, so `fact' detaches that one itself.)
(have! '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (<= a b)))))

;;; The two attainment points.  `dk-fact!' takes the DEEPEST landing -- the
;;; fully detached existential -- not the partly-peeled implications beside it.
(set! cab-cx (cab-skolem! (dk-fact! 'extreme-value-max 'f 'a 'b)))
(set! cab-cn (cab-skolem! (dk-fact! 'extreme-value-min 'f 'a 'b)))

;;; At each attainment point: f is defined there, |f| there is a real and
;;; nonnegative, and the two one-sided abs bounds hold.
(for-each
 (lambda (c)
   (mac-h 'ccint-membership (list 'IN c '(CCINT a b)))
   (cab-split!)
   (fact 'fun-apply-type-c 'f 'RR 'RR c)
   (fact 'rr-abs-closed (list 'f c))
   (fact 'rr-abs-nonneg (list 'f c))
   (fact 'rr-le-abs (list 'f c))                     ; y <= |y|
   (fact 'rr-neg-abs-le (list 'f c)))                ; -|y| <= y
 (list cab-cx cab-cn))

;;; THE MERGE: one m above both |f(cx)| and |f(cn)|.  No MAX operator.
(set! cab-absx (list 'abs (list 'f cab-cx)))
(set! cab-absn (list 'abs (list 'f cab-cn)))
(set! cab-m (cab-skolem! (dk-fact! 'rr-upper-of-two cab-absx cab-absn)))

(ew cab-m)
(cab-goal-and!
 (lambda ()
   (cond ((eq? (car (dk-goal)) 'IN) (ass))            ; m in RR
         ((eq? (car (dk-goal)) '<=)                   ; 0 <= m
          (cab-ineq (list '<= 0 cab-absx) (list '<= cab-absx cab-m)))
         (else                                        ; forall z in [a,b]
          (cab-bound! (cadr (car (cab-di-landed!))))))))

(qed 'continuous-abs-bounded-on-ccint)
(topic! 'continuous-abs-bounded-on-ccint 'analysis)
(alias! 'continuous-abs-bounded-on-ccint
        "a continuous function on a closed interval is bounded in absolute value"
        "sup |f| on a closed bounded interval"
        "M bounds |f| on [a,b]")
