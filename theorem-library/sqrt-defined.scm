;;; sqrt-defined.scm -- SQRT DEFINED by the intermediate value theorem, and the
;;; five supports that used to characterise it RETIRED as theorems.
;;;
;;; THE DEFINITION lives where SQRT is introduced, structure-library/real-powers.scm:
;;;
;;;     SQRT(a)  ==  IOTA x.  x in RR  and  0 <= x  and  x*x = a
;;;
;;; Until 2026-08-17 SQRT was a bare `register-constant!' pinned by five
;;; `well-known' supports -- sqrt-nonneg, sqrt-sq, sqrt-of-sq, sqrt-mono,
;;; sqrt-mul -- and four of them (all but sqrt-mul) were the ENTIRE bill of
;;; cc-is-metric-space and of cc-magnitude-triangle; no cc-magnitude-* theorem
;;; billed anything else.  This file discharges all five, so that family reads
;;; `modulo 0'.
;;;
;;; WHAT THE DESCRIPTION COSTS, and why it is not circular.  `iota-d' posts
;;; exactly two subgoals: the existence-and-uniqueness obligation, and the
;;; original goal with the defining property assumed.  So the file is in
;;; dependency order:
;;;
;;;   sqrt-exists   0 <= a  =>  some nonnegative real squares to a.
;;;                 `ivt' on z |-> z*z over [0, 1+a] at the value a: the map is
;;;                 in FUN(RR,RR) and continuous (sq-continuous.scm), 0*0 = 0
;;;                 <= a at the left end, and (1+a)*(1+a) = 1 + 2a + a*a >= a at
;;;                 the right, the last because a square is nonnegative.
;;;                 1+a, not a: for a < 1 the interval [0,a] does not reach the
;;;                 root, and 1+a dominates for every a >= 0 at once.
;;;   sqrt-unique   0 <= x, 0 <= y, x*x = y*y  =>  x = y.  (x-y)(x+y) = 0 by
;;;                 `crs', then rr-no-zero-divisors: either x = y outright, or
;;;                 x + y = 0, which with both nonnegative forces both to 0.
;;;   sqrt-prop     the two together, through `iota-d': SQRT(a) is a nonnegative
;;;                 real and its square is a.  Everything below is this plus
;;;                 uniqueness.
;;;   sqrt-char     the uniqueness in usable form: any nonnegative real square
;;;                 root of a IS SQRT(a).  sqrt-of-sq and sqrt-mul are one
;;;                 citation of it apiece.
;;;
;;; WHY THE `x in RR' IS IN THE DESCRIPTION.  `<=' is primitive and unguarded --
;;; the RR order axioms constrain it on reals without forbidding it to relate a
;;; real to a non-real, which is the point ivt-proof.scm's header makes about
;;; its own witness.  Without the typing, sqrt-unique does not apply to the
;;; description's own candidates and the IOTA describes nothing.
;;;
;;; THE ONE PLACE `ineq' DOES THE WORK OF AN EQUALITY REWRITE.  Twice below the
;;; step wanted is "these two equations give that third one", where `subst'
;;; would need the equation the other way round and there is no reverse in
;;; context.  The oracle takes it directly: the products are opaque ATOMS to it,
;;; the equations linear in those atoms -- provided every atom carries an
;;; `IN _ RR' certificate, which is why each such block types its products with
;;; rr-mul-closed first.
;;;
;;; WHAT IT COSTS.  Nothing: `modulo 0'.
;;;
;;; `sqrt-rpow' is NOT touched.  It ties this defined SQRT to a still-axiomatic
;;; RPOW, so it is a claim about RPOW and stays a `well-known' support.
;;;
;;; Loads after ivt-proof (ivt), sq-continuous (sq-fun-in-fun, sq-continuous-at),
;;; ccint-basics (ccint-membership), rr-order-basics (rr-sq-nonneg,
;;; rr-no-zero-divisors, rr-prod-le-prod), rr-abs-basics (rr-abs-closed,
;;; rr-abs-nonneg, rr-abs-mult, rr-abs-of-nonneg) and binary-minus-laws
;;; (rr-sub-in-rr).  Must PRECEDE cc-magnitude and cc-metric-space-proof, which
;;; cite the five.

;;; ---- file-local driver helpers (the `sd-' prefix) --------------------

(define sd-sq '(VNB-LAMBDA z_ RR (* z_ z_)))

;;; `di' until the head stops being a quantifier or an implication.  Guarded on
;;; fuel as well as on the head: `di' only WARNS when it cannot decompose, so a
;;; head test alone spins on a no-op.
(define (sd-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; `ai' every context conjunction to exhaustion.  Note that `ai' REMOVES the
;;; conjunction it splits (primitive-inferences.scm, and-elim), so a later
;;; citation of an AND-guarded theorem must `have!' its guard back -- which is
;;; safe precisely because the AND is no longer there to alpha-self-loop against.
(define (sd-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 20)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

;;; `ineq' wants 1-based assumption indices, and the premises are named ONE BY
;;; ONE: a single premise whose atoms cannot be certified in RR poisons the
;;; whole call.
(define (sd-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sd-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (sd-ineq . forms) (apply ineq (map sd-idx forms)))

(define (sd-fvs forms) (apply append (map free-vars forms)))

;;; `ai' the existential EX, split what lands, and return the eigenvariable, read
;;; off by free-variable difference.  `obtain' will not do: it diffs its own lane
;;; and is blind to an existential that is ALREADY in the context, which is
;;; exactly where `fact' puts one.
(define (sd-skolem! ex)
  (let ((fv0 (sd-fvs (dk-asms))))
    (dk-landed (lambda () (ai ex)))
    (sd-split!)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (sd-fvs (dk-asms)))))
      (if (null? fresh)
          (error "sd-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

(define (sd-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-leaves)))

;;; =====================================================================
;;; (1)  EXISTENCE.   0 <= a  =>  some nonnegative real squares to a.
;;; =====================================================================

(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
     (FORSOME x_ (AND (IN x_ RR) (AND (<= 0 x_) (= (* x_ x_) a))))))))
(sd-peel!)
(sd-split!)

;; the interval [0, 1+a]
(fact 'rr-zero-in)
(fact 'rr-one-in)
(have! '(AND (IN 1 RR) (IN a RR)))
(fact 'rr-add-closed 1 'a)
(have! '(<= 0 (+ 1 a)) (lambda () (sd-ineq '(<= 0 a))))

;; the map, and its continuity ON the interval -- `ivt' wants the universal
;; verbatim, so it is built and proved rather than searched for.
(fact 'sq-fun-in-fun)
(define sd-cont
  (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x (list 'CCINT 0 '(+ 1 a)))
                     (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS sd-sq 'x))))
(have! sd-cont
  (lambda ()
    (sd-peel!)
    (mac-h 'ccint-membership (list 'IN 'x (list 'CCINT 0 '(+ 1 a))))
    (sd-split!)
    (fact 'sq-continuous-at 'x)
    (ass)))

;; the two endpoint values.  `lam-b' is safe here: both arguments are typed
;; above, which is what a beta reduction needs and needs FIRST.
(define sd-lo (list sd-sq 0))
(define sd-hi (list sd-sq '(+ 1 a)))
(have! (list 'AND (list '<= sd-lo 'a) (list '<= 'a sd-hi))
  (lambda ()
    (for-each
     (lambda (k)
       (dk-focus! k)
       (lam-b)
       (if (equal? (dk-goal) '(<= (* 0 0) a))
           (begin (have! '(= (* 0 0) 0) (lambda () (crs)))
                  (subst '(= (* 0 0) 0))
                  (ass))
           ;; (1+a)(1+a) = 1 + 2a + a*a, and a square is nonnegative, so the
           ;; residue is linear in the atoms a and a*a.
           (begin
             (have! '(AND (IN a RR) (IN a RR)))
             (fact 'rr-mul-closed 'a 'a)
             (fact 'rr-sq-nonneg 'a)
             (have! '(= (* (+ 1 a) (+ 1 a)) (+ (+ 1 (+ a a)) (* a a)))
                    (lambda () (crs)))
             (subst '(= (* (+ 1 a) (+ 1 a)) (+ (+ 1 (+ a a)) (* a a))))
             (sd-ineq '(<= 0 a) '(<= 0 (* a a))))))
     (dk-opened (lambda () (di))))))

;; ... and the theorem.  The witness comes back inside CCINT(0,1+a); only its
;; typing and its lower bound are wanted.
(define sd-ex (dk-fact! 'ivt sd-sq 0 '(+ 1 a) 'a))
(define sd-w  (sd-skolem! sd-ex))
(mac-h 'ccint-membership (list 'IN sd-w (list 'CCINT 0 '(+ 1 a))))
(sd-split!)
(have! (list '= (list '* sd-w sd-w) (list sd-sq sd-w)) (lambda () (lam-b) (crs)))
(have! (list '= (list '* sd-w sd-w) 'a)
       (lambda () (subst (list '= (list '* sd-w sd-w) (list sd-sq sd-w))) (ass)))
(ew sd-w)
(from-context!)
(qed 'sqrt-exists)
(topic! 'sqrt-exists 'analysis)
(alias! 'sqrt-exists "existence of square roots" "every nonnegative real has a square root")

;;; =====================================================================
;;; (2)  UNIQUENESS.   0 <= x, 0 <= y, x*x = y*y  =>  x = y.
;;; =====================================================================

(sp (make-wff '(FORALL x_ (FORALL y_
     (IMPLIES (AND (IN x_ RR) (IN y_ RR))
       (IMPLIES (AND (<= 0 x_) (<= 0 y_))
         (IMPLIES (= (* x_ x_) (* y_ y_)) (= x_ y_))))))))
(sd-peel!)
(sd-split!)
(fact 'rr-sub-in-rr 'x_ 'y_)
(have! '(AND (IN x_ RR) (IN y_ RR)))
(fact 'rr-add-closed 'x_ 'y_)
;; the difference of squares, brought to 0 by the hypothesis
(have! '(= (* (- x_ y_) (+ x_ y_)) (- (* x_ x_) (* y_ y_))) (lambda () (crs)))
(have! '(= (* (- x_ y_) (+ x_ y_)) 0)
  (lambda ()
    (subst '(= (* (- x_ y_) (+ x_ y_)) (- (* x_ x_) (* y_ y_))))
    (subst '(= (* x_ x_) (* y_ y_)))
    (crs)))
(fact 'rr-no-zero-divisors '(- x_ y_) '(+ x_ y_))
(use-cases '((= (- x_ y_) 0) (= (+ x_ y_) 0))
  ;; x - y = 0 is the conclusion, linearly
  (lambda () (sd-ineq '(= (- x_ y_) 0)))
  ;; x + y = 0 with both nonnegative pins both at 0
  (lambda () (sd-ineq '(= (+ x_ y_) 0) '(<= 0 x_) '(<= 0 y_))))
(qed 'sqrt-unique)
(topic! 'sqrt-unique 'analysis)
(alias! 'sqrt-unique "uniqueness of nonnegative square roots")

;;; =====================================================================
;;; (3)  THE DEFINING PROPERTY.  SQRT(a) is a nonnegative real, and its
;;;      square is a.  This is the `iota-d' step, and the only one.
;;; =====================================================================

;;; the existence-and-uniqueness leaf `iota-d' posts: a witness satisfying the
;;; description, plus its uniqueness.  Both halves are the two theorems above.
(define (sd-exuniq!)
  (have! '(AND (IN a RR) (<= 0 a)))
  (let* ((ex (dk-fact! 'sqrt-exists 'a))
         (w  (sd-skolem! ex)))
    (ew w)
    (for-each
     (lambda (k)
       (dk-focus! k)
       (if (eq? (car (dk-goal)) 'FORALL)
           (begin
             (sd-peel!)
             (sd-split!)
             (let ((y (caddr (dk-goal))))            ; goal (= w y)
               (have! (list 'AND (list 'IN w 'RR) (list 'IN y 'RR)))
               (have! (list 'AND (list '<= 0 w) (list '<= 0 y)))
               (have! (list '= (list '* w w) (list '* y y))
                      (lambda () (subst (list '= (list '* w w) 'a))
                                 (subst (list '= (list '* y y) 'a))
                                 (crs)))
               (fact 'sqrt-unique w y)
               (ass)))
           (from-context!)))
     (dk-opened (lambda () (di))))))

(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
     (AND (IN (SQRT a) RR) (AND (<= 0 (SQRT a)) (= (* (SQRT a) (SQRT a)) a)))))))
(sd-peel!)
(sd-split!)
(mac 'SQRT)
(define sd-io (cadr (cadr (dk-goal))))       ; the IOTA term, as the engine built it
(for-each
 (lambda (l)
   (dk-focus! l)
   (if (eq? (car (dk-goal)) 'FORSOME)
       (sd-exuniq!)
       (ass)))                               ; the defining property IS the goal
 (dk-opened (lambda () (iota-d sd-io))))
(qed 'sqrt-prop)
(topic! 'sqrt-prop 'analysis)
(alias! 'sqrt-prop "the defining property of the square root")

;;; =====================================================================
;;; (4)  CHARACTERISATION.  A nonnegative real square root of a IS SQRT(a).
;;; =====================================================================

(sp (make-wff '(FORALL a (FORALL x_
     (IMPLIES (AND (IN a RR) (<= 0 a))
       (IMPLIES (AND (IN x_ RR) (<= 0 x_))
         (IMPLIES (= (* x_ x_) a) (= (SQRT a) x_))))))))
;; `sqrt-prop' is cited BEFORE the split: `sd-peel!' lands the guard as one
;; conjunction, which is exactly what an AND-guarded `fact' wants, and a `have!'
;; of a formula already in context is an alpha self-loop, not a no-op.
(sd-peel!)
(fact 'sqrt-prop 'a)
(sd-split!)
(have! '(AND (IN (SQRT a) RR) (IN x_ RR)))
(have! '(AND (<= 0 (SQRT a)) (<= 0 x_)))
(have! '(= (* (SQRT a) (SQRT a)) (* x_ x_))
       (lambda () (subst '(= (* (SQRT a) (SQRT a)) a))
                  (subst '(= (* x_ x_) a))
                  (crs)))
(fact 'sqrt-unique '(SQRT a) 'x_)
(ass)
(qed 'sqrt-char)
(topic! 'sqrt-char 'analysis)
(alias! 'sqrt-char "characterisation of the square root")

;;; =====================================================================
;;; (5)  THE FIVE RETIRED SUPPORTS, statements unchanged.
;;; =====================================================================

;;; sqrt(a) is a nonnegative real.
(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
                 (AND (IN (SQRT a) RR) (<= 0 (SQRT a)))))))
(sd-peel!)
(fact 'sqrt-prop 'a)
(sd-split!)
(from-context!)
(qed 'sqrt-nonneg)
(topic! 'sqrt-nonneg 'plumbing)

;;; sqrt(a)^2 = a -- the defining property, projected.
(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
                 (= (* (SQRT a) (SQRT a)) a)))))
(sd-peel!)
(fact 'sqrt-prop 'a)
(sd-split!)
(ass)
(qed 'sqrt-sq)
(topic! 'sqrt-sq 'algebra)

;;; sqrt(a^2) = |a| for EVERY real a -- no sign hypothesis, which is the whole
;;; content: |a| is the nonnegative square root of a*a whatever the sign of a.
;;; The equation |a|*|a| = a*a is rr-abs-mult and rr-abs-of-nonneg composed, and
;;; the composition is `ineq' rather than `subst' -- see the header.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (= (SQRT (* a a)) (abs a))))))
(sd-peel!)
(have! '(AND (IN a RR) (IN a RR)))
(fact 'rr-mul-closed 'a 'a)
(fact 'rr-sq-nonneg 'a)
(fact 'rr-abs-closed 'a)
(fact 'rr-abs-nonneg 'a)
(fact 'rr-abs-closed '(* a a))
(have! '(AND (IN (abs a) RR) (IN (abs a) RR)))
(fact 'rr-mul-closed '(abs a) '(abs a))
;; (AND (IN a RR) (IN a RR)) is still in context from the rr-mul-closed above --
;; re-`have!'ing it would be an alpha self-loop, not a no-op.
(fact 'rr-abs-mult 'a 'a)                       ; |a*a| = |a|*|a|
(fact 'rr-abs-of-nonneg '(* a a))               ; |a*a| = a*a
(have! '(= (* (abs a) (abs a)) (* a a))
       (lambda () (sd-ineq '(= (abs (* a a)) (* (abs a) (abs a)))
                           '(= (abs (* a a)) (* a a)))))
(have! '(AND (IN (* a a) RR) (<= 0 (* a a))))
(have! '(AND (IN (abs a) RR) (<= 0 (abs a))))
(fact 'sqrt-char '(* a a) '(abs a))
(ass)
(qed 'sqrt-of-sq)
(topic! 'sqrt-of-sq 'algebra)

;;; sqrt is nondecreasing.  Proved WITHOUT a negation: rr-leq-total decides the
;;; two roots, and in the wrong branch rr-prod-le-prod squares it back to
;;; b <= a, which with a <= b is antisymmetry and makes the two roots equal.
(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
                 (FORALL b (IMPLIES (AND (IN b RR) (<= a b))
                   (<= (SQRT a) (SQRT b))))))))
(sd-peel!)
(sd-split!)
(have! '(<= 0 b) (lambda () (sd-ineq '(<= 0 a) '(<= a b))))
(have! '(AND (IN a RR) (<= 0 a)))
(fact 'sqrt-prop 'a)
(sd-split!)
(have! '(AND (IN b RR) (<= 0 b)))
(fact 'sqrt-prop 'b)
(sd-split!)
;; both squares typed -- `ineq' certifies every atom of every premise it takes
(have! '(AND (IN (SQRT a) RR) (IN (SQRT a) RR)))
(fact 'rr-mul-closed '(SQRT a) '(SQRT a))
(have! '(AND (IN (SQRT b) RR) (IN (SQRT b) RR)))
(fact 'rr-mul-closed '(SQRT b) '(SQRT b))
(have! '(AND (IN (SQRT a) RR) (IN (SQRT b) RR)))
(fact 'rr-leq-total '(SQRT a) '(SQRT b))
(use-cases '((<= (SQRT a) (SQRT b)) (<= (SQRT b) (SQRT a)))
  (lambda () (ass))
  (lambda ()
    (have! '(AND (AND (<= 0 (SQRT b)) (<= (SQRT b) (SQRT a)))
                 (AND (<= 0 (SQRT b)) (<= (SQRT b) (SQRT a)))))
    (fact 'rr-prod-le-prod '(SQRT b) '(SQRT a) '(SQRT b) '(SQRT a))
    (have! '(<= b a)
           (lambda () (sd-ineq '(<= (* (SQRT b) (SQRT b)) (* (SQRT a) (SQRT a)))
                               '(= (* (SQRT a) (SQRT a)) a)
                               '(= (* (SQRT b) (SQRT b)) b))))
    (have! '(AND (IN a RR) (IN b RR)))
    (have! '(AND (<= a b) (<= b a)))
    (fact 'rr-leq-antisymmetric 'a 'b)
    (subst '(= a b))
    (fact 'rr-leq-reflexive '(SQRT b))
    (ass)))
(qed 'sqrt-mono)
(topic! 'sqrt-mono 'inequalities)

;;; sqrt(a*b) = sqrt(a)*sqrt(b).  sqrt(a)*sqrt(b) is nonnegative and squares to
;;; a*b, so `sqrt-char' names it.
(sp (make-wff '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a))
                 (FORALL b (IMPLIES (AND (IN b RR) (<= 0 b))
                   (= (SQRT (* a b)) (* (SQRT a) (SQRT b)))))))))
(sd-peel!)
(sd-split!)
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-mul-closed 'a 'b)
(have! '(AND (<= 0 a) (<= 0 b)))
(fact 'rr-leq-mul-nonneg 'a 'b)
(have! '(AND (IN a RR) (<= 0 a)))
(fact 'sqrt-prop 'a)
(sd-split!)
(have! '(AND (IN b RR) (<= 0 b)))
(fact 'sqrt-prop 'b)
(sd-split!)
(have! '(AND (IN (SQRT a) RR) (IN (SQRT b) RR)))
(fact 'rr-mul-closed '(SQRT a) '(SQRT b))
(have! '(AND (<= 0 (SQRT a)) (<= 0 (SQRT b))))
(fact 'rr-leq-mul-nonneg '(SQRT a) '(SQRT b))
;; (sa*sb)^2 = (sa^2)(sb^2) is a ring identity; the two squares then rewrite.
(have! '(= (* (* (SQRT a) (SQRT b)) (* (SQRT a) (SQRT b)))
           (* (* (SQRT a) (SQRT a)) (* (SQRT b) (SQRT b))))
       (lambda () (crs)))
(have! '(= (* (* (SQRT a) (SQRT b)) (* (SQRT a) (SQRT b))) (* a b))
  (lambda ()
    (subst '(= (* (* (SQRT a) (SQRT b)) (* (SQRT a) (SQRT b)))
               (* (* (SQRT a) (SQRT a)) (* (SQRT b) (SQRT b)))))
    (subst '(= (* (SQRT a) (SQRT a)) a))
    (subst '(= (* (SQRT b) (SQRT b)) b))
    (crs)))
(have! '(AND (IN (* a b) RR) (<= 0 (* a b))))
(have! '(AND (IN (* (SQRT a) (SQRT b)) RR) (<= 0 (* (SQRT a) (SQRT b)))))
(fact 'sqrt-char '(* a b) '(* (SQRT a) (SQRT b)))
(ass)
(qed 'sqrt-mul)
(topic! 'sqrt-mul 'algebra)
