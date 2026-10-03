;;; theorem-library/rpow-defined.scm -- THE AXIOMATIC REAL POWER RETIRED:
;;; RPOW is DEFINED as RPOW-STAR, and its laws are THEOREMS under their old
;;; names and with their old statements (the user's decision, 2026-10-03).
;;;
;;;     rpow-def :  forall a_ b_.  RPOW(a_, b_) == RPOW-STAR(a_, b_)
;;;
;;; RPOW is an ALREADY-REGISTERED operator (structure-library/real-powers.scm
;;; registers it at load position 240, and the Hoelder support of
;;; analysis-inequalities.scm states itself with it), so it cannot be a
;;; `def-constant' or a `def-functoid'.  It is defined the way EPLUS and ETIMES
;;; are (extended-reals-pos.scm, extended-arith.scm): a `definitional'-wrapped
;;; `add-axiom!' of a quasi-equation, preceded by `declare-named-only!' so that
;;; the equation never fires as a live rewrite and is cited by name only.
;;;
;;; THE LAWS.  Each statement below is copied LITERALLY from the `support' form
;;; that stood in real-powers.scm: the exponent ranges over QQ, which
;;; `qq-subset-rr' carries into RR, where RPOW-STAR's laws live.  A proof
;;; rewrites every RPOW of its goal into RPOW-STAR by instantiating `rpow-def'
;;; and substituting (`rpd-unfold!'), then cites the RPOW-STAR law.  The four
;;; that are not one citation away:
;;;   rpow-nat           RPOW-STAR's `rpow-star-nat' (limsup-tests.scm).
;;;   rpow-mono-base,    non-strict monotonicity, through the main branch
;;;   rpow-mono-exp-ge1, x^s = R-EXP(s . log x) (`rpow-star-value'), `r-exp-mono'
;;;   rpow-mono-exp-le1  and a non-strict comparison of the exponents s . log x;
;;;                      the sign of log x (resp. the order of log a, log c) is
;;;                      split on the boundary case x = 1 (resp. a = c).
;;;   sqrt-rpow          a^(1/2) is a nonnegative real whose square is a^1 = a,
;;;                      so it IS sqrt(a) (`sqrt-char').
;;;   amgm-2-sqrt        does not mention RPOW: sqrt(ab) <= sqrt(m.m) = m for
;;;                      m = (a+b)/2, since ab <= m.m is a sum of squares.
;;;
;;; THE UNFOLD.  `rpow-def' does NOT fire as a macete (`mac 'rpow-def' reports
;;; "macete not applicable"; probe of 2026-10-03): the rewrite is
;;; `(subst (fact 'rpow-def x y))' at each instance, which `rpd-unfold!' does.
;;;
;;; THE BILL.  No `support'.  The one `add-axiom!' is the definition, stamped
;;; `definitional'.  All fifteen laws bill `modulo 0' (probe on the band of
;;; 2026-10-02): the RPOW-STAR laws they cite are themselves `modulo 0'.
;;;
;;; LOAD WINDOW [limsup-tests, pss-topics): `rpow-star-nat' is proven in
;;; limsup-tests.scm; pss-topics.scm files the topics of these names.

;;; ---- file-local driver helpers (the `rpd-' prefix) --------------------

(define (rpd-check name)
  (if (not (proof-done? *ps*))
      (error "rpow-defined: proof did not close" name
             (expression->string (dk-goal)))))

;;; the innermost (RPOW x y) of a term, or #f
(define (rpd-find-rpow t)
  (cond ((not (pair? t)) #f)
        ((and (eq? (car t) 'RPOW) (= (length t) 3))
         (or (rpd-find-rpow (cadr t)) (rpd-find-rpow (caddr t)) t))
        (#t (let loop ((l t))
              (cond ((null? l) #f)
                    ((not (pair? l)) #f)
                    ((rpd-find-rpow (car l)))
                    (#t (loop (cdr l))))))))

;;; rewrite every RPOW of the goal into RPOW-STAR, innermost first:
;;; instantiate rpow-def at the instance and substitute it.
(define (rpd-unfold!)
  (let loop ((n 0))
    (let ((r (rpd-find-rpow (dk-goal))))
      (if r
          (begin
            (if (> n 8) (error "rpd-unfold!: no progress" (expression->string (dk-goal))))
            (subst (dk-cite! 'rpow-def (cadr r) (caddr r)))
            (loop (+ n 1)))))))

;;; peel, split the conjunctive guards, carry each QQ variable into RR
(define (rpd-prep!)
  (dk-peel!)
  (dk-split-all!)
  (for-each (lambda (f)
              (if (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'QQ)
                       (not (dk-asm? (list 'IN (cadr f) 'RR))))
                  (fact 'qq-subset-rr (cadr f))))
            (dk-asms)))

(define (rpd-need! f) (if (not (dk-asm? f)) (have! f)))

;;; s . log(x) in RR (LOG is total)
(define (rpd-type-slog! s x)
  (if (not (dk-asm? (list 'IN (list 'LOG x) 'RR))) (fact 'log-in-rr x))
  (rpd-need! (list 'AND (list 'IN s 'RR) (list 'IN (list 'LOG x) 'RR)))
  (if (not (dk-asm? (list 'IN (list '* s (list 'LOG x)) 'RR)))
      (fact 'rr-mul-closed s (list 'LOG x))))

;;; (<= (LOG a) (LOG c)) from 0 < a, a <= c: split on a = c
(define (rpd-log-le! a c)
  (fact 'log-in-rr a)
  (fact 'log-in-rr c)
  (have! (list '<= (list 'LOG a) (list 'LOG c))
    (lambda ()
      (use-em (list '= a c)
        (lambda ()
          (subst (list '= a c))
          (fact 'rr-leq-reflexive (list 'LOG c))
          (ass))
        (lambda ()
          (have! (list 'AND (list '<= a c) (list 'NOT (list '= a c))))
          (fact 'rr-le-ne-lt a c)
          (fact 'log-strictly-increasing a c)
          (dk-ineq! (list '< (list 'LOG a) (list 'LOG c))))))))

;;; (<= 0 (LOG a)) from 1 <= a: split on 1 = a
(define (rpd-log-nonneg! a)
  (fact 'log-in-rr a)
  (fact 'rr-one-in)
  (have! (list '<= 0 (list 'LOG a))
    (lambda ()
      (use-em (list '= 1 a)
        (lambda ()
          (subst (list '= a 1))
          (fact 'log-one)
          (subst '(= (LOG 1) 0))
          (dk-ineq!))
        (lambda ()
          (have! (list 'AND (list '<= 1 a) (list 'NOT (list '= 1 a))))
          (fact 'rr-le-ne-lt 1 a)
          (fact 'log-pos-above-one a)
          (dk-ineq! (list '< 0 (list 'LOG a))))))))

;;; (<= (LOG a) 0) from 0 < a, a <= 1: split on a = 1
(define (rpd-log-nonpos! a)
  (fact 'log-in-rr a)
  (fact 'rr-one-in)
  (have! (list '<= (list 'LOG a) 0)
    (lambda ()
      (use-em (list '= a 1)
        (lambda ()
          (subst (list '= a 1))
          (fact 'log-one)
          (subst '(= (LOG 1) 0))
          (dk-ineq!))
        (lambda ()
          (have! (list 'AND (list '<= a 1) (list 'NOT (list '= a 1))))
          (fact 'rr-le-ne-lt a 1)
          (fact 'log-neg-below-one a)
          (dk-ineq! (list '< (list 'LOG a) 0)))))))

;;; =====================================================================
;;; 1.  THE DEFINITION.
;;; =====================================================================

(declare-named-only! 'rpow-def
  "left-hand side is the registered operator RPOW: cited by name, never a live rewrite")
(fluid-let ((*current-provenance* 'definitional))
  (add-axiom! *library* 'rpow-def
    '(FORALL a_ (FORALL b_ (== (RPOW a_ b_) (RPOW-STAR a_ b_))))))

;;; =====================================================================
;;; 2.  THE PROJECTIONS AND THE VALUES AT 0 AND 1.
;;; =====================================================================

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ)
       (AND (IN (RPOW a b) RR) (< 0 (RPOW a b)))))))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-in-rr 'a 'b)
(fact 'rpow-star-pos 'a 'b)
(dk-conj-close! (lambda () (ass)))
(rpd-check 'rpow-pos)
(qed 'rpow-pos)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (RPOW a 0) 1)))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-zero 'a)
(ass)
(rpd-check 'rpow-zero)
(qed 'rpow-zero)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (RPOW a 1) a)))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-one 'a)
(ass)
(rpd-check 'rpow-one)
(qed 'rpow-one)

;;; =====================================================================
;;; 3.  THE ALGEBRAIC LAWS.
;;; =====================================================================

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (IN d QQ)
       (= (RPOW a (+ b d)) (* (RPOW a b) (RPOW a d)))))))))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-add 'a 'b 'd)
(ass)
(rpd-check 'rpow-add)
(qed 'rpow-add)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL c (IMPLIES (AND (IN c RR) (< 0 c))
       (FORALL b (IMPLIES (IN b QQ)
         (= (RPOW (* a c) b) (* (RPOW a b) (RPOW c b)))))))))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-mul-base 'a 'c 'b)
(ass)
(rpd-check 'rpow-mul-base)
(qed 'rpow-mul-base)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (IN d QQ)
       (= (RPOW (RPOW a b) d) (RPOW a (* b d)))))))))))
(rpd-prep!)
(fact 'rpow-star-in-rr 'a 'b)
(rpd-unfold!)
(fact 'rpow-star-pow 'a 'b 'd)
(ass)
(rpd-check 'rpow-pow)
(qed 'rpow-pow)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (IN b QQ)
       (= (RPOW a (- 0 b)) (recip (RPOW a b)))))))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-in-rr 'a 'b)
(fact 'rpow-star-pos 'a 'b)
(fact 'rr-pos-ne-zero '(RPOW-STAR a b))
(fact 'recip-star-value '(RPOW-STAR a b))
(fact 'rr-zero-in)
(have! '(= (- 0 b) (- b)) (lambda () (mac 'binary-minus-def) (crs)))
(subst '(= (- 0 b) (- b)))
(subst '(= (recip (RPOW-STAR a b)) (RECIP-STAR (RPOW-STAR a b))))
(fact 'rpow-star-neg 'a 'b)
(ass)
(rpd-check 'rpow-neg)
(qed 'rpow-neg)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL n (IMPLIES (IN n NN) (= (RPOW a n) (power a n))))))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-nat 'n 'a)
(ass)
(rpd-check 'rpow-nat)
(qed 'rpow-nat)

;;; =====================================================================
;;; 4.  THE BASE-ZERO CONVENTIONS.
;;; =====================================================================

(sp (make-wff
  '(FORALL b (IMPLIES (AND (IN b QQ) (< 0 b)) (= (RPOW 0 b) 0)))))
(rpd-prep!)
(rpd-unfold!)
(fact 'rpow-star-zero-base 'b)
(ass)
(rpd-check 'rpow-zero-base)
(qed 'rpow-zero-base)

(sp (make-wff '(= (RPOW 0 0) 1)))
(rpd-unfold!)
(fact 'rpow-star-zero-zero)
(ass)
(rpd-check 'rpow-zero-zero)
(qed 'rpow-zero-zero)

;;; =====================================================================
;;; 5.  MONOTONICITY, non-strict, through the main branch.
;;; =====================================================================

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL c (IMPLIES (AND (IN c RR) (<= a c))
       (FORALL b (IMPLIES (AND (IN b QQ) (<= 0 b))
         (<= (RPOW a b) (RPOW c b))))))))))
(rpd-prep!)
(have! '(< 0 c) (lambda () (dk-ineq! '(< 0 a) '(<= a c))))
(rpd-unfold!)
(rpd-type-slog! 'b 'a)
(rpd-type-slog! 'b 'c)
(mac 'rpow-star-value)
(rpd-log-le! 'a 'c)
(have! '(AND (<= 0 b) (<= (LOG a) (LOG c))))
(fact 'rr-le-scale-nonneg 'b '(LOG a) '(LOG c))
(fact 'r-exp-mono '(* b (LOG a)) '(* b (LOG c)))
(ass)
(rpd-check 'rpow-mono-base)
(qed 'rpow-mono-base)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (<= 1 a))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (AND (IN d QQ) (<= b d))
       (<= (RPOW a b) (RPOW a d))))))))))
(rpd-prep!)
(have! '(< 0 a) (lambda () (dk-ineq! '(<= 1 a))))
(rpd-unfold!)
(rpd-type-slog! 'b 'a)
(rpd-type-slog! 'd 'a)
(mac 'rpow-star-value)
(rpd-log-nonneg! 'a)
(fact 'rr-le-scale-nonneg-right 'b 'd '(LOG a))
(fact 'r-exp-mono '(* b (LOG a)) '(* d (LOG a)))
(ass)
(rpd-check 'rpow-mono-exp-ge1)
(qed 'rpow-mono-exp-ge1)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (AND (< 0 a) (<= a 1)))
     (FORALL b (IMPLIES (IN b QQ) (FORALL d (IMPLIES (AND (IN d QQ) (<= b d))
       (<= (RPOW a d) (RPOW a b))))))))))
(rpd-prep!)
(rpd-unfold!)
(rpd-type-slog! 'b 'a)
(rpd-type-slog! 'd 'a)
(mac 'rpow-star-value)
(rpd-log-nonpos! 'a)
(fact 'rr-neg-closed '(LOG a))
(have! '(<= 0 (- (LOG a))) (lambda () (dk-ineq! '(<= (LOG a) 0))))
(fact 'rr-le-scale-nonneg-right 'b 'd '(- (LOG a)))
(have! '(= (* b (- (LOG a))) (- (* b (LOG a)))) (lambda () (crs)))
(have! '(= (* d (- (LOG a))) (- (* d (LOG a)))) (lambda () (crs)))
(have! '(<= (- (* b (LOG a))) (- (* d (LOG a))))
  (lambda ()
    (subst '(= (- (* b (LOG a))) (* b (- (LOG a)))))
    (subst '(= (- (* d (LOG a))) (* d (- (LOG a)))))
    (ass)))
(have! '(<= (* d (LOG a)) (* b (LOG a)))
  (lambda () (dk-ineq! '(<= (- (* b (LOG a))) (- (* d (LOG a)))))))
(fact 'r-exp-mono '(* d (LOG a)) '(* b (LOG a)))
(ass)
(rpd-check 'rpow-mono-exp-le1)
(qed 'rpow-mono-exp-le1)

;;; =====================================================================
;;; 6.  THE SQUARE ROOT IS THE 1/2 POWER, AND AM-GM IN ROOT FORM.
;;; =====================================================================

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (= (SQRT a) (RPOW a (/ 1 2)))))))
(rpd-prep!)
(have! '(IN 2 RR))
(have! '(NOT (= 2 0)) (lambda () (arith)))
(have! '(AND (IN 2 RR) (NOT (= 2 0))))
(fact 'rr-recip-closed 2)
(fact 'rr-one-in)
(have! '(AND (IN 1 RR) (IN (recip 2) RR)))
(fact 'rr-mul-closed 1 '(recip 2))
(have! '(IN (/ 1 2) RR) (lambda () (mac 'binary-divide-def) (ass)))
(rpd-unfold!)
(fact 'rpow-star-in-rr 'a '(/ 1 2))
(fact 'rpow-star-pos 'a '(/ 1 2))
(define rpd-h '(RPOW-STAR a (/ 1 2)))
(have! (list '<= 0 rpd-h) (lambda () (dk-ineq! (list '< 0 rpd-h))))
(define rpd-add (dk-cite! 'rpow-star-add 'a '(/ 1 2) '(/ 1 2)))
(have! '(= (+ (/ 1 2) (/ 1 2)) 1) (lambda () (mac 'binary-divide-def) (arith)))
(fact 'rpow-star-one 'a)
(have! (list '= (list '* rpd-h rpd-h) 'a)
  (lambda ()
    (subst (list '= (list '* rpd-h rpd-h) (cadr rpd-add)))
    (subst '(= (+ (/ 1 2) (/ 1 2)) 1))
    (ass)))
(have! '(<= 0 a) (lambda () (dk-ineq! '(< 0 a))))
(have! '(AND (IN a RR) (<= 0 a)))
(have! (list 'AND (list 'IN rpd-h 'RR) (list '<= 0 rpd-h)))
(fact 'sqrt-char 'a rpd-h)
(ass)
(rpd-check 'sqrt-rpow)
(qed 'sqrt-rpow)

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (<= 0 a)) (FORALL b (IMPLIES (AND (IN b RR) (<= 0 b))
     (<= (SQRT (* a b)) (/ (+ a b) 2))))))))
(rpd-prep!)
(mac 'binary-divide-def)
(define rpd-m '(* (+ a b) (recip 2)))
(define rpd-mm (list '* rpd-m rpd-m))
(define rpd-s '(SQRT (* a b)))
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-mul-closed 'a 'b)
(have! '(AND (<= 0 a) (<= 0 b)))
(fact 'rr-leq-mul-nonneg 'a 'b)
(have! '(AND (IN (* a b) RR) (<= 0 (* a b))))
(dk-split! (dk-cite! 'sqrt-nonneg '(* a b)))
(have! '(IN 2 RR))
(have! '(NOT (= 2 0)) (lambda () (arith)))
(have! '(AND (IN 2 RR) (NOT (= 2 0))))
(fact 'rr-recip-closed 2)
(fact 'rr-add-closed 'a 'b)
(have! '(AND (IN (+ a b) RR) (IN (recip 2) RR)))
(fact 'rr-mul-closed '(+ a b) '(recip 2))
(have! (list 'AND (list 'IN rpd-m 'RR) (list 'IN rpd-m 'RR)))
(fact 'rr-mul-closed rpd-m rpd-m)
(have! (list '<= 0 rpd-m) (lambda () (dk-ineq! '(<= 0 a) '(<= 0 b))))
(have! (list '<= '(* a b) rpd-mm) (lambda () (sos "a - b")))
(fact 'rr-sq-nonneg rpd-m)
(have! (list 'AND (list 'IN rpd-mm 'RR) (list '<= '(* a b) rpd-mm)))
(fact 'sqrt-mono '(* a b) rpd-mm)
(have! (list 'AND (list 'IN rpd-mm 'RR) (list '<= 0 rpd-mm)))
(have! (list 'AND (list 'IN rpd-m 'RR) (list '<= 0 rpd-m)))
(define rpd-ch (dk-cite! 'sqrt-char rpd-mm rpd-m))
(if (and (pair? rpd-ch) (eq? (car rpd-ch) 'IMPLIES))
    (detach-with! rpd-ch (lambda () (rfl))))
(dk-split! (dk-cite! 'sqrt-nonneg rpd-mm))
(dk-ineq! (list '<= rpd-s (list 'SQRT rpd-mm)) (list '= (list 'SQRT rpd-mm) rpd-m))
(rpd-check 'amgm-2-sqrt)
(qed 'amgm-2-sqrt)

;;; =====================================================================
;;; 6.  THE TWO INEQUALITIES, under their old names and QQ statements, from
;;;     the real-exponent RPOW-STAR forms of theorem-library/rpow-star-
;;;     convexity.scm (young-inequality-star, bernoulli-rpow-star).  The
;;;     star theorems take conjunctive guards; rpd-prep! has split them, so
;;;     each conjunction is landed again for `fact' to detach.
;;; =====================================================================

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a))
     (FORALL b (IMPLIES (AND (IN b RR) (< 0 b))
       (FORALL p (IMPLIES (AND (IN p QQ) (< 1 p))
         (FORALL q (IMPLIES (AND (IN q QQ) (< 1 q))
           (IMPLIES (= (+ (/ 1 p) (/ 1 q)) 1)
             (<= (* a b) (+ (/ (RPOW a p) p) (/ (RPOW b q) q))))))))))))))
(rpd-prep!)
(dk-have! '(AND (IN a RR) (< 0 a)))
(dk-have! '(AND (IN b RR) (< 0 b)))
(dk-have! '(AND (IN p RR) (< 1 p)))
(dk-have! '(AND (IN q RR) (< 1 q)))
(fact 'young-inequality-star 'a 'b 'p 'q)
(rpd-unfold!)
(ass)
(rpd-check 'young-inequality)
(qed 'young-inequality)

(sp (make-wff
  '(FORALL x (IMPLIES (AND (IN x RR) (< 0 (+ 1 x)))
     (FORALL b (IMPLIES (AND (IN b QQ) (<= 1 b))
       (<= (+ 1 (* b x)) (RPOW (+ 1 x) b))))))))
(rpd-prep!)
(dk-have! '(AND (IN x RR) (< 0 (+ 1 x))))
(dk-have! '(AND (IN b RR) (<= 1 b)))
(fact 'bernoulli-rpow-star 'x 'b)
(rpd-unfold!)
(ass)
(rpd-check 'bernoulli-rpow)
(qed 'bernoulli-rpow)

(display ";; rpow-defined: qed failures: ")
(display *vnb-qed-failures*)
(newline)
