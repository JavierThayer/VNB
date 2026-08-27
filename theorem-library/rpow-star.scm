;;; theorem-library/rpow-star.scm -- THE REAL POWER, DEFINED, with the
;;; base-zero conventions carried:
;;;
;;;     RPOW-STAR(x, s)  ==  IF  0 < x   then  R-EXP(s . LOG(x))
;;;                          else IF 0 < s  then  0  else  1
;;;
;;; the user's definition (2026-08-26), in the shape they specified the
;;; following day.  The name follows the tree's standing convention for a
;;; DEFINED companion to an AXIOMATISED operator -- CARD/CARD-STAR,
;;; RECIP/RECIP-STAR -- and `structure-library/real-powers.scm' is deliberately
;;; NOT touched: its RPOW keeps its fourteen `well-known' supports and its one
;;; customer (Hoelder, analysis-inequalities.scm).  Nothing here claims the two
;;; heads agree; see the closing note.
;;;
;;; =====================================================================
;;; 1.  WHY AN `IF' AND NOT A DESCRIPTION, and what the third branch is for.
;;;
;;; The mathematical instinct is that x^s is UNDEFINED at x = 0, LOG(0) being
;;; undefined.  In THIS tree that instinct is wrong, and the reason is a
;;; decision made two files down: **LOG is TOTAL**.  `log-in-rr' reads
;;;
;;;     forall([x_], log(x_) in rr)
;;;
;;; with no guard whatever, because RECIP-STAR is the totalised reciprocal
;;; (`IF(u = 0, 0, recip(u))') and C-INT-OR is the ORIENTED integral, whose
;;; third branch returns 0 when the integrand is antiderivable in NEITHER
;;; direction.  So LOG(0) is a defined real, R-EXP is total, and
;;; `R-EXP(s . LOG(0))' was already a defined POSITIVE real before this file
;;; had any conventions in it.  There was never a hole at x = 0 to leave; there
;;; was only junk.  Making the functoid partial instead would have been the one
;;; description in a stack of totalisations, and would have handed back the
;;; thing that made this file cheap -- no definedness obligation anywhere.
;;;
;;; So the conventions are ADOPTED rather than discovered, and the `IF' is the
;;; house pattern for that: RECIP-STAR (recip-star.scm:157) and C-INT-OR
;;; (c-int-oriented.scm:283), the two functoids LOG is built from, are both
;;; total-by-IF, and C-INT-OR's is nested exactly like this one.
;;;
;;; **THE THIRD BRANCH IS A DON'T-CARE, AND NO THEOREM BELOW MENTIONS IT.**
;;; It fires at x <= 0 with s <= 0, i.e. at 0^0 -- where it delivers the
;;; adopted 1 -- AND at 0^(-1), where 1 is not a convention anybody holds, it
;;; is simply the value an IF is obliged to return.  RPOW is careful in the
;;; same place: `rpow-zero-base' is guarded 0 < b and `rpow-zero-zero' is
;;; b = 0, and neither says anything about a negative exponent at base zero.
;;; `rpow-star-zero-zero' below is therefore stated AT 0^0 ONLY, not as the
;;; else-branch, so 0^(-1) stays unspecified exactly as it was.  The same goes
;;; for a NEGATIVE base: (-2)^s takes a branch value here, and no law names it.
;;;
;;; =====================================================================
;;; 2.  WHAT THE CONVENTIONS COST, and it is exactly what was predicted.
;;;
;;; Before the conventions, SIX of the laws held at every real base, because
;;; they never inverted LOG and LOG is total.  They do not survive.  The
;;; counter-example is one line: at x = 0 with s = 1, t = -1,
;;;
;;;     0^(1 + (-1))  =  0^0  =  1        but      0^1 . 0^(-1)  =  0 . 1  =  0
;;;
;;; so `rpow-star-add' is FALSE at base 0 and now carries `0 < x'.  This is not
;;; a defect of the shape -- it is the arithmetic of the conventions breaking
;;; the algebra at zero, which is why 0^0 is contentious at all.  Every law
;;; below is guarded `0 < x' for that reason, matching RPOW, whose fourteen
;;; supports are guarded the same way.
;;;
;;; =====================================================================
;;; 3.  THE BRANCH EQUATIONS, and the rule this file keeps.
;;;
;;; `rpow-star-value', `rpow-star-zero-base' and `rpow-star-zero-zero' are the
;;; three branch equations.  **Every later proof reasons with THOSE; the IF is
;;; opened exactly three times, here, and never again.**  That is
;;; c-int-oriented.scm's discipline (its section 3 says so in the same words)
;;; and it is what keeps the conventions from leaking a case split into every
;;; driver downstream: `mac' of the guarded `rpow-star-value' rewrites a power
;;; away wherever `0 < x' is in context, and the guard is always right there,
;;; being the law's own hypothesis.
;;;
;;; =====================================================================
;;; 4.  THE BILL.  Nothing here is asserted -- no `support', no
;;; `theory-add-axiom!'.  Every theorem that touches the main branch inherits,
;;; unchanged, the 35-leaf `well-known' residue that every log-* and r-exp-*
;;; theorem already bills (the MVT/EVT block through Cor 4.11).  The two
;;; base-zero conventions touch neither LOG nor R-EXP and are `modulo 0'.
;;;
;;; =====================================================================
;;; WHAT IS PROVED
;;;
;;;   rpow-star-unfold        the raw unfold, so `mac-h' can reach the
;;;                           definition in an ASSUMPTION (a `def-functoid'
;;;                           installs a macete and no theorem)
;;;   rpow-star-value         0 < x  =>  x^s = R-EXP(s . LOG x)   MAIN BRANCH
;;;   rpow-star-zero-base     0 < s  =>  0^s = 0
;;;   rpow-star-zero-zero     0^0 = 1
;;;   rpow-star-in-rr,
;;;   rpow-star-pos           the projections
;;;   log-rpow-star           log(x^s) = s.log(x)
;;;   rpow-star-zero          x^0 = 1
;;;   rpow-star-one           x^1 = x
;;;   rpow-star-add           x^(s+t) = x^s . x^t
;;;   rpow-star-mul-base      (x.y)^s = x^s . y^s
;;;   rpow-star-pow           (x^s)^t = x^(s.t)
;;;   rpow-star-neg           x^(-s) = 1/(x^s)
;;;   rpow-star-mono-exp      1 < x, s < t  =>  x^s < x^t
;;;   rpow-star-mono-base     0 < x < y, 0 < s  =>  x^s < y^s
;;;
;;; NOT PROVED HERE, and each its own piece of work:
;;;   * agreement with the NN-power, x^n = power(x, n) for n in NN.  An
;;;     induction off rpow-star-add and rpow-star-one.  **DO NOT write it
;;;     against the `power' head** -- the 2-arg POWER head carries a SECOND
;;;     live reading, `power-exp' declaring POWER(A,B) == FUN(B,A), and the two
;;;     compose into the false `fun(3,2) = 8'.  See the deletion of power-exp.
;;;   * agreement with SQRT, x^(1/2) = SQRT(x).  Both sides positive, both
;;;     square to x; wants rr-no-zero-divisors as sqrt-defined.scm's
;;;     uniqueness half does.
;;;   * agreement with RPOW itself on 0 < x, b in QQ.  NOT provable: RPOW is
;;;     axiomatic and its axioms do not pin it uniquely (nothing says a^b is
;;;     continuous in b, which is what makes the rational-power map extend
;;;     uniquely).  It would have to be asserted, and it is better to retire
;;;     RPOW than to bridge it -- which the two conventions here now make
;;;     possible, RPOW-STAR satisfying `rpow-zero-base' and `rpow-zero-zero'
;;;     where before it could not.
;;;
;;; Loads after r-exp, log, recip-star, rr-order-basics (rr-lt-scale-pos,
;;; rr-mul-comm, rr-lt-irrefl) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `rp-' prefix) --------------------

(define (rp-check name)
  (if (not (proof-done? *ps*))
      (error "rpow-star: proof did not close" name
             (expression->string (dk-goal)))))

(define (rp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; a `have!' of a formula already in context is an ALPHA SELF-LOOP, not a no-op
(define (rp-need! f) (if (not (member f (dk-asms))) (have! f)))

;;; LOG is total, so log(x) is a real for EVERY x: no guard, ever.
(define (rp-type-log! x) (fact 'log-in-rr x))

;;; s . log(x) in RR, and R-EXP of it in RR.  The second is what a residual
;;; `T = T' needs: `=' is PARTIAL, so reflexivity is not free -- T = T IS the
;;; definedness assertion.
(define (rp-type-slog! s x)
  (rp-type-log! x)
  (rp-need! (list 'AND (list 'IN s 'RR) (list 'IN (list 'LOG x) 'RR)))
  (fact 'rr-mul-closed s (list 'LOG x)))
(define (rp-type-pow! s x)
  (rp-type-slog! s x)
  (fact 'r-exp-in-rr (list '* s (list 'LOG x))))

;;; `ineq' demands an (IN t RR) certificate for every atom of every NAMED
;;; premise, so name the premises rather than sweeping the context.
(define (rp-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rp-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (else (lp (cdr l) (+ i 1))))))

;;; the IF terms, as the engine builds them
(define (rp-if x s)
  (list 'IF (list '< 0 x)
        (list 'R-EXP (list '* s (list 'LOG x)))
        (list 'IF (list '< 0 s) 0 1)))
(define (rp-inner s) (list 'IF (list '< 0 s) 0 1))

;;; `if-true' / `if-false' DO NOT rewrite the goal.  They open two leaves
;;; (pi-if-true!, primitive-inferences.scm:535): one whose goal is the
;;; CONDITION (resp. its negation), and one that keeps the ORIGINAL goal and
;;; gains the branch equation `(= <the IF> <that branch>)' as an ASSUMPTION.
;;; So the pattern is: discharge the condition leaf from context, and on the
;;; other leaf either `ass' -- when the goal IS the handed equation -- or
;;; `subst' the handed equation and carry on.  recip-star.scm's
;;; "the goal after the unfold IS the equation if-false hands over" is the
;;; same observation.
(define (rp-branch! ifterm true? k)
  (let ((cond- (cadr ifterm)))
    (for-each
     (lambda (l)
       (dk-focus! l)
       (let ((g (dk-goal)))
         (if (or (equal? g cond-) (equal? g (list 'NOT cond-)))
             (ass)
             (k))))
     (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))))

;;; =====================================================================
;;; 5.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'RPOW-STAR '(x_ s_)
  '(IF (< 0 x_)
       (R-EXP (* s_ (LOG x_)))
       (IF (< 0 s_) 0 1)))
(notation! 'RPOW-STAR 'kind 'functoid 'arity 2
           'english "$1 to the power $2"
           'noun "$1 to the power $2"
           'tex "{$1}^{$2}")

;;; THE RAW UNFOLD, AS A THEOREM.  `def-functoid' installs a rewrite MACETE and
;;; no theorem, so `mac' reaches the definition in a GOAL and `mac-h' CANNOT
;;; reach it in an ASSUMPTION by the functoid's own name -- it warns `unknown
;;; theorem/macete' and the driver sails on with the hypothesis untouched.
(sp (make-wff (list 'FORALL 'x_ (list 'FORALL 's_
      (list '== '(RPOW-STAR x_ s_) (rp-if 'x_ 's_))))))
(rp-peel!)
(mac 'RPOW-STAR)
(qrfl)
(rp-check 'rpow-star-unfold)
(qed 'rpow-star-unfold)
(topic! 'rpow-star-unfold 'analysis)
(alias! 'rpow-star-unfold "the defining equation of the real power")

;;; =====================================================================
;;; 6.  THE THREE BRANCH EQUATIONS.  The IF is opened here and nowhere else.
;;; =====================================================================

;;; MAIN BRANCH.  Every law below rewrites with this one.
(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(IMPLIES (< 0 x_) (= (RPOW-STAR x_ s_) (R-EXP (* s_ (LOG x_))))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-pow! 's_ 'x_)
  (mac 'RPOW-STAR)
  (rp-branch! (rp-if 'x_ 's_) #t (lambda () (ass)))))
(rp-check 'rpow-star-value)
(qed 'rpow-star-value)
(topic! 'rpow-star-value 'analysis)
(alias! 'rpow-star-value "above zero the real power is exp(s.log x)")

;;; THE FIRST CONVENTION,  0^s = 0  for s > 0.
(sp (make-wff (forall-guarded 's_ '(IN s_ RR)
      '(IMPLIES (< 0 s_) (= (RPOW-STAR 0 s_) 0)))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-zero-in)
  (fact 'rr-lt-irrefl 0)                       ; NOT (0 < 0): the outer branch
  (mac 'RPOW-STAR)
  (rp-branch! (rp-if 0 's_) #f
    (lambda ()
      (subst (list '= (rp-if 0 's_) (rp-inner 's_)))
      (rp-branch! (rp-inner 's_) #t (lambda () (ass)))))))
(rp-check 'rpow-star-zero-base)
(qed 'rpow-star-zero-base)
(topic! 'rpow-star-zero-base 'analysis)
(alias! 'rpow-star-zero-base "0^s = 0 for positive s")

;;; THE SECOND CONVENTION,  0^0 = 1.  Stated AT 0^0, not as the else-branch --
;;; so that 0^(-1), which takes the same branch, stays unspecified.
(sp (make-wff '(= (RPOW-STAR 0 0) 1)))
(quietly (lambda ()
  (fact 'rr-zero-in)
  (fact 'rr-one-in)
  (fact 'rr-lt-irrefl 0)
  (mac 'RPOW-STAR)
  (rp-branch! (rp-if 0 0) #f
    (lambda ()
      (subst (list '= (rp-if 0 0) (rp-inner 0)))
      (rp-branch! (rp-inner 0) #f (lambda () (ass)))))))
(rp-check 'rpow-star-zero-zero)
(qed 'rpow-star-zero-zero)
(topic! 'rpow-star-zero-zero 'analysis)
(alias! 'rpow-star-zero-zero "0^0 = 1, the adopted convention")

;;; =====================================================================
;;; 7.  THE PROJECTIONS.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(IMPLIES (< 0 x_) (IN (RPOW-STAR x_ s_) RR)))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-slog! 's_ 'x_)
  (mac 'rpow-star-value)
  (fact 'r-exp-in-rr '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-in-rr)
(qed 'rpow-star-in-rr)
(topic! 'rpow-star-in-rr 'plumbing)
(alias! 'rpow-star-in-rr "a real power is a real")

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(IMPLIES (< 0 x_) (< 0 (RPOW-STAR x_ s_))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-slog! 's_ 'x_)
  (mac 'rpow-star-value)
  (fact 'r-exp-pos '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-pos)
(qed 'rpow-star-pos)
(topic! 'rpow-star-pos 'analysis)
(alias! 'rpow-star-pos "above zero the real power is positive")

;;; log(x^s) = s.log(x) -- the projection the tower goes through.
(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(IMPLIES (< 0 x_) (= (LOG (RPOW-STAR x_ s_)) (* s_ (LOG x_)))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-slog! 's_ 'x_)
  (mac 'rpow-star-value)
  (fact 'log-r-exp '(* s_ (LOG x_)))
  (ass)))
(rp-check 'log-rpow-star)
(qed 'log-rpow-star)
(topic! 'log-rpow-star 'analysis)
(alias! 'log-rpow-star "log(x^s) = s.log(x)")

;;; =====================================================================
;;; 8.  THE VALUES AT 0 AND 1 IN THE EXPONENT.
;;; =====================================================================

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 0 x_) (= (RPOW-STAR x_ 0) 1)))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-zero-in)
  (rp-type-pow! 0 'x_)
  (mac 'rpow-star-value)
  (have! '(= (* 0 (LOG x_)) 0) (lambda () (crs)))
  (subst '(= (* 0 (LOG x_)) 0))
  (fact 'r-exp-zero)
  (ass)))
(rp-check 'rpow-star-zero)
(qed 'rpow-star-zero)
(topic! 'rpow-star-zero 'analysis)
(alias! 'rpow-star-zero "x^0 = 1")

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 0 x_) (= (RPOW-STAR x_ 1) x_)))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-one-in)
  (rp-type-pow! 1 'x_)
  (mac 'rpow-star-value)
  (have! '(= (* 1 (LOG x_)) (LOG x_)) (lambda () (crs)))
  (subst '(= (* 1 (LOG x_)) (LOG x_)))
  (fact 'r-exp-log 'x_)
  (ass)))
(rp-check 'rpow-star-one)
(qed 'rpow-star-one)
(topic! 'rpow-star-one 'analysis)
(alias! 'rpow-star-one "x^1 = x")

;;; =====================================================================
;;; 9.  THE FUNCTIONAL EQUATION IN THE EXPONENT,  x^(s+t) = x^s . x^t.
;;; FALSE at x = 0 under the conventions (see section 2), hence the guard.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_)
                (list '(IN x_ RR) '(IN s_ RR) '(IN t_ RR))
      '(IMPLIES (< 0 x_)
         (= (RPOW-STAR x_ (+ s_ t_))
            (* (RPOW-STAR x_ s_) (RPOW-STAR x_ t_)))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-log! 'x_)
  (rp-need! '(AND (IN s_ RR) (IN t_ RR)))
  (fact 'rr-add-closed 's_ 't_)
  (rp-type-slog! 's_ 'x_)
  (rp-type-slog! 't_ 'x_)
  (rp-type-slog! '(+ s_ t_) 'x_)
  (mac 'rpow-star-value)
  (have! '(= (* (+ s_ t_) (LOG x_)) (+ (* s_ (LOG x_)) (* t_ (LOG x_))))
    (lambda () (crs)))
  (subst '(= (* (+ s_ t_) (LOG x_)) (+ (* s_ (LOG x_)) (* t_ (LOG x_)))))
  (fact 'r-exp-add '(* s_ (LOG x_)) '(* t_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-add)
(qed 'rpow-star-add)
(topic! 'rpow-star-add 'analysis)
(alias! 'rpow-star-add "the real power turns sums of exponents into products"
        "x^(s+t) = x^s . x^t")

;;; =====================================================================
;;; 10.  THE FUNCTIONAL EQUATION IN THE BASE,  (x.y)^s = x^s . y^s.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ y_ s_)
                (list '(IN x_ RR) '(IN y_ RR) '(IN s_ RR))
      '(IMPLIES (< 0 x_) (IMPLIES (< 0 y_)
         (= (RPOW-STAR (* x_ y_) s_)
            (* (RPOW-STAR x_ s_) (RPOW-STAR y_ s_))))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-need! '(AND (IN x_ RR) (IN y_ RR)))
  (fact 'rr-mul-closed 'x_ 'y_)
  (fact 'rr-mul-pos 'x_ 'y_)                   ; 0 < x_.y_ : the third guard
  (rp-type-slog! 's_ 'x_)
  (rp-type-slog! 's_ 'y_)
  (rp-type-slog! 's_ '(* x_ y_))
  (mac 'rpow-star-value)
  (fact 'log-mul 'x_ 'y_)
  (subst '(= (LOG (* x_ y_)) (+ (LOG x_) (LOG y_))))
  (have! '(= (* s_ (+ (LOG x_) (LOG y_))) (+ (* s_ (LOG x_)) (* s_ (LOG y_))))
    (lambda () (crs)))
  (subst '(= (* s_ (+ (LOG x_) (LOG y_))) (+ (* s_ (LOG x_)) (* s_ (LOG y_)))))
  (fact 'r-exp-add '(* s_ (LOG x_)) '(* s_ (LOG y_)))
  (ass)))
(rp-check 'rpow-star-mul-base)
(qed 'rpow-star-mul-base)
(topic! 'rpow-star-mul-base 'analysis)
(alias! 'rpow-star-mul-base "(x.y)^s = x^s . y^s")

;;; =====================================================================
;;; 11.  THE TOWER,  (x^s)^t = x^(s.t).  The OUTER power needs its own guard,
;;; `0 < x^s', which is rpow-star-pos -- so the positivity projection is not
;;; decoration here, it is what makes the tower expressible at all.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_)
                (list '(IN x_ RR) '(IN s_ RR) '(IN t_ RR))
      '(IMPLIES (< 0 x_)
         (= (RPOW-STAR (RPOW-STAR x_ s_) t_) (RPOW-STAR x_ (* s_ t_)))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-slog! 's_ 'x_)
  (fact 'rpow-star-pos 'x_ 's_)                ; 0 < x^s : the outer guard
  (fact 'rpow-star-in-rr 'x_ 's_)
  (rp-need! '(AND (IN s_ RR) (IN t_ RR)))
  (fact 'rr-mul-closed 's_ 't_)
  (rp-type-slog! '(* s_ t_) 'x_)
  (rp-type-slog! 't_ '(RPOW-STAR x_ s_))
  (fact 'log-rpow-star 'x_ 's_)
  (mac 'rpow-star-value)
  (subst '(= (LOG (RPOW-STAR x_ s_)) (* s_ (LOG x_))))
  (have! '(= (* t_ (* s_ (LOG x_))) (* (* s_ t_) (LOG x_)))
    (lambda () (crs)))
  (subst '(= (* t_ (* s_ (LOG x_))) (* (* s_ t_) (LOG x_))))
  (fact 'r-exp-in-rr '(* (* s_ t_) (LOG x_)))
  (rfl)))
(rp-check 'rpow-star-pow)
(qed 'rpow-star-pow)
(topic! 'rpow-star-pow 'analysis)
(alias! 'rpow-star-pow "(x^s)^t = x^(s.t)")

;;; =====================================================================
;;; 12.  THE NEGATIVE EXPONENT,  x^(-s) = 1/(x^s).
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN x_ RR) '(IN s_ RR))
      '(IMPLIES (< 0 x_)
         (= (RPOW-STAR x_ (- s_)) (RECIP-STAR (RPOW-STAR x_ s_)))))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-neg-closed 's_)
  (rp-type-slog! 's_ 'x_)
  (rp-type-slog! '(- s_) 'x_)
  (mac 'rpow-star-value)
  (have! '(= (* (- s_) (LOG x_)) (- (* s_ (LOG x_)))) (lambda () (crs)))
  (subst '(= (* (- s_) (LOG x_)) (- (* s_ (LOG x_)))))
  (fact 'r-exp-neg '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-neg)
(qed 'rpow-star-neg)
(topic! 'rpow-star-neg 'analysis)
(alias! 'rpow-star-neg "x^(-s) = 1/(x^s)")

;;; =====================================================================
;;; 13.  MONOTONICITY.  In the EXPONENT it is log(x) > 0, i.e. x above 1; in
;;; the BASE it is strict monotonicity of LOG.  Neither step is `ineq':
;;; scaling s < t by log(x) > 0 is a product of two unknowns and
;;; Fourier-Motzkin is LINEAR.  `rr-lt-scale-pos' is the move, and its
;;; antecedent is a CONJUNCTION, which `fact' will not split -- so the `have!'
;;; of the AND comes first.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_)
                (list '(IN x_ RR) '(IN s_ RR) '(IN t_ RR))
      '(IMPLIES (< 1 x_) (IMPLIES (< s_ t_)
         (< (RPOW-STAR x_ s_) (RPOW-STAR x_ t_)))))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-one-in) (fact 'rr-zero-in)
  (fact 'rr-zero-lt-one)
  (rp-need! '(AND (IN 0 RR) (IN 1 RR)))
  (have! '(< 0 x_) (lambda () (ineq (rp-idx '(< 1 x_)) (rp-idx '(< 0 1)))))
  (rp-type-slog! 's_ 'x_)
  (rp-type-slog! 't_ 'x_)
  (mac 'rpow-star-value)
  (fact 'log-pos-above-one 'x_)
  (have! '(< (* s_ (LOG x_)) (* t_ (LOG x_)))
    (lambda ()
      (fact 'rr-mul-comm 's_ '(LOG x_))
      (fact 'rr-mul-comm 't_ '(LOG x_))
      (subst '(= (* s_ (LOG x_)) (* (LOG x_) s_)))
      (subst '(= (* t_ (LOG x_)) (* (LOG x_) t_)))
      (rp-need! '(AND (< 0 (LOG x_)) (< s_ t_)))
      (fact 'rr-lt-scale-pos '(LOG x_) 's_ 't_)
      (ass)))
  (fact 'r-exp-strictly-increasing '(* s_ (LOG x_)) '(* t_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-mono-exp)
(qed 'rpow-star-mono-exp)
(topic! 'rpow-star-mono-exp 'analysis)
(alias! 'rpow-star-mono-exp
        "above 1, the real power is increasing in the exponent")

(sp (make-wff (forall-guarded '(x_ y_ s_)
                (list '(IN x_ RR) '(IN y_ RR) '(IN s_ RR))
      '(IMPLIES (< 0 x_) (IMPLIES (< x_ y_) (IMPLIES (< 0 s_)
         (< (RPOW-STAR x_ s_) (RPOW-STAR y_ s_))))))))
(quietly (lambda ()
  (rp-peel!)
  (fact 'rr-zero-in)
  (have! '(< 0 y_) (lambda () (ineq (rp-idx '(< 0 x_)) (rp-idx '(< x_ y_)))))
  (rp-type-slog! 's_ 'x_)
  (rp-type-slog! 's_ 'y_)
  (mac 'rpow-star-value)
  (fact 'log-strictly-increasing 'x_ 'y_)
  (have! '(< (* s_ (LOG x_)) (* s_ (LOG y_)))
    (lambda ()
      (rp-need! '(AND (< 0 s_) (< (LOG x_) (LOG y_))))
      (fact 'rr-lt-scale-pos 's_ '(LOG x_) '(LOG y_))
      (ass)))
  (fact 'r-exp-strictly-increasing '(* s_ (LOG x_)) '(* s_ (LOG y_)))
  (ass)))
(rp-check 'rpow-star-mono-base)
(qed 'rpow-star-mono-base)
(topic! 'rpow-star-mono-base 'analysis)
(alias! 'rpow-star-mono-base "the real power is increasing in the base")
