;;; theorem-library/rpow-star.scm -- THE REAL POWER, DEFINED:
;;;
;;;     RPOW-STAR(x, s)  ==  R-EXP(s . LOG(x))
;;;
;;; the user's definition (2026-08-26).  The name follows the tree's standing
;;; convention for a DEFINED companion to an AXIOMATISED operator -- CARD
;;; against CARD-STAR, RECIP against RECIP-STAR -- and `structure-library/
;;; real-powers.scm' is deliberately NOT touched: its RPOW keeps its fourteen
;;; `well-known' supports and its one customer (Hoelder, in
;;; analysis-inequalities.scm).  The two heads coexist; nothing here claims
;;; they agree.
;;;
;;; =====================================================================
;;; 1.  WHAT THIS BUYS OVER RPOW, and it is two things.
;;;
;;; THE EXPONENT IS AN ARBITRARY REAL.  Every one of RPOW's supports carries
;;; `IN b QQ' -- it is a^b for RATIONAL b only, and real-powers.scm's header
;;; names the missing construction ("a^b via the intermediate value theorem,
;;; the continuous extension of the rational-power map") as the thing that
;;; would discharge them.  R-EXP(s . LOG x) is indifferent to what s is.  No
;;; continuous extension, no density argument, no rational approximants.
;;;
;;; THE TERM IS TOTAL, so there is NO definedness obligation anywhere in this
;;; file.  LOG is in FUN(RR,RR) on the nose -- that is what
;;; `recip-star-lam-in-fun' and `c-int-or-in-rr' being UNCONDITIONAL was for
;;; (log.scm) -- and R-EXP is total because LOG is onto (r-exp.scm section 1).
;;; So `RPOW-STAR(x, s)' is a well-formed term for EVERY x and s, real or not,
;;; and the description-vs-definedness dance SQRT needed (the `x_ in RR'
;;; conjunct inside its IOTA, without which uniqueness is unprovable) does not
;;; arise: this is a plain equation, not a description.
;;;
;;; The `0 < x' guard is therefore about the LAWS, not about the definition.
;;; Which of the laws actually need it is worth reading off the list below: it
;;; is fewer than one expects.  `rpow-star-in-rr', `rpow-star-pos',
;;; `rpow-star-zero', `rpow-star-add', `log-rpow-star' and `rpow-star-neg' hold
;;; for EVERY real x, positivity and all, because they never invert LOG.  Only
;;; the laws that must recover x from LOG(x) -- `rpow-star-one' (x^1 = x) and
;;; `rpow-star-mul-base' ((xy)^s = x^s y^s, through log-mul) -- pay for it.
;;;
;;; =====================================================================
;;; 2.  THE BASE-0 CONVENTIONS ARE OUT OF REACH, and that is structural.
;;;
;;; real-powers.scm posits 0^b = 0 for b > 0 (`rpow-zero-base') and 0^0 = 1
;;; (`rpow-zero-zero').  NEITHER is available here, and no cleverness recovers
;;; them: `rpow-star-pos' below says 0 < RPOW-STAR(x, s) for every real s and
;;; EVERY x whatever -- R-EXP's values are positive, full stop -- so
;;; RPOW-STAR(0, b) is a positive real and is not 0.  It is whatever
;;; R-EXP(b . LOG(0)) is, and LOG(0) is C-INT-OR's fall-through value.
;;;
;;; This is not a defect of the definition; it is the definition declining to
;;; adopt a convention.  A totalised variant -- IF(0 < x, R-EXP(s . LOG x),
;;; IF(0 < s, 0, 1)) -- would carry both conventions and cost every law an
;;; extra branch.  NOT DONE, and deliberately: it is a decision about what
;;; 0^0 should be, not a theorem, and the tree's rule is that a stamp records
;;; its claim.  Hoelder-with-zero-entries is what wants it (real-powers.scm's
;;; comment on rpow-zero-base says so), and Hoelder is still a support.
;;;
;;; =====================================================================
;;; 3.  THE BILL.  Nothing here is asserted -- no `support', no
;;; `theory-add-axiom!'.  Every theorem below inherits, unchanged, the
;;; 35-leaf `well-known' residue that every log-* and r-exp-* theorem already
;;; bills (the MVT/EVT block through Cor 4.11).  So this file adds no debt of
;;; its own, and it does not CLEAR any either: `rpow' appears nowhere in
;;; PROOF-DEBT.md, nothing proven leaning on it.  What changes is structure --
;;; fourteen independent assertions about a new operator become consequences
;;; of one equation -- not the tier.
;;;
;;; =====================================================================
;;; WHAT IS PROVED
;;;
;;;   rpow-star-unfold        the unfold equation, so `mac-h' can reach the
;;;                           definition in an ASSUMPTION (a `def-functoid'
;;;                           installs a macete and no theorem; see the note
;;;                           at the head of section 4)
;;;   rpow-star-in-rr,
;;;   rpow-star-pos           the projections -- both UNGUARDED in x
;;;   log-rpow-star           log(x^s) = s.log(x)      -- the key projection
;;;   rpow-star-zero          x^0 = 1                  -- unguarded in x
;;;   rpow-star-one           x^1 = x                  -- needs 0 < x
;;;   rpow-star-add           x^(s+t) = x^s . x^t      -- unguarded in x
;;;   rpow-star-mul-base      (x.y)^s = x^s . y^s      -- needs 0 < x, 0 < y
;;;   rpow-star-pow           (x^s)^t = x^(s.t)        -- unguarded in x
;;;   rpow-star-neg           x^(-s) = 1/(x^s)         -- unguarded in x
;;;   rpow-star-mono-exp      1 < x, s < t  =>  x^s < x^t
;;;   rpow-star-mono-base     0 < x < y, 0 < s  =>  x^s < y^s
;;;
;;; NOT PROVED HERE, and each is its own piece of work:
;;;   * agreement with the NN-power, x^n = power(x, n) for n in NN.  An
;;;     induction on n off rpow-star-add and rpow-star-one; RPOW has it as the
;;;     axiom `rpow-nat'.  Watch the overloaded `power' head -- power-exp reads
;;;     (power 2 n) as the function space FUN(n,2), which PSS.md:60 already
;;;     flags.
;;;   * agreement with SQRT, x^(1/2) = SQRT(x).  Both sides are positive and
;;;     both square to x, so it is one application of uniqueness; it wants
;;;     rr-no-zero-divisors the way sqrt-defined.scm's uniqueness half does.
;;;   * agreement with RPOW itself on 0 < x, b in QQ.  This is NOT a theorem
;;;     the tree can prove: RPOW is axiomatic, and its axioms do not pin it
;;;     uniquely (nothing says a^b is CONTINUOUS in b, which is what makes the
;;;     rational-power map extend uniquely).  It would have to be asserted, and
;;;     it is better to retire RPOW than to bridge it.
;;;
;;; Loads after r-exp (r-exp-in-rr, r-exp-pos, r-exp-zero, r-exp-log,
;;; log-r-exp, r-exp-add, r-exp-neg, r-exp-strictly-increasing), log (log-in-rr,
;;; log-mul, log-pos-above-one, log-strictly-increasing), rr-order-basics and
;;; driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `rp-' prefix) --------------------

(define (rp-check name)
  (if (not (proof-done? *ps*))
      (error "rpow-star: proof did not close" name
             (expression->string (dk-goal)))))

;;; `di' is greedy but not uniformly so -- peel until the head stops being a
;;; quantifier or an implication, and guard on progress.
(define (rp-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 16))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; a `have!' of a formula already in context is an ALPHA SELF-LOOP, not a
;;; no-op -- see the cut/alpha entry in CLAUDE.md
(define (rp-need! f) (if (not (member f (dk-asms))) (have! f)))

;;; LOG is total, so log(x) is a real for EVERY x: no guard, ever.  This lands
;;; the typings the ring simplifier needs before it is asked anything.
(define (rp-type-log! x) (fact 'log-in-rr x))

;;; s . log(x) in RR
(define (rp-type-slog! s x)
  (rp-type-log! x)
  (rp-need! (list 'AND (list 'IN s 'RR) (list 'IN (list 'LOG x) 'RR)))
  (fact 'rr-mul-closed s (list 'LOG x)))

;;; =====================================================================
;;; 4.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'RPOW-STAR '(x_ s_)
  '(R-EXP (* s_ (LOG x_))))
(notation! 'RPOW-STAR 'kind 'functoid 'arity 2
           'english "$1 to the power $2"
           'noun "$1 to the power $2"
           'tex "{$1}^{$2}")

;;; THE UNFOLD EQUATION, AS A THEOREM.  `def-functoid' installs a rewrite
;;; MACETE and no theorem, so `mac' reaches the definition in a GOAL and
;;; `mac-h' CANNOT reach it in an ASSUMPTION by the functoid's own name -- it
;;; warns `unknown theorem/macete' and the driver sails on with the hypothesis
;;; untouched.  The equation is provable in one line, and the resulting
;;; THEOREM is what `mac-h' rebuilds its rule from.
(sp (make-wff '(FORALL x_ (FORALL s_
      (== (RPOW-STAR x_ s_) (R-EXP (* s_ (LOG x_))))))))
(rp-peel!)
(mac 'RPOW-STAR)
(qrfl)
(rp-check 'rpow-star-unfold)
(qed 'rpow-star-unfold)
(topic! 'rpow-star-unfold 'analysis)
(alias! 'rpow-star-unfold "the defining equation of the real power")

;;; =====================================================================
;;; 5.  THE PROJECTIONS.  Both are UNGUARDED in the base: they never invert
;;; LOG, and LOG is total.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(IN (RPOW-STAR x_ s_) RR))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-slog! 's_ 'x_)
  (fact 'r-exp-in-rr '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-in-rr)
(qed 'rpow-star-in-rr)
(topic! 'rpow-star-in-rr 'plumbing)
(alias! 'rpow-star-in-rr "a real power is a real")

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(< 0 (RPOW-STAR x_ s_)))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-slog! 's_ 'x_)
  (fact 'r-exp-pos '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-pos)
(qed 'rpow-star-pos)
(topic! 'rpow-star-pos 'analysis)
(alias! 'rpow-star-pos "a real power is positive"
        "this is what puts the base-0 conventions out of reach")

;;; log(x^s) = s.log(x) -- the projection every later law goes through.
(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(= (LOG (RPOW-STAR x_ s_)) (* s_ (LOG x_))))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-slog! 's_ 'x_)
  (fact 'log-r-exp '(* s_ (LOG x_)))
  (ass)))
(rp-check 'log-rpow-star)
(qed 'log-rpow-star)
(topic! 'log-rpow-star 'analysis)
(alias! 'log-rpow-star "log(x^s) = s.log(x)")

;;; =====================================================================
;;; 6.  THE VALUES AT 0 AND 1.
;;; =====================================================================

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR) '(= (RPOW-STAR x_ 0) 1))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-log! 'x_)
  (have! '(= (* 0 (LOG x_)) 0) (lambda () (crs)))
  (subst '(= (* 0 (LOG x_)) 0))
  (fact 'r-exp-zero)
  (ass)))
(rp-check 'rpow-star-zero)
(qed 'rpow-star-zero)
(topic! 'rpow-star-zero 'analysis)
(alias! 'rpow-star-zero "x^0 = 1")

;;; x^1 = x -- and HERE the positivity is needed: this is the first law that
;;; must recover x from LOG(x), which is `r-exp-log' and is false off the
;;; positives.
(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 0 x_) (= (RPOW-STAR x_ 1) x_)))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-log! 'x_)
  (have! '(= (* 1 (LOG x_)) (LOG x_)) (lambda () (crs)))
  (subst '(= (* 1 (LOG x_)) (LOG x_)))
  (fact 'r-exp-log 'x_)
  (ass)))
(rp-check 'rpow-star-one)
(qed 'rpow-star-one)
(topic! 'rpow-star-one 'analysis)
(alias! 'rpow-star-one "x^1 = x, for POSITIVE x")

;;; =====================================================================
;;; 7.  THE FUNCTIONAL EQUATION IN THE EXPONENT,  x^(s+t) = x^s . x^t.
;;; Unguarded in x: it is r-exp-add composed with distributivity, and LOG is
;;; never inverted.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_) (list '(IN s_ RR) '(IN t_ RR))
      '(= (RPOW-STAR x_ (+ s_ t_))
          (* (RPOW-STAR x_ s_) (RPOW-STAR x_ t_))))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-log! 'x_)
  (rp-need! '(AND (IN s_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG x_))
  (rp-need! '(AND (IN t_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 't_ '(LOG x_))
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
;;; 8.  THE FUNCTIONAL EQUATION IN THE BASE,  (x.y)^s = x^s . y^s.
;;; This one DOES need both bases positive -- it goes through `log-mul'.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ y_ s_)
                (list '(IN x_ RR) '(IN y_ RR) '(IN s_ RR))
      '(IMPLIES (< 0 x_) (IMPLIES (< 0 y_)
         (= (RPOW-STAR (* x_ y_) s_)
            (* (RPOW-STAR x_ s_) (RPOW-STAR y_ s_))))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-log! 'x_) (rp-type-log! 'y_)
  (mac 'RPOW-STAR)
  (fact 'log-mul 'x_ 'y_)
  (subst '(= (LOG (* x_ y_)) (+ (LOG x_) (LOG y_))))
  (rp-need! '(AND (IN s_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG x_))
  (rp-need! '(AND (IN s_ RR) (IN (LOG y_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG y_))
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
;;; 9.  THE TOWER,  (x^s)^t = x^(s.t).  `log-rpow-star' is the whole content:
;;; the inner power's logarithm is s.log(x) on the nose, so the outer one is
;;; t.(s.log x), and associativity finishes.  Unguarded in x.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_) (list '(IN s_ RR) '(IN t_ RR))
      '(= (RPOW-STAR (RPOW-STAR x_ s_) t_) (RPOW-STAR x_ (* s_ t_))))))
(quietly (lambda ()
  (rp-peel!)
  (rp-type-log! 'x_)
  (fact 'log-rpow-star 'x_ 's_)
  (mac 'RPOW-STAR)
  (subst '(= (LOG (RPOW-STAR x_ s_)) (* s_ (LOG x_))))
  (rp-need! '(AND (IN s_ RR) (IN t_ RR)))
  (fact 'rr-mul-closed 's_ 't_)
  (have! '(= (* t_ (* s_ (LOG x_))) (* (* s_ t_) (LOG x_)))
    (lambda () (crs)))
  (subst '(= (* t_ (* s_ (LOG x_))) (* (* s_ t_) (LOG x_))))
  ;; `=' is PARTIAL, so the residual `T = T' is not closed by reflexivity
  ;; alone -- it IS the assertion that T is defined.  Land that: the exponent
  ;; is a real, so R-EXP of it is a real.  (Typing `s_ * t_' and not `t_ * s_'
  ;; matters: the goal carries the first, and rr-mul-closed is not commutative
  ;; for the purposes of matching.)
  (rp-need! '(AND (IN (* s_ t_) RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed '(* s_ t_) '(LOG x_))
  (fact 'r-exp-in-rr '(* (* s_ t_) (LOG x_)))
  (rfl)))
(rp-check 'rpow-star-pow)
(qed 'rpow-star-pow)
(topic! 'rpow-star-pow 'analysis)
(alias! 'rpow-star-pow "(x^s)^t = x^(s.t)")

;;; =====================================================================
;;; 10.  THE NEGATIVE EXPONENT,  x^(-s) = 1/(x^s).  Unguarded in x.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_) (list '(IN s_ RR))
      '(= (RPOW-STAR x_ (- s_)) (RECIP-STAR (RPOW-STAR x_ s_))))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-slog! 's_ 'x_)
  (have! '(= (* (- s_) (LOG x_)) (- (* s_ (LOG x_)))) (lambda () (crs)))
  (subst '(= (* (- s_) (LOG x_)) (- (* s_ (LOG x_)))))
  (fact 'r-exp-neg '(* s_ (LOG x_)))
  (ass)))
(rp-check 'rpow-star-neg)
(qed 'rpow-star-neg)
(topic! 'rpow-star-neg 'analysis)
(alias! 'rpow-star-neg "x^(-s) = 1/(x^s)")

;;; =====================================================================
;;; 11.  MONOTONICITY.  Two statements, and they lean on different halves:
;;; in the EXPONENT it is log(x) > 0, i.e. x above 1 (log-pos-above-one); in
;;; the BASE it is strict monotonicity of LOG itself.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ s_ t_)
                (list '(IN x_ RR) '(IN s_ RR) '(IN t_ RR))
      '(IMPLIES (< 1 x_) (IMPLIES (< s_ t_)
         (< (RPOW-STAR x_ s_) (RPOW-STAR x_ t_)))))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-log! 'x_)
  (fact 'log-pos-above-one 'x_)
  (rp-need! '(AND (IN s_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG x_))
  (rp-need! '(AND (IN t_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 't_ '(LOG x_))
  ;; NOT `ineq': s_ . log(x_) against t_ . log(x_) is a product of two
  ;; unknowns, and Fourier-Motzkin is LINEAR -- it has nothing to work with.
  ;; This is a SCALING step, `rr-lt-scale-pos', whose scalar sits on the LEFT
  ;; while the definition puts log(x_) on the right; hence the two commutations.
  ;; rr-lt-scale-pos's antecedent is a CONJUNCTION, which `fact' will not
  ;; split, so the `have!' of the AND has to come first.
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
(alias! 'rpow-star-mono-exp "above 1, the real power is increasing in the exponent")

(sp (make-wff (forall-guarded '(x_ y_ s_)
                (list '(IN x_ RR) '(IN y_ RR) '(IN s_ RR))
      '(IMPLIES (< 0 x_) (IMPLIES (< x_ y_) (IMPLIES (< 0 s_)
         (< (RPOW-STAR x_ s_) (RPOW-STAR y_ s_))))))))
(quietly (lambda ()
  (rp-peel!)
  (mac 'RPOW-STAR)
  (rp-type-log! 'x_) (rp-type-log! 'y_)
  (fact 'log-strictly-increasing 'x_ 'y_)
  (rp-need! '(AND (IN s_ RR) (IN (LOG x_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG x_))
  (rp-need! '(AND (IN s_ RR) (IN (LOG y_) RR)))
  (fact 'rr-mul-closed 's_ '(LOG y_))
  ;; Here the scalar is ALREADY on the left, so rr-lt-scale-pos applies on the
  ;; nose -- no commutation.  The AND antecedent still has to be landed first.
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
