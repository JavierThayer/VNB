;;; theorem-library/log.scm -- THE LOGARITHM, DEFINED AS AN INTEGRAL, and its
;;; basic laws.  The one that costs anything is the functional equation, and
;;; what it costs is a CHANGE OF VARIABLES.
;;;
;;;     LOG(x)  :=  C-INT-OR( z_ |-> RECIP-STAR(z_),  1,  x )
;;;
;;; BOTH HALVES OF THAT ARE TOTAL, AND THAT IS THE WHOLE REASON THE DEFINITION
;;; CAN BE MADE AT ALL.
;;;
;;;  * `RECIP-STAR' (recip-star.scm) is the reciprocal totalised at 0, so
;;;    `recip-star-lam-in-fun' -- the integrand is a member of FUN(RR,RR), which
;;;    Def 4.6 demands of its phi -- carries NO hypothesis.  The bare map
;;;    z_ |-> recip(z_) is not in FUN(RR,RR) at all.
;;;  * `C-INT-OR' (c-int-oriented.scm) branches on IS-ANTIDERIVABLE rather than
;;;    on the order, so `c-int-or-in-rr' is UNCONDITIONAL.  Under an
;;;    order-branching wrapper the body of the lambda below would be undefined
;;;    at every x <= 0 and LOG would not be a member of FUN(RR,RR).
;;;
;;; Neither functoid is unfolded here.  Both files package their IF behind
;;; read-offs precisely so that citers never see it, and every proof below works
;;; from those read-offs; `mac LOG' is used on the goal in exactly four places
;;; (log-unfold, log-in-rr, log-one, log-diff) and `log-unfold' is proved so
;;; that a later `mac-h' has a THEOREM to rebuild its rule from.
;;;
;;; WHAT THE FUNCTIONAL EQUATION ACTUALLY COSTS.  log(x.y) = log x + log y is an
;;; equation between integral VALUES, so `antiderivable-affine-subst' and its
;;; siblings -- which conclude only that the substituted integrand HAS an
;;; antiderivative -- cannot reach it.  `c-int-change-of-variable-transfer'
;;; (c-int-change-of-variable.scm) is the value formula, and it is what section 7
;;; cites.  Around it there are two pieces of work and no analysis at all:
;;;
;;;  1. THE POINTWISE EQUATION, `recip-star-scale':
;;;
;;;        recip*(lam.u) . lam  =  recip*(u),        lam /= 0,
;;;
;;;     at EVERY real u, 0 INCLUDED -- both sides are 0 there, because
;;;     recip*(lam.0) = recip*(0) = 0 and 0.lam = 0.  The transfer form asks for
;;;     the equation over all of RR, and a PARTIAL reciprocal could not have
;;;     supplied it at 0.  This is the totalisation paying for itself a second
;;;     time.  Away from 0 it is not `recip-star-value' but `recip-star-inverse'
;;;     that does the work: (lam.u).A = 1 and u.B = 1 give (A.lam).u = B.u, and
;;;     `rr-cancel-mul-right' cancels the u.
;;;  2. THE INTERVAL BOOKKEEPING -- the affine map carries the CLOSED [a,b] into
;;;     the closed image AND the OPEN (a,b) into the open one, two universals,
;;;     neither implying the other (Def 4.6 is continuous on the closed interval
;;;     and differentiable on the open one).  `antiderivable-affine-subst-pos'
;;;     computes exactly these in its section 2 and does not export them, so
;;;     section 7 reproduces that block.
;;;
;;; THE ORIENTATION IS WHAT MAKES THE REST FREE.  `c-int-or-value' evaluates the
;;; oriented integral between ANY two points of an interval of antiderivability,
;;; with no ordering hypothesis, so once the ordered substitution law is in hand
;;; the general one is `rr-lt-trichotomy' plus `c-int-or-reverse' (section 8),
;;; and additivity in the bounds needs only an ambient interval containing three
;;; positive points.  There is no MIN operator in this tree and none is wanted:
;;; `rr-min-pos' hands back a positive lower bound of two positives
;;; EXISTENTIALLY, used twice, and no maximum is needed either -- u + v + w
;;; exceeds each of three positives, which is one `ineq' (section 9).  With
;;; additivity, `log-diff' says
;;;
;;;     int_u^v recip*  =  log v - log u        (u, v > 0),
;;;
;;; and then log(x.y) = log x + log y is the scale law at lam := x, a := 1,
;;; b := y read through it -- nothing anywhere asks whether y is above or below
;;; 1, which is what having built the orientation first buys.
;;;
;;; THE FUNDAMENTAL THEOREM (section 15) is nearly free -- C-INT was DEFINED
;;; from the antiderivative -- but not quite, and the gap is worth naming:
;;; IS-DIFF-AT is Caratheodory and its identity is GLOBAL, over every real,
;;; while log agrees with an antiderivative of recip* only on an interval.
;;; `diff-at-local' (diff-at-local.scm) is exactly that gap, and with it the
;;; proof is: halve c (`rr-pos-halvable', so c = d + d), take an antiderivative
;;; F on [d, c+d] -- which IS the ball of radius d about c -- read F's own
;;; Caratheodory witness off Def 4.6's derivative clause, and observe that on
;;; that ball log(x) - log(c) = F(x) - F(c), by `log-diff' and equation (64).
;;;
;;; MONOTONICITY (section 12) is the only place anything is ESTIMATED, and the
;;; estimate is `mvt-lower-bound', not an epsilon: on [u,v] the integrand is at
;;; least recip*(v) by `rr-recip-antitone', so f(v) - f(u) >= recip*(v).(v-u) > 0.
;;;
;;; WHAT IS PROVED, and the shape of the bill.  `log-unfold' and `log-one' are
;;; `modulo 0'; everything else inherits, unchanged, the fifteen leaves that
;;; `c-int-value' bills (Cor 4.11's debt, through equation (64)) together with
;;; what `continuous-is-antiderivable' bills for rung 3.  Nothing here adds a
;;; leaf of its own: there is no `support' and no `theory-add-axiom!' in this
;;; file.
;;;
;;; Loads after c-int-change-of-variable (the value formula),
;;; continuous-antiderivable (continuous-is-antiderivable), c-int-oriented,
;;; recip-star, diff-at-local, mvt-bounds-proof, bernstein-ccint
;;; (affine-continuous-at), directional-derivative (deriv-affine,
;;; affine-lam-in-fun), continuity-basics (const-lam-in-fun),
;;; sequential-continuity (rr-recip-antitone), rr-halving (rr-pos-halvable),
;;; rr-recip-order, rr-abs-basics (rr-abs-bound), rr-order-basics, ccint-basics,
;;; equality-basics and driver-kit.
;;; =====================================================================

(define (lg-check name)
  (if (not (proof-done? *ps*))
      (error "log: proof did not close" name (expression->string (dk-goal)))))

(define (lg-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 24) (error "lg-peel-to!: never reached" head
                           (expression->string (dk-goal))))
          (else (di) (loop (+ n 1))))))

(define (lg-need! f) (if (not (member f (dk-asms))) (have! f)))

(define (lg-di-var!) (cadr (car (dk-landed (lambda () (di))))))

(define (lg-order-indices)
  (let loop ((l (dk-asms)) (k 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <=)))
           (loop (cdr l) (+ k 1) (cons k acc)))
          (else (loop (cdr l) (+ k 1) acc)))))
(define (lg-ineq!) (apply ineq (lg-order-indices)))

(define (lg-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

(define (lg-beta*!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (> n 10) 'stop (begin (lam-b) (if (equal? g (dk-goal)) 'done (loop (+ n 1))))))))

;;; ---- the shapes ------------------------------------------------------

(define LG-RS '(VNB-LAMBDA z_ RR (RECIP-STAR z_)))       ; the integrand
(define LG-LAM '(VNB-LAMBDA x_ RR (LOG x_)))             ; the map

;;; =====================================================================
;;; 0.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'LOG '(x_) (list 'C-INT-OR LG-RS 1 'x_))
(notation! 'LOG 'kind 'functoid 'arity 1
           'english "the logarithm of $1"
           'noun "logarithm of $1"
           'tex "\\log\\left($1\\right)")

;;; =====================================================================
;;; 1.  THE UNFOLD EQUATION, as a THEOREM.
;;; =====================================================================

(sp (make-wff (list 'FORALL 'x_ (list '== (list 'LOG 'x_) (list 'C-INT-OR LG-RS 1 'x_)))))
(quietly (lambda () (di) (mac 'LOG) (qrfl)))
(lg-check 'log-unfold)
(qed 'log-unfold)
(topic! 'log-unfold 'analysis)
(alias! 'log-unfold
        "the defining equation of the logarithm"
        "log(x) is the oriented integral of the totalised reciprocal from 1 to x")

;;; =====================================================================
;;; 2.  THE VALUE IS ALWAYS A REAL -- UNCONDITIONAL.
;;; =====================================================================

(sp (make-wff '(FORALL x_ (IN (LOG x_) RR))))
(quietly (lambda ()
  (di)
  (mac 'LOG)
  (fact 'c-int-or-in-rr LG-RS 1 'x_)
  (ass)))
(lg-check 'log-in-rr)
(qed 'log-in-rr)
(topic! 'log-in-rr 'analysis)
(alias! 'log-in-rr
        "the logarithm of any real is a real")

;;; =====================================================================
;;; 3.  LOG IS A MAP RR -> RR -- UNCONDITIONAL.
;;; =====================================================================

(sp (make-wff (list 'IN LG-LAM '(FUN RR RR))))
(quietly (lambda ()
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'FORALL)
                  (let ((v (lg-di-var!)))
                    (fact 'log-in-rr v)
                    (ass))
                  (begin (fact 'rr-is-set) (ass))))
            (dk-opened (lambda () (lam-t))))))
(lg-check 'log-lam-in-fun)
(qed 'log-lam-in-fun)
(topic! 'log-lam-in-fun 'analysis)
(alias! 'log-lam-in-fun
        "the logarithm is a function from the reals to the reals")

;;; =====================================================================
;;; 4.  log 1 = 0.
;;; =====================================================================

(sp (make-wff '(= (LOG 1) 0)))
(quietly (lambda ()
  (mac 'LOG)
  (fact 'c-int-or-degenerate LG-RS 1)
  (ass)))
(lg-check 'log-one)
(qed 'log-one)
(topic! 'log-one 'analysis)
(alias! 'log-one
        "log 1 = 0")

;;; =====================================================================
;;; 5.  THE INTEGRAND IS ANTIDERIVABLE ON ANY INTERVAL TO THE RIGHT OF 0.
;;; =====================================================================

(sp (make-wff (forall-guarded '(a b) (list '(IN a RR) '(IN b RR) '(< 0 a) '(< a b))
                (list 'IS-ANTIDERIVABLE LG-RS 'a 'b))))
(quietly (lambda ()
  (lg-peel-to! 'IS-ANTIDERIVABLE)
  (fact 'recip-star-lam-in-fun)
  (have! (forall-guarded 'x_ '(IN x_ (CCINT a b))
                         (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS LG-RS 'x_))
    (lambda ()
      (let ((v (lg-di-var!)))
        (dk-split! (dk-fact! 'ccint-parts 'a 'b v))
        (fact 'recip-star-continuous-on-ccint 'a 'b v)
        (ass))))
  (fact 'continuous-is-antiderivable LG-RS 'a 'b)
  (ass)))
(lg-check 'recip-star-antiderivable-pos)
(qed 'recip-star-antiderivable-pos)
(topic! 'recip-star-antiderivable-pos 'analysis)
(alias! 'recip-star-antiderivable-pos
        "the totalised reciprocal is antiderivable on any interval to the right of zero")

;;; =====================================================================
;;; 6.  THE ARITHMETIC OF THE SUBSTITUTION:  recip*(lam.u).lam = recip*(u).
;;;     TRUE FOR EVERY REAL u, 0 INCLUDED -- both sides are 0 there.  That is
;;;     the totalisation paying for itself: the pointwise equation the change
;;;     of variables wants is stated over ALL of RR, and a partial reciprocal
;;;     could not have satisfied it.
;;; =====================================================================

(sp (make-wff (forall-guarded '(lam u) (list '(IN lam RR) '(IN u RR))
     '(IMPLIES (NOT (= lam 0))
               (= (* (RECIP-STAR (* lam u)) lam) (RECIP-STAR u))))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in)
  (fact 'recip-star-in-rr 'u)
  (lg-need! '(AND (IN lam RR) (IN u RR)))
  (fact 'rr-mul-in-rr 'lam 'u)
  (fact 'recip-star-in-rr '(* lam u))
  (use-em '(= u 0)
    ;; u = 0: both sides are 0.
    (lambda ()
      (fact 'rr-mul-zero 'lam)                       ; lam * 0 = 0
      (fact 'recip-star-zero)
      (subst '(= u 0))
      (subst '(= (* lam 0) 0))
      (subst '(= (RECIP-STAR 0) 0))
      (crs))
    ;; u /= 0: cancel u against the two inverse equations.
    (lambda ()
      (have! '(NOT (= (* lam u) 0))
        (lambda ()
          (di)
          (fact 'rr-no-zero-divisors 'lam 'u)
          (use-cases '((= lam 0) (= u 0))
            (lambda () (ai '(NOT (= lam 0))))
            (lambda () (ai '(NOT (= u 0)))))))
      (fact 'recip-star-inverse '(* lam u))           ; (lam.u).A = 1
      (fact 'recip-star-inverse 'u)                   ; u.B = 1
      (let ((A '(RECIP-STAR (* lam u)))
            (B '(RECIP-STAR u)))
        (lg-need! (list 'AND (list 'IN A 'RR) '(IN lam RR)))
        (fact 'rr-mul-in-rr A 'lam)
        (have! (list '= (list '* (list '* A 'lam) 'u) (list '* B 'u))
          (lambda ()
            (have! (list '= (list '* (list '* A 'lam) 'u)
                            (list '* (list '* 'lam 'u) A))
                   (lambda () (crs)))
            (subst (list '= (list '* (list '* A 'lam) 'u)
                            (list '* (list '* 'lam 'u) A)))
            (subst (list '= (list '* (list '* 'lam 'u) A) 1))
            (have! (list '= (list '* B 'u) (list '* 'u B)) (lambda () (crs)))
            (subst (list '= (list '* B 'u) (list '* 'u B)))
            (subst (list '= (list '* 'u B) 1))
            (rfl)))
        (fact 'rr-cancel-mul-right (list '* A 'lam) B 'u)
        (ass))))))
(lg-check 'recip-star-scale)
(qed 'recip-star-scale)
(topic! 'recip-star-scale 'analysis)
(alias! 'recip-star-scale
        "recip*(lam.u).lam = recip*(u), at every real u")

;;; =====================================================================
;;; 7.  THE SUBSTITUTION  t = lam.u,  ORDERED CASE.
;;;
;;;     C-INT-OR(recip*, lam.a, lam.b)  =  C-INT-OR(recip*, a, b)      (0 < lam)
;;;
;;; `c-int-change-of-variable-transfer' (c-int-change-of-variable.scm) does the
;;; analysis; everything here is bookkeeping, and it is the bookkeeping
;;; `antiderivable-affine-subst-pos' worked out first -- the affine map carries
;;; the CLOSED [a,b] into the closed image and the OPEN (a,b) into the open one,
;;; two universals, neither implying the other.  The pointwise equation the
;;; transfer form wants is `recip-star-scale', and it holds at EVERY real,
;;; 0 included.
;;; =====================================================================

(define LG-AF '(VNB-LAMBDA x RR (+ 0 (* lam x))))       ; A(t) = 0 + lam.t
(define LG-CL '(VNB-LAMBDA x RR lam))                   ; A'  = the constant lam
(define (lg-at v) (list LG-AF v))
(define (lg-zero-add v) (list '= (list '+ 0 (list '* 'lam v)) (list '* 'lam v)))

(define LG-CONT
  (forall-guarded 'u_ '(IN u_ (CCINT a b))
                  (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS LG-AF 'u_)))
(define LG-DIFF
  (forall-guarded 'w_ (conjuncts->and (list '(IN w_ RR) '(< a w_) '(< w_ b)))
                  (list 'IS-DIFF-AT LG-AF 'w_ (list LG-CL 'w_))))
(define LG-MI
  (forall-guarded 'u_ '(IN u_ (CCINT a b))
                  (list 'IN (lg-at 'u_) (list 'CCINT (lg-at 'a) (lg-at 'b)))))
(define LG-MINT
  (forall-guarded 'w_ (conjuncts->and (list '(IN w_ RR) '(< a w_) '(< w_ b)))
                  (conjuncts->and (list (list '< (lg-at 'a) (lg-at 'w_))
                                        (list '< (lg-at 'w_) (lg-at 'b))))))
(define LG-PW
  (forall-guarded 'x_ '(IN x_ RR)
                  (list '== (list LG-RS 'x_)
                            (list '* (list LG-RS (lg-at 'x_)) (list LG-CL 'x_)))))

(sp (make-wff (forall-guarded '(lam a b)
      (list '(IN lam RR) '(IN a RR) '(IN b RR) '(< 0 lam) '(< 0 a) '(< a b))
      (list '= (list 'C-INT-OR LG-RS (list '* 'lam 'a) (list '* 'lam 'b))
               (list 'C-INT-OR LG-RS 'a 'b)))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in)
  (fact 'rr-lt-implies-le 0 'lam)
  (fact 'rr-pos-ne-zero 'lam)
  (lg-need! '(AND (IN lam RR) (IN a RR)))
  (fact 'rr-mul-in-rr 'lam 'a)
  (lg-need! '(AND (IN lam RR) (IN b RR)))
  (fact 'rr-mul-in-rr 'lam 'b)
  (fact 'rr-mul-pos 'lam 'a)
  (lg-need! '(AND (< 0 lam) (< a b)))
  (fact 'rr-lt-scale-pos 'lam 'a 'b)
  (fact 'recip-star-lam-in-fun)
  (lg-need! '(AND (IN 0 RR) (IN lam RR)))
  (fact 'affine-lam-in-fun 0 'lam)
  (fact 'const-lam-in-fun 'lam)
  (fact 'recip-star-antiderivable-pos 'a 'b)
  (fact 'recip-star-antiderivable-pos '(* lam a) '(* lam b))
  (have! (lg-zero-add 'a) (lambda () (crs)))
  (have! (lg-zero-add 'b) (lambda () (crs)))

  ;; the integrand is antiderivable between the IMAGE endpoints, written as the
  ;; theorem writes them -- applied, not reduced.
  (have! (list 'IS-ANTIDERIVABLE LG-RS (lg-at 'a) (lg-at 'b))
    (lambda () (lg-beta*!) (subst (lg-zero-add 'a)) (subst (lg-zero-add 'b)) (ass)))

  ;; (1) A is continuous on the CLOSED [a,b].
  (have! LG-CONT
    (lambda ()
      (let ((v (lg-di-var!)))
        (dk-split! (dk-fact! 'ccint-parts 'a 'b v))
        (lg-need! (list 'AND '(IN 0 RR) (list 'AND '(IN lam RR) (list 'IN v 'RR))))
        (fact 'affine-continuous-at 0 'lam v)
        (ass))))

  ;; (2) ... and differentiable on the OPEN (a,b), with derivative A'(t).
  (have! LG-DIFF
    (lambda ()
      (di)
      (let* ((lnd (dk-landed-1 (lambda () (di))))
             (v   (cadr (cadr lnd))))
        (dk-split! lnd)
        (lam-b)
        (lg-need! (list 'AND '(IN 0 RR) (list 'AND '(IN lam RR) (list 'IN v 'RR))))
        (fact 'deriv-affine 0 'lam v)
        (ass))))

  ;; (3) A carries the CLOSED interval into the closed image ...
  (have! LG-MI
    (lambda ()
      (let ((v (lg-di-var!)))
        (dk-split! (dk-fact! 'ccint-parts 'a 'b v))
        (lg-need! (list 'AND '(IN lam RR) (list 'IN v 'RR)))
        (fact 'rr-mul-in-rr 'lam v)
        (have! (lg-zero-add v) (lambda () (crs)))
        (lg-beta*!)
        (subst (lg-zero-add v)) (subst (lg-zero-add 'a)) (subst (lg-zero-add 'b))
        (lg-need! (list 'AND '(<= 0 lam) (list '<= 'a v)))
        (fact 'rr-le-scale-nonneg 'lam 'a v)
        (lg-need! (list 'AND '(<= 0 lam) (list '<= v 'b)))
        (fact 'rr-le-scale-nonneg 'lam v 'b)
        (for-each (lambda (nd) (dk-focus! nd)
                    (if (eq? (car (dk-goal)) 'IN) (ass) (lg-ineq!)))
                  (dk-opened (lambda () (mac 'ccint-membership) (lg-split-goal!)))))))

  ;; (4) ... and the OPEN one into the open image.
  (have! LG-MINT
    (lambda ()
      (di)
      (let* ((lnd (dk-landed-1 (lambda () (di))))
             (v   (cadr (cadr lnd))))
        (dk-split! lnd)
        (lg-need! (list 'AND '(IN lam RR) (list 'IN v 'RR)))
        (fact 'rr-mul-in-rr 'lam v)
        (have! (lg-zero-add v) (lambda () (crs)))
        (lg-beta*!)
        (subst (lg-zero-add v)) (subst (lg-zero-add 'a)) (subst (lg-zero-add 'b))
        (lg-need! (list 'AND '(< 0 lam) (list '< 'a v)))
        (fact 'rr-lt-scale-pos 'lam 'a v)
        (lg-need! (list 'AND '(< 0 lam) (list '< v 'b)))
        (fact 'rr-lt-scale-pos 'lam v 'b)
        (for-each (lambda (nd) (dk-focus! nd) (lg-ineq!))
                  (dk-opened (lambda () (lg-split-goal!)))))))

  ;; (5) the pointwise equation:  recip*(t) == recip*(A(t)).A'(t), at EVERY real.
  (have! LG-PW
    (lambda ()
      (let ((v (lg-di-var!)))
        (lg-need! (list 'AND '(IN lam RR) (list 'IN v 'RR)))
        (fact 'rr-mul-in-rr 'lam v)
        (lg-need! (list 'AND '(IN 0 RR) (list 'IN (list '* 'lam v) 'RR)))
        (fact 'rr-add-in-rr 0 (list '* 'lam v))
        (fact 'fun-apply-type-c LG-AF 'RR 'RR v)
        (lg-beta*!)
        (have! (lg-zero-add v) (lambda () (crs)))
        (subst (lg-zero-add v))
        (fact 'recip-star-scale 'lam v)
        (subst (list '= (list '* (list 'RECIP-STAR (list '* 'lam v)) 'lam)
                        (list 'RECIP-STAR v)))
        (qrfl))))

  ;; the change of variables itself ...
  (fact 'c-int-change-of-variable-transfer LG-RS LG-RS LG-AF LG-CL 'a 'b)
  (fact 'c-int-in-rr LG-RS '(* lam a) '(* lam b))
  (have! (list '= (list 'C-INT LG-RS 'a 'b)
                  (list 'C-INT LG-RS '(* lam a) '(* lam b)))
    (lambda ()
      (subst (list '= (list 'C-INT LG-RS 'a 'b)
                      (list 'C-INT LG-RS (lg-at 'a) (lg-at 'b))))
      (lg-beta*!)
      (subst (lg-zero-add 'a)) (subst (lg-zero-add 'b))
      (rfl)))
  ;; ... and back into the oriented vocabulary.
  (fact 'c-int-or-anti LG-RS 'a 'b)
  (fact 'c-int-or-anti LG-RS '(* lam a) '(* lam b))
  (subst (list '= (list 'C-INT-OR LG-RS '(* lam a) '(* lam b))
                  (list 'C-INT LG-RS '(* lam a) '(* lam b))))
  (subst (list '= (list 'C-INT-OR LG-RS 'a 'b) (list 'C-INT LG-RS 'a 'b)))
  (fact 'eq-sym (list 'C-INT LG-RS 'a 'b) (list 'C-INT LG-RS '(* lam a) '(* lam b)))
  (ass)))
(lg-check 'c-int-or-scale-ordered)
(qed 'c-int-or-scale-ordered)
(topic! 'c-int-or-scale-ordered 'analysis)
(alias! 'c-int-or-scale-ordered
        "the oriented integral of recip* is invariant under scaling the bounds")

;;; =====================================================================
;;; 8.  ... AND WITH NO ORDERING HYPOTHESIS AT ALL.
;;;
;;; The ordered case applies to [a,b] or to [b,a] -- both are intervals to the
;;; right of 0 -- and `c-int-or-reverse' carries the sign across.  This is what
;;; the oriented integral was built for: the equation now holds for any two
;;; positive endpoints, in either order.
;;; =====================================================================

(sp (make-wff (forall-guarded '(lam a b)
      (list '(IN lam RR) '(IN a RR) '(IN b RR) '(< 0 lam) '(< 0 a) '(< 0 b))
      (list '= (list 'C-INT-OR LG-RS '(* lam a) '(* lam b))
               (list 'C-INT-OR LG-RS 'a 'b)))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in)
  (lg-need! '(AND (IN lam RR) (IN a RR)))
  (fact 'rr-mul-in-rr 'lam 'a)
  (lg-need! '(AND (IN lam RR) (IN b RR)))
  (fact 'rr-mul-in-rr 'lam 'b)
  (fact 'c-int-or-in-rr LG-RS 'b 'a)
  (fact 'c-int-or-in-rr LG-RS '(* lam b) '(* lam a))
  (fact 'rr-lt-trichotomy 'a 'b)
  (use-cases '((< a b) (= a b) (< b a))
    (lambda () (fact 'c-int-or-scale-ordered 'lam 'a 'b) (ass))
    (lambda ()
      (subst '(= a b))
      (fact 'c-int-or-degenerate LG-RS '(* lam b))
      (fact 'c-int-or-degenerate LG-RS 'b)
      (subst (list '= (list 'C-INT-OR LG-RS '(* lam b) '(* lam b)) 0))
      (subst (list '= (list 'C-INT-OR LG-RS 'b 'b) 0))
      (crs))
    (lambda ()
      (fact 'c-int-or-scale-ordered 'lam 'b 'a)
      (fact 'c-int-or-reverse LG-RS '(* lam b) '(* lam a))
      (fact 'c-int-or-reverse LG-RS 'b 'a)
      (subst (list '= (list 'C-INT-OR LG-RS '(* lam a) '(* lam b))
                      (list '- (list 'C-INT-OR LG-RS '(* lam b) '(* lam a)))))
      (subst (list '= (list 'C-INT-OR LG-RS 'a 'b)
                      (list '- (list 'C-INT-OR LG-RS 'b 'a))))
      (subst (list '= (list 'C-INT-OR LG-RS '(* lam b) '(* lam a))
                      (list 'C-INT-OR LG-RS 'b 'a)))
      (crs)))))
(lg-check 'c-int-or-scale)
(qed 'c-int-or-scale)
(topic! 'c-int-or-scale 'analysis)
(alias! 'c-int-or-scale
        "scaling both bounds by a positive factor leaves the integral of recip* unchanged"
        "int_{lam.a}^{lam.b} recip* = int_a^b recip*, for any positive a, b, lam")

;;; =====================================================================
;;; 9.  ADDITIVITY IN THE BOUNDS, for any three POSITIVE points.
;;;
;;; `c-int-or-additive' wants an ambient interval of antiderivability holding
;;; all three.  There is no MIN operator in this tree and none is wanted:
;;; `rr-min-pos' hands back a positive lower bound of two positives
;;; EXISTENTIALLY, twice, and the upper bound needs no maximum either --
;;; u + v + w exceeds each of three positives, and that is one `ineq'.
;;; =====================================================================

(define (lg-obtain-min! x y)
  (let ((ex (dk-fact! 'rr-min-pos x y)))
    (let ((bod (car (dk-landed* (lambda () (ai ex))))))
      (dk-split! bod)
      (cadr (cadr bod)))))

(sp (make-wff (forall-guarded '(u v w)
      (list '(IN u RR) '(IN v RR) '(IN w RR) '(< 0 u) '(< 0 v) '(< 0 w))
      (list '= (list 'C-INT-OR LG-RS 'u 'w)
               (list '+ (list 'C-INT-OR LG-RS 'u 'v)
                        (list 'C-INT-OR LG-RS 'v 'w))))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in)
  (lg-need! '(AND (IN v RR) (IN w RR)))
  (fact 'rr-add-in-rr 'v 'w)
  (lg-need! '(AND (IN u RR) (IN (+ v w) RR)))
  (fact 'rr-add-in-rr 'u '(+ v w))
  (let* ((m (lg-obtain-min! 'u 'v))
         (p (lg-obtain-min! m 'w))
         (q '(+ u (+ v w))))
    (have! (list '< p q) (lambda () (lg-ineq!)))
    (fact 'recip-star-antiderivable-pos p q)
    (for-each
     (lambda (t)
       (have! (list 'IN t (list 'CCINT p q))
         (lambda ()
           (for-each (lambda (nd) (dk-focus! nd)
                       (if (eq? (car (dk-goal)) 'IN) (ass) (lg-ineq!)))
                     (dk-opened (lambda () (mac 'ccint-membership) (lg-split-goal!)))))))
     '(u v w))
    (fact 'c-int-or-additive LG-RS p q 'u 'v 'w)
    (ass))))
(lg-check 'recip-star-int-additive)
(qed 'recip-star-int-additive)
(topic! 'recip-star-int-additive 'analysis)
(alias! 'recip-star-int-additive
        "additivity in the bounds for recip*, at any three positive points")

;;; =====================================================================
;;; 10.  THE INTEGRAL BETWEEN TWO POSITIVES IS A DIFFERENCE OF LOGARITHMS.
;;; =====================================================================

(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR) '(< 0 u) '(< 0 v))
      (list '= (list 'C-INT-OR LG-RS 'u 'v) '(- (LOG v) (LOG u))))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-one-in)
  (fact 'rr-zero-lt-one)
  (fact 'recip-star-int-additive 1 'u 'v)
  (fact 'c-int-or-in-rr LG-RS 1 'u)
  (fact 'c-int-or-in-rr LG-RS 'u 'v)
  (mac 'LOG)
  (subst (list '= (list 'C-INT-OR LG-RS 1 'v)
                  (list '+ (list 'C-INT-OR LG-RS 1 'u)
                           (list 'C-INT-OR LG-RS 'u 'v))))
  (crs)))
(lg-check 'log-diff)
(qed 'log-diff)
(topic! 'log-diff 'analysis)
(alias! 'log-diff
        "the integral of recip* between two positives is a difference of logarithms")

;;; =====================================================================
;;; 11.  THE FUNCTIONAL EQUATION.   log(x.y) = log x + log y,  x, y > 0.
;;;
;;; The scale law at lam := x carries int_1^y onto int_x^{xy} -- no ordering
;;; hypothesis, so nothing here asks whether y is above or below 1 -- and
;;; `log-diff' reads both integrals off as differences of logarithms.
;;; =====================================================================

(sp (make-wff (forall-guarded '(x_ y_) (list '(IN x_ RR) '(IN y_ RR) '(< 0 x_) '(< 0 y_))
      '(= (LOG (* x_ y_)) (+ (LOG x_) (LOG y_))))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in)
  (fact 'rr-one-in)
  (fact 'rr-zero-lt-one)
  (lg-need! '(AND (IN x_ RR) (IN y_ RR)))
  (fact 'rr-mul-in-rr 'x_ 'y_)
  (fact 'rr-mul-pos 'x_ 'y_)
  (fact 'log-in-rr 'x_) (fact 'log-in-rr 'y_) (fact 'log-in-rr '(* x_ y_))
  (fact 'c-int-or-in-rr LG-RS 'x_ '(* x_ y_))
  ;; the scale law at lam := x, a := 1, b := y, with x.1 normalised to x
  (fact 'c-int-or-scale 'x_ 1 'y_)
  (have! '(= (* x_ 1) x_) (lambda () (crs)))
  (have! (list '= (list 'C-INT-OR LG-RS 'x_ '(* x_ y_)) (list 'C-INT-OR LG-RS 1 'y_))
    (lambda ()
      (subst (list '= (list 'C-INT-OR LG-RS 1 'y_)
                      (list 'C-INT-OR LG-RS '(* x_ 1) '(* x_ y_))))
      (subst '(= (* x_ 1) x_))
      (crs)))
  (fact 'log-diff 'x_ '(* x_ y_))
  (fact 'log-diff 1 'y_)
  (fact 'log-one)
  (have! '(= (LOG y_) (- (LOG (* x_ y_)) (LOG x_)))
    (lambda ()
      (subst (list '= '(- (LOG (* x_ y_)) (LOG x_))
                      (list 'C-INT-OR LG-RS 'x_ '(* x_ y_))))
      (subst (list '= (list 'C-INT-OR LG-RS 'x_ '(* x_ y_))
                      (list 'C-INT-OR LG-RS 1 'y_)))
      (subst (list '= (list 'C-INT-OR LG-RS 1 'y_) '(- (LOG y_) (LOG 1))))
      (subst '(= (LOG 1) 0))
      (crs)))
  (subst '(= (LOG y_) (- (LOG (* x_ y_)) (LOG x_))))
  (crs)))
(lg-check 'log-mul)
(qed 'log-mul)
(topic! 'log-mul 'analysis)
(alias! 'log-mul
        "the logarithm turns products into sums"
        "log(x.y) = log x + log y for positive x and y")

;;; =====================================================================
;;; 12.  LOG IS STRICTLY INCREASING ON THE POSITIVES.
;;;
;;; The only place in this file where anything is ESTIMATED, and the estimate
;;; is `mvt-lower-bound', not an epsilon: on [u,v] the integrand is at least
;;; recip*(v) -- `rr-recip-antitone' -- so f(v) - f(u) >= recip*(v).(v-u) > 0,
;;; and `c-int-or-value' identifies that difference with the integral.
;;; =====================================================================

(define (lg-idx f)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "lg-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (else (lp (cdr l) (+ i 1))))))
(define (lg-ineq . fs) (apply ineq (map lg-idx fs)))

;; `ineq' demands an (IN t RR) certificate for every atom of every NAMED
;; premise, so a blanket sweep of the context's order facts fails as soon as
;; one of them mentions a term nothing has typed.  Name the premises.
(define (lg-in-ccint! t lo hi . prem)
  (have! (list 'IN t (list 'CCINT lo hi))
    (lambda ()
      (for-each (lambda (nd) (dk-focus! nd)
                  (if (eq? (car (dk-goal)) 'IN) (ass) (apply lg-ineq prem)))
                (dk-opened (lambda () (mac 'ccint-membership) (lg-split-goal!)))))))

(sp (make-wff (forall-guarded '(u v) (list '(IN u RR) '(IN v RR) '(< 0 u) '(< u v))
                '(< (LOG u) (LOG v)))))
(quietly (lambda ()
  (lg-peel-to! '<)
  (fact 'rr-zero-in)
  (have! '(< 0 v) (lambda () (lg-ineq '(< 0 u) '(< u v))))
  (fact 'rr-lt-implies-le 'u 'v)
  (fact 'rr-pos-ne-zero 'u)
  (fact 'rr-pos-ne-zero 'v)
  (fact 'log-in-rr 'u) (fact 'log-in-rr 'v)
  (fact 'c-int-or-in-rr LG-RS 'u 'v)
  (fact 'log-diff 'u 'v)
  (fact 'recip-star-in-rr 'v)
  (fact 'recip-star-value 'v)
  (fact 'rr-recip-pos 'v)
  (have! '(< 0 (RECIP-STAR v))
    (lambda () (subst '(= (RECIP-STAR v) (recip v))) (ass)))
  (fact 'rr-leq-reflexive 'u) (fact 'rr-leq-reflexive 'v)
  (fact 'recip-star-antiderivable-pos 'u 'v)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE LG-RS 'u 'v))
  (let ((f (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
    (lg-in-ccint! 'u 'u 'v '(<= u u) '(<= u v))
    (lg-in-ccint! 'v 'u 'v '(<= u v) '(<= v v))
    (fact 'c-int-or-value f LG-RS 'u 'v 'u 'v)          ; = f(v) - f(u)
    (fact 'antiderivative-map-in-fun f LG-RS 'u 'v)
    (fact 'fun-apply-type-c f 'RR 'RR 'u)
    (fact 'fun-apply-type-c f 'RR 'RR 'v)
    ;; Def 4.6's two universals.  `mac-h' is destructive and c-int-or-value has
    ;; already been cited, so this is the last use of IS-ANTIDERIVATIVE.
    (dk-split! (dk-landed-1
      (lambda () (mac-h 'IS-ANTIDERIVATIVE (list 'IS-ANTIDERIVATIVE f LG-RS 'u 'v)))))
    ;; Def 4.6's continuity clause IS mvt-lower-bound's, up to the bound
    ;; variable's name, so it detaches from the context as it stands; only the
    ;; derivative clause has to be restated, `mvt-lower-bound' asking for a
    ;; BOUND on the derivative where Def 4.6 names it.
    (let ((df (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                            (dk-contains? z 'IS-DIFF-AT)))
                           (dk-asms)))))
      ;; at each interior point the derivative is recip*, hence >= recip*(v)
      (have! (forall-guarded 'x (conjuncts->and (list '(IN x RR) '(< u x) '(< x v)))
               (list 'FORSOME 'L (list 'AND (list 'IS-DIFF-AT f 'x 'L)
                                             (list '<= '(RECIP-STAR v) 'L))))
        (lambda ()
          (di)
          (let* ((lnd (dk-landed-1 (lambda () (di))))
                 (tv  (cadr (cadr lnd))))
            (dk-split! lnd)
            (lg-need! lnd)
            (inst+ df tv)
            (fact 'recip-star-in-rr tv)
            (have! (list '< 0 tv)
                   (lambda () (lg-ineq '(< 0 u) (list '< 'u tv))))
            (fact 'rr-pos-ne-zero tv)
            (fact 'recip-star-value tv)
            (have! (list '= (list LG-RS tv) (list 'RECIP-STAR tv))
              (lambda () (lam-b) (rfl)))
            (ew (list 'RECIP-STAR tv))
            (for-each
             (lambda (nd)
               (dk-focus! nd)
               (if (eq? (car (dk-goal)) 'IS-DIFF-AT)
                   (begin (subst (list '= (list 'RECIP-STAR tv) (list LG-RS tv))) (ass))
                   (begin
                     (fact 'rr-lt-implies-le tv 'v)
                     (subst (list '= (list 'RECIP-STAR tv) (list 'recip tv)))
                     (subst '(= (RECIP-STAR v) (recip v)))
                     (fact 'rr-recip-antitone tv 'v)
                     (ass))))
             (dk-opened (lambda () (di)))))))
      ;; mvt-lower-bound's typing antecedent is ONE nested conjunction, so it
      ;; goes into the context whole or the citation lands the implication.
      (lg-need! (list 'AND (list 'IN f '(FUN RR RR))
                      (list 'AND '(IN u RR)
                            (list 'AND '(IN v RR)
                                  (list 'AND '(IN (RECIP-STAR v) RR) '(< u v))))))
      (fact 'mvt-lower-bound f 'u 'v '(RECIP-STAR v))
      (lg-need! '(AND (IN v RR) (IN u RR)))
      (fact 'rr-sub-in-rr 'v 'u)
      (have! '(< 0 (- v u)) (lambda () (lg-ineq '(< u v))))
      (fact 'rr-mul-pos '(RECIP-STAR v) '(- v u))
      (lg-need! '(AND (IN (RECIP-STAR v) RR) (IN (- v u) RR)))
      (fact 'rr-mul-in-rr '(RECIP-STAR v) '(- v u))
      (lg-ineq (list '= (list 'C-INT-OR LG-RS 'u 'v) '(- (LOG v) (LOG u)))
               (list '= (list 'C-INT-OR LG-RS 'u 'v) (list '- (list f 'v) (list f 'u)))
               (list '<= (list '* '(RECIP-STAR v) '(- v u))
                         (list '- (list f 'v) (list f 'u)))
               '(< 0 (* (RECIP-STAR v) (- v u))))))))
(lg-check 'log-strictly-increasing)
(qed 'log-strictly-increasing)
(topic! 'log-strictly-increasing 'analysis)
(alias! 'log-strictly-increasing
        "the logarithm is strictly increasing on the positives")

;;; =====================================================================
;;; 13.  ... hence log is NEGATIVE below 1 and POSITIVE above it.
;;; =====================================================================

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 0 x_) (IMPLIES (< x_ 1) (< (LOG x_) 0))))))
(quietly (lambda ()
  (lg-peel-to! '<)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'log-in-rr 'x_) (fact 'log-in-rr 1)
  (fact 'log-strictly-increasing 'x_ 1)
  (fact 'log-one)
  (lg-ineq '(< (LOG x_) (LOG 1)) '(= (LOG 1) 0))))
(lg-check 'log-neg-below-one)
(qed 'log-neg-below-one)
(topic! 'log-neg-below-one 'analysis)
(alias! 'log-neg-below-one
        "the logarithm is negative below 1")

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 1 x_) (< 0 (LOG x_))))))
(quietly (lambda ()
  (lg-peel-to! '<)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-zero-lt-one)
  (fact 'log-in-rr 'x_) (fact 'log-in-rr 1)
  (fact 'log-strictly-increasing 1 'x_)
  (fact 'log-one)
  (lg-ineq '(< (LOG 1) (LOG x_)) '(= (LOG 1) 0))))
(lg-check 'log-pos-above-one)
(qed 'log-pos-above-one)
(topic! 'log-pos-above-one 'analysis)
(alias! 'log-pos-above-one
        "the logarithm is positive above 1")

;;; =====================================================================
;;; 14.  log(1/x) = -log(x).   The functional equation at y := recip*(x),
;;; where `recip-star-inverse' makes the product 1 and `log-one' kills it.
;;; =====================================================================

(sp (make-wff (forall-guarded 'x_ '(IN x_ RR)
      '(IMPLIES (< 0 x_) (= (LOG (RECIP-STAR x_)) (- (LOG x_)))))))
(quietly (lambda ()
  (lg-peel-to! '=)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-pos-ne-zero 'x_)
  (fact 'recip-star-in-rr 'x_)
  (fact 'recip-star-value 'x_)
  (fact 'rr-recip-pos 'x_)
  (have! '(< 0 (RECIP-STAR x_))
    (lambda () (subst '(= (RECIP-STAR x_) (recip x_))) (ass)))
  (fact 'recip-star-inverse 'x_)
  (fact 'log-mul 'x_ '(RECIP-STAR x_))
  (fact 'log-one)
  (fact 'log-in-rr 'x_) (fact 'log-in-rr '(RECIP-STAR x_))
  (have! '(= (+ (LOG x_) (LOG (RECIP-STAR x_))) 0)
    (lambda ()
      (subst '(= (+ (LOG x_) (LOG (RECIP-STAR x_)))
                 (LOG (* x_ (RECIP-STAR x_)))))
      (subst '(= (* x_ (RECIP-STAR x_)) 1))
      (ass)))
  (have! '(= (- (LOG x_)) (- 0 (LOG x_))) (lambda () (crs)))
  (subst '(= (- (LOG x_)) (- 0 (LOG x_))))
  (subst '(= 0 (+ (LOG x_) (LOG (RECIP-STAR x_)))))
  (crs)))
(lg-check 'log-recip)
(qed 'log-recip)
(topic! 'log-recip 'analysis)
(alias! 'log-recip
        "log(1/x) = -log(x)")

;;; =====================================================================
;;; 15.  THE FUNDAMENTAL THEOREM OF THE CALCULUS, for this integral:
;;;
;;;          log'(c) = recip*(c)      for every c > 0.
;;;
;;; C-INT was DEFINED from the antiderivative, so there is no analysis to do
;;; here -- but IS-DIFF-AT is Caratheodory and its identity is GLOBAL, while
;;; log agrees with an antiderivative of recip* only on an interval.  That gap
;;; is exactly what `diff-at-local' (diff-at-local.scm) closes, so the proof is:
;;; halve c to get a radius, take an antiderivative F on [d, c+d] (which is the
;;; ball about c of radius d, c being d + d), read F's own Caratheodory witness
;;; off Def 4.6's derivative clause, and observe that log and F differ by the
;;; constant F(1)-worth of bookkeeping that `log-diff' and `c-int-or-value'
;;; between them make explicit -- on the ball, log(x) - log(c) = F(x) - F(c).
;;; =====================================================================

(define (lg-pos-rr! t)
  (have! (list 'POS-RR t)
    (lambda ()
      (fact 'rr-lt-implies-le 0 t)
      (fact 'rr-pos-ne-zero t)
      (fact 'neq-sym t 0)
      (for-each (lambda (nd) (dk-focus! nd) (ass))
                (dk-opened (lambda () (mac 'pos-rr) (lg-split-goal!)))))))

;; `mac-h' on IS-ANTIDERIVATIVE is DESTRUCTIVE, so equation (64) is read off
;; ONCE, as a universal over the interval, before the unfold that deletes the
;; hypothesis it needs.
(define (lg-value-univ F d q)
  (forall-guarded 'y_ (list 'IN 'y_ (list 'CCINT d q))
    (list '= (list 'C-INT-OR LG-RS 'c_ 'y_)
             (list '- (list F 'y_) (list F 'c_)))))

(define (lg-from-pos-rr! t)
  (mac-h 'pos-rr (list 'POS-RR t))
  (dk-split! (list 'AND (list 'IN t 'RR)
                   (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t)))))
  (fact 'neq-sym 0 t)
  (have! (list '< 0 t) (lambda () (mac '<) (from-context!))))

(sp (make-wff (forall-guarded 'c_ '(IN c_ RR)
      (list 'IMPLIES '(< 0 c_) (list 'IS-DIFF-AT LG-LAM 'c_ '(RECIP-STAR c_))))))
(quietly (lambda ()
  (lg-peel-to! 'IS-DIFF-AT)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'log-lam-in-fun)
  (fact 'recip-star-in-rr 'c_)
  (fact 'rr-pos-ne-zero 'c_)
  (lg-pos-rr! 'c_)
  (let* ((ex  (dk-fact! 'rr-pos-halvable 'c_))
         (bod (car (dk-landed* (lambda () (ai ex)))))
         (d   (cadr (cadr bod))))
    (dk-split! bod)
    (lg-from-pos-rr! d)
    (lg-need! (list 'AND '(IN c_ RR) (list 'IN d 'RR)))
    (fact 'rr-add-in-rr 'c_ d)
    (fact 'rr-neg-closed d)
    (let ((q (list '+ 'c_ d))
          (heq (list '= (list '+ d d) 'c_))
          (dpos (list '< 0 d)))
      (have! (list '< d 'c_) (lambda () (lg-ineq heq dpos)))
      (have! (list '< 'c_ q) (lambda () (lg-ineq dpos)))
      (have! (list '< d q)   (lambda () (lg-ineq heq dpos)))
      (fact 'rr-lt-implies-le d 'c_)
      (fact 'rr-lt-implies-le 'c_ q)
      (fact 'recip-star-antiderivable-pos d q)
      (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE LG-RS d q))
      (let ((F (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
        (fact 'antiderivative-map-in-fun F LG-RS d q)
        (lg-in-ccint! 'c_ d q (list '<= d 'c_) (list '<= 'c_ q))
        (have! (lg-value-univ F d q)
          (lambda () (let ((yv (lg-di-var!)))
                       (fact 'c-int-or-value F LG-RS d q 'c_ yv)
                       (ass))))
        (dk-split! (dk-landed-1
          (lambda () (mac-h 'IS-ANTIDERIVATIVE (list 'IS-ANTIDERIVATIVE F LG-RS d q)))))
        (let ((df (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                (dk-contains? z 'IS-DIFF-AT)))
                               (dk-asms)))))
          (lg-need! (list 'AND '(IN c_ RR)
                          (list 'AND (list '< d 'c_) (list '< 'c_ q))))
          (inst+ df 'c_)
          (have! (list '= (list LG-RS 'c_) '(RECIP-STAR c_))
                 (lambda () (lam-b) (rfl)))
          (have! (list 'IS-DIFF-AT F 'c_ '(RECIP-STAR c_))
            (lambda () (subst (list '= '(RECIP-STAR c_) (list LG-RS 'c_))) (ass)))
          ;; F's own Caratheodory witness, which is GLOBAL -- that is the half
          ;; of IS-DIFF-AT that log cannot supply for itself.
          (dk-split! (dk-landed-1
            (lambda () (mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT F 'c_ '(RECIP-STAR c_))))))
          (let* ((pbod (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))
                 (psi  (cadr (cadr pbod))))
            (dk-split! pbod)
            (let ((cu (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                                    (dk-contains? z psi)
                                                    (dk-contains? z F)))
                                   (dk-asms)))))
              (have! (forall-guarded 'x_ '(IN x_ RR)
                       (list 'IMPLIES (list '<= (list 'abs '(- x_ c_)) d)
                             (list '= (list '- (list LG-LAM 'x_) (list LG-LAM 'c_))
                                      (list '* (list psi 'x_) '(- x_ c_)))))
                (lambda ()
                  (let* ((lands (dk-landed (lambda () (di))))
                         (xv (cadr (car (filter (dk-head? 'IN) lands))))
                         (dif (list '- xv 'c_))
                         (bnd (list 'AND (list '<= (list '- d) dif)
                                          (list '<= dif d))))
                    ;; a GUARDED universal lands its typing in one `di' and
                    ;; stops; the abs bound is the NEXT antecedent.
                    (lg-peel-to! '=)
                    (lg-need! (list 'AND (list 'IN xv 'RR) '(IN c_ RR)))
                    (fact 'rr-sub-in-rr xv 'c_)
                    (fact 'rr-abs-bound dif d)
                    (ai (list 'IFF (list '<= (list 'abs dif) d) bnd))
                    (detach! (list 'IMPLIES (list '<= (list 'abs dif) d) bnd))
                    (dk-split! bnd)
                    (have! (list '< 0 xv)
                      (lambda () (lg-ineq (list '<= (list '- d) dif) heq dpos)))
                    (have! (list '<= d xv)
                      (lambda () (lg-ineq (list '<= (list '- d) dif) heq)))
                    (have! (list '<= xv q)
                      (lambda () (lg-ineq (list '<= dif d))))
                    (lg-in-ccint! xv d q (list '<= d xv) (list '<= xv q))
                    (fact 'log-diff 'c_ xv)
                    (inst+ (lg-value-univ F d q) xv)
                    (inst+ cu xv)
                    (lam-b)
                    (subst (list '= (list '- (list 'LOG xv) '(LOG c_))
                                    (list 'C-INT-OR LG-RS 'c_ xv)))
                    (subst (list '= (list 'C-INT-OR LG-RS 'c_ xv)
                                    (list '- (list F xv) (list F 'c_))))
                    (ass))))
              (fact 'diff-at-local LG-LAM psi 'c_ '(RECIP-STAR c_) d)
              (ass)))))))))
(lg-check 'log-deriv)
(qed 'log-deriv)
(topic! 'log-deriv 'analysis)
(alias! 'log-deriv
        "the fundamental theorem: the derivative of the logarithm is the totalised reciprocal")
