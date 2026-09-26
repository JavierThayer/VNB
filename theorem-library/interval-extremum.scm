;;; interval-extremum.scm -- PROPOSITION 2.10 FOR A FUNCTION ON ITS INTERVAL.
;;;
;;; The user's notes (Supplements to Calculus), section 2.4:
;;;
;;;     Proposition 2.10.  Suppose f is a function defined on [a, b] with a
;;;     local maximum at x in [a, b].  If [D+ f](x) is defined, then
;;;     [D+ f](x) <= 0.  If [D- f](x) is defined, then [D- f](x) >= 0.  In
;;;     particular, if x is not one of the endpoints of [a, b] and f is
;;;     differentiable at x, then f'(x) = 0.
;;;
;;; WHAT IS PROVEN HERE is the third sentence -- the "in particular" -- for a
;;; function ON [a, b], with the LOCAL maximum of Definition 2.9 (structure-
;;; library/interval-extremum.scm) and the LOCAL derivative HAS-DERIV-AT
;;; (structure-library/interval-calculus.scm), and the same for a local
;;; minimum.  The library's own Prop 2.10 (`interior-max-deriv-zero',
;;; theorem-library/interval-extremum-proof.scm) asks for f in FUN(RR, RR) and
;;; for a GLOBAL maximum over all of [a, b]; docs/real-calculus-statements.tex,
;;; section 7, records exactly that deviation.  Those theorems are not retired:
;;; they are the lemmas these rest on.
;;;
;;; THE FIRST TWO SENTENCES ARE NOT STATED, and the reason is a missing
;;; definition, not a missing proof.  [D+ f](x) and [D- f](x) are the ONE-SIDED
;;; derivatives of the notes' section 2.1 (the limits of the difference
;;; quotient as theta decreases / increases to x).  The tree has one-sided
;;; LIMITS -- IS-RIGHT-LIMIT / IS-LEFT-LIMIT, structure-library/regulated.scm
;;; -- but both are predicates of a TOTAL function: their first conjunct is
;;; `f in FUN(RR, RR)'.  A one-sided derivative of a function on [a, b], at an
;;; endpoint, is not expressible with them.  What is missing is one definition
;;; in the shape of HAS-DERIV-AT,
;;;
;;;     HAS-RIGHT-DERIV-AT(f, x, l)  iff  forsome eps > 0. forall d > 0.
;;;        forsome delta > 0. forall t. x < t <= x + delta and t in dom f
;;;           implies  |(f(t) - f(x))/(t - x) - l| <= d
;;;
;;; (or, in the library's style, the Caratheodory factor on [x, x + eps)), and
;;; its two read-offs.  With it, the first two sentences are the same driver as
;;; below with the one-sided window in place of the symmetric one.  Reported,
;;; not attempted.
;;;
;;; THE ROUTE.  A local maximum is a GLOBAL maximum on a small enough closed
;;; subinterval, and on a subinterval strictly inside (a, b) the constant
;;; extension EXTEND-CONST(f, a, b) agrees with f -- so the library's
;;; total-function theorem applies to the extension verbatim.  Concretely, with
;;; alpha the radius the local maximum hands over,
;;;
;;;     w = min(alpha, theta - a, b - theta),   h = w/2,
;;;     [theta - h, theta + h]  is inside  [a, b]  and inside the alpha-window,
;;;
;;; so F = EXTEND-CONST(f, a, b) has a maximum on [theta - h, theta + h] at the
;;; interior point theta, and is differentiable there by
;;; `extend-const-deriv-fwd'.  `interior-max-deriv-zero' finishes.  The halving
;;; is not economy: it is what makes theta - h > a and theta + h < b STRICT,
;;; which `interior-max-deriv-zero' demands.
;;;
;;; Helper prefix: ix-.
;;;
;;; Dependencies: structure-library/interval-extremum.scm,
;;; structure-library/interval-calculus.scm,
;;; theorem-library/interval-calculus-laws.scm (extend-const-*, ooint-*),
;;; theorem-library/interior-extremum-proof.scm (interior-max/min-deriv-zero),
;;; ccint-basics.scm, rr-abs-basics.scm (rr-abs-bound), rr-order-basics.scm
;;; (rr-min-pos), rr-halving.scm (through dk-halve!), pos-rr-of-lt.scm.

;;; ---- file-local driver helpers ---------------------------------------

(define ix-ext '(EXTEND-CONST f a b))

;;; from (IN z (OOINT lo hi)) in context, land and split the three atoms.
(define (ix-ooint-parts! z lo hi)
  (dk-have! (list 'AND (list 'IN z 'RR) (list 'AND (list '< lo z) (list '< z hi)))
    (lambda () (fact 'ooint-membership lo hi z) (prop)))
  (dk-split-all!))

;;; from (IN z (CCINT lo hi)) in context, land and split the three atoms.
(define (ix-ccint-parts! z lo hi)
  (dk-have! (list 'AND (list 'IN z 'RR) (list 'AND (list '<= lo z) (list '<= z hi)))
    (lambda () (fact 'ccint-membership lo hi z) (prop)))
  (dk-split-all!))

;;; the goal (IN z (CCINT lo hi)): unfold and close each conjunct, the typing
;;; from the context and the two inequalities from PREMS by the oracle.
(define (ix-ccint-goal! prems)
  (mac 'ccint-membership)
  (dk-conj-close!
   (lambda () (if (eq? (car (dk-goal)) 'IN) (ass) (apply dk-ineq! prems)))))

;;; the local-extremum universal, discriminated on the ABS it contains.
(define (ix-window-univ)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'ABS)))
           "the local extremum window universal"))

;;; ---------------------------------------------------------------------
;;; THE COMMON DRIVER.  PRED is IS-LOCAL-MAX-AT or IS-LOCAL-MIN-AT, THM the
;;; matching total-function theorem, and SIDE builds the conclusion of the
;;; universal that THM asks for, from the two applied terms.
;;; ---------------------------------------------------------------------
(define (ix-fermat! pred thm side)
  (dk-peel!)
  (ix-ooint-parts! 'theta 'a 'b)
  (dk-have! '(< a b)
    (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(IN theta RR) '(< a theta) '(< theta b))))
  (dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
  ;; open the local extremum: the FUN typing, theta in [a,b], the radius
  (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f '(CCINT a b) 'theta)))))
  (let ((al (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius existential"))))
    (fact 'rr-pos-rr-in-rr al)
    (fact 'rr-lt-of-pos-rr al)
    ;; w = min(alpha, theta - a, b - theta) > 0, and h = w/2
    (fact 'rr-sub-in-rr 'theta 'a)
    (fact 'rr-sub-in-rr 'b 'theta)
    (dk-have! '(< 0 (- theta a))
      (lambda () (dk-ineq! '(IN a RR) '(IN theta RR) '(< a theta))))
    (dk-have! '(< 0 (- b theta))
      (lambda () (dk-ineq! '(IN b RR) '(IN theta RR) '(< theta b))))
    (let* ((w1 (dk-skolem! (dk-fact! 'rr-min-pos al '(- theta a))))
           (w  (dk-skolem! (dk-fact! 'rr-min-pos w1 '(- b theta)))))
      (fact 'rr-pos-rr-of-lt w)
      (let* ((h  (dk-halve! w))
             (ap (list '- 'theta h))
             (bp (list '+ 'theta h))
             ;; every atom the oracle needs about the three radii
             (base (list (list '= (list '+ h h) w) (list '<= w w1)
                         (list '<= w1 al) (list '<= w1 '(- theta a))
                         (list '<= w '(- b theta)) (list '< 0 h)
                         (list 'IN h 'RR) (list 'IN w 'RR) (list 'IN w1 'RR)
                         (list 'IN al 'RR) '(IN a RR) '(IN b RR) '(IN theta RR))))
        (fact 'rr-sub-in-rr 'theta h)
        (fact 'rr-add-in-rr 'theta h)
        (dk-have! (list '< 'a ap) (lambda () (apply dk-ineq! base)))
        (dk-have! (list '< bp 'b) (lambda () (apply dk-ineq! base)))
        (dk-have! (list '< ap 'theta) (lambda () (apply dk-ineq! base)))
        (dk-have! (list '< 'theta bp) (lambda () (apply dk-ineq! base)))
        ;; the extension: a function on the line, differentiable at theta
        (fact 'extend-const-in-fun 'a 'b 'f)
        (fact 'extend-const-deriv-fwd 'a 'b 'f 'theta 'l)
        (fact 'extend-const-ccint-fixes 'a 'b 'theta 'f)
        ;; the extremum of the EXTENSION on the small interval
        (let ((univ (ix-window-univ)))
          (dk-have!
           (list 'FORALL 'x
                 (list 'IMPLIES (list 'IN 'x (list 'CCINT ap bp))
                       (side (list ix-ext 'x) (list ix-ext 'theta))))
           (lambda ()
             (let ((z (dk-di-var!)))
               (ix-ccint-parts! z ap bp)
               (fact 'rr-sub-in-rr z 'theta)
               (dk-have! (list 'IN z '(CCINT a b))
                 (lambda ()
                   (ix-ccint-goal!
                    (append base (list (list 'IN z 'RR) (list '< 'a ap) (list '< bp 'b)
                                       (list '<= ap z) (list '<= z bp))))))
               (dk-have! (list '<= (list 'ABS (list '- z 'theta)) al)
                 (lambda ()
                   (fact 'rr-abs-bound (list '- z 'theta) al)
                   (dk-have! (list 'AND (list '<= (list '- al) (list '- z 'theta))
                                   (list '<= (list '- z 'theta) al))
                     (lambda ()
                       (dk-conj-close!
                        (lambda ()
                          (apply dk-ineq!
                                 (append base (list (list 'IN z 'RR) (list '<= ap z)
                                                    (list '<= z bp))))))))
                   (prop)))
               (dk-apply! univ z)
               (fact 'extend-const-ccint-fixes 'a 'b z 'f)
               (subst (list '== (list ix-ext z) (list 'f z)))
               (subst (list '== (list ix-ext 'theta) '(f theta)))
               (ass))))
          ;; interior-max/min-deriv-zero, with its conjunctive antecedent built
          (dk-have! (list 'AND (list 'IN ix-ext '(FUN RR RR))
                          (list 'AND (list 'IN ap 'RR)
                                (list 'AND (list 'IN bp 'RR)
                                      (list 'AND '(IN theta RR)
                                            (list 'AND (list '< ap 'theta)
                                                  (list '< 'theta bp))))))
            (lambda () (dk-conj-close! (lambda () (ass)))))
          (fact thm ix-ext ap bp 'theta 'l)
          (ass))))))

;;; =====================================================================
;;; 2.10 -- AN INTERIOR LOCAL MAXIMUM OF A DIFFERENTIABLE FUNCTION ON [a, b]
;;; HAS DERIVATIVE ZERO.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], forall([f, theta in ooint(a,b), l],
   is-local-max-at(f, ccint(a,b), theta) implies
   has-deriv-at(f, theta, l) implies
   l = 0))"))
(ix-fermat! 'IS-LOCAL-MAX-AT 'interior-max-deriv-zero
            (lambda (fz ft) (list '<= fz ft)))
(qed 'interval-local-max-deriv-zero)
(topic! 'interval-local-max-deriv-zero 'analysis)
(alias! 'interval-local-max-deriv-zero
        "at an interior local maximum of a function on a closed interval the derivative is zero")

;;; =====================================================================
;;; 2.10 -- THE SAME AT A LOCAL MINIMUM.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], forall([f, theta in ooint(a,b), l],
   is-local-min-at(f, ccint(a,b), theta) implies
   has-deriv-at(f, theta, l) implies
   l = 0))"))
(ix-fermat! 'IS-LOCAL-MIN-AT 'interior-min-deriv-zero
            (lambda (fz ft) (list '<= ft fz)))
(qed 'interval-local-min-deriv-zero)
(topic! 'interval-local-min-deriv-zero 'analysis)
(alias! 'interval-local-min-deriv-zero
        "at an interior local minimum of a function on a closed interval the derivative is zero")
