;;; nvs-taylor-proof.scm -- Taylor's theorem with remainder bound for a map
;;; between two finite-dimensional real normed vector spaces.  PROVED.
;;;
;;; It stood as a STATEMENT ONLY (nvs-taylor-statement.scm, 2026-07-22), an
;;; asserted `support' warranted `reference' to Dieudonne 8.14.3, with a
;;; `rests-on' edge recording the intended reduction.  This file carries that
;;; reduction out, so the Dieudonne citation is discharged: nothing is asserted
;;; here, and the bill is the curve theorem's own leaves plus the typing
;;; supports the reduction needs.
;;;
;;; THE MODELLING (unchanged, and it is why the proof is short).  Rather than a
;;; multilinear-derivative apparatus -- D^k f(a) as a k-linear map, an operator
;;; norm, a segment sup -- restrict f to the line through a in direction h:
;;;
;;;     phi(t) = f( a (+) t.h )   :  RR -> VEC(cm),
;;;
;;; already a curve in the library's sense, and phi^(k)(0) = D^k f(a).h^k, so
;;; TAYLOR-POLY-V(cm, phi, 0, 1, n) IS the multivariable Taylor polynomial.
;;; This is Dieudonne's own reduction and how multivariable Taylor is usually
;;; taught.  Crucially the hypothesis TAYLOR-DIFFERENTIABLE-V is stated OF PHI,
;;; so no chain rule is owed -- the statement was written to make that true.
;;;
;;; THE PROOF is `vector-taylor-remainder-bound' (vector-taylor-proof.scm) at
;;; m := cm, f := phi, a := 0, x := 1.  Three things then separate the two:
;;;
;;;   (1) phi must be typed: phi in FUN(RR, VEC cm).  This is `seg-curve-in-fun'
;;;       (directional-derivative.scm:475) with codomain VEC(cm) instead of RR --
;;;       the SAME three citations, since SEG-CURVE(m,f,a,eta) unfolds to exactly
;;;       this lambda.  Not reused directly only because that lemma fixes the
;;;       codomain to RR.
;;;   (2) the curve theorem concludes about phi(1); the statement writes
;;;       f(a (+) h).  Beta-reduce and apply the unital law 1.h = h.
;;;   (3) the curve theorem's bound carries a factor (x-a)^(n+1) = (1-0)^(n+1),
;;;       which is 1.  Nothing in the tree said 1^k = 1, so `rr-power-one' is
;;;       proved here by induction off power-zero / power-succ.
;;;
;;; IS-FINITE-DIMENSIONAL(dm) is never used -- only cm's is.  It stays in the
;;; statement to match Dieudonne.
;;;
;;; MECHANICS, and (2) is the one worth keeping.  The natural move is to rewrite
;;; the GOAL: prove f(a(+)h) = phi(1) and `subst' it.  That route ends at
;;; `rfl' on  f(a(+)h) = f(a(+)h)  and REFUSES -- `=' is partial, so that is a
;;; DEFINEDNESS claim about an application, which reflexivity will not grant
;;; (primitive-inferences.scm:578 says so: "there needs a proof (e.g. via
;;; (IN t S))").  Rewriting the HYPOTHESIS instead avoids the question entirely:
;;; `lam-b-h' beta-reduces phi(1) in place, and `mac-h' with `nvs-act-one' --
;;; which is stated pre-composed, vadd(m)(y, act(m)(1,x)) = vadd(m)(y,x), the
;;; exact shape in hand -- finishes it, spawning no side conditions.  Same for
;;; the factor, via the shim below.

;;; The directional curve  phi(t) = f(a (+) t.h), and the remainder vector.
;;; Spliced rather than repeated: the term occurs five times below.
(define nt-phi '(VNB-LAMBDA t RR (f ((VADD dm) a ((ACT dm) t h)))))
(define nt-remainder
  `((VADD cm) (f ((VADD dm) a h))
              ((VNEG cm) (TAYLOR-POLY-V cm ,nt-phi 0 1 n))))

(define (nt-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (nt-open)
  (filter (lambda (s) (null? (sequent-node-in-arrows s))) (proof-open-goals *ps*)))
(define (nt-peel!)
  (let loop ((k 20))
    (let ((before (nt-goal)))
      (when (and (> k 0) (memq (car before) '(FORALL IMPLIES)))
        (di)
        (if (equal? (nt-goal) before)
            (error "nvs-taylor: di made no progress on" before)
            (loop (- k 1)))))))

;;; -----------------------------------------------------------------------
;;; rr-power-one -- 1^k = 1.  Nothing in the tree stated it: the RR power
;;; results are power-zero-succ / power-in-rr / power-two-pos, none of them this.
;;; `power' is axiomatised by power-zero and power-succ (number-systems.scm:839),
;;; so it is an ordinary NN induction.  Both axioms carry CONJUNCTIVE
;;; antecedents, so each `fact' wants its AND landed first (CLAUDE.md).
;;; -----------------------------------------------------------------------

(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN) (= (power 1 k_) 1)))))
(ni)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (nt-goal)) 'FORALL)
       (begin                                   ; step
         (di) (di)
         (have! '(IN 1 CC) (lambda () (arith)))
         (have! '(AND (IN 1 CC) (IN k_ NN)) (lambda () (prop)))
         (fact 'power-succ 1 'k_)
         (subst '(= (power 1 (succ k_)) (* 1 (power 1 k_))))
         (subst '(= (power 1 k_) 1))
         (arith))
       (begin                                   ; base
         (have! '(IN 1 CC) (lambda () (arith)))
         (fact 'power-zero 1)
         (ass))))
 (nt-open))
(qed 'rr-power-one)
(topic! 'rr-power-one 'analysis)

;;; -----------------------------------------------------------------------
;;; nt-unit-factor -- the shim that clears the curve theorem's (x-a)^(n+1).
;;; Stated so its LEFT-HAND SIDE is exactly the term the citation leaves in the
;;; hypothesis, which is what lets `mac-h' remove it in one step.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(y_ k_) '((IN y_ RR) (IN k_ NN))
                '(= (* y_ (power (- 1 0) (succ k_))) y_))))
(nt-peel!)
(have! '(= (- 1 0) 1) (lambda () (arith)))
(subst '(= (- 1 0) 1))
(have! '(IN (succ k_) NN) (lambda () (fact 'nn-succ-closed 'k_) (ass)))
(fact 'rr-power-one '(succ k_))
(subst '(= (power 1 (succ k_)) 1))
(crs)
(qed 'nt-unit-factor)
(topic! 'nt-unit-factor 'plumbing)

;;; -----------------------------------------------------------------------
;;; nvs-taylor-remainder-bound.
;;; -----------------------------------------------------------------------

(sp (make-wff (forall-guarded '(dm cm f a h n)
  (list
    '(IS-NORMED-VECTOR-SPACE dm)
    '(IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE dm))
    '(IS-NORMED-VECTOR-SPACE cm)
    '(IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE cm))
    '(IN f (FUN (VEC dm) (VEC cm)))
    '(IN a (VEC dm))
    '(IN h (VEC dm))
    '(IN n NN)
    `(TAYLOR-DIFFERENTIABLE-V cm ,nt-phi 0 1 n))
  `(FORSOME theta
     (AND (< 0 theta)
     (AND (< theta 1)
       (<= (* (FACTORIAL (succ n)) ((VNRM cm) ,nt-remainder))
           ((VNRM cm) ((NTH-DERIV-V cm ,nt-phi (succ n)) theta)))))))))
(nt-peel!)

;;; (1) phi is a curve.  seg-curve-in-fun's proof, at codomain VEC(cm).
(have! (list 'IN nt-phi '(FUN RR (VEC cm)))
  (lambda ()
    (dk-lam-t!)                                  ; closes RR in SET, leaves the typing
    (let ((tv (cadr (car (dk-landed (lambda () (di)))))))
      (fact 'nvs-act-in-vec  'dm tv 'h)
      (fact 'nvs-vadd-in-vec 'dm 'a (list '(ACT dm) tv 'h))
      (fact 'fun-apply-type-c 'f '(VEC dm) '(VEC cm)
            (list '(VADD dm) 'a (list '(ACT dm) tv 'h)))
      (ass))))

;;; (2) cite the curve theorem.  Its first antecedent is one seven-fold AND, so
;;; it is assembled and landed whole; the ground facts go in first, because
;;; `prop' decides the conjunction from the context and cannot invent 0 < 1.
(have! '(< 0 1)   (lambda () (arith)))
(have! '(IN 0 RR) (lambda () (arith)))
(have! '(IN 1 RR) (lambda () (arith)))
(have! (conjuncts->and
        (list '(IS-NORMED-VECTOR-SPACE cm)
              '(IS-FINITE-DIMENSIONAL (NORMED-VECTOR-SPACE-AS-MODULE cm))
              (list 'IN nt-phi '(FUN RR (VEC cm)))
              '(IN 0 RR) '(IN 1 RR) '(IN n NN) '(< 0 1)))
  (lambda () (prop)))
(fact 'vector-taylor-remainder-bound 'cm nt-phi 0 1 'n)

;;; (3) skolemize, then rewrite the LANDED INEQUALITY into the goal's shape.
(dk-split! (car (filter (lambda (x) (and (pair? x) (eq? (car x) 'FORSOME))) (dk-asms))))

(define nt-theta
  (caddr (car (filter (lambda (x) (and (pair? x) (eq? (car x) '<) (equal? (cadr x) 0)))
                      (dk-asms)))))
(define (nt-ineq)
  (car (filter (lambda (x) (and (pair? x) (eq? (car x) '<=))) (dk-asms))))

(lam-b-h (nt-ineq))                              ; phi(1) -> f(a (+) 1.h)
(mac-h 'nvs-act-one (nt-ineq))                   ; 1.h -> h, pre-composed with VADD

;; the factor.  nt-unit-factor is guarded on `y_ in RR', so land that first.
(have! '(IN (succ n) NN) (lambda () (fact 'nn-succ-closed 'n) (ass)))
(fact 'nth-deriv-v-in-vec 'cm nt-phi '(succ n) nt-theta)
(fact 'vnrm-real 'cm (list (list 'NTH-DERIV-V 'cm nt-phi '(succ n)) nt-theta))
(mac-h 'nt-unit-factor (nt-ineq))

(ew nt-theta)
(prop)                                           ; the three conjuncts are all in context

(if (proof-done? *ps*)
    (qed 'nvs-taylor-remainder-bound)
    (begin
      (display "\n*** nvs-taylor-remainder-bound did NOT close.  Open goals:\n")
      (for-each (lambda (l)
                  (display "   GOAL: ")
                  (display (expression->string (wff-formula (sequent-node-assertion l))))
                  (newline))
                (nt-open))
      (error "nvs-taylor-remainder-bound: unfinished")))
(topic! 'nvs-taylor-remainder-bound 'analysis)
