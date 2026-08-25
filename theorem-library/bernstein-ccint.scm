;;; bernstein-ccint.scm -- THEOREM 5.2 of docs/calculus.pdf moved off [0,1] and
;;; onto an arbitrary nondegenerate [a,b], by the affine change of variable
;;;
;;;     A(t) = a + (b-a) t   :  [0,1] -> [a,b]
;;;     U(x) = (x-a)/(b-a)   :  [a,b] -> [0,1]
;;;
;;; RUNG 3(a) of the integration arc.  bernstein-density.scm proves the density
;;; theorem on the unit interval and nowhere else; c-int is wanted on [a,b], so
;;; this is the transfer.
;;;
;;; THE STATEMENT IS WRITTEN OUT WITH `abs', not with CONVERGES-UNIFORMLY.  That
;;; predicate (ascoli-arzela-statement.scm:94) demands
;;; `seq in FUN(NN, FUN(PTS s, RR))' for a METRIC SPACE s, and CCINT(a,b) is not
;;; one in this tree: there is no metric subspace structure, and building one is
;;; a foundational decision several proofs are waiting on.  So the uniform
;;; hypothesis is spelled out -- one threshold `cap_' serving every n_ >= cap_
;;; and every x_ of the interval -- exactly as uniform-continuity-ccint.scm,
;;; ccint-abs-bounded.scm and bernstein-density.scm spell it out.
;;;
;;; WHAT THE TRANSFER COSTS, in full: five lemmas, and none of them is analysis.
;;;
;;;   ccint-parts         the FORWARD reading of ccint-membership (below).
;;;   ccint-affine-in     A carries [0,1] into [a,b].  The one step `ineq' cannot
;;;                       take on its own is that (b-a)t and (b-a)(1-t) SUM to
;;;                       (b-a) -- two products of non-constant factors are two
;;;                       unrelated opaque atoms to it -- so that identity goes
;;;                       in by `crs' first, and then one Farkas certificate
;;;                       closes each endpoint.
;;;   ccint-coaffine-in   U carries [a,b] into [0,1].  Here the reciprocal
;;;                       enters, and it enters ONLY through rr-recip-inverse:
;;;                       (x-a) <= (b-a) scaled by the nonnegative recip(b-a),
;;;                       whose right-hand side is (b-a)recip(b-a) = 1.  Every
;;;                       reordering of a product is an EXPLICIT `crs' identity
;;;                       substituted into the goal, because `ineq' does not
;;;                       normalise monomials: u.recip(v) and recip(v).u are
;;;                       different atoms and neither is a linear consequence of
;;;                       the other.
;;;   ccint-affine-inverse   A(U(x)) = x.  Two `subst's: expose the product
;;;                       (b-a)recip(b-a), replace it by 1, and `crs'.
;;;   affine-continuous-at   x |-> c + lam x is continuous everywhere.  Free:
;;;                       `deriv-affine' (directional-derivative.scm) gives its
;;;                       derivative at every point and `diff-implies-continuous'
;;;                       does the rest.  No epsilon-delta argument is written.
;;;
;;; A TRAP THIS FILE PAID FOR, worth stating once.  `contra--usable-indices' --
;;; the premise list `ineq' is handed -- accepts an EQUATION, an `=' being
;;; arithmetic in shape.  In lemma 1 that is exactly what is wanted: the whole
;;; content there IS an equation.  In lemma 2 the equation (b-a)recip(b-a) = 1
;;; contributes the ATOM (b-a).recip(b-a), a product of two non-constant factors,
;;; which `ineq' treats as opaque and refuses unless the context certifies it
;;; real -- and ONE such premise makes the whole call fail with "goal not a
;;; linear-RR consequence", blaming the goal.  The fix is not to filter the
;;; premise but to TYPE the atom: two `rr-mul-in-rr' citations, placed before the
;;; first `ineq'.
;;;
;;; Needs bernstein-density (bernstein-uniform-approximation), ccint-basics
;;; (ccint-membership), directional-derivative (deriv-affine, affine-lam-in-fun),
;;; differentiation (diff-implies-continuous), continuity-compose
;;; (compose-continuous-at), compose-apply-proof (compose-apply, compose-type),
;;; rr-order-basics, binary-minus-laws (rr-sub-in-rr) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `bc-' prefix) ----------------------

(define bc-r '(recip (- b a)))

;; Fourier-Motzkin over the context's order facts and equations.  The indices
;; are computed HERE and not taken from `contra--usable-indices': `contra' is
;; copilot machinery and loads after theorem-library, so a library proof that
;; cited it would invert the dependency (the same rule load.scm states for
;; `preamble').
;;
;; Equations are INCLUDED, and that is deliberate: lemma 1's whole content is
;; the equation (b-a)t + (b-a)(1-t) = (b-a), which `ineq' cannot discover for
;; itself -- it treats each product of two non-constant factors as one opaque
;; atom.  The price is that every atom of every named premise must be certified
;; real, or the call fails with "goal not a linear-RR consequence" and blames
;; the goal; hence the `rr-mul-in-rr' citations that type those products before
;; the first `ineq' in each lemma below.
(define (bc-order-indices)
  (let loop ((l (dk-asms)) (k 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ k 1) (cons k acc)))
          (else (loop (cdr l) (+ k 1) acc)))))

(define (bc-ineq!) (apply ineq (bc-order-indices)))

;; `di' splits a conjunctive GOAL one level per call.  Split every AND leaf.
(define (bc-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

;; the three conjuncts of a CCINT membership, landed FORWARD and leaving the
;; membership itself in place
(define (bc-of-ccint! v lo hi)
  (dk-split! (dk-fact! 'ccint-parts lo hi v)))

;; rewrite the goal's term u into the crs-equal term w
(define (bc-rw! u w)
  (have! (list '= u w) (lambda () (crs)))
  (subst (list '= u w)))

(define (bc-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; `have!' of a formula the context ALREADY carries is a self-loop, and `have!'
;; says so and stops ("no main branch").  The AND antecedents below are wanted
;; in several branches and are sometimes inherited; ask first.
(define (bc-need! f)
  (if (not (member f (dk-asms))) (have! f)))

;;; =====================================================================
;;; 0.  ccint-parts -- the FORWARD reading of ccint-membership.
;;;
;;; ccint-membership is an IFF, hence a macete, and the only way to use it on a
;;; HYPOTHESIS is `mac-h' -- which REPLACES that hypothesis, so a proof that
;;; needs both `x in [a,b]' and its three consequences loses one of them.  The
;;; standard dodge is to unfold inside a `have!' lane; a single forward theorem
;;; is cheaper, and every use below is then an ordinary `fact'.
;;;
;;; Its binders are lo_/hi_/pt_ rather than a/b/x_ so that no citation below
;;; instantiates a binder at a variable of the same name; nothing observed here
;;; requires that, it is simply one fewer thing to wonder about when a `fact'
;;; lands nothing.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    '(FORALL lo_ (FORALL hi_ (FORALL pt_ (IMPLIES (IN pt_ (CCINT lo_ hi_))
       (AND (IN pt_ RR) (AND (<= lo_ pt_) (<= pt_ hi_)))))))))
  (dk-peel-to! 'AND)
  (mac-h 'ccint-membership '(IN pt_ (CCINT lo_ hi_)))
  (ass)))
(qed 'ccint-parts)
(topic! 'ccint-parts 'analysis)
(alias! 'ccint-parts "the three conjuncts of membership in [a,b], read forward")

;;; =====================================================================
;;; 1.  A(t) = a + (b-a)t carries [0,1] into [a,b].
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    '(FORALL a (FORALL b (FORALL t_ (IMPLIES (AND (IN a RR) (AND (IN b RR) (< a b)))
       (IMPLIES (IN t_ (CCINT 0 1))
         (IN (+ a (* (- b a) t_)) (CCINT a b)))))))))
  (dk-peel-to! 'IN)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (bc-of-ccint! 't_ 0 1)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'rr-sub-in-rr 1 't_)
  (fact 'rr-lt-diff-pos 'a 'b)
  (fact 'rr-lt-implies-le 0 '(- b a))
  (have! '(<= 0 (- 1 t_)) (lambda () (bc-ineq!)))
  (have! '(AND (IN (- b a) RR) (IN t_ RR)))
  (have! '(AND (<= 0 (- b a)) (<= 0 t_)))
  (fact 'rr-leq-mul-nonneg '(- b a) 't_)
  (fact 'rr-mul-in-rr '(- b a) 't_)
  (have! '(AND (IN (- b a) RR) (IN (- 1 t_) RR)))
  (have! '(AND (<= 0 (- b a)) (<= 0 (- 1 t_))))
  (fact 'rr-leq-mul-nonneg '(- b a) '(- 1 t_))
  (fact 'rr-mul-in-rr '(- b a) '(- 1 t_))
  ;; the identity `ineq' cannot see: the two products exhaust (b-a).
  (have! '(= (+ (* (- b a) t_) (* (- b a) (- 1 t_))) (- b a)) (lambda () (crs)))
  (fact 'rr-add-in-rr 'a '(* (- b a) t_))
  (mac 'ccint-membership)
  (bc-split-goal!)
  (for-each (lambda (nd) (dk-focus! nd)
              (if (eq? (car (dk-goal-of nd)) 'IN) (ass) (bc-ineq!)))
            (proof-leaves))))
(qed 'ccint-affine-in)
(topic! 'ccint-affine-in 'analysis)
(alias! 'ccint-affine-in "t |-> a + (b-a)t carries [0,1] into [a,b]")

;;; =====================================================================
;;; 2.  U(x) = (x-a) recip(b-a) carries [a,b] into [0,1].
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x_
      (list 'IMPLIES '(AND (IN a RR) (AND (IN b RR) (< a b)))
        (list 'IMPLIES '(IN x_ (CCINT a b))
          (list 'IN (list '* '(- x_ a) bc-r) '(CCINT 0 1)))))))))
  (dk-peel-to! 'IN)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (bc-of-ccint! 'x_ 'a 'b)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'rr-sub-in-rr 'x_ 'a)
  (fact 'rr-lt-diff-pos 'a 'b)
  (fact 'rr-pos-ne-zero '(- b a))
  (have! '(AND (IN (- b a) RR) (NOT (= (- b a) 0))))
  (fact 'rr-recip-closed '(- b a))
  (fact 'rr-recip-pos '(- b a))
  (fact 'rr-recip-inverse '(- b a))
  (fact 'rr-lt-implies-le 0 bc-r)
  (have! (list '= (list '* bc-r '(- b a)) 1)
    (lambda () (bc-rw! (list '* bc-r '(- b a)) (list '* '(- b a) bc-r)) (ass)))
  (have! (list '= 1 (list '* bc-r '(- b a)))
    (lambda () (fact 'eq-sym (list '* bc-r '(- b a)) 1) (ass)))
  ;; the product atoms the two equations above put into every later `ineq' call
  (fact 'rr-mul-in-rr bc-r '(- b a))
  (fact 'rr-mul-in-rr '(- b a) bc-r)
  (have! '(<= 0 (- x_ a)) (lambda () (bc-ineq!)))
  (have! '(<= (- x_ a) (- b a)) (lambda () (bc-ineq!)))
  ;; 0 <= (x-a).recip(b-a)
  (have! (list 'AND '(IN (- x_ a) RR) (list 'IN bc-r 'RR)))
  (have! (list 'AND '(<= 0 (- x_ a)) (list '<= 0 bc-r)))
  (fact 'rr-leq-mul-nonneg '(- x_ a) bc-r)
  (fact 'rr-mul-in-rr '(- x_ a) bc-r)
  ;; (x-a).recip(b-a) <= 1, by scaling (x-a) <= (b-a) with the nonnegative recip
  (have! (list 'AND (list '<= 0 bc-r) '(<= (- x_ a) (- b a))))
  (fact 'rr-le-scale-nonneg bc-r '(- x_ a) '(- b a))
  (mac 'ccint-membership)
  (bc-split-goal!)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (let ((g (dk-goal)))
       (cond ((eq? (car g) 'IN) (ass))
             ((equal? (cadr g) 0) (ass))             ; the lower bound, landed above
             (else                                   ; the upper bound
              (bc-rw! (list '* '(- x_ a) bc-r) (list '* bc-r '(- x_ a)))
              (subst (list '= 1 (list '* bc-r '(- b a))))
              (ass)))))
   (proof-leaves))))
(qed 'ccint-coaffine-in)
(topic! 'ccint-coaffine-in 'analysis)
(alias! 'ccint-coaffine-in "x |-> (x-a)/(b-a) carries [a,b] into [0,1]")

;;; =====================================================================
;;; 3.  A(U(x)) = x.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x_
      (list 'IMPLIES '(AND (IN a RR) (AND (IN b RR) (AND (< a b) (IN x_ RR))))
        (list '= (list '+ 'a (list '* '(- b a) (list '* '(- x_ a) bc-r))) 'x_)))))))
  (dk-peel-to! '=)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (AND (< a b) (IN x_ RR)))))
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'rr-sub-in-rr 'x_ 'a)
  (fact 'rr-lt-diff-pos 'a 'b)
  (fact 'rr-pos-ne-zero '(- b a))
  (have! '(AND (IN (- b a) RR) (NOT (= (- b a) 0))))
  (fact 'rr-recip-closed '(- b a))
  (fact 'rr-recip-inverse '(- b a))
  (bc-rw! (list '+ 'a (list '* '(- b a) (list '* '(- x_ a) bc-r)))
          (list '+ 'a (list '* (list '* '(- b a) bc-r) '(- x_ a))))
  (subst (list '= (list '* '(- b a) bc-r) 1))
  (crs)))
(qed 'ccint-affine-inverse)
(topic! 'ccint-affine-inverse 'analysis)
(alias! 'ccint-affine-inverse "a + (b-a)((x-a)/(b-a)) = x")

;;; =====================================================================
;;; 4.  The affine map is continuous everywhere -- from its DERIVATIVE, not
;;; from an epsilon-delta argument.
;;; =====================================================================

(quietly (lambda ()
  (sp (make-wff
    '(FORALL c (FORALL lam (FORALL t_ (IMPLIES (AND (IN c RR) (AND (IN lam RR) (IN t_ RR)))
       (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (+ c (* lam x))) t_)))))))
  (dk-peel-to! 'IS-CONTINUOUS-AT)
  (fact 'deriv-affine 'c 'lam 't_)
  (fact 'diff-implies-continuous '(VNB-LAMBDA x RR (+ c (* lam x))) 't_ 'lam)
  (ass)))
(qed 'affine-continuous-at)
(topic! 'affine-continuous-at 'analysis)
(alias! 'affine-continuous-at "x |-> c + lam.x is continuous at every point")

;;; =====================================================================
;;; 5.  THE TRANSFER ITSELF.
;;;
;;;   f continuous on [a,b],  a < b,  eps > 0
;;;      ==>  there is a threshold cap such that for every n >= cap and every
;;;           x of [a,b],   | f(x) - B_n(f o A)(U(x)) |  <=  eps.
;;;
;;; Three citations and no estimate: the composite f o A is continuous on [0,1]
;;; (compose-continuous-at, with ccint-affine-in putting A(t) inside the interval
;;; where f's continuity is assumed), Theorem 5.2 applies to it there, and at a
;;; point x of [a,b] the value (f o A)(U(x)) is f(x) -- compose-apply to strip
;;; the COMPOSE, one beta to strip the lambda, ccint-affine-inverse to collapse
;;; A(U(x)).
;;;
;;; The approximant named in the conclusion is BERNSTEIN-POLY(f o A, n, U(x)),
;;; a Bernstein polynomial IN THE UNIT COORDINATE.  It is NOT claimed here to be
;;; a polynomial in x -- that would need the binomial expansion of (1-U(x))^(n-l)
;;; and a re-indexing, and nothing in the tree does it.  See the note at the end
;;; of the file.
;;; =====================================================================

(define bc-aff '(VNB-LAMBDA x RR (+ a (* (- b a) x))))
(define bc-g   (list 'COMPOSE 'fn_ bc-aff))
(define bc-u   '(* (- x_ a) (recip (- b a))))

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'fn_ (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'ep_
      (list 'IMPLIES '(IN fn_ (FUN RR RR))
      (list 'IMPLIES '(AND (IN a RR) (AND (IN b RR) (< a b)))
      (list 'IMPLIES '(FORALL x_ (IMPLIES (IN x_ (CCINT a b))
                         (IS-CONTINUOUS-AT RR-MS RR-MS fn_ x_)))
      (list 'IMPLIES '(POS-RR ep_)
        (list 'FORSOME 'cap_ (list 'AND '(IN cap_ NN)
          (list 'FORALL 'n_ (list 'IMPLIES '(AND (IN n_ NN) (<= cap_ n_))
            (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (CCINT a b))
              (list '<= (list 'abs (list '- '(fn_ x_)
                                         (list 'BERNSTEIN-POLY bc-g 'n_ bc-u)))
                    'ep_)))))))))))))))))
  (dk-peel-to! 'FORSOME)
  (dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'rr-is-set)
  (have! '(AND (IN a RR) (IN (- b a) RR)))
  (fact 'affine-lam-in-fun 'a '(- b a))
  (bc-need! (list 'AND (list 'IN bc-aff '(FUN RR RR)) '(IN fn_ (FUN RR RR))))
  (fact 'compose-type 'RR 'RR 'RR 'fn_ bc-aff)

  ;; f's continuity hypothesis, taken on its CONSEQUENT rather than on a symbol
  ;; it contains: several universals about IS-CONTINUOUS-AT arrive later.
  (define bc-cont
    (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                  (dk-contains? z 'IS-CONTINUOUS-AT)))
                 (dk-asms))))

  ;; f o A is continuous at every point of [0,1]
  (have! (list 'FORALL 't_ (list 'IMPLIES '(IN t_ (CCINT 0 1))
           (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS bc-g 't_)))
    (lambda ()
      (let ((v (bc-di-var!)))
        (bc-of-ccint! v 0 1)
        ;; affine-continuous-at's antecedent is a three-way AND, which `fact'
        ;; will not split: without it the citation lands the IMPLICATION and the
        ;; composition below then lands another one, silently.
        (bc-need! (list 'AND '(IN a RR) (list 'AND '(IN (- b a) RR) (list 'IN v 'RR))))
        (fact 'affine-continuous-at 'a '(- b a) v)
        (bc-need! '(AND (IN a RR) (AND (IN b RR) (< a b))))
        (fact 'ccint-affine-in 'a 'b v)
        (inst+ bc-cont (list '+ 'a (list '* '(- b a) v)))
        (have! (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS 'fn_ (list bc-aff v))
          (lambda () (lam-b) (ass)))
        (fact 'compose-continuous-at 'fn_ bc-aff v)
        (ass))))

  ;; Theorem 5.2 on the unit interval, for the composite
  (fact 'bernstein-uniform-approximation bc-g 'ep_)
  (dk-ai-head! 'FORSOME)                       ; skolemize the threshold
  (let* ((bod (car (dk-asms)))                 ; (AND (IN cap NN) (FORALL ...))
         (cap (cadr (cadr bod)))
         (uni (caddr bod)))
    (dk-split! bod)
    (ew cap)
    (di)
    (for-each
     (lambda (nd)
       (dk-focus! nd)
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (begin
             (di)                                          ; peel FORALL n_ ...
             (let ((nv (cadr (cadr (cadr (dk-goal))))))     ; ... reading n_ off the guard
             (dk-split! (dk-landed-1 (lambda () (di))))     ; ... then landing that guard
             (let* ((v  (bc-di-var!))                       ; x_ in [a,b]
                    (uu (list '* (list '- v 'a) '(recip (- b a))))
                    (gt (list bc-g uu)))
               (bc-of-ccint! v 'a 'b)
               (bc-need! '(AND (IN a RR) (AND (IN b RR) (< a b))))
               (fact 'ccint-coaffine-in 'a 'b v)
               (bc-of-ccint! uu 0 1)               ; U(x) is a real, which both
                                                   ; compose-apply and `lam-b' need
               (bc-need! '(AND (IN a RR) (AND (IN b RR) (AND (< a b) (IN x_ RR)))))
               (fact 'ccint-affine-inverse 'a 'b v)
               (fact 'fun-apply-type-c 'fn_ 'RR 'RR v)
               (bc-need! (list 'AND (list 'IN bc-aff '(FUN RR RR)) '(IN fn_ (FUN RR RR))))
               (fact 'compose-apply 'RR 'RR 'RR 'fn_ bc-aff uu)
               ;; f(x) IS (f o A)(U(x))
               (have! (list '= (list 'fn_ v) gt)
                 (lambda ()
                   (subst (list '= gt (list 'fn_ (list bc-aff uu))))
                   (lam-b)
                   (subst (list '= (list '+ 'a (list '* '(- b a) uu)) v))
                   (rfl)))
               (subst (list '= (list 'fn_ v) gt))
               ;; ... and the [0,1] estimate, read at n and at U(x), IS the goal
               (let ((h1 (dk-deepest (lambda () (inst+ uni nv)))))
                 (dk-deepest (lambda () (inst+ h1 uu))))
               (ass))))))
     (proof-leaves)))))
(qed 'bernstein-uniform-approximation-ccint)
(topic! 'bernstein-uniform-approximation-ccint 'analysis)
(alias! 'bernstein-uniform-approximation-ccint
        "Theorem 5.2 on [a,b]"
        "a continuous function on [a,b] is the uniform limit of the Bernstein polynomials of its unit-interval reparametrisation")

;;; =====================================================================
;;; WHAT THIS DOES NOT GIVE, AND IT IS THE RUNG'S REAL OBSTACLE.
;;;
;;; The assembly rung 3 is aiming at -- "every continuous function on [a,b] is
;;; antiderivable" -- needs the APPROXIMANTS to be antiderivable, and this file
;;; does not make them so.  BERNSTEIN-POLY(g,n,x) is
;;;
;;;     SUM_{l<succ n}  g(l/n) . C(n,l) . x^l . (1-x)^(n-l)
;;;
;;; and `poly-is-antiderivable' (theorem-library/antiderivative.scm) applies to
;;; the coefficient-lambda shape SUM_{k<m} a_k x^k and to nothing else.  Getting
;;; from one to the other is the binomial expansion of (1-x)^(n-l) followed by a
;;; re-indexing of the double sum, and NO part of that is in the tree: the
;;; binomial theorem is (`binomial-theorem'), but no theorem says a Bernstein
;;; basis polynomial equals a coefficient polynomial, and SERIES-PARTIAL-SUM has
;;; no reindexing law to carry the shift l |-> l+j.
;;;
;;; The alternative that avoids the expansion is the classical integration
;;; identity for the Bernstein basis,
;;;
;;;     d/dx  ( (1/(n+1)) SUM_{j=succ l}^{succ n} B_{j,succ n}(x) )  =  B_{l,n}(x)
;;;
;;; which the Pascal recurrence in bernstein-basis.scm makes reachable, but it is
;;; a telescoping-sum argument of its own size.  Either way it is a separate
;;; piece of work, and the estimate in this file is independent of it.
;;;
;;; UPDATE 2026-08-25.  The first paragraph above is no longer the obstacle, and
;;; neither of the two routes it names is needed.
;;;
;;; `series-partial-sum-antiderivable' (theorem-library/series-antiderivable.scm,
;;; `modulo 0') says that a SERIES-PARTIAL-SUM whose every summand is
;;; antiderivable is antiderivable.  It is not about polynomials -- it is Prop
;;; 4.8's two-term closure lifted to n terms by induction -- so there is nothing
;;; to convert: BERNSTEIN-POLY IS a SERIES-PARTIAL-SUM, with exactly the sum
;;; structure `poly-is-antiderivable' has, and the only question left is whether
;;; the SUMMAND  x |-> g(l/n) . B_{l,n}(x)  is antiderivable.
;;; `antiderivable-scale' peels the constant g(l/n) and leaves x |-> B_{l,n}(x).
;;;
;;; THAT is where the obstacle now sits, and it is one step earlier than the
;;; binomial expansion: THERE IS NO C(n,l) IN THE TREE AT ALL, and no closed
;;; form for the basis.  BERNSTEIN-BASIS is COMB-KK (binomial.scm), defined by
;;; the Pascal recursion on the degree, and binomial.scm states only that it is
;;; a total ZZ-indexed family and that it vanishes off 0..m.  So "peel the
;;; constant factor C(n,l), leaving x^l (1-x)^(n-l)" is not a move that exists.
;;;
;;; What DOES exist, proven and already on the RR surface, is the recurrence:
;;; `bernstein-basis-succ' (bernstein-moments.scm),
;;;
;;;     B_{k,succ n}(x)  =  x B_{k-1,n}(x)  +  (1 - x) B_{k,n}(x).
;;;
;;; An induction on n over "B_{k,n} is antiderivable" does NOT close on it: the
;;; antiderivable maps on [a,b] are a VECTOR SPACE and not an algebra, and the
;;; step multiplies by x.  The repair is to strengthen the hypothesis so that
;;; the multiplication stays inside it,
;;;
;;;     P(n):  for every k in ZZ and every j in NN,
;;;            x |-> x^j . B_{k,n}(x)  is antiderivable on [a,b],
;;;
;;; whose step is the recurrence multiplied through by x^j,
;;;
;;;     x^j B_{k,succ n}(x)  =  x^(succ j) B_{k-1,n}(x)
;;;                           + x^j B_{k,n}(x)  -  x^(succ j) B_{k,n}(x),
;;;
;;; i.e. three instances of P(n) combined by `antiderivable-add' and
;;; `antiderivable-sub' (antiderivative-transfer.scm, both `modulo 0'), and
;;; whose base is B_{k,0} = IF k = 0 THEN 1 ELSE 0 -- `power-antiderivable' or
;;; `zero-is-antiderivable' on a case split.  P(n) at j = 0 gives B_{k,n}
;;; itself.  No binomial expansion, no SERIES-PARTIAL-SUM reindexing law and no
;;; telescoping identity appears anywhere in it: every step is a vector-space
;;; move plus the recurrence.
;;;
;;; BUILT, 2026-08-25, in theorem-library/bernstein-antiderivable.scm.  P(n) is
;;; `bernstein-term-antiderivable' and the rung is `bernstein-poly-antiderivable';
;;; both bill {rr-is-normed-field, comb-kk-in-fun, comb-kk-null}, which is the
;;; Bernstein basis's own floor and nothing more.  The index ranges over NN, not
;;; ZZ: over ZZ the step would need "k not in NN implies k < 0", which this tree
;;; has no order to supply, while over NN the same boundary is `nn-zero-or-succ'
;;; -- excluded middle -- exactly as `bernstein-basis-nonneg' takes it.  The ZZ
;;; index arithmetic came to three facts: (- k 1) is an integer, it is negative
;;; when k is 0, and it is q when k is succ q (proved from `nn-succ-plus-one'
;;; plus one `crs' rather than cited from `bt-succ-minus-1', which is why that
;;; `well-known' support is in bernstein-basis-nonneg's bill and not in these).
;;; =====================================================================

;;; UPDATE 2026-08-25, second.  bernstein-antiderivable.scm settles
;;; x |-> BERNSTEIN-POLY(g,n,x); the approximant NAMED ABOVE is
;;; BERNSTEIN-POLY(f o A, n, U(x)), a Bernstein polynomial in the UNIT
;;; coordinate, and those are different maps.  The bridge is the affine
;;; SUBSTITUTION lemma -- phi antiderivable and A affine with A' /= 0 give
;;; t |-> phi(A(t)) antiderivable, with antiderivative recip(lam).(Phi o A) --
;;; proved `modulo 0' in theorem-library/antiderivable-affine-subst.scm from
;;; `deriv-chain' over `deriv-affine' and `compose-continuous-at' over
;;; `affine-continuous-at', both scaled.  No estimate appears in it.  The
;;; approximant of THIS file is `bernstein-ccint-approximant-antiderivable'
;;; there, and it bills exactly what bernstein-poly-antiderivable bills.
;;; =====================================================================
