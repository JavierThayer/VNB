;;; continuity-scale.scm -- the SCALAR MULTIPLE of a real map: its FUN typing
;;; and its continuity, both PROVEN `modulo 0'.
;;;
;;;   scale-lam-in-fun     c in RR, f in FUN(RR,RR)
;;;                          =>  (VNB-LAMBDA x RR (* c (f x))) in FUN(RR,RR)
;;;   scale-continuous-at  c in RR, f continuous at a
;;;                          =>  x |-> c.f(x) is continuous at a
;;;
;;; WHY THE FILE EXISTS.  The scalar-multiple lambda was the ONE shape of the
;;; continuity/typing algebra the tree did not carry: continuity-sum has
;;; sum-lam-in-fun / sum-continuous-at, continuity-product has prod-lam-in-fun /
;;; product-continuous-at, continuity-sub has the difference, neg-continuous the
;;; negation -- and nothing had x |-> c.f(x).  `deriv-scalar-mult'
;;; (deriv-polynomial.scm) has been working around the gap since it was written,
;;; and Prop 4.8's SCALAR half (antiderivative.scm) stopped on exactly these two
;;; leaves.  Landing them fixes the gap, not just that theorem.
;;;
;;; THE TYPING IS NOT A COROLLARY OF THE DERIVATIVE, and the failed route is
;;; worth recording: `deriv-scalar-mult' plus `diff-at-in-fun' does give
;;; (VNB-LAMBDA x RR (* c (f x))) in FUN(RR,RR), but only where f is
;;; DIFFERENTIABLE, and Definition 4.6 gives that on the OPEN interval only,
;;; while the typing conjunct it feeds is unconditional.  So the typing is
;;; proved directly, the way sum-lam-in-fun is: `lam-t', peel, `fun-apply-type-c'
;;; for (f x), `rr-mul-closed' for the product.  `lam-t' opens TWO leaves -- the
;;; pointwise typing AND the sethood of RR -- and the second is `rr-is-set'.
;;;
;;; NO EPS/DELTA IS DONE HERE, and that is the point, exactly as in
;;; continuity-sub.scm.  Three theorems already in the library compose:
;;;
;;;   const-continuous-at     (continuity-basics)   x |-> c is continuous at a
;;;   product-continuous-at   (continuity-product)  ... so is its product with f
;;;   cont-transfer-ptwise-eq (continuity-transfer) ... and so is anything
;;;                                                 agreeing with it pointwise
;;;
;;; THE BRIDGE IS THE WHOLE STORY.  `product-continuous-at' concludes about the
;;; LITERAL term it builds,
;;;
;;;     (VNB-LAMBDA x RR (* ((VNB-LAMBDA x RR c) x) (f x)))
;;;
;;; which is not the term this theorem is about.  The two denote the same
;;; function and are different S-expressions; the gap is about SYNTAX, and
;;; `cont-transfer-ptwise-eq' is what closes it -- beta-reduce both sides at a
;;; typed real point and the two bodies are literally equal, so one `crs' does
;;; it.  The product term is READ OFF the landed conclusion rather than
;;; reconstructed here: rebuilding it means guessing how `subst-free' renamed
;;; the two nested `x' binders, and a term that misses matches nothing.
;;;
;;; THE ONE TRAP is `mac-h' being destructive.  Both `scale-lam-in-fun' and
;;; `const-continuous-at' want typings -- (IN f (FUN RR RR)), (IN a RR) -- that
;;; this theorem does not assume; they are conjuncts of the continuity
;;; hypothesis, and unfolding it to read them off DELETES the hypothesis the
;;; next `fact' needs.  So each is extracted inside a `have!' LANE
;;; (`sc-typing!' / `sc-point!'), exactly as continuity-sub.scm does it.
;;;
;;; Loads after continuity-basics (const-continuous-at), continuity-product
;;; (product-continuous-at), continuity-transfer (cont-transfer-ptwise-eq),
;;; fun-apply-type-proof (fun-apply-type-c) and metric-continuity; before
;;; antiderivative, whose scalar half consumes both.

;;; ---- file-local driver helpers (the `sc-' prefix) --------------------

(define (sc-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (sc-split!)
  (let loop ((l (dk-asms)) (n 0))
    (cond ((or (null? l) (> n 18)) #t)
          ((and (pair? (car l)) (eq? (caar l) 'AND))
           (ai (car l)) (loop (dk-asms) (+ n 1)))
          (else (loop (cdr l) n)))))

(define (sc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "sc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

(define (sc-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (sc-has-lambda-app? (car g)) (sc-has-lambda-app? (cdr g))))
        (else #f)))

;;; `lam-b' to exhaustion.  Safe here because the argument is already typed in
;;; RR when this runs -- firing it before the typing is evident still reduces
;;; and then OWES (IN arg RR) at a node whose context predates the binder.
(define (sc-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (sc-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; =====================================================================
;;; (1) x |-> c.f(x) is a function RR -> RR.
;;; =====================================================================

(define sc-scale-lam '(VNB-LAMBDA x RR (* c (f x))))

(quietly (lambda ()
(sp (make-wff (forall-guarded '(c f) (list '(IN c RR) '(IN f (FUN RR RR)))
                (list 'IN sc-scale-lam '(FUN RR RR)))))
(sc-peel!)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORALL)
       (let ((z (cadr (car (sc-di-landed!)))))
         (fact 'fun-apply-type-c 'f 'RR 'RR z)
         (have! (list 'AND '(IN c RR) (list 'IN (list 'f z) 'RR)))
         (fact 'rr-mul-closed 'c (list 'f z))
         (ass))
       (begin (fact 'rr-is-set) (ass))))
 (dk-opened (lambda () (lam-t))))))
(qed 'scale-lam-in-fun)
(topic! 'scale-lam-in-fun 'analysis)
(alias! 'scale-lam-in-fun
        "a scalar multiple of a real function is a function")

;;; =====================================================================
;;; (2) scale-continuous-at.
;;; =====================================================================

;;; eigenvariables, set as the proof runs
(define sc-c #f)          ; the scalar
(define sc-f #f)          ; the map
(define sc-a #f)          ; the point

;;; (IN FN (FUN RR RR)) read off FN's continuity WITHOUT destroying it: the
;;; unfold runs inside the have! lane, so it replaces the hypothesis on that
;;; side branch only.
(define (sc-typing! fn)
  (have! (list 'IN fn '(FUN RR RR))
    (lambda ()
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS fn sc-a))
      (sc-split!)
      (slot-h 'PTS (list 'IN fn '(FUN (PTS RR-MS) (PTS RR-MS))))
      (ass))))

;;; ... and (IN a RR), the same way.
(define (sc-point!)
  (have! (list 'IN sc-a 'RR)
    (lambda ()
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS sc-f sc-a))
      (sc-split!)
      (slot-h 'PTS (list 'IN sc-a '(PTS RR-MS)))
      (ass))))

(quietly (lambda ()
(sp (make-wff
     '(FORALL c (IMPLIES (IN c RR)
        (FORALL f (FORALL a (IMPLIES
          (IS-CONTINUOUS-AT RR-MS RR-MS f a)
          (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA x RR (* c (f x))) a))))))))
(sc-peel!)

;;; the three eigenvariables off the GOAL, which names all three in their roles
(let* ((g0 (dk-goal)) (lam (list-ref g0 3)) (body (list-ref lam 3)))
  (set! sc-a (list-ref g0 4))
  (set! sc-c (list-ref body 1))
  (set! sc-f (car (list-ref body 2))))

(define sc-scale (list-ref (dk-goal) 3))

(sc-typing! sc-f)
(sc-point!)

;;; the constant map is continuous at a, and so is its product with f.  Both
;;; terms are READ OFF the landed conclusions -- see the header.
(define sc-const (list-ref (dk-fact! 'const-continuous-at sc-c sc-a) 3))
(define sc-prod  (list-ref (dk-fact! 'product-continuous-at sc-const sc-f sc-a) 3))

(fact 'scale-lam-in-fun sc-c sc-f)

;;; the bridge: after the betas the two bodies are literally equal
(have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ RR)
                               (list '= (list sc-scale 'w_) (list sc-prod 'w_))))
  (lambda ()
    (let ((v (cadr (car (sc-di-landed!)))))       ; (IN w_ RR) -- BEFORE any beta
      (sc-beta!)
      (fact 'fun-apply-type-c sc-f 'RR 'RR v)
      (crs))))

(fact 'cont-transfer-ptwise-eq sc-scale sc-prod sc-a)
(ass)))
(qed 'scale-continuous-at)
(topic! 'scale-continuous-at 'analysis)
(alias! 'scale-continuous-at
        "a scalar multiple of a continuous map is continuous")
