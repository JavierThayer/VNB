;;; antiderivative.scm -- docs/calculus.pdf CHAPTER 4 SECTION 2: Definition 4.6
;;; (antiderivative / antiderivable), Proposition 4.8 (closed under sums; the
;;; scalar half is handed off), Proposition 4.10 (two antiderivatives of the
;;; same function differ by a constant) and Corollary 4.11 (so f(b) - f(a) does
;;; not depend on which antiderivative is taken).
;;;
;;; THIS IS THE VOCABULARY RUNG 4 CONSUMES.  Cor 4.11 is exactly the
;;; well-definedness that lets `C-INT(phi,a,b)' be DEFINED as f(b) - f(a) for an
;;; arbitrary antiderivative f; nothing else in this file is needed for that,
;;; and nothing here presupposes existence.
;;;
;;; DEFINITION 4.6, AND THE ONE CLAUSE THE NOTES DO NOT WRITE.  The notes' three
;;; clauses are (1) f continuous on [a,b], (2) f differentiable on (a,b),
;;; (3) f'(theta) = phi(theta) there.  Clauses (2) and (3) MERGE here, because
;;; IS-DIFF-AT (differentiation.scm) carries the value: `IS-DIFF-AT(f, th,
;;; phi(th))' says both at once, and there is no separate "is differentiable"
;;; predicate to state (2) with.  The clause the notes leave to the reader is
;;; `a < b'.  It is IN the predicate here and not left to each citer, because
;;; every theorem this file leans on -- deriv-zero-implies-constant,
;;; mvt-upper-bound, mvt-lower-bound -- carries it as a hypothesis, and a
;;; definition that omitted it would push the same conjunct onto every citation
;;; site and every downstream statement.  [a,b] is a NONDEGENERATE interval here.
;;;
;;; The continuity clause is stated the way the whole calculus arc states it:
;;; f is a member of FUN(RR,RR) which is IS-CONTINUOUS-AT(RR-MS, RR-MS, f, x) at
;;; each x of CCINT(a,b) -- continuity of a map on the LINE, tested at the points
;;; of the interval, not continuity of a restriction to a subspace.  There is no
;;; metric subspace structure on CCINT(a,b) in this tree, and building one is a
;;; foundational decision several proofs are waiting on; deriv-constant-proof,
;;; mvt-bounds-proof, bernstein-density and uniform-continuity-ccint all use this
;;; convention, so the predicate matches them on the nose and every citation is a
;;; direct `fact'.
;;;
;;; WHAT IS PROVED HERE, AND WITH WHAT
;;;
;;;   deriv-sub          d/dx (f - g) = f' - g'.  Not previously in the tree:
;;;                      deriv-sum and deriv-scalar-mult were, and the difference
;;;                      is their composition through diff-transfer-ptwise-eq
;;;                      (deriv-scalar-mult at c = -1, deriv-sum, then transfer
;;;                      the conclusion from  x |-> f(x) + (-1).g(x)  to the term
;;;                      the tree writes,  x |-> f(x) - g(x)).  `modulo 0'.
;;;
;;;   antiderivative-differ-by-constant   PROP 4.10.  The notes' proof exactly:
;;;                      h = f - g has derivative 0 on (a,b) and is continuous on
;;;                      [a,b], so Cor 2.15 (deriv-zero-implies-constant) makes it
;;;                      constant; the constant is h(a) = f(a) - g(a).
;;;
;;;   antiderivative-endpoint-difference  COR 4.11, two instances of 4.10.
;;;
;;;   antiderivative-add      PROP 4.8, the SUM half, and `antiderivable-add'
;;;                      one level up.
;;;
;;;   antiderivative-scale    PROP 4.8, the SCALAR half, and `antiderivable-scale'
;;;                      one level up -- so Proposition 4.8 entire: the
;;;                      antiderivable functions on [a,b] are a vector space.
;;;                      It was handed off when this file was written, for want
;;;                      of two lemmas about the term x |-> c.f(x); both are now
;;;                      in theorem-library/continuity-scale.scm
;;;                      (`scale-lam-in-fun', `scale-continuous-at', both
;;;                      `modulo 0'), and the driver below is the sum half's
;;;                      with `scale-' for `sum-'.
;;;
;;;   poly-is-antiderivable   EXAMPLE 4.7 restated in the new vocabulary:
;;;                      poly-antiderivative already produces the antiderivative,
;;;                      and diff-implies-continuous supplies clause (1) of Def
;;;                      4.6 free -- a function differentiable at every real is
;;;                      continuous at every point of [a,b].
;;;
;;; A NOTE ON `=' VS `=='.  diff-transfer-ptwise-eq asks for a POINTWISE
;;; QUASI-equality, and `crs' does not decide a `==' goal (it reports "not a
;;; provable commutative-ring identity" and the head is the reason, not the
;;; algebra).  The move used three times below is: prove the `=' by `crs',
;;; `subst' it into the `==' goal, and close the resulting X == X with `qrfl'.
;;;
;;; Needs differentiation (IS-DIFF-AT, diff-implies-continuous), deriv-sum-product
;;; (deriv-sum), deriv-polynomial (deriv-scalar-mult), diff-transfer
;;; (diff-transfer-ptwise-eq), continuity-sub (sub-continuous-at, sub-lam-in-fun),
;;; continuity-sum (sum-lam-in-fun, sum-continuous-at), deriv-constant-proof
;;; (deriv-zero-implies-constant), ccint-basics (ccint-membership),
;;; poly-antiderivative (poly-antiderivative, anti-lam-in-fun, poly-lam-in-fun),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `ad-' prefix) ----------------------

;; peel a guarded universal, returning the eigenvariable of the guard it landed
(define (ad-di-var!) (cadr (car (dk-landed (lambda () (di))))))

;; (IN t RR) off a CCINT membership, WITHOUT destroying the membership: `mac-h'
;; replaces the hypothesis it unfolds, so the unfold happens in a `have!' lane.
;; skolemize the existential the PREVIOUS tactic landed, and return its
;; unpacked body (`obtain' cannot: it diffs the context around its own lane, so
;; a FORSOME already sitting there is invisible to it -- and it returns only the
;; eigenvariable, where both conjuncts are wanted here).
(define (ad-obtain!)
  (let ((a (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
    (dk-landed* (lambda () (dk-split! a)))))

;; `di' splits a conjunctive GOAL one level per call, so a seven-conjunct
;; definition needs six.  Split every AND leaf to exhaustion.
(define (ad-split-goal!)
  (let loop ((fuel 12))
    (let ((ands (filter (lambda (nd) (eq? (car (dk-goal-of nd)) 'AND)) (proof-leaves))))
      (if (and (pair? ands) (> fuel 0))
          (begin (for-each (lambda (nd) (dk-focus! nd) (di)) ands) (loop (- fuel 1)))
          #t))))

(define (ad-rr-of! v lo hi)
  (have! (list 'IN v 'RR)
    (lambda () (mac-h 'ccint-membership (list 'IN v (list 'CCINT lo hi))) (prop))))

;;; =====================================================================
;;; 0.  DEFINITION 4.6.
;;; =====================================================================

;;; Definition 4.6 itself -- IS-ANTIDERIVATIVE and IS-ANTIDERIVABLE, with their
;;; notation! -- MOVED 2026-09-20 (batch 12-A) to
;;; structure-library/antiderivative.scm.  Twelve other files state theorems
;;; with them while this proof file loads at ~514 of 546.  The projections and
;;; the Chapter 4 proofs below are unchanged.

;;; =====================================================================
;;; 0b.  THE PROJECTIONS.  `mac-h' REPLACES the hypothesis it unfolds, so a
;;; proof that needs one conjunct of Def 4.6 while keeping IS-ANTIDERIVATIVE
;;; itself (Cor 4.11 does: it cites Prop 4.10, whose antecedent is the whole
;;; predicate) cannot get it by unfolding in the main branch.  Same reason
;;; diff-at-in-fun exists beside IS-DIFF-AT.
;;; =====================================================================

(define (ad-project! goal)
  (quietly (lambda ()
    (sp (make-wff
         (list 'FORALL 'f (list 'FORALL 'phi (list 'FORALL 'a (list 'FORALL 'b
           (list 'IMPLIES '(IS-ANTIDERIVATIVE f phi a b) goal)))))))
    (dk-peel-to! (car goal))
    (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b))
    (dk-split! (car (dk-asms)))
    (prop))))

(ad-project! '(IN f (FUN RR RR)))
(qed 'antiderivative-map-in-fun)
(topic! 'antiderivative-map-in-fun 'analysis)

(ad-project! '(IN phi (FUN RR RR)))
(qed 'antiderivative-fn-in-fun)
(topic! 'antiderivative-fn-in-fun 'analysis)

(ad-project! '(AND (IN a RR) (AND (IN b RR) (< a b))))
(qed 'antiderivative-endpoints)
(topic! 'antiderivative-endpoints 'analysis)
(alias! 'antiderivative-endpoints "an antiderivative is taken on a nondegenerate [a,b]")

;;; =====================================================================
;;; 1.  deriv-sub -- the derivative of a difference.
;;;
;;; deriv-scalar-mult at c = -1 turns g into -g; deriv-sum adds; and the value
;;; L + (-1).M is rewritten to L - M by `crs'.  The transfer is needed because
;;; deriv-sum concludes about the LITERAL term it builds,
;;; x |-> f(x) + (x |-> (-1).g(x))(x), which is not the term
;;; sub-lam-in-fun / sub-continuous-at speak about.
;;; =====================================================================

(define ad-neg-lam '(VNB-LAMBDA x RR (* (- 1) (g x))))
(define ad-sum-lam (list 'VNB-LAMBDA 'x 'RR (list '+ '(f x) (list ad-neg-lam 'x))))
(define ad-sub-lam '(VNB-LAMBDA x RR (- (f x) (g x))))

(quietly (lambda ()
(sp (make-wff
     '(FORALL f (FORALL g (FORALL a (FORALL L (FORALL M
        (IMPLIES (AND (IS-DIFF-AT f a L) (IS-DIFF-AT g a M))
                 (IS-DIFF-AT (VNB-LAMBDA x RR (- (f x) (g x))) a (- L M))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(dk-ai-head! 'AND)
(fact 'rr-one-in)
(fact 'rr-neg-closed 1)
(fact 'diff-at-in-fun 'f 'a 'L)
(fact 'diff-at-in-fun 'g 'a 'M)
(fact 'diff-value-real 'f 'a 'L)
(fact 'diff-value-real 'g 'a 'M)
(fact 'deriv-scalar-mult '(- 1) 'g 'a 'M)
(have! (list 'AND (list 'IS-DIFF-AT 'f 'a 'L)
                  (list 'IS-DIFF-AT ad-neg-lam 'a '(* (- 1) M))))
(fact 'deriv-sum 'f ad-neg-lam 'a 'L '(* (- 1) M))
(fact 'sub-lam-in-fun 'f 'g)
(have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ RR)
                          (list '== (list ad-sub-lam 'w_) (list ad-sum-lam 'w_))))
  (lambda ()
    (let ((v (ad-di-var!)))
      (fact 'fun-apply-type-c 'f 'RR 'RR v)
      (fact 'fun-apply-type-c 'g 'RR 'RR v)
      (lam-b) (lam-b)
      (let ((lhs (list '- (list 'f v) (list 'g v)))
            (rhs (list '+ (list 'f v) (list '* '(- 1) (list 'g v)))))
        (have! (list '= lhs rhs) (lambda () (crs)))
        (subst (list '= lhs rhs))
        (qrfl)))))
(fact 'diff-transfer-ptwise-eq ad-sub-lam ad-sum-lam 'a '(+ L (* (- 1) M)))
(have! '(= (- L M) (+ L (* (- 1) M))) (lambda () (crs)))
(subst '(= (- L M) (+ L (* (- 1) M))))
(ass)))
(qed 'deriv-sub)
(topic! 'deriv-sub 'analysis)
(alias! 'deriv-sub "the derivative of a difference is the difference of the derivatives")

;;; =====================================================================
;;; 2.  PROPOSITION 4.10 -- two antiderivatives of phi on [a,b] differ by a
;;; constant.  The constant is produced, not merely asserted to exist: it is
;;; f(a) - g(a).
;;; =====================================================================

(define ad-h   '(VNB-LAMBDA x RR (- (f x) (g x))))
(define ad-cst '(- (f a) (g a)))

(quietly (lambda ()
(sp (make-wff
     '(FORALL f (FORALL g (FORALL phi (FORALL a (FORALL b
        (IMPLIES (IS-ANTIDERIVATIVE f phi a b)
        (IMPLIES (IS-ANTIDERIVATIVE g phi a b)
          (FORSOME cst_ (AND (IN cst_ RR)
            (FORALL s_ (IMPLIES (IN s_ (CCINT a b))
              (= (f s_) (+ (g s_) cst_)))))))))))))))
(dk-peel-to! 'FORSOME)
(dk-split! (dk-landed-1
             (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b)))))
(dk-split! (dk-landed-1
             (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE g phi a b)))))

;; The two unfolds land the SAME SHAPES twice over, so the four universals are
;; taken by POSITION in the landing order, never by shape: g's pair is on top
;; because g's unfold ran second.
(define ad-cf (list-ref (dk-asms) 4))            ; f is continuous on [a,b]
(define ad-df (list-ref (dk-asms) 3))            ; f' = phi on (a,b)
(define ad-cg (list-ref (dk-asms) 1))            ; g is continuous on [a,b]
(define ad-dg (list-ref (dk-asms) 0))            ; g' = phi on (a,b)

(fact 'sub-lam-in-fun 'f 'g)

;; h = f - g is continuous on [a,b] ...
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (CCINT a b))
                          (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS ad-h 'x_)))
  (lambda ()
    (let ((v (ad-di-var!)))
      (inst+ ad-cf v) (inst+ ad-cg v)
      (fact 'sub-continuous-at 'f 'g v) (ass))))

;; ... and has derivative 0 on (a,b).  The guard here is a CONJUNCTION, so the
;; universal peels in TWO `di's -- the first lands nothing -- and `inst+' will
;; not detach it until the AND is in context as one formula.
(have! (list 'FORALL 'th_ (list 'IMPLIES '(AND (IN th_ RR) (AND (< a th_) (< th_ b)))
                          (list 'IS-DIFF-AT ad-h 'th_ 0)))
  (lambda ()
    (di)
    (dk-split! (dk-landed-1 (lambda () (di))))
    (let ((v (caddr (dk-goal))))                 ; the eigenvariable, off the GOAL
      (have! (list 'AND (list 'IN v 'RR) (list 'AND (list '< 'a v) (list '< v 'b))))
      (inst+ ad-df v) (inst+ ad-dg v)
      (fact 'fun-apply-type-c 'phi 'RR 'RR v)
      (have! (list 'AND (list 'IS-DIFF-AT 'f v (list 'phi v))
                        (list 'IS-DIFF-AT 'g v (list 'phi v))))
      (fact 'deriv-sub 'f 'g v (list 'phi v) (list 'phi v))
      (have! (list '= 0 (list '- (list 'phi v) (list 'phi v))) (lambda () (crs)))
      (subst (list '= 0 (list '- (list 'phi v) (list 'phi v))))
      (ass))))

;; Cor 2.15 on h, and the endpoint a as a point of [a,b].
(have! (list 'AND (list 'IN ad-h '(FUN RR RR))
                  '(AND (IN a RR) (AND (IN b RR) (< a b)))))
(fact 'deriv-zero-implies-constant ad-h 'a 'b)
(fact 'rr-lt-implies-le 'a 'b)
(fact 'rr-leq-reflexive 'a)
(have! '(IN a (CCINT a b)) (lambda () (mac 'ccint-membership) (prop)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'a)
(fact 'fun-apply-type-c 'g 'RR 'RR 'a)
(fact 'rr-sub-in-rr '(f a) '(g a))

(ew ad-cst)
(di)                                             ; the AND goal splits in two
(for-each
 (lambda (n)
   (dk-focus! n)
   (if (eq? (car (dk-goal)) 'IN)
       (ass)                                     ; f(a) - g(a) is a real
       (let ((v (ad-di-var!)))                   ; s_ in [a,b]
         (ad-rr-of! v 'a 'b)
         (fact 'fun-apply-type-c 'f 'RR 'RR v)
         (fact 'fun-apply-type-c 'g 'RR 'RR v)
         (have! (list 'AND (list 'IN v '(CCINT a b)) '(IN a (CCINT a b))))
         (fact 'deriv-zero-implies-constant ad-h 'a 'b v 'a)
         (lam-b-h (list '= (list ad-h v) (list ad-h 'a)))
         (let ((lhs '(- (f a) (g a)))
               (rhs (list '- (list 'f v) (list 'g v))))
           (have! (list '= lhs rhs) (lambda () (fact 'eq-sym rhs lhs) (ass)))
           (subst (list '= lhs rhs))
           (crs)))))
 (proof-leaves))))
(qed 'antiderivative-differ-by-constant)
(topic! 'antiderivative-differ-by-constant 'analysis)
(alias! 'antiderivative-differ-by-constant
        "Proposition 4.10"
        "two antiderivatives of the same function on [a,b] differ by a constant")

;;; =====================================================================
;;; 3.  COROLLARY 4.11 -- f(b) - f(a) does not depend on the antiderivative.
;;;
;;; THIS IS THE WELL-DEFINEDNESS RUNG 4 NEEDS.  Read the constant of 4.10 at the
;;; two endpoints and subtract; the constant cancels, which is one `crs'.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff
     '(FORALL f (FORALL g (FORALL phi (FORALL a (FORALL b
        (IMPLIES (IS-ANTIDERIVATIVE f phi a b)
        (IMPLIES (IS-ANTIDERIVATIVE g phi a b)
          (= (- (f b) (f a)) (- (g b) (g a))))))))))))
(dk-peel-to! '=)
(dk-split! (dk-fact! 'antiderivative-endpoints 'f 'phi 'a 'b))
(fact 'antiderivative-map-in-fun 'f 'phi 'a 'b)
(fact 'antiderivative-map-in-fun 'g 'phi 'a 'b)

;; both endpoints are points of [a,b]
(fact 'rr-lt-implies-le 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(have! '(IN a (CCINT a b)) (lambda () (mac 'ccint-membership) (prop)))
(have! '(IN b (CCINT a b)) (lambda () (mac 'ccint-membership) (prop)))
(for-each (lambda (t)
            (fact 'fun-apply-type-c 'f 'RR 'RR t)
            (fact 'fun-apply-type-c 'g 'RR 'RR t))
          '(a b))

;; the constant of Prop 4.10, read at a and at b
(fact 'antiderivative-differ-by-constant 'f 'g 'phi 'a 'b)
(let* ((ps  (ad-obtain!))
       (cst (cadr (car (filter (dk-head? 'IN) ps))))
       (uni (car (filter (dk-head? 'FORALL) ps))))
  (inst+ uni 'a)
  (inst+ uni 'b)
  (subst (list '= '(f b) (list '+ '(g b) cst)))
  (subst (list '= '(f a) (list '+ '(g a) cst)))
  (crs))))
(qed 'antiderivative-endpoint-difference)
(topic! 'antiderivative-endpoint-difference 'analysis)
(alias! 'antiderivative-endpoint-difference
        "Corollary 4.11"
        "f(b) - f(a) is the same for every antiderivative f of phi on [a,b]")

;;; =====================================================================
;;; 4.  EXAMPLE 4.7 in the Definition-4.6 vocabulary.
;;;
;;; poly-antiderivative already produces the antiderivative and its value at
;;; every real; all this adds is clause (1) of Def 4.6, and that clause is FREE:
;;; a map differentiable at every point of RR is continuous at every point of
;;; RR, so `diff-implies-continuous' discharges it at each point of [a,b] from
;;; the same citation that discharges clause (3).
;;;
;;; The one mechanical point: Def 4.6 asks for IS-DIFF-AT(F, th, phi(th)) with
;;; phi the polynomial LAMBDA, while poly-antiderivative concludes about the
;;; beta-REDUCT, the partial sum at th.  So the goal is beta-reduced BEFORE the
;;; citation, with th already typed -- `lam-b' on an untyped argument still
;;; fires and then owes (IN th RR) at a node where th does not occur.
;;; =====================================================================

(define (ad-poly-lam cf m)
  (list 'VNB-LAMBDA 'x_ 'RR
        (list 'SERIES-PARTIAL-SUM
              (list 'VNB-LAMBDA 'k_ 'NN (list '* (list cf 'k_) (list 'power 'x_ 'k_)))
              m)))
(define (ad-anti-lam cf m)
  (list 'VNB-LAMBDA 'x_ 'RR
        (list 'SERIES-PARTIAL-SUM
              (list 'VNB-LAMBDA 'k_ 'NN
                    (list '* (list '* (list 'recip '(succ k_)) (list cf 'k_))
                             (list 'power 'x_ '(succ k_))))
              m)))

(quietly (lambda ()
(sp (make-wff
     (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
       (list 'FORALL 'cf (list 'IMPLIES '(IN cf (FUN NN RR))
         (list 'FORALL 'a (list 'FORALL 'b (list 'IMPLIES
            '(AND (IN a RR) (AND (IN b RR) (< a b)))
            (list 'IS-ANTIDERIVABLE (ad-poly-lam 'cf '(succ n)) 'a 'b))))))))))
(dk-peel-to! 'IS-ANTIDERIVABLE)
(dk-split! '(AND (IN a RR) (AND (IN b RR) (< a b))))
(fact 'nn-succ-closed 'n)
(fact 'anti-lam-in-fun 'cf '(succ n))
(fact 'poly-lam-in-fun 'cf '(succ n))
(mac 'IS-ANTIDERIVABLE)
(ew (ad-anti-lam 'cf '(succ n)))
(mac 'IS-ANTIDERIVATIVE)
(ad-split-goal!)                              ; the defining conjunction, split
(for-each
 (lambda (nd)
   (dk-focus! nd)
   (let ((g (dk-goal)))
     (cond
       ((memq (car g) '(IN <)) (ass))
       ;; clause (1): continuity at each point of [a,b].  The two universals
       ;; have the same head, so they are told apart on the GUARD: a CCINT
       ;; membership here, a three-way AND in the derivative clause.
       ((eq? (car (cadr (caddr g))) 'IN)
        (let* ((v (ad-di-var!))
               (sps (list 'SERIES-PARTIAL-SUM
                          (list 'VNB-LAMBDA 'k_ 'NN
                                (list '* '(cf k_) (list 'power v 'k_)))
                          '(succ n))))
          (ad-rr-of! v 'a 'b)
          (fact 'poly-antiderivative 'n 'cf v)
          ;; LUTINS instantiation (2026-09-18): `diff-implies-continuous' is
          ;; cited AT the partial sum, which the certificate never accepts.
          ;; It is the derivative VALUE of the IS-DIFF-AT just landed, so the
          ;; typing is one unfold away -- on a `have!' side branch, `mac-h'
          ;; being destructive and the hypothesis still needed by the `ass'.
          (have! (list 'IN sps 'RR)
            (lambda ()
              (mac-h 'IS-DIFF-AT (list 'IS-DIFF-AT (ad-anti-lam 'cf '(succ n)) v sps))
              (let lp ((k 0))
                (let ((tgt (any-pred (lambda (aa) (and (pair? aa) (memq (car aa) '(AND FORSOME))))
                                     (dk-asms))))
                  (if (and tgt (< k 20)) (begin (ai tgt) (lp (+ k 1))))))
              (ass)))
          (fact 'diff-implies-continuous (ad-anti-lam 'cf '(succ n)) v sps)
          (ass)))
       ;; clause (3): the derivative, at each interior point
       (else
        (di)
        (dk-split! (dk-landed-1 (lambda () (di))))
        (let ((v (caddr (dk-goal))))
          (lam-b)
          (fact 'poly-antiderivative 'n 'cf v)
          (ass))))))
 (proof-leaves))))
(qed 'poly-is-antiderivable)
(topic! 'poly-is-antiderivable 'analysis)
(alias! 'poly-is-antiderivable
        "Example 4.7"
        "every polynomial function is antiderivable on every [a,b]")

;;; =====================================================================
;;; 5.  PROPOSITION 4.8, the SUM half.
;;;
;;; "The set of antiderivable functions on [a,b] is a vector space."  The sum is
;;; what Cor 4.17 will consume; the SCALAR half follows it below, and reads the
;;; same way -- the two lemmas it was waiting on (`scale-lam-in-fun',
;;; `scale-continuous-at') are proved in continuity-scale.scm, which loads
;;; before this file.
;;;
;;; Def 4.6's derivative clause asks for IS-DIFF-AT(F, th, PHI(th)) with PHI the
;;; SUM LAMBDA, so the goal is beta-reduced -- th typed first -- before
;;; `deriv-sum' is cited.
;;; =====================================================================

(define ad-sum-f   '(VNB-LAMBDA x RR (+ (f x) (g x))))
(define ad-sum-phi '(VNB-LAMBDA x RR (+ (phi x) (psi x))))

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'f (list 'FORALL 'g (list 'FORALL 'phi (list 'FORALL 'psi
      (list 'FORALL 'a (list 'FORALL 'b
        (list 'IMPLIES '(IS-ANTIDERIVATIVE f phi a b)
        (list 'IMPLIES '(IS-ANTIDERIVATIVE g psi a b)
          (list 'IS-ANTIDERIVATIVE ad-sum-f ad-sum-phi 'a 'b)))))))))))
  (dk-peel-to! 'IS-ANTIDERIVATIVE)
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b)))))
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE g psi a b)))))
  ;; four universals of the same two shapes: taken on the head of the
  ;; CONSEQUENT plus the map they speak about, never by position.
  (define (ad-univ head sym)
    (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                                  (dk-contains? z head) (dk-contains? z sym)))
                 (dk-asms))))
  (define ad-cf (ad-univ 'IS-CONTINUOUS-AT 'f))
  (define ad-df (ad-univ 'IS-DIFF-AT 'phi))
  (define ad-cg (ad-univ 'IS-CONTINUOUS-AT 'g))
  (define ad-dg (ad-univ 'IS-DIFF-AT 'psi))
  (fact 'sum-lam-in-fun 'f 'g)
  (fact 'sum-lam-in-fun 'phi 'psi)
  (mac 'IS-ANTIDERIVATIVE)
  (ad-split-goal!)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (let ((gl (dk-goal)))
       (cond
         ((memq (car gl) '(IN <)) (ass))
         ((eq? (car (cadr (caddr gl))) 'IN)              ; continuity clause
          (let ((v (ad-di-var!)))
            (inst+ ad-cf v) (inst+ ad-cg v)
            (fact 'sum-continuous-at 'f 'g v)
            (ass)))
         (else                                           ; derivative clause
          (di)
          (dk-split! (dk-landed-1 (lambda () (di))))
          (let ((v (caddr (dk-goal))))
            (have! (list 'AND (list 'IN v 'RR)
                              (list 'AND (list '< 'a v) (list '< v 'b))))
            (inst+ ad-df v) (inst+ ad-dg v)
            (fact 'fun-apply-type-c 'phi 'RR 'RR v)
            (fact 'fun-apply-type-c 'psi 'RR 'RR v)
            (lam-b)                                      ; PHI(th) -> phi(th)+psi(th)
            (have! (list 'AND (list 'IS-DIFF-AT 'f v (list 'phi v))
                              (list 'IS-DIFF-AT 'g v (list 'psi v))))
            (fact 'deriv-sum 'f 'g v (list 'phi v) (list 'psi v))
            (ass))))))
   (proof-leaves))))
(qed 'antiderivative-add)
(topic! 'antiderivative-add 'analysis)
(alias! 'antiderivative-add
        "Proposition 4.8 (sum)"
        "a sum of antiderivatives is an antiderivative of the sum")

;;; ... and the same statement one level up, in IS-ANTIDERIVABLE.
(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'phi (list 'FORALL 'psi (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IS-ANTIDERIVABLE phi a b)
      (list 'IMPLIES '(IS-ANTIDERIVABLE psi a b)
        (list 'IS-ANTIDERIVABLE ad-sum-phi 'a 'b)))))))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi a b))
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE psi a b))
  (dk-ai-head! 'FORSOME)
  (dk-ai-head! 'FORSOME)
  ;; The two existentials bind the SAME name, so the eigenvariables come back in
  ;; context order, which is not the order they were introduced in: read each
  ;; one off the formula that says WHICH function it is an antiderivative of.
  (let* ((wit (lambda (fn)
                (cadr (car (filter (lambda (z) (and (pair? z)
                                                    (eq? (car z) 'IS-ANTIDERIVATIVE)
                                                    (eq? (caddr z) fn)))
                                   (dk-asms))))))
         (fv  (wit 'phi))
         (gv  (wit 'psi)))
    (mac 'IS-ANTIDERIVABLE)
    (ew (list 'VNB-LAMBDA 'x 'RR (list '+ (list fv 'x) (list gv 'x))))
    (fact 'antiderivative-add fv gv 'phi 'psi 'a 'b)
    (ass))))
(qed 'antiderivable-add)
(topic! 'antiderivable-add 'analysis)
(alias! 'antiderivable-add "a sum of antiderivable functions is antiderivable")

;;; =====================================================================
;;; 6.  PROPOSITION 4.8, the SCALAR half -- and with it Prop 4.8 entire.
;;;
;;; Same driver as the sum half, with `scale-lam-in-fun' / `scale-continuous-at'
;;; (continuity-scale.scm) in place of `sum-lam-in-fun' / `sum-continuous-at',
;;; and `deriv-scalar-mult' (deriv-polynomial.scm) in place of `deriv-sum'.  Def
;;; 4.6's derivative clause asks for IS-DIFF-AT(F, th, PHI(th)) with PHI the
;;; SCALED lambda, so the goal is beta-reduced -- th typed FIRST, or `lam-b' owes
;;; an unprovable (IN th RR) at a node where th does not occur -- before the
;;; citation.
;;; =====================================================================


(define ad-scale-f   '(VNB-LAMBDA x RR (* c (f x))))
(define ad-scale-phi '(VNB-LAMBDA x RR (* c (phi x))))

(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'c (list 'FORALL 'f (list 'FORALL 'phi (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IN c RR)
      (list 'IMPLIES '(IS-ANTIDERIVATIVE f phi a b)
        (list 'IS-ANTIDERIVATIVE ad-scale-f ad-scale-phi 'a 'b))))))))))
  (dk-peel-to! 'IS-ANTIDERIVATIVE)
  (dk-split! (dk-landed-1
               (lambda () (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE f phi a b)))))
  ;; two universals of different shapes: taken on the head of the CONSEQUENT
  (define (ad-univ head)
    (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'FORALL) (dk-contains? z head)))
                 (dk-asms))))
  (define ad-cf (ad-univ 'IS-CONTINUOUS-AT))
  (define ad-df (ad-univ 'IS-DIFF-AT))
  (fact 'scale-lam-in-fun 'c 'f)
  (fact 'scale-lam-in-fun 'c 'phi)
  (mac 'IS-ANTIDERIVATIVE)
  (ad-split-goal!)
  (for-each
   (lambda (nd)
     (dk-focus! nd)
     (let ((gl (dk-goal)))
       (cond
         ((memq (car gl) '(IN <)) (ass))
         ((eq? (car (cadr (caddr gl))) 'IN)              ; continuity clause
          (let ((v (ad-di-var!)))
            (inst+ ad-cf v)
            (fact 'scale-continuous-at 'c 'f v)
            (ass)))
         (else                                           ; derivative clause
          (di)
          (dk-split! (dk-landed-1 (lambda () (di))))
          (let ((v (caddr (dk-goal))))
            (have! (list 'AND (list 'IN v 'RR)
                              (list 'AND (list '< 'a v) (list '< v 'b))))
            (inst+ ad-df v)
            (fact 'fun-apply-type-c 'phi 'RR 'RR v)
            (lam-b)                                      ; PHI(th) -> c.phi(th)
            (fact 'deriv-scalar-mult 'c 'f v (list 'phi v))
            (ass))))))
   (proof-leaves))))
(qed 'antiderivative-scale)
(topic! 'antiderivative-scale 'analysis)
(alias! 'antiderivative-scale
        "Proposition 4.8 (scalar)"
        "a scalar multiple of an antiderivative is an antiderivative of the multiple")

;;; ... and the same statement one level up, in IS-ANTIDERIVABLE.
(quietly (lambda ()
  (sp (make-wff
    (list 'FORALL 'c (list 'FORALL 'phi (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IN c RR)
      (list 'IMPLIES '(IS-ANTIDERIVABLE phi a b)
        (list 'IS-ANTIDERIVABLE ad-scale-phi 'a 'b)))))))))
  (dk-peel-to! 'IS-ANTIDERIVABLE)
  (mac-h 'IS-ANTIDERIVABLE '(IS-ANTIDERIVABLE phi a b))
  (let ((fv (cadr (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME)))))))
    (mac 'IS-ANTIDERIVABLE)
    (ew (list 'VNB-LAMBDA 'x 'RR (list '* 'c (list fv 'x))))
    (fact 'antiderivative-scale 'c fv 'phi 'a 'b)
    (ass))))
(qed 'antiderivable-scale)
(topic! 'antiderivable-scale 'analysis)
(alias! 'antiderivable-scale
        "a scalar multiple of an antiderivable function is antiderivable")

;;; =====================================================================
;;; WHERE THIS GOES NEXT.
;;;
;;; `C-INT' -- the definite integral of the notes' (64) -- is DEFINED in
;;; theorem-library/c-int.scm, which loads immediately after this file:
;;;
;;;   (def-functoid 'C-INT '(phi a b)
;;;     '(IOTA v_ (AND (IN v_ RR)
;;;                    (FORSOME f_ (AND (IS-ANTIDERIVATIVE f_ phi a b)
;;;                                     (= v_ (- (f_ b) (f_ a))))))))
;;;
;;; and `antiderivative-endpoint-difference' above is, verbatim, the UNIQUENESS
;;; obligation `iota-def' posts for it.  EXISTENCE -- IS-ANTIDERIVABLE(phi,a,b)
;;; for a continuous phi -- is rung 3's headline and is NOT proved; see the
;;; closing note of theorem-library/bernstein-ccint.scm.  C-INT does not wait on
;;; it: the IOTA is simply undefined where phi is not antiderivable, which is the
;;; tree's normal treatment of a partial function.  Only the theorem "C-INT is
;;; defined for every continuous phi" waits.
;;;
;;; Prop 4.12 and Prop 4.13 (linearity) are proved there as `c-int-add' and
;;; `c-int-scale', out of `antiderivative-add' / `antiderivative-scale' above
;;; plus one `crs'.
;;; =====================================================================
