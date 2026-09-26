;;; c-int.scm -- docs/calculus.pdf CHAPTER 4, equation (64): the DEFINITE
;;; INTEGRAL of a continuous function, `C-INT'.  Rung 4.
;;;
;;;              /b
;;;   C-INT(phi, a, b)  =  |  phi(theta) d theta  =  f(b) - f(a)
;;;              /a
;;;
;;; for any antiderivative f of phi on [a,b].  The name is the user's: it is
;;; C-INT and not INT so that the Lebesgue-Caratheodory integral, defined later,
;;; can have the plain name.  The argument order -- the FUNCTION first, then the
;;; bounds -- is SERIES-PARTIAL-SUM's, which is the summation operator this was
;;; asked to read like.
;;;
;;; THE DEFINITION, AND WHY IT IS AN IOTA WITH A TYPING CONJUNCT
;;;
;;;   (def-functoid 'C-INT '(phi a b)
;;;     '(IOTA v_ (AND (IN v_ RR)
;;;                    (FORSOME f_ (AND (IS-ANTIDERIVATIVE f_ phi a b)
;;;                                     (= v_ (- (f_ b) (f_ a))))))))
;;;
;;; Eight functoids in the tree are defined by definite description, and they
;;; agree on one rule: the IOTA body pins the VALUE's membership, either through
;;; the characterising predicate or by an explicit conjunct.  DERIV
;;; (differentiation.scm) and SERIES-LIMIT (dominated-convergence.scm) carry no
;;; typing conjunct because IS-DIFF-AT and CONVERGES-TO each state (IN L RR) /
;;; (IN L (PTS s)) themselves; SQRT (real-powers.scm), DEG (poly-degree.scm),
;;; PRED (nn-pred.scm), NNFST/NNSND (nn-pairing.scm), CARD (cardinality.scm)
;;; and DUAL-NORM (linear-functional.scm) all open with one.  IS-ANTIDERIVATIVE
;;; says nothing whatever about v_ -- the equation is what mentions it -- so
;;; C-INT is in the second group and opens with (IN v_ RR).
;;;
;;; THE TWO OBLIGATIONS `iota-def' POSTS, and where they stand:
;;;
;;;   UNIQUENESS is `antiderivative-endpoint-difference' (Cor 4.11,
;;;              antiderivative.scm), VERBATIM: f(b) - f(a) = g(b) - g(a) for any
;;;              two antiderivatives of the same phi.  That corollary was proved
;;;              for exactly this.
;;;   EXISTENCE  is IS-ANTIDERIVABLE(phi, a, b), which for a CONTINUOUS phi is
;;;              rung 3's headline and is NOT proved -- see the closing note of
;;;              theorem-library/bernstein-ccint.scm.  C-INT does NOT wait on it.
;;;              The IOTA is simply undefined where phi is not antiderivable,
;;;              which is the tree's normal treatment of a partial function (`='
;;;              is partial in VNB; PRED is undefined at 0 for the same reason
;;;              and says so).  Every theorem below therefore carries an
;;;              antiderivative or an IS-ANTIDERIVABLE as a HYPOTHESIS; what
;;;              waits on rung 3 is only the theorem
;;;              "phi continuous on [a,b] => C-INT(phi,a,b) is defined".
;;;
;;; WHAT IS PROVED HERE
;;;
;;;   c-int-value   EQUATION (64), and the workhorse: every property below goes
;;;                 through it.  `mac' unfolds C-INT in the goal to the IOTA
;;;                 term; `iota-d' posts existence-and-uniqueness and hands the
;;;                 defining property back as an assumption.  The witness for
;;;                 existence is f itself, so that half is `ew' + `rfl'; the
;;;                 uniqueness half is Cor 4.11 plus eq-sym/eq-trans; and the
;;;                 main branch skolemizes the defining property and applies
;;;                 Cor 4.11 again.
;;;   c-int-in-rr   the integral of an antiderivable function is a REAL -- i.e.
;;;                 the description is non-empty there.  This is the DEFINEDNESS
;;;                 statement, and it is the one rung 3 will feed: with
;;;                 "continuous => antiderivable" in hand it becomes
;;;                 "continuous => the integral exists" by one citation.
;;;   c-int-add     PROPOSITION 4.13, the notes' own computation written out.
;;;   c-int-scale   PROPOSITION 4.12's other half.  Together with c-int-add, and
;;;                 with `antiderivable-add' / `antiderivable-scale' saying the
;;;                 domain is a vector space, that IS Prop 4.12: the definite
;;;                 integral is a linear functional on the antiderivable
;;;                 functions on [a,b].
;;;
;;; THE BILL.  c-int-value and everything through it bills exactly what
;;; `antiderivative-endpoint-difference' bills -- the fifteen-fact MVT/EVT
;;; residue, `trust: well-known' -- and adds NOTHING of its own.  The definition
;;; is free; the debt is Corollary 4.11's, inherited unchanged.
;;;
;;; ONE MECHANICAL POINT, twice.  `c-int-add' and `c-int-scale' must SUBSTITUTE
;;; the three (64) equations into the goal BEFORE beta-reducing the sum/scale
;;; lambda, and must have a, b typed in RR before either: `lam-b' on an untyped
;;; argument still fires and then owes (IN arg RR) at a node whose context
;;; predates the binder, and that leaf can never be closed.
;;;
;;; Needs antiderivative (IS-ANTIDERIVATIVE, antiderivative-endpoint-difference,
;;; antiderivative-endpoints, antiderivative-map-in-fun, antiderivative-add,
;;; antiderivative-scale), equality-basics (eq-sym, eq-trans),
;;; fun-apply-type-proof (fun-apply-type-c), binary-minus-laws (rr-sub-in-rr)
;;; and driver-kit.
;;; =====================================================================

;;; =====================================================================
;;; 0.  THE DEFINITION.
;;; =====================================================================

(def-functoid 'C-INT '(phi a b)
  '(IOTA v_ (AND (IN v_ RR)
                 (FORSOME f_ (AND (IS-ANTIDERIVATIVE f_ phi a b)
                                  (= v_ (- (f_ b) (f_ a))))))))
;;; The reading.  `english' is what wff->english / the proof reader print; `tex'
;;; is what expr->tex prints, and it fires -- the operator-table branch of
;;; expr->tex sits ABOVE tex-output's own binop table since 2026-08-10, so a
;;; declared template beats a default.  NO `noun': that slot is the unary SORT
;;; reading ("x is a Euclidean ring"), which `operator-sort' offers only for
;;; arity-1 heads and `describe' would print here as nonsense.
(notation! 'C-INT 'kind 'functoid 'arity 3
           'english "the integral of $1 from $2 to $3"
           'tex "\\int_{$2}^{$3} $1")

;;; ---- file-local driver helpers (the `ci-' prefix) --------------------

(define (ci-diff fn) (list '- (list fn 'b) (list fn 'a)))

(define (ci-endpoints! fn of)
  (dk-split! (dk-fact! 'antiderivative-endpoints fn of 'a 'b)))

(define (ci-values! fn of)
  (fact 'antiderivative-map-in-fun fn of 'a 'b)
  (fact 'fun-apply-type-c fn 'RR 'RR 'a)
  (fact 'fun-apply-type-c fn 'RR 'RR 'b)
  (fact 'rr-sub-in-rr (list fn 'b) (list fn 'a)))

(define (ci-obtain!)
  (let ((z (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
    (dk-landed* (lambda () (dk-split! z)))))

(define (ci-witness parts)
  (cadr (car (filter (dk-head? 'IS-ANTIDERIVATIVE) parts))))

;;; skolemize an IS-ANTIDERIVABLE hypothesis; the eigenvariable is read off the
;;; IS-ANTIDERIVATIVE formula that names WHICH function it antidifferentiates,
;;; never off context order (two such existentials bind the same name).
(define (ci-skolem! of)
  (mac-h 'IS-ANTIDERIVABLE (list 'IS-ANTIDERIVABLE of 'a 'b))
  (dk-ai-head! 'FORSOME)
  (cadr (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'IS-ANTIDERIVATIVE)
                                      (eq? (caddr z) of)))
                     (dk-asms)))))

;;; =====================================================================
;;; c-int-value -- equation (64).
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff '(FORALL f (FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVATIVE f phi a b)
            (= (C-INT phi a b) (- (f b) (f a))))))))))
(dk-peel-to! '=)
(ci-endpoints! 'f 'phi)
(ci-values! 'f 'phi)
(mac 'c-int)
(define ci-io (cadr (dk-goal)))
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (if (eq? (car (dk-goal)) 'FORSOME)
       (begin
         (ew (ci-diff 'f))
         (for-each
          (lambda (nd)
            (dk-focus! nd)
            (if (eq? (car (dk-goal)) 'FORALL)
                (begin
                  (di)
                  (dk-split! (dk-landed-1 (lambda () (di))))
                  (let* ((y  (caddr (dk-goal)))
                         (ps (ci-obtain!))
                         (g  (ci-witness ps)))
                    (fact 'antiderivative-endpoint-difference 'f g 'phi 'a 'b)
                    (fact 'eq-sym y (ci-diff g))
                    (fact 'eq-trans (ci-diff 'f) (ci-diff g) y)
                    (ass)))
                (for-each
                 (lambda (m)
                   (dk-focus! m)
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (begin
                         (ew 'f)
                         (for-each (lambda (k)
                                     (dk-focus! k)
                                     (if (eq? (car (dk-goal)) '=) (rfl) (ass)))
                                   (dk-opened (lambda () (di)))))))
                 (dk-opened (lambda () (di))))))
          (dk-opened (lambda () (di)))))
       (let ((def (car (filter (lambda (z) (and (pair? z) (eq? (car z) 'AND)
                                                (dk-contains? z 'IOTA)))
                               (dk-asms)))))
         (dk-split! def)
         (let* ((ps (ci-obtain!))
                (g  (ci-witness ps)))
           (fact 'antiderivative-endpoint-difference 'f g 'phi 'a 'b)
           (fact 'eq-sym (ci-diff 'f) (ci-diff g))
           (fact 'eq-trans ci-io (ci-diff g) (ci-diff 'f))
           (ass)))))
 (dk-opened (lambda () (iota-d ci-io))))))
(qed 'c-int-value)
(topic! 'c-int-value 'analysis)
(alias! 'c-int-value
        "equation (64)"
        "the integral of phi over [a,b] is f(b) - f(a) for any antiderivative f")

;;; =====================================================================
;;; c-int-in-rr -- the integral of an antiderivable function is a real.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff '(FORALL phi (FORALL a (FORALL b
   (IMPLIES (IS-ANTIDERIVABLE phi a b) (IN (C-INT phi a b) RR)))))))
(dk-peel-to! 'IN)
(let ((g (ci-skolem! 'phi)))
  (ci-endpoints! g 'phi)
  (ci-values! g 'phi)
  (fact 'c-int-value g 'phi 'a 'b)
  (subst (list '= '(C-INT phi a b) (ci-diff g)))
  (ass))))
(qed 'c-int-in-rr)
(topic! 'c-int-in-rr 'analysis)
(alias! 'c-int-in-rr "the definite integral of an antiderivable function is a real")

;;; ---- beta to a fixpoint (arguments already typed) --------------------
(define (ci-has-lambda-app? g)
  (cond ((and (pair? g) (pair? (car g)) (eq? (caar g) 'VNB-LAMBDA)) #t)
        ((pair? g) (or (ci-has-lambda-app? (car g)) (ci-has-lambda-app? (cdr g))))
        (else #f)))
(define (ci-beta!)
  (let loop ((fuel 20))
    (if (and (> fuel 0) (ci-has-lambda-app? (dk-goal)))
        (let ((before (dk-goal)))
          (lam-b)
          (if (equal? (dk-goal) before) #t (loop (- fuel 1))))
        #t)))

;;; =====================================================================
;;; c-int-add -- PROPOSITION 4.13.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff
  '(FORALL phi (FORALL psi (FORALL a (FORALL b
     (IMPLIES (IS-ANTIDERIVABLE phi a b)
     (IMPLIES (IS-ANTIDERIVABLE psi a b)
       (= (C-INT (VNB-LAMBDA x RR (+ (phi x) (psi x))) a b)
          (+ (C-INT phi a b) (C-INT psi a b)))))))))))
(dk-peel-to! '=)
(let* ((fv (ci-skolem! 'phi))
       (gv (ci-skolem! 'psi)))
  (ci-endpoints! fv 'phi)
  (ci-values! fv 'phi)
  (ci-values! gv 'psi)
  (let* ((sum   (dk-fact! 'antiderivative-add fv gv 'phi 'psi 'a 'b))
         (sum-f (cadr sum))
         (sum-p (caddr sum)))
    (fact 'c-int-value sum-f sum-p 'a 'b)
    (fact 'c-int-value fv 'phi 'a 'b)
    (fact 'c-int-value gv 'psi 'a 'b)
    (subst (list '= (list 'C-INT sum-p 'a 'b) (ci-diff sum-f)))
    (subst (list '= '(C-INT phi a b) (ci-diff fv)))
    (subst (list '= '(C-INT psi a b) (ci-diff gv)))
    (ci-beta!)
    (crs)))))
(qed 'c-int-add)
(topic! 'c-int-add 'analysis)
(alias! 'c-int-add
        "Proposition 4.13"
        "the integral of a sum is the sum of the integrals")

;;; =====================================================================
;;; c-int-scale -- PROPOSITION 4.12's other half.
;;; =====================================================================

(quietly (lambda ()
(sp (make-wff
  '(FORALL c (FORALL phi (FORALL a (FORALL b
     (IMPLIES (IN c RR)
     (IMPLIES (IS-ANTIDERIVABLE phi a b)
       (= (C-INT (VNB-LAMBDA x RR (* c (phi x))) a b)
          (* c (C-INT phi a b)))))))))))
(dk-peel-to! '=)
(let ((fv (ci-skolem! 'phi)))
  (ci-endpoints! fv 'phi)
  (ci-values! fv 'phi)
  (let* ((sc   (dk-fact! 'antiderivative-scale 'c fv 'phi 'a 'b))
         (sc-f (cadr sc))
         (sc-p (caddr sc)))
    (fact 'c-int-value sc-f sc-p 'a 'b)
    (fact 'c-int-value fv 'phi 'a 'b)
    (subst (list '= (list 'C-INT sc-p 'a 'b) (ci-diff sc-f)))
    (subst (list '= '(C-INT phi a b) (ci-diff fv)))
    (ci-beta!)
    (crs)))))

(qed 'c-int-scale)
(topic! 'c-int-scale 'analysis)
(alias! 'c-int-scale
        "Proposition 4.12 (scalar)"
        "the integral of a scalar multiple is the multiple of the integral")
