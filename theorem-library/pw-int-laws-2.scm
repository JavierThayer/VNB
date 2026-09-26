;;; pw-int-laws-2.scm -- the LINEARITY and the ADDITIVITY of the integral on
;;; [a, b], continuing theorem-library/pw-antiderivative-laws.scm.
;;;
;;; THE SOURCE IS THE USER'S NOTES, ~/docs/calculus.pdf, chapter 4, section 2.
;;; Each headline theorem below is stated the way the notes state it:
;;;
;;;   Remark 4.9      "if f is an antiderivative of phi on [a,b], then f
;;;                    restricted to a subinterval [c,d] is an antiderivative
;;;                    of phi restricted to [c,d]."
;;;                                          `pw-antiderivative-restrict'
;;;   Proposition 4.10 "If f, g are antiderivatives of phi on [a,b] then there
;;;                    is a constant C such that f(s) = g(s) + C for all
;;;                    s in [a,b]."          `pw-antiderivative-differ-by-constant'
;;;                                          (the explicit C) and
;;;                                          `pw-antiderivative-differ-by-some-constant'
;;;                                          (the notes' existential form)
;;;   Proposition 4.12 "The definite integral is a linear functional on the
;;;                    space of antiderivable functions on [a,b]."
;;;                    The SUM half is `pw-antiderivative-sum' (4.13, proved in
;;;                    pw-antiderivative-laws.scm); the SCALAR MULTIPLE half is
;;;                    `pw-antiderivative-real-mul' here.  The two together ARE
;;;                    4.12; there is no single formula for it, because the
;;;                    space of antiderivable functions is not a structure in
;;;                    this tree and "linear functional" would have to be said
;;;                    of one.
;;;
;;; and the additivity of the integral over two adjacent intervals,
;;; `pw-int-adjacent', which the notes do not number but which every later
;;; estimate uses; it is Remark 4.9 plus `pw-int-value' three times.
;;;
;;; THE COMPLEX SIDE (the user's notes ~/docs/complex-analysis.pdf 3.1,
;;; equation (44) and the sentence after it, "it follows easily that (44) is
;;; complex linear in f"):
;;;
;;;   `cc-int-value'     (44) with one piecewise antiderivative of each
;;;                      coordinate: the integral is
;;;                      (F(b) - F(a)) + (G(b) - G(a)) i
;;;   `cc-int-in-cc'     it is a complex number
;;;   `cc-int-sum'       linear in f, the SUM
;;;   `cc-int-real-mul'  linear in f, the REAL scalar
;;;
;;; The COMPLEX scalar is NOT proved here.  It is the same argument with the
;;; 2x2 real matrix of w -- re(w f) = re(w) re(f) - im(w) im(f) and its twin
;;; (`cc-re-mul', `cc-im-mul') -- so each coordinate primitive is a LINEAR
;;; COMBINATION of the two given ones, and the tree has no law for that: it
;;; would be `pw-antiderivative-real-mul' twice and `pw-antiderivative-sum'
;;; once, through four intermediate lambdas, or one new
;;; `pw-antiderivative-linear' (c F + d G is a primitive of c phi + d psi)
;;; proved once and used twice.  Note that the final ring identity needs NO
;;; appeal to i * i = -1: w * (P + Q i) is expanded by taking the real and
;;; imaginary parts of the product (`cc-re-mul', `cc-im-mul', with `cc-re-im-of'
;;; for the coordinates of P + Q i) and then reassembling with
;;; `cc-re-im-decompose'.
;;;
;;; THE SHAPE OF EVERY STATEMENT ABOUT A SUM OR A MULTIPLE.  The tree has no
;;; addition and no scalar multiplication on FUN(A, RR), so the sum c*f is a
;;; GIVEN function agreeing POINTWISE with it -- the shape
;;; `pw-antiderivative-sum' and every rule of interval-calculus-laws.scm
;;; section (8) uses, and the shape the caller always has in hand.  Writing
;;; `c * f' as a term would need an algebra of functions that does not exist
;;; and would not be the notes' statement either.
;;;
;;; THE STATEMENT CHECKS, against CLAUDE.md's species of false or
;;; underdetermined statement, made before any proof was written.
;;;
;;; (1) NO STRICT `=' ON A PW-INT TERM WITHOUT AN ANTIDERIVATIVE.  PW-INT is an
;;;     IOTA and an IOTA is never certified defined (the LUTINS rule), so every
;;;     equation between PW-INT terms below stands under an
;;;     IS-PRIMITIVE hypothesis that earns the definedness, exactly as
;;;     `pw-int-value' does.  `pw-int-adjacent' carries ONE such hypothesis, on
;;;     [a,b], and the two restricted integrals are defined BY Remark 4.9.
;;;
;;; (2) THE RESTRICTION NEEDS THE INCLUSION OF THE INTERVALS.  RESTRICT(phi,
;;;     CCINT(c,d)) is a function on [c,d] only when CCINT(c,d) is a subset of
;;;     CCINT(a,b); the hypotheses `a <= c', `c < d', `d <= b' give it
;;;     (`ccint-subset-ccint' below), and `c < d' is needed on its own, since
;;;     IS-PRIMITIVE carries `c < d' as a conjunct and a degenerate
;;;     subinterval is not one.
;;;
;;; (3) IN `pw-int-adjacent' THE MIDPOINT IS STRICTLY INSIDE: c in OOINT(a,b),
;;;     not c in CCINT(a,b).  At c = a the left interval [a,a] is degenerate
;;;     and PW-INT(phi, a, a) is UNDEFINED (IS-PRIMITIVE(F,phi,a,a) is
;;;     false, its conjunct `a < a' failing), so the equation would assert the
;;;     definedness of an undefined term.  The notes' implicit a < c < b is the
;;;     guard.
;;;
;;; (4) THE CONSTANT OF 4.10 IS NAMED: C = f(a) - g(a), which is what the
;;;     proof produces and what a consumer needs; the notes' `there is a
;;;     constant C' is the corollary `-by-some-constant', proved from it in
;;;     four lines.
;;;
;;; (5) `F' AND `f' ARE ONE SYMBOL (both readers fold to lower case), so the
;;;     notes' f and g are `pwf_' and `paw_', phi and psi `pphi_' and `ppsi_',
;;;     as in pw-antiderivative-laws.scm.  The binders added here are `pcc_'
;;;     (the scalar), `pbs_' (the point of 4.10), `pcv_' / `pdv_' (the
;;;     subinterval).  None folds onto a class name (NN ZZ QQ RR CC ORD SET
;;;     EMPTY-SET POS-INF NEG-INF RR-STAR RR-POS-STAR), onto an accessor, or
;;;     onto `rps_' / `rpt_', which the body of IS-PRIMITIVE binds.
;;;
;;; (6) THE ANTECEDENTS ARE CURRIED, and no statement has more than five
;;;     adjacent unguarded binders: with eight of them `fact' MIS-INSTANTIATES
;;;     (batch 16-A).
;;;
;;; Helper prefix: p2-.
;;;
;;; Dependencies: structure-library/path-integral.scm;
;;; theorem-library/pw-antiderivative-laws.scm (the read-offs, pw-int-value,
;;; pw-restrict-continuous-on,
;;; pw-antiderivative-one-piece, ooint-inner-radius);
;;; has-deriv-at-more.scm (has-deriv-at-real-mul); interval-calculus-laws.scm
;;; (extend-const-*, has-deriv-at-local, ooint-*); continuity-scale.scm
;;; (scale-continuous-at); metric-subspace-laws.scm (restrict-apply,
;;; restrict-in-fun, subspace-restrict-continuous-at); ccint-basics.scm;
;;; regulated-primitive-laws.scm (the primitive-* read-offs, countable-union-2,
;;; countable-subset); zero-deriv-off-countable.scm (zero-deriv-off-countable);
;;; rr-order-basics (rr-le-cases).  (Batch 21: the exceptional set is COUNTABLE,
;;; Dieudonne VIII.7; the finite-set bricks card-union-nn, card-subset-nn and
;;; pw-zero-deriv-off-finite-set were replaced by the three countable ones.)

;;; ---- file-local driver helpers ---------------------------------------

(define (p2-head g) (and (pair? g) (car g)))

(define p2-cc '(CCINT a b))

;;; close an AND goal conjunct by conjunct: `ass' when the conjunct is already
;;; in the context, `dk-ineq!' with PREMS named by FORMULA otherwise.
(define (p2-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

(define (p2-in-ccint! z lo hi prems)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (p2-conj-ineq! prems))))

(define (p2-in-ooint! z lo hi prems)
  (dk-have! (list 'IN z (list 'OOINT lo hi))
    (lambda () (mac 'ooint-membership) (p2-conj-ineq! prems))))

;;; the three conjuncts of a CCINT membership, WITHOUT consuming it.
(define (p2-ccint-parts! z lo hi)
  (dk-split-all! (list (dk-fact! 'ccint-parts lo hi z))))

;;; the three conjuncts of an OOINT membership, WITHOUT consuming it.
(define (p2-ooint-parts! z lo hi)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN z (list 'OOINT lo hi)))))))

;;; the endpoint typings of [a,b] that every endpoint difference needs.
(define (p2-endpoints!)
  (fact 'rr-leq-reflexive 'a)
  (fact 'rr-leq-reflexive 'b)
  (dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
  (p2-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
  (p2-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b))))

;;; =====================================================================
;;; (1) PROPOSITION 4.12, THE SCALAR MULTIPLE.
;;;
;;;   "The definite integral is a linear functional on the space of
;;;    antiderivable functions on [a,b]."
;;;
;;; The sum half is `pw-antiderivative-sum' (4.13).  This is the other half,
;;; in the same shape: c*F and c*phi are GIVEN functions agreeing pointwise.
;;; The route is the sum's, with `scale-continuous-at' for the continuity of
;;; the total multiple and `has-deriv-at-real-mul' for the derivative; the
;;; exceptional set does not change, so no union is needed.
;;; =====================================================================

(define p2-hmul '(VNB-LAMBDA x RR (* pcc_ ((EXTEND-CONST pwf_ a b) x))))

(sp (make-wff "forall([a in rr, b in rr],
   forall([pwf_, pphi_, pcc_ in rr],
     is-primitive(pwf_, pphi_, a, b) implies
     forall([pauh_ in fun(ccint(a,b), rr), pchi_ in fun(ccint(a,b), rr)],
       forall([pay_ in ccint(a,b)], pauh_(pay_) == pcc_ * pwf_(pay_)) implies
       forall([pay_ in ccint(a,b)], pchi_(pay_) == pcc_ * pphi_(pay_)) implies
       is-primitive(pauh_, pchi_, a, b) and
       pw-int(pchi_, a, b) = pcc_ * pw-int(pphi_, a, b))))"))
(dk-peel!)
(define p2-mul-hagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pauh_)))
           "the pointwise multiple of the primitive"))
(define p2-mul-cagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)))
           "the pointwise multiple of the integrand"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(p2-endpoints!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set p2-cc 'RR)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'extend-const-in-fun 'a 'b 'pwf_)
(fact 'ooint-subset-ccint 'a 'b)
;; the total multiple of the extension is a function on the line ...
(dk-have! (list 'IN p2-hmul '(FUN RR RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (not (eq? (p2-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'fun-apply-type-c '(EXTEND-CONST pwf_ a b) 'RR 'RR z)
             (have! (list 'AND '(IN pcc_ RR)
                          (list 'IN (list '(EXTEND-CONST pwf_ a b) z) 'RR)))
             (fact 'rr-mul-closed 'pcc_ (list '(EXTEND-CONST pwf_ a b) z))
             (ass))))
     (dk-opened (lambda () (lam-t))))))
;; ... and it is continuous everywhere.
(dk-have! (list 'FORALL 'pax_ (list 'IMPLIES '(IN pax_ RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS p2-hmul 'pax_)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'extend-const-continuous-at 'a 'b 'pwf_ z)
      (fact 'scale-continuous-at 'pcc_ '(EXTEND-CONST pwf_ a b) z)
      (ass))))
;; pauh_ agrees with it on [a,b], so pauh_ is continuous on [a,b].
(dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
            (list '== (list 'pauh_ 'pay_) (list p2-hmul 'pay_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (dk-apply! p2-mul-hagree z)
      (p2-ccint-parts! z 'a 'b)
      (fact 'extend-const-fixes 'a 'b z 'pwf_)
      (dk-lam-b!)
      (subst (list '== (list '(EXTEND-CONST pwf_ a b) z) (list 'pwf_ z)))
      (ass))))
(fact 'pw-restrict-continuous-on 'a 'b p2-hmul 'pauh_)
;; the derivative off the SAME exceptional set
(let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'pwf_ 'pphi_ 'a 'b)))
       (d1 (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)
                                             (dk-contains? fm s1)))
                           "the derivative universal"))))
  (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
              (list 'IMPLIES (list 'NOT (list 'IN 'pat_ s1))
                    '(HAS-DERIV-AT pauh_ pat_ (pchi_ pat_)))))
    (lambda ()
      (dk-peel!)
      (fact 'subset-mem-fwd '(OOINT a b) p2-cc 'pat_)
      (fact 'fun-apply-type-c 'pphi_ p2-cc 'RR 'pat_)
      (dk-apply! d1 'pat_)
      (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b 'pat_))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr rv)
        (fact 'rr-sub-in-rr 'pat_ rv)
        (fact 'rr-add-in-rr 'pat_ rv)
        (let ((oo (list 'OOINT (list '- 'pat_ rv) (list '+ 'pat_ rv))))
          (fact 'restrict-in-fun 'pauh_ p2-cc 'RR oo)
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ oo)
                      (list '== '(pauh_ hbx_) '(* pcc_ (pwf_ hbx_)))))
            (lambda ()
              (let ((y (dk-di-var!)))
                (fact 'subset-mem-fwd oo p2-cc y)
                (dk-apply! p2-mul-hagree y)
                (ass))))
          (fact 'has-deriv-at-real-mul rv 'pwf_ 'pauh_ 'pcc_ 'pat_ '(pphi_ pat_))
          (dk-apply! p2-mul-cagree 'pat_)
          (subst (list '== '(pchi_ pat_) '(* pcc_ (pphi_ pat_))))
          (ass)))))
  (dk-have! '(IS-PRIMITIVE pauh_ pchi_ a b)
    (lambda ()
      (mac 'IS-PRIMITIVE)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (p2-head (dk-goal)) 'FORSOME))
             (ass)
             (begin
               (ew s1)
               (dk-conj-close! (lambda () (ass))))))))))
;; the integral identity
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-int-value 'pauh_ 'pchi_ 'a 'b)
(for-each (lambda (f)
            (fact 'fun-apply-type-c f p2-cc 'RR 'a)
            (fact 'fun-apply-type-c f p2-cc 'RR 'b))
          '(pwf_ pauh_))
(dk-apply! p2-mul-hagree 'a)
(dk-apply! p2-mul-hagree 'b)
(dk-conj-close!
 (lambda ()
   (if (eq? (p2-head (dk-goal)) 'IS-PRIMITIVE)
       (ass)
       (begin
         (subst '(= (PW-INT pchi_ a b) (- (pauh_ b) (pauh_ a))))
         (subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
         (subst '(== (pauh_ a) (* pcc_ (pwf_ a))))
         (subst '(== (pauh_ b) (* pcc_ (pwf_ b))))
         (crs)))))
(qed 'pw-antiderivative-real-mul)
(topic! 'pw-antiderivative-real-mul 'analysis)
(alias! 'pw-antiderivative-real-mul
        "Proposition 4.12, the scalar multiple"
        "a real multiple of a piecewise antiderivative is one of the multiple of the integrand, and the integral is homogeneous")

;;; =====================================================================
;;; (2) PROPOSITION 4.10 IN FULL.
;;;
;;;   "If f, g are antiderivatives of phi on [a,b] then there is a constant C
;;;    such that f(s) = g(s) + C for all s in [a,b]."
;;;
;;; pw-antiderivative-laws.scm proved the ENDPOINT form (Corollary 4.11).  The
;;; full statement is the same difference-of-extensions argument, with
;;; `zero-deriv-off-countable' applied on [a, s] instead of on [a, b]; the
;;; derivative condition transports because OOINT(a,s) is inside OOINT(a,b).
;;; The point s = a is the degenerate case and is closed by ring arithmetic.
;;; =====================================================================

(define p2-hdiff
  '(VNB-LAMBDA x RR (- ((EXTEND-CONST pwf_ a b) x) ((EXTEND-CONST paw_ a b) x))))

;;; the value of the difference of the extensions at a point of [a,b].
(define (p2-hdiff-value! z)
  (fact 'extend-const-fixes 'a 'b z 'pwf_)
  (fact 'extend-const-fixes 'a 'b z 'paw_)
  (dk-have! (list '= (list p2-hdiff z) (list '- (list 'pwf_ z) (list 'paw_ z)))
    (lambda ()
      (dk-lam-b!)
      (subst (list '== (list '(EXTEND-CONST pwf_ a b) z) (list 'pwf_ z)))
      (subst (list '== (list '(EXTEND-CONST paw_ a b) z) (list 'paw_ z)))
      (rfl))))

;;; everything two piecewise antiderivatives of one phi have in common: the
;;; difference of their constant extensions is a continuous total function
;;; whose derivative is 0 on (a,b) off a countable set.  Returns that set.
(define (p2-differ-setup!)
  (dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
  (dk-split-all!)
  (p2-endpoints!)
  (fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-in-fun 'paw_ 'pphi_ 'a 'b)
  (fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
  (fact 'primitive-continuous 'paw_ 'pphi_ 'a 'b)
  (fact 'extend-const-in-fun 'a 'b 'pwf_)
  (fact 'extend-const-in-fun 'a 'b 'paw_)
  (fact 'fun-apply-type-c 'pwf_ p2-cc 'RR 'a)
  (fact 'fun-apply-type-c 'pwf_ p2-cc 'RR 'b)
  (fact 'fun-apply-type-c 'paw_ p2-cc 'RR 'a)
  (fact 'fun-apply-type-c 'paw_ p2-cc 'RR 'b)
  (fact 'ooint-subset-ccint 'a 'b)
  ;; the difference of the extensions is a function on the line ...
  (dk-have! (list 'IN p2-hdiff '(FUN RR RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (not (eq? (p2-head (dk-goal)) 'FORALL))
             (begin (fact 'rr-is-set) (ass))
             (let ((z (dk-di-var!)))
               (fact 'fun-apply-type-c '(EXTEND-CONST pwf_ a b) 'RR 'RR z)
               (fact 'fun-apply-type-c '(EXTEND-CONST paw_ a b) 'RR 'RR z)
               (fact 'rr-sub-in-rr (list '(EXTEND-CONST pwf_ a b) z)
                                   (list '(EXTEND-CONST paw_ a b) z))
               (ass))))
       (dk-opened (lambda () (lam-t))))))
  ;; ... and is continuous everywhere
  (dk-have! (list 'FORALL 'pax_ (list 'IMPLIES '(IN pax_ RR)
              (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS p2-hdiff 'pax_)))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'extend-const-continuous-at 'a 'b 'pwf_ z)
        (fact 'extend-const-continuous-at 'a 'b 'paw_ z)
        (fact 'sub-continuous-at '(EXTEND-CONST pwf_ a b)
                                 '(EXTEND-CONST paw_ a b) z)
        (ass))))
  ;; the two exceptional sets, their union, and the vanishing derivative
  (let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                   'pwf_ 'pphi_ 'a 'b)))
         (d1 (begin (dk-split-all!)
                    (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                               (dk-contains? fm 'HAS-DERIV-AT)
                                               (dk-contains? fm s1)))
                             "the first derivative universal")))
         (s2 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                   'paw_ 'pphi_ 'a 'b)))
         (d2 (begin (dk-split-all!)
                    (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                               (dk-contains? fm 'HAS-DERIV-AT)
                                               (dk-contains? fm s2)))
                             "the second derivative universal")))
         (un (list 'UNION s1 s2)))
    ;; the union is COUNTABLE (`countable-union-2') and lies on the line,
    ;; which `zero-deriv-off-countable' asks for on its own.
    (fact 'countable-union-2 s1 s2)
    (dk-have! (list 'SUBSET un 'RR)
      (lambda ()
        (let* ((w  (subset-by-element!))
               (um (dk-fact! 'union-membership s1 s2 w))
               (i1 (dk-fact! 'subset-mem-fwd s1 p2-cc w))
               (i2 (dk-fact! 'subset-mem-fwd s2 p2-cc w))
               (i3 (dk-fact! 'ccint-elt-in-rr 'a 'b w)))
          (dk-only! um i1 i2 i3 (list 'IN w un))
          (prop))))
    (dk-have! (list 'FORALL 'pat_ (list 'IMPLIES '(IN pat_ (OOINT a b))
                (list 'IMPLIES (list 'NOT (list 'IN 'pat_ un))
                      (list 'IS-DIFF-AT p2-hdiff 'pat_ 0))))
      (lambda ()
        (dk-peel!)
        (let ((um (dk-fact! 'union-membership s1 s2 'pat_)))
          (dk-have! (list 'NOT (list 'IN 'pat_ s1))
            (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop)))
          (dk-have! (list 'NOT (list 'IN 'pat_ s2))
            (lambda () (dk-only! um (list 'NOT (list 'IN 'pat_ un))) (prop))))
        (fact 'subset-mem-fwd '(OOINT a b) p2-cc 'pat_)
        (fact 'fun-apply-type-c 'pphi_ p2-cc 'RR 'pat_)
        (dk-apply! d1 'pat_)
        (dk-apply! d2 'pat_)
        (fact 'extend-const-deriv-fwd 'a 'b 'pwf_ 'pat_ '(pphi_ pat_))
        (fact 'extend-const-deriv-fwd 'a 'b 'paw_ 'pat_ '(pphi_ pat_))
        (fact 'deriv-difference '(EXTEND-CONST pwf_ a b) '(EXTEND-CONST paw_ a b)
              'pat_ '(pphi_ pat_) '(pphi_ pat_))
        (dk-have! '(= 0 (- (pphi_ pat_) (pphi_ pat_))) (lambda () (crs)))
        (subst '(= 0 (- (pphi_ pat_) (pphi_ pat_))))
        (ass)))
    un))

(sp (make-wff "forall([pwf_, paw_, pphi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   is-primitive(paw_, pphi_, a, b) implies
   forall([pbs_ in ccint(a,b)],
     pwf_(pbs_) = paw_(pbs_) + (pwf_(a) - paw_(a))))"))
(dk-peel!)
(let* ((sv (cadr (cadr (dk-goal))))
       (un (p2-differ-setup!)))
  (fact 'ccint-elt-in-rr 'a 'b sv)
  (p2-ccint-parts! sv 'a 'b)
  (fact 'fun-apply-type-c 'pwf_ p2-cc 'RR sv)
  (fact 'fun-apply-type-c 'paw_ p2-cc 'RR sv)
  (use-em (list '= 'a sv)
    ;; ---- the degenerate point s = a ------------------------------------
    (lambda ()
      (subst (list '= 'a sv))
      (crs))
    ;; ---- a < s : the difference is constant on [a, s] -------------------
    (lambda ()
      (fact 'rr-le-cases 'a sv)
      (dk-have! (list '< 'a sv)
        (lambda ()
          (dk-only! (list 'OR (list '< 'a sv) (list '= 'a sv))
                    (list 'NOT (list '= 'a sv)))
          (prop)))
      (dk-have! (list 'FORALL 'pat_
                  (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT 'a sv))
                    (list 'IMPLIES (list 'NOT (list 'IN 'pat_ un))
                          (list 'IS-DIFF-AT p2-hdiff 'pat_ 0))))
        (lambda ()
          (dk-peel!)
          (p2-ooint-parts! 'pat_ 'a sv)
          (p2-in-ooint! 'pat_ 'a 'b
                        (list '(IN pat_ RR) (list 'IN sv 'RR) '(IN b RR)
                              '(< a pat_) (list '< 'pat_ sv) (list '<= sv 'b)))
          (dk-apply! (dk-pick (lambda (fm)
                                (and (pair? fm) (eq? (car fm) 'FORALL)
                                     (dk-contains? fm 'IS-DIFF-AT)
                                     (dk-contains? fm 'OOINT)
                                     (dk-contains? fm 'b)))
                              "the derivative universal on (a,b)")
                     'pat_)
          (ass)))
      (fact 'zero-deriv-off-countable un p2-hdiff 'a sv)
      (p2-hdiff-value! 'a)
      (p2-hdiff-value! sv)
      (dk-have! (list '= '(- (pwf_ a) (paw_ a))
                      (list '- (list 'pwf_ sv) (list 'paw_ sv)))
        (lambda ()
          (subst (list '= '(- (pwf_ a) (paw_ a)) (list p2-hdiff 'a)))
          (subst (list '= (list '- (list 'pwf_ sv) (list 'paw_ sv))
                       (list p2-hdiff sv)))
          (ass)))
      (subst (list '= '(- (pwf_ a) (paw_ a))
                   (list '- (list 'pwf_ sv) (list 'paw_ sv))))
      (crs))))
(qed 'pw-antiderivative-differ-by-constant)
(topic! 'pw-antiderivative-differ-by-constant 'analysis)
(alias! 'pw-antiderivative-differ-by-constant
        "Proposition 4.10"
        "two piecewise antiderivatives of one integrand differ by the constant f(a) - g(a) on the whole interval")

;;; the notes' own wording: THERE IS a constant C.
(sp (make-wff "forall([pwf_, paw_, pphi_, a, b],
   is-primitive(pwf_, pphi_, a, b) implies
   is-primitive(paw_, pphi_, a, b) implies
   forsome([pbc_], pbc_ in rr and
     forall([pbs_ in ccint(a,b)], pwf_(pbs_) = paw_(pbs_) + pbc_)))"))
(dk-peel!)
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(p2-endpoints!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-in-fun 'paw_ 'pphi_ 'a 'b)
(fact 'fun-apply-type-c 'pwf_ p2-cc 'RR 'a)
(fact 'fun-apply-type-c 'paw_ p2-cc 'RR 'a)
(fact 'rr-sub-in-rr '(pwf_ a) '(paw_ a))
(ew '(- (pwf_ a) (paw_ a)))
(dk-conj-close!
 (lambda ()
   (if (not (eq? (p2-head (dk-goal)) 'FORALL))
       (ass)
       (let ((z (dk-di-var!)))
         (fact 'pw-antiderivative-differ-by-constant 'pwf_ 'paw_ 'pphi_ 'a 'b)
         (dk-apply! (dk-pick (lambda (fm)
                               (and (pair? fm) (eq? (car fm) 'FORALL)
                                    (dk-contains? fm 'pwf_)
                                    (dk-contains? fm 'paw_)))
                             "Proposition 4.10 at this interval")
                    z)
         (ass)))))
(qed 'pw-antiderivative-differ-by-some-constant)
(topic! 'pw-antiderivative-differ-by-some-constant 'analysis)
(alias! 'pw-antiderivative-differ-by-some-constant
        "Proposition 4.10, the notes' wording"
        "two piecewise antiderivatives of one integrand differ by a constant")

;;; =====================================================================
;;; (3) REMARK 4.9 -- THE RESTRICTION TO A SUBINTERVAL.
;;;
;;;   "Clearly if f is an antiderivative of phi on [a,b], then f restricted to
;;;    a subinterval [c,d] is an antiderivative of phi restricted to [c,d]."
;;;
;;; "Clearly" costs four things here, and each is a conjunct of the
;;; definition: the two FUN typings (`restrict-in-fun', with the inclusion of
;;; the intervals); the continuity of the restriction ON THE SMALLER SUBSPACE
;;; (`subspace-restrict-continuous-at' -- a subspace of a subspace, not a
;;; restriction to the line); the exceptional set, which must be a subset of
;;; [c,d] and is therefore S INTERSECTED with it, still countable by
;;; `countable-subset'; and the derivative, which is LOCAL and transports by
;;; `has-deriv-at-local' over an interval inside [c,d].
;;; =====================================================================

;;; the inclusion of the intervals; nothing in the tree states it.
(sp (make-wff "forall([a in rr, b in rr, pcv_ in rr, pdv_ in rr],
   a <= pcv_ implies pdv_ <= b implies
   subset(ccint(pcv_, pdv_), ccint(a, b)))"))
(dk-peel!)
(let ((w (subset-by-element!)))
  (p2-ccint-parts! w 'pcv_ 'pdv_)
  (mac 'ccint-membership)
  (p2-conj-ineq!
   (list (list 'IN w 'RR) '(IN a RR) '(IN b RR) '(IN pcv_ RR) '(IN pdv_ RR)
         '(<= a pcv_) '(<= pdv_ b)
         (list '<= 'pcv_ w) (list '<= w 'pdv_))))
(qed 'ccint-subset-ccint)
(topic! 'ccint-subset-ccint 'analysis)
(alias! 'ccint-subset-ccint "a closed subinterval is a subset")

(define p2-rcd '(RESTRICT pwf_ (CCINT pcv_ pdv_)))
(define p2-rphi '(RESTRICT pphi_ (CCINT pcv_ pdv_)))
(define p2-cd '(CCINT pcv_ pdv_))

(sp (make-wff "forall([a in rr, b in rr, pcv_ in rr, pdv_ in rr],
   forall([pwf_, pphi_],
     is-primitive(pwf_, pphi_, a, b) implies
     a <= pcv_ implies pcv_ < pdv_ implies pdv_ <= b implies
     is-primitive(restrict(pwf_, ccint(pcv_, pdv_)),
                          restrict(pphi_, ccint(pcv_, pdv_)),
                          pcv_, pdv_)))"))
(dk-peel!)
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'ccint-subset-ccint 'a 'b 'pcv_ 'pdv_)
(fact 'restrict-in-fun 'pwf_ p2-cc 'RR p2-cd)
(fact 'restrict-in-fun 'pphi_ p2-cc 'RR p2-cd)
(fact 'ooint-subset-ccint 'pcv_ 'pdv_)
(fact 'rr-is-metric-space)
(dk-have! '(SUBSET (CCINT a b) (PTS RR-MS))
  (lambda () (slot 'PTS) (fact 'ccint-subset-rr 'a 'b) (ass)))
;; the continuity of the restriction, on the SMALLER subspace
(dk-have! (list 'IS-CONTINUOUS-ON p2-rcd p2-cd)
  (lambda ()
    (let ((cu (begin
                (dk-split-all!
                 (dk-landed* (lambda ()
                   (mac-h 'IS-CONTINUOUS-ON
                          (list 'IS-CONTINUOUS-ON 'pwf_ p2-cc)))))
                (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                           (dk-contains? fm 'IS-CONTINUOUS-AT)))
                         "the continuity universal on [a,b]"))))
      (mac 'IS-CONTINUOUS-ON)
      (dk-conj-close!
       (lambda ()
         (if (not (eq? (p2-head (dk-goal)) 'FORALL))
             (ass)
             (let ((z (dk-di-var!)))
               (fact 'subset-mem-fwd p2-cd p2-cc z)
               (dk-apply! cu z)
               (fact 'subspace-restrict-continuous-at 'RR-MS p2-cc p2-cd
                     'RR-MS 'pwf_ z)
               (ass))))))))
;; the exceptional set, cut down to [c,d]
(let* ((s1 (dk-skolem! (dk-fact! 'primitive-exceptional-set
                                 'pwf_ 'pphi_ 'a 'b)))
       (d1 (begin (dk-split-all!)
                  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm 'HAS-DERIV-AT)
                                             (dk-contains? fm s1)))
                           "the derivative universal")))
       (sx (list 'INTERSECTION s1 p2-cd)))
  (dk-have! (list 'SUBSET sx s1)
    (lambda ()
      (let* ((w  (subset-by-element!))
             (im (dk-fact! 'intersection-membership s1 p2-cd w)))
        (dk-only! im (list 'IN w sx))
        (prop))))
  (dk-have! (list 'SUBSET sx p2-cd)
    (lambda ()
      (let* ((w  (subset-by-element!))
             (im (dk-fact! 'intersection-membership s1 p2-cd w)))
        (dk-only! im (list 'IN w sx))
        (prop))))
  (fact 'countable-subset sx s1)
  (dk-have! (list 'FORALL 'pat_
              (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT 'pcv_ 'pdv_))
                (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sx))
                      (list 'HAS-DERIV-AT p2-rcd 'pat_ (list p2-rphi 'pat_)))))
    (lambda ()
      (dk-peel!)
      (fact 'subset-mem-fwd (list 'OOINT 'pcv_ 'pdv_) p2-cd 'pat_)
      ;; the inner radius is taken BEFORE `mac-h' consumes the membership.
      (let ((rv (dk-skolem! (dk-fact! 'ooint-inner-radius 'pcv_ 'pdv_ 'pat_))))
        (dk-split-all!)
        (p2-ooint-parts! 'pat_ 'pcv_ 'pdv_)
        (let ((im (dk-fact! 'intersection-membership s1 p2-cd 'pat_)))
          (dk-have! (list 'NOT (list 'IN 'pat_ s1))
            (lambda ()
              (dk-only! im (list 'NOT (list 'IN 'pat_ sx))
                        (list 'IN 'pat_ p2-cd))
              (prop))))
        (p2-in-ooint! 'pat_ 'a 'b
                      (list '(IN pat_ RR) '(IN a RR) '(IN b RR)
                            '(IN pcv_ RR) '(IN pdv_ RR)
                            '(<= a pcv_) '(<= pdv_ b)
                            '(< pcv_ pat_) '(< pat_ pdv_)))
        (fact 'subset-mem-fwd '(OOINT a b) p2-cc 'pat_)
        (fact 'fun-apply-type-c 'pphi_ p2-cc 'RR 'pat_)
        (dk-apply! d1 'pat_)
        (fact 'rr-pos-rr-in-rr rv)
        (fact 'rr-sub-in-rr 'pat_ rv)
        (fact 'rr-add-in-rr 'pat_ rv)
        (let ((oo (list 'OOINT (list '- 'pat_ rv) (list '+ 'pat_ rv))))
          (fact 'restrict-in-fun p2-rcd p2-cd 'RR oo)
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ oo)
                      (list '== (list p2-rcd 'hbx_) '(pwf_ hbx_))))
            (lambda ()
              (let ((y (dk-di-var!)))
                (fact 'subset-mem-fwd oo p2-cd y)
                (fact 'restrict-apply 'pwf_ p2-cd y)
                (ass))))
          (fact 'has-deriv-at-local rv p2-rcd 'pwf_ 'pat_ '(pphi_ pat_))
          (fact 'restrict-apply 'pphi_ p2-cd 'pat_)
          (subst (list '== (list p2-rphi 'pat_) '(pphi_ pat_)))
          (ass)))))
  (mac 'IS-PRIMITIVE)
  (dk-conj-close!
   (lambda ()
     (if (not (eq? (p2-head (dk-goal)) 'FORSOME))
         (ass)
         (begin
           (ew sx)
           (dk-conj-close! (lambda () (ass))))))))
(qed 'pw-antiderivative-restrict)
(topic! 'pw-antiderivative-restrict 'analysis)
(alias! 'pw-antiderivative-restrict
        "Remark 4.9"
        "a piecewise antiderivative restricts to a subinterval")

;;; =====================================================================
;;; (4) ADDITIVITY OVER TWO ADJACENT INTERVALS.
;;;
;;; The notes do not number it, but it is the immediate consequence of
;;; Remark 4.9 and equation (64), and every later estimate uses it: for
;;; a < c < b the integral over [a,b] is the sum of the integrals of the two
;;; RESTRICTIONS.  The midpoint is STRICTLY inside -- at c = a the left
;;; interval is degenerate and PW-INT(phi, a, a) does not denote.
;;; =====================================================================

(define p2-lcc '(CCINT a pcv_))
(define p2-rcc '(CCINT pcv_ b))

(sp (make-wff "forall([a in rr, b in rr, pcv_ in ooint(a, b)],
   forall([pwf_, pphi_],
     is-primitive(pwf_, pphi_, a, b) implies
     pw-int(pphi_, a, b)
       = pw-int(restrict(pphi_, ccint(a, pcv_)), a, pcv_)
       + pw-int(restrict(pphi_, ccint(pcv_, b)), pcv_, b)))"))
(dk-peel!)
(p2-ooint-parts! 'pcv_ 'a 'b)
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(p2-endpoints!)
(fact 'rr-leq-reflexive 'pcv_)
(dk-have! '(<= a pcv_)
  (lambda () (dk-ineq! '(IN a RR) '(IN pcv_ RR) '(< a pcv_))))
(dk-have! '(<= pcv_ b)
  (lambda () (dk-ineq! '(IN b RR) '(IN pcv_ RR) '(< pcv_ b))))
(p2-in-ccint! 'pcv_ 'a 'b (list '(IN pcv_ RR) '(<= a pcv_) '(<= pcv_ b)))
(p2-in-ccint! 'a 'a 'pcv_ (list '(IN a RR) '(<= a a) '(<= a pcv_)))
(p2-in-ccint! 'pcv_ 'a 'pcv_
              (list '(IN pcv_ RR) '(<= a pcv_) '(<= pcv_ pcv_)))
(p2-in-ccint! 'pcv_ 'pcv_ 'b
              (list '(IN pcv_ RR) '(<= pcv_ pcv_) '(<= pcv_ b)))
(p2-in-ccint! 'b 'pcv_ 'b (list '(IN b RR) '(<= pcv_ b) '(<= b b)))
(for-each (lambda (z) (fact 'fun-apply-type-c 'pwf_ p2-cc 'RR z))
          '(a b pcv_))
(fact 'pw-antiderivative-restrict 'a 'b 'a 'pcv_ 'pwf_ 'pphi_)
(fact 'pw-antiderivative-restrict 'a 'b 'pcv_ 'b 'pwf_ 'pphi_)
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-int-value (list 'RESTRICT 'pwf_ p2-lcc) (list 'RESTRICT 'pphi_ p2-lcc)
      'a 'pcv_)
(fact 'pw-int-value (list 'RESTRICT 'pwf_ p2-rcc) (list 'RESTRICT 'pphi_ p2-rcc)
      'pcv_ 'b)
(fact 'restrict-apply 'pwf_ p2-lcc 'a)
(fact 'restrict-apply 'pwf_ p2-lcc 'pcv_)
(fact 'restrict-apply 'pwf_ p2-rcc 'pcv_)
(fact 'restrict-apply 'pwf_ p2-rcc 'b)
(subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
(subst (list '= (list 'PW-INT (list 'RESTRICT 'pphi_ p2-lcc) 'a 'pcv_)
             (list '- (list (list 'RESTRICT 'pwf_ p2-lcc) 'pcv_)
                   (list (list 'RESTRICT 'pwf_ p2-lcc) 'a))))
(subst (list '= (list 'PW-INT (list 'RESTRICT 'pphi_ p2-rcc) 'pcv_ 'b)
             (list '- (list (list 'RESTRICT 'pwf_ p2-rcc) 'b)
                   (list (list 'RESTRICT 'pwf_ p2-rcc) 'pcv_))))
(subst (list '== (list (list 'RESTRICT 'pwf_ p2-lcc) 'a) '(pwf_ a)))
(subst (list '== (list (list 'RESTRICT 'pwf_ p2-lcc) 'pcv_) '(pwf_ pcv_)))
(subst (list '== (list (list 'RESTRICT 'pwf_ p2-rcc) 'pcv_) '(pwf_ pcv_)))
(subst (list '== (list (list 'RESTRICT 'pwf_ p2-rcc) 'b) '(pwf_ b)))
(crs)
(qed 'pw-int-adjacent)
(topic! 'pw-int-adjacent 'analysis)
(alias! 'pw-int-adjacent
        "the integral over [a,b] is the sum of the integrals over [a,c] and [c,b]")

;;; =====================================================================
;;; (5) CC-INT: THE VALUE, AND THE TYPING.
;;;
;;; Equation (44) of the user's notes (~/docs/complex-analysis.pdf 3.1) reads
;;;
;;;     int_a^b f(t) dt  =  int_a^b Re f(t) dt  +  i int_a^b Im f(t) dt
;;;
;;; and is the DEFINITION of CC-INT.  These two theorems are what every law
;;; below consumes: the value of CC-INT in terms of one piecewise
;;; antiderivative of each coordinate, and the fact that it is a complex
;;; number.  Both stand under the hypothesis that EACH COORDINATE has a
;;; piecewise antiderivative -- the CC-valued integral is defined exactly when
;;; its two real integrals are, and an IOTA is never certified defined.
;;; =====================================================================

(define (p2-relam f) (list 'VNB-LAMBDA 'pat_ p2-cc (list 'real-part (list f 'pat_))))
(define (p2-imlam f) (list 'VNB-LAMBDA 'pat_ p2-cc (list 'imag-part (list f 'pat_))))

(define (p2-cc-typings! f g)
  (dk-split! (dk-fact! 'primitive-endpoints f (p2-relam 'pphi_) 'a 'b))
  (dk-split-all!)
  (p2-endpoints!)
  (fact 'pw-antiderivative-value-in-rr f (p2-relam 'pphi_) 'a 'b)
  (fact 'pw-antiderivative-value-in-rr g (p2-imlam 'pphi_) 'a 'b)
  (for-each (lambda (h)
              (dk-apply! (dk-pick (lambda (fm)
                                    (and (pair? fm) (eq? (car fm) 'FORALL)
                                         (dk-contains? fm h)))
                                  "the value typing")
                         'a)
              (dk-apply! (dk-pick (lambda (fm)
                                    (and (pair? fm) (eq? (car fm) 'FORALL)
                                         (dk-contains? fm h)))
                                  "the value typing")
                         'b))
            (list f g))
  (fact 'rr-sub-in-rr (list f 'b) (list f 'a))
  (fact 'rr-sub-in-rr (list g 'b) (list g 'a))
  (fact 'rr-subset-cc (list '- (list f 'b) (list f 'a)))
  (fact 'rr-subset-cc (list '- (list g 'b) (list g 'a)))
  (fact 'cc-i-in)
  (have! (list 'AND (list 'IN (list '- (list g 'b) (list g 'a)) 'CC) '(IN +i CC)))
  (fact 'cc-mul-closed (list '- (list g 'b) (list g 'a)) '+i)
  (have! (list 'AND (list 'IN (list '- (list f 'b) (list f 'a)) 'CC)
               (list 'IN (list '* (list '- (list g 'b) (list g 'a)) '+i) 'CC)))
  (fact 'cc-add-closed (list '- (list f 'b) (list f 'a))
        (list '* (list '- (list g 'b) (list g 'a)) '+i)))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'pwf_ (list 'FORALL 'paw_
         (list 'IMPLIES (list 'IS-PRIMITIVE 'pwf_ (p2-relam 'pphi_) 'a 'b)
         (list 'IMPLIES (list 'IS-PRIMITIVE 'paw_ (p2-imlam 'pphi_) 'a 'b)
           (list '= '(CC-INT pphi_ a b)
                 (list '+ '(- (pwf_ b) (pwf_ a))
                       (list '* '(- (paw_ b) (paw_ a)) '+i)))))))))))
(dk-peel!)
(p2-cc-typings! 'pwf_ 'paw_)
(fact 'pw-int-value 'pwf_ (p2-relam 'pphi_) 'a 'b)
(fact 'pw-int-value 'paw_ (p2-imlam 'pphi_) 'a 'b)
(fact 'cc-int-unfold 'pphi_ 'a 'b)
(subst (list '== '(CC-INT pphi_ a b)
             (list '+ (list 'PW-INT (p2-relam 'pphi_) 'a 'b)
                   (list '* (list 'PW-INT (p2-imlam 'pphi_) 'a 'b) '+i))))
(subst (list '= (list 'PW-INT (p2-relam 'pphi_) 'a 'b) '(- (pwf_ b) (pwf_ a))))
(subst (list '= (list 'PW-INT (p2-imlam 'pphi_) 'a 'b) '(- (paw_ b) (paw_ a))))
(rfl)
(qed 'cc-int-value)
(topic! 'cc-int-value 'analysis)
(alias! 'cc-int-value
        "equation (44)"
        "the complex integral is the endpoint difference of each coordinate primitive")

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'pwf_ (list 'FORALL 'paw_
         (list 'IMPLIES (list 'IS-PRIMITIVE 'pwf_ (p2-relam 'pphi_) 'a 'b)
         (list 'IMPLIES (list 'IS-PRIMITIVE 'paw_ (p2-imlam 'pphi_) 'a 'b)
           '(IN (CC-INT pphi_ a b) CC)))))))))
(dk-peel!)
(p2-cc-typings! 'pwf_ 'paw_)
(fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
(subst (list '= '(CC-INT pphi_ a b)
             (list '+ '(- (pwf_ b) (pwf_ a))
                   (list '* '(- (paw_ b) (paw_ a)) '+i))))
(ass)
(qed 'cc-int-in-cc)
(topic! 'cc-int-in-cc 'analysis)
(alias! 'cc-int-in-cc "the complex integral of an antiderivable function is a complex number")

;;; =====================================================================
;;; (6) THE NOTES' "(44) IS COMPLEX LINEAR IN f": THE SUM.
;;;
;;; Each coordinate of the sum is the sum of the coordinates (`cc-re-add',
;;; `cc-im-add'), so `pw-antiderivative-sum' (Propositions 4.12 / 4.13) gives a
;;; piecewise antiderivative of each coordinate of chi -- the pointwise sum of
;;; the two given ones -- and `cc-int-value' turns the three integrals into
;;; endpoint differences, where the identity is a ring identity in CC.
;;; =====================================================================

;;; the coordinate lane, run once for the real part and once for the
;;; imaginary part.  LAM builds the coordinate lambda, ADDLAW is `cc-re-add' or
;;; `cc-im-add', F and G are the given antiderivatives of the coordinate of phi
;;; and of psi, and S0 is `pw-antiderivative-sum' already instantiated at a, b
;;; (`dk-fact!' of it a second time lands nothing new and would error).
;;; Returns the pointwise sum function, a piecewise antiderivative of the
;;; coordinate of chi.
(define (p2-coord-sum! lam proj addlaw f g s0)
  (let ((gf (list 'VNB-LAMBDA 'pax_ p2-cc (list '+ (list f 'pax_) (list g 'pax_)))))
    (fact 'primitive-in-fun f (lam 'pphi_) 'a 'b)
    (fact 'primitive-in-fun g (lam 'ppsi_) 'a 'b)
    (dk-have! (list 'IN gf (list 'FUN p2-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p2-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c f p2-cc 'RR z)
                 (fact 'fun-apply-type-c g p2-cc 'RR z)
                 (have! (list 'AND (list 'IN (list f z) 'RR)
                              (list 'IN (list g z) 'RR)))
                 (fact 'rr-add-closed (list f z) (list g z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                (list '== (list gf 'pay_)
                      (list '+ (list f 'pay_) (list g 'pay_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (dk-lam-b!)
          (qrfl))))
    ;; the coordinate of chi: a function on [a,b], and the sum of the
    ;; coordinates of phi and psi.
    (dk-have! (list 'IN (lam 'pchi_) (list 'FUN p2-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p2-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c 'pchi_ p2-cc 'CC z)
                 (fact 'real-part-in-rr (list 'pchi_ z))
                 (fact 'imag-part-in-rr (list 'pchi_ z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                (list '== (list (lam 'pchi_) 'pay_)
                      (list '+ (list (lam 'pphi_) 'pay_)
                            (list (lam 'ppsi_) 'pay_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (fact 'fun-apply-type-c 'pphi_ p2-cc 'CC z)
          (fact 'fun-apply-type-c 'ppsi_ p2-cc 'CC z)
          (dk-apply! p2-sum-agree z)
          (dk-lam-b!)
          (subst (list '== (list 'pchi_ z)
                       (list '+ (list 'pphi_ z) (list 'ppsi_ z))))
          (fact addlaw (list 'pphi_ z) (list 'ppsi_ z))
          (subst (list '= (list proj (list '+ (list 'pphi_ z) (list 'ppsi_ z)))
                       (list '+ (list proj (list 'pphi_ z))
                             (list proj (list 'ppsi_ z)))))
          (qrfl))))
    (dk-split! (dk-apply! (dk-apply! s0 f g (lam 'pphi_) (lam 'ppsi_))
                          gf (lam 'pchi_)))
    gf))

(define (p2-vals-in-rr! f lam)
  (let ((u (dk-fact! 'pw-antiderivative-value-in-rr f lam 'a 'b)))
    (dk-apply! u 'a)
    (dk-apply! u 'b)))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'ppsi_ (list 'FORALL 'pchi_
         (list 'IMPLIES (list 'IN 'pphi_ (list 'FUN p2-cc 'CC))
         (list 'IMPLIES (list 'IN 'ppsi_ (list 'FUN p2-cc 'CC))
         (list 'IMPLIES (list 'IN 'pchi_ (list 'FUN p2-cc 'CC))
         (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                          '(== (pchi_ pay_) (+ (pphi_ pay_) (ppsi_ pay_)))))
           (list 'FORALL 'pwf_ (list 'FORALL 'paw_ (list 'FORALL 'pauh_
             (list 'FORALL 'pbw_
               (list 'IMPLIES
                     (list 'IS-PRIMITIVE 'pwf_ (p2-relam 'pphi_) 'a 'b)
               (list 'IMPLIES
                     (list 'IS-PRIMITIVE 'paw_ (p2-imlam 'pphi_) 'a 'b)
               (list 'IMPLIES
                     (list 'IS-PRIMITIVE 'pauh_ (p2-relam 'ppsi_) 'a 'b)
               (list 'IMPLIES
                     (list 'IS-PRIMITIVE 'pbw_ (p2-imlam 'ppsi_) 'a 'b)
                 '(= (CC-INT pchi_ a b)
                     (+ (CC-INT pphi_ a b) (CC-INT ppsi_ a b)))))))))))))))))))))
(dk-peel!)
(define p2-sum-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)
                             (dk-contains? fm 'ppsi_)))
           "the pointwise sum of the integrands"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ (p2-relam 'pphi_) 'a 'b))
(dk-split-all!)
(p2-endpoints!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set p2-cc 'RR)
(fact 'cc-i-in)
(let* ((s0 (dk-fact! 'pw-antiderivative-sum 'a 'b))
       (g1 (p2-coord-sum! p2-relam 'real-part 'cc-re-add 'pwf_ 'pauh_ s0))
       (g2 (p2-coord-sum! p2-imlam 'imag-part 'cc-im-add 'paw_ 'pbw_ s0)))
  (p2-vals-in-rr! 'pwf_ (p2-relam 'pphi_))
  (p2-vals-in-rr! 'paw_ (p2-imlam 'pphi_))
  (p2-vals-in-rr! 'pauh_ (p2-relam 'ppsi_))
  (p2-vals-in-rr! 'pbw_ (p2-imlam 'ppsi_))
  (fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
  (fact 'cc-int-value 'a 'b 'ppsi_ 'pauh_ 'pbw_)
  (fact 'cc-int-value 'a 'b 'pchi_ g1 g2)
  (subst (list '= '(CC-INT pchi_ a b)
               (list '+ (list '- (list g1 'b) (list g1 'a))
                     (list '* (list '- (list g2 'b) (list g2 'a)) '+i))))
  (subst '(= (CC-INT pphi_ a b)
             (+ (- (pwf_ b) (pwf_ a)) (* (- (paw_ b) (paw_ a)) +i))))
  (subst '(= (CC-INT ppsi_ a b)
             (+ (- (pauh_ b) (pauh_ a)) (* (- (pbw_ b) (pbw_ a)) +i))))
  (dk-lam-b!)
  (crs))
(qed 'cc-int-sum)
(topic! 'cc-int-sum 'analysis)
(alias! 'cc-int-sum
        "the complex integral is additive in the integrand")

;;; =====================================================================
;;; (7) THE REAL SCALAR MULTIPLE OF A CC-VALUED INTEGRAND.
;;;
;;; With (6) this is the notes' "(44) is linear in f" over the REALS: each
;;; coordinate of c*phi is c times the coordinate of phi
;;; (`cc-re-real-mul', `cc-im-real-mul'), so `pw-antiderivative-real-mul'
;;; (Proposition 4.12) applies coordinatewise.  The COMPLEX scalar is the same
;;; argument with the 2x2 real matrix of w and is NOT proved here: see the
;;; report.
;;; =====================================================================

(define (p2-coord-mul! lam proj mullaw f s0)
  (let ((gf (list 'VNB-LAMBDA 'pax_ p2-cc (list '* 'pcc_ (list f 'pax_)))))
    (fact 'primitive-in-fun f (lam 'pphi_) 'a 'b)
    (dk-have! (list 'IN gf (list 'FUN p2-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p2-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c f p2-cc 'RR z)
                 (have! (list 'AND '(IN pcc_ RR) (list 'IN (list f z) 'RR)))
                 (fact 'rr-mul-closed 'pcc_ (list f z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                (list '== (list gf 'pay_) (list '* 'pcc_ (list f 'pay_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (dk-lam-b!)
          (qrfl))))
    (dk-have! (list 'IN (lam 'pchi_) (list 'FUN p2-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p2-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c 'pchi_ p2-cc 'CC z)
                 (fact 'real-part-in-rr (list 'pchi_ z))
                 (fact 'imag-part-in-rr (list 'pchi_ z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                (list '== (list (lam 'pchi_) 'pay_)
                      (list '* 'pcc_ (list (lam 'pphi_) 'pay_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (fact 'fun-apply-type-c 'pphi_ p2-cc 'CC z)
          (dk-apply! p2-mul-agree z)
          (dk-lam-b!)
          (subst (list '== (list 'pchi_ z) (list '* 'pcc_ (list 'pphi_ z))))
          (fact mullaw 'pcc_ (list 'pphi_ z))
          (subst (list '= (list proj (list '* 'pcc_ (list 'pphi_ z)))
                       (list '* 'pcc_ (list proj (list 'pphi_ z)))))
          (qrfl))))
    (dk-split! (dk-apply! (dk-apply! s0 f (lam 'pphi_) 'pcc_) gf (lam 'pchi_)))
    gf))

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'pchi_ (list 'FORALL 'pcc_
         (list 'IMPLIES '(IN pcc_ RR)
         (list 'IMPLIES (list 'IN 'pphi_ (list 'FUN p2-cc 'CC))
         (list 'IMPLIES (list 'IN 'pchi_ (list 'FUN p2-cc 'CC))
         (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p2-cc)
                          '(== (pchi_ pay_) (* pcc_ (pphi_ pay_)))))
           (list 'FORALL 'pwf_ (list 'FORALL 'paw_
             (list 'IMPLIES
                   (list 'IS-PRIMITIVE 'pwf_ (p2-relam 'pphi_) 'a 'b)
             (list 'IMPLIES
                   (list 'IS-PRIMITIVE 'paw_ (p2-imlam 'pphi_) 'a 'b)
               '(= (CC-INT pchi_ a b) (* pcc_ (CC-INT pphi_ a b)))))))))))))))))
(dk-peel!)
(define p2-mul-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)
                             (dk-contains? fm 'pcc_)))
           "the pointwise multiple of the integrand"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ (p2-relam 'pphi_) 'a 'b))
(dk-split-all!)
(p2-endpoints!)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set p2-cc 'RR)
(fact 'cc-i-in)
(let* ((s0 (dk-fact! 'pw-antiderivative-real-mul 'a 'b))
       (g1 (p2-coord-mul! p2-relam 'real-part 'cc-re-real-mul 'pwf_ s0))
       (g2 (p2-coord-mul! p2-imlam 'imag-part 'cc-im-real-mul 'paw_ s0)))
  (p2-vals-in-rr! 'pwf_ (p2-relam 'pphi_))
  (p2-vals-in-rr! 'paw_ (p2-imlam 'pphi_))
  (fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
  (fact 'cc-int-value 'a 'b 'pchi_ g1 g2)
  (subst (list '= '(CC-INT pchi_ a b)
               (list '+ (list '- (list g1 'b) (list g1 'a))
                     (list '* (list '- (list g2 'b) (list g2 'a)) '+i))))
  (subst '(= (CC-INT pphi_ a b)
             (+ (- (pwf_ b) (pwf_ a)) (* (- (paw_ b) (paw_ a)) +i))))
  (dk-lam-b!)
  (crs))
(qed 'cc-int-real-mul)
(topic! 'cc-int-real-mul 'analysis)
(alias! 'cc-int-real-mul
        "the complex integral is homogeneous under a real scalar")
