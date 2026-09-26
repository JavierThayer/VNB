;;; pw-int-laws-3.scm -- LINEARITY over the reals as ONE law, the COMPLEX
;;; scalar, and the additivity of the complex integral over adjacent
;;; intervals.  Continues theorem-library/pw-int-laws-2.scm.
;;;
;;; THE SOURCES.  ~/docs/calculus.pdf chapter 4 for the real integral and
;;; ~/docs/complex-analysis.pdf 3.1 for the complex one:
;;;
;;;   Proposition 4.12  "The definite integral is a linear functional on the
;;;                      space of antiderivable functions on [a,b]."
;;;                      Its two halves, `pw-antiderivative-sum' (4.13) and
;;;                      `pw-antiderivative-real-mul', are proven; a general
;;;                      LINEAR COMBINATION c F + d G is the two of them
;;;                      composed, and is stated once here as
;;;                      `pw-antiderivative-linear' because the complex scalar
;;;                      uses it twice.
;;;   (44), and the sentence after it, "it follows easily that (44) is complex
;;;                      linear in f".  The SUM and the REAL scalar are
;;;                      `cc-int-sum' and `cc-int-real-mul' (batch 17-A); the
;;;                      COMPLEX scalar is `cc-int-complex-mul' here, and with
;;;                      it "(44) is complex linear in f" is complete.
;;;   the additivity over two adjacent intervals, which the notes do not
;;;                      number: `cc-int-adjacent', the complex twin of
;;;                      `pw-int-adjacent'.
;;;
;;; ---------------------------------------------------------------------
;;; THE COMPLEX SCALAR, AND WHY NO APPEAL TO i * i = -1 IS NEEDED.
;;;
;;; For w and z complex, `cc-re-mul' and `cc-im-mul' give
;;;
;;;     re(w z) = re(w) re(z) - im(w) im(z),  im(w z) = re(w) im(z) + im(w) re(z),
;;;
;;; so each COORDINATE of w phi is a real LINEAR COMBINATION of the two
;;; coordinates of phi -- which is exactly what `pw-antiderivative-linear'
;;; integrates.  The final identity is then between two complex numbers each
;;; written as X + Y i with the SAME real X and Y: on the left by (44) applied
;;; to w phi, on the right by `cc-re-im-decompose' applied to w * CC-INT(phi)
;;; after `cc-re-im-of' has named the coordinates of CC-INT(phi).  No
;;; multiplication of i by i occurs anywhere, so `cc-i-squared' is not cited.
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT CHECKS, against CLAUDE.md's species of false or
;;; underdetermined statement, made before any proof was written.
;;;
;;; (1) NO STRICT `=' ON A PW-INT OR CC-INT TERM WITHOUT AN ANTIDERIVATIVE.
;;;     PW-INT is an IOTA and an IOTA is never certified defined (the LUTINS
;;;     rule); CC-INT is a sum of two of them.  Every equation below therefore
;;;     stands under IS-PRIMITIVE hypotheses that earn the
;;;     definedness, exactly as `pw-int-value' and `cc-int-value' do: two for
;;;     `cc-int-complex-mul' and `cc-int-adjacent' (one per coordinate of the
;;;     integrand), and for the restricted integrals of `cc-int-adjacent' the
;;;     definedness is Remark 4.9 (`pw-antiderivative-restrict').
;;;
;;; (2) THE SCALARS ARE TYPED.  c and d are guarded `in rr' and w `in cc';
;;;     without those guards `pcc_ * pwf_(y)' is arithmetic on an untyped
;;;     argument and the pointwise typing of the combination fails.
;;;
;;; (3) THE COMBINATION IS A GIVEN FUNCTION, NOT A TERM.  The tree has no
;;;     addition and no scalar multiplication on FUN(A, RR), so `c F + d G' is
;;;     a given `pauh_' agreeing POINTWISE with it, with its own FUN typing --
;;;     the shape `pw-antiderivative-sum' and `pw-antiderivative-real-mul' use.
;;;     The FUN typings of pauh_ and pchi_ are hypotheses and are not
;;;     redundant: pointwise agreement says nothing about a function being a
;;;     set of pairs at all.
;;;
;;; (4) THE MIDPOINT OF `cc-int-adjacent' IS STRICTLY INSIDE, `pcv_ in
;;;     ooint(a, b)': IS-PRIMITIVE carries `a < b' as a conjunct, so a
;;;     degenerate half-interval is not one, and `pw-int-adjacent' (on which
;;;     this rests) carries the same guard for the same reason.
;;;
;;; (5) THE RESTRICTED INTEGRAND OF `cc-int-adjacent'.  CC-INT of the
;;;     restriction of phi to [a, c] takes the coordinates of THAT function
;;;     over [a, c]; Remark 4.9 (`pw-antiderivative-restrict') produces instead
;;;     the RESTRICTION of the coordinate of phi over [a, b].  The two are
;;;     different TERMS with the same values, and
;;;     `pw-antiderivative-integrand-congruence' identifies them; the
;;;     congruence needs the FUN typing of the second, which is
;;;     `restrict-in-fun' over `ccint-subset-ccint'.
;;;
;;; ---------------------------------------------------------------------
;;; Helper prefix: p3-.  Binder names: p3-lambdas use `pax_' and `pat_', as
;;; pw-int-laws-2.scm does (the coordinate lambdas of CC-INT are built with
;;; `pat_' by the definition itself, so a coordinate lambda must use that
;;; binder or it is a different term).
;;;
;;; Dependencies: structure-library/path-integral.scm;
;;; theorem-library/pw-antiderivative-laws.scm (pw-int-value,
;;; pw-antiderivative-sum, pw-antiderivative-integrand-congruence), pw-int-laws-2.scm
;;; (pw-antiderivative-real-mul, pw-antiderivative-restrict, pw-int-adjacent,
;;; cc-int-value, ccint-subset-ccint), cc-basics / cc-coords (cc-re-mul,
;;; cc-im-mul, cc-re-im-of, cc-re-im-decompose, real-part-in-rr,
;;; imag-part-in-rr).

;;; ---- file-local driver helpers ---------------------------------------

(define (p3-head g) (and (pair? g) (car g)))

(define p3-cc '(CCINT a b))

(define (p3-relam f dm) (list 'VNB-LAMBDA 'pat_ dm (list 'real-part (list f 'pat_))))
(define (p3-imlam f dm) (list 'VNB-LAMBDA 'pat_ dm (list 'imag-part (list f 'pat_))))

(define (p3-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

(define (p3-in-ccint! z lo hi prems)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (p3-conj-ineq! prems))))

;;; the endpoint typings of [a,b] that every endpoint difference needs
(define (p3-endpoints!)
  (fact 'rr-leq-reflexive 'a)
  (fact 'rr-leq-reflexive 'b)
  (dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
  (p3-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
  (p3-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b))))

;;; [a,b] is a SET -- the second subgoal of every `lam-t' below
(define (p3-ccint-is-set!)
  (fact 'rr-is-set)
  (fact 'ccint-subset-rr 'a 'b)
  (fact 'subclass-of-set-is-set p3-cc 'RR))

;;; =====================================================================
;;; (1) THE LINEAR COMBINATION -- Proposition 4.12 in one formula.
;;; =====================================================================

(sp (make-wff "forall([a in rr, b in rr],
   forall([pcc_ in rr, pdd_ in rr],
   forall([pwf_, paw_, pphi_, ppsi_],
     is-primitive(pwf_, pphi_, a, b) implies
     is-primitive(paw_, ppsi_, a, b) implies
     forall([pauh_ in fun(ccint(a,b), rr), pchi_ in fun(ccint(a,b), rr)],
       forall([pay_ in ccint(a,b)],
              pauh_(pay_) == pcc_ * pwf_(pay_) + pdd_ * paw_(pay_)) implies
       forall([pay_ in ccint(a,b)],
              pchi_(pay_) == pcc_ * pphi_(pay_) + pdd_ * ppsi_(pay_)) implies
       is-primitive(pauh_, pchi_, a, b) and
       pw-int(pchi_, a, b)
         = pcc_ * pw-int(pphi_, a, b) + pdd_ * pw-int(ppsi_, a, b)))))"))
(dk-peel!)
(define p3-lin-hagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pauh_)))
           "the pointwise combination of the primitives"))
(define p3-lin-iagree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)))
           "the pointwise combination of the integrands"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ 'pphi_ 'a 'b))
(dk-split-all!)
(p3-endpoints!)
(p3-ccint-is-set!)
(fact 'primitive-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-in-fun 'paw_ 'ppsi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'primitive-integrand-in-fun 'paw_ 'ppsi_ 'a 'b)

;;; c * f, as a function on [a,b], with its typing and its value law
(define (p3-scale! cf f)
  (let ((gf (list 'VNB-LAMBDA 'pax_ p3-cc (list '* cf (list f 'pax_)))))
    (dk-have! (list 'IN gf (list 'FUN p3-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p3-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c f p3-cc 'RR z)
                 (have! (list 'AND (list 'IN cf 'RR) (list 'IN (list f z) 'RR)))
                 (fact 'rr-mul-closed cf (list f z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p3-cc)
                (list '== (list gf 'pay_) (list '* cf (list f 'pay_)))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (dk-lam-b!)
          (qrfl))))
    gf))

(define p3-u1 (p3-scale! 'pcc_ 'pwf_))
(define p3-x1 (p3-scale! 'pcc_ 'pphi_))
(define p3-u2 (p3-scale! 'pdd_ 'paw_))
(define p3-x2 (p3-scale! 'pdd_ 'ppsi_))

;;; the two scalar multiples are piecewise antiderivatives
(let ((r0 (dk-fact! 'pw-antiderivative-real-mul 'a 'b)))
  (dk-split! (dk-apply! (dk-apply! r0 'pwf_ 'pphi_ 'pcc_) p3-u1 p3-x1))
  (dk-split! (dk-apply! (dk-apply! r0 'paw_ 'ppsi_ 'pdd_) p3-u2 p3-x2)))

;;; pauh_ and pchi_ are the pointwise SUMS of those
(define (p3-sum-agree! hh g1 g2 agree)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p3-cc)
              (list '== (list hh 'pay_) (list '+ (list g1 'pay_) (list g2 'pay_)))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'ccint-elt-in-rr 'a 'b z)
        (dk-apply! agree z)
        (dk-lam-b!)
        (ass)))))

(p3-sum-agree! 'pauh_ p3-u1 p3-u2 p3-lin-hagree)
(p3-sum-agree! 'pchi_ p3-x1 p3-x2 p3-lin-iagree)
(dk-split! (dk-apply! (dk-apply! (dk-fact! 'pw-antiderivative-sum 'a 'b)
                                 p3-u1 p3-u2 p3-x1 p3-x2)
                      'pauh_ 'pchi_))

;;; the integral identity, reduced to endpoint values and closed by `crs'
(fact 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-int-value 'paw_ 'ppsi_ 'a 'b)
(fact 'pw-int-value 'pauh_ 'pchi_ 'a 'b)
(for-each (lambda (f)
            (fact 'fun-apply-type-c f p3-cc 'RR 'a)
            (fact 'fun-apply-type-c f p3-cc 'RR 'b))
          '(pwf_ paw_ pauh_))
(dk-apply! p3-lin-hagree 'a)
(dk-apply! p3-lin-hagree 'b)
(dk-conj-close!
 (lambda ()
   (if (eq? (p3-head (dk-goal)) 'IS-PRIMITIVE)
       (ass)
       (begin
         (subst '(= (PW-INT pchi_ a b) (- (pauh_ b) (pauh_ a))))
         (subst '(= (PW-INT pphi_ a b) (- (pwf_ b) (pwf_ a))))
         (subst '(= (PW-INT ppsi_ a b) (- (paw_ b) (paw_ a))))
         (subst '(== (pauh_ a) (+ (* pcc_ (pwf_ a)) (* pdd_ (paw_ a)))))
         (subst '(== (pauh_ b) (+ (* pcc_ (pwf_ b)) (* pdd_ (paw_ b)))))
         (crs)))))
(qed 'pw-antiderivative-linear)
(topic! 'pw-antiderivative-linear 'analysis)
(alias! 'pw-antiderivative-linear
        "a linear combination of primitives is a primitive of the combination")

;;; =====================================================================
;;; (2) THE COMPLEX SCALAR: "(44) IS COMPLEX LINEAR IN f".
;;; =====================================================================

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pphi_ (list 'FORALL 'pchi_ (list 'FORALL 'pcw_
         (list 'IMPLIES '(IN pcw_ CC)
         (list 'IMPLIES (list 'IN 'pphi_ (list 'FUN p3-cc 'CC))
         (list 'IMPLIES (list 'IN 'pchi_ (list 'FUN p3-cc 'CC))
         (list 'IMPLIES (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p3-cc)
                          '(== (pchi_ pay_) (* pcw_ (pphi_ pay_)))))
           (list 'FORALL 'pwf_ (list 'FORALL 'paw_
             (list 'IMPLIES
                   (list 'IS-PRIMITIVE 'pwf_ (p3-relam 'pphi_ p3-cc) 'a 'b)
             (list 'IMPLIES
                   (list 'IS-PRIMITIVE 'paw_ (p3-imlam 'pphi_ p3-cc) 'a 'b)
               '(= (CC-INT pchi_ a b) (* pcw_ (CC-INT pphi_ a b)))))))))))))))))
(dk-peel!)
(define p3-cw-agree
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'pchi_)
                             (dk-contains? fm 'pcw_)))
           "the pointwise complex multiple of the integrand"))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ (p3-relam 'pphi_ p3-cc) 'a 'b))
(dk-split-all!)
(p3-endpoints!)
(p3-ccint-is-set!)
(fact 'cc-i-in)
(fact 'real-part-in-rr 'pcw_)
(fact 'imag-part-in-rr 'pcw_)
(fact 'rr-neg-closed '(imag-part pcw_))
(fact 'primitive-in-fun 'pwf_ (p3-relam 'pphi_ p3-cc) 'a 'b)
(fact 'primitive-in-fun 'paw_ (p3-imlam 'pphi_ p3-cc) 'a 'b)

;;; the coordinate lane.  LAM is the coordinate lambda (p3-relam / p3-imlam),
;;; PROJ the projection it applies, MULLAW `cc-re-mul' or `cc-im-mul', RHS the
;;; function building that law's right-hand side at a complex argument, CF and
;;; DF the two real coefficients and F and G the primitives they multiply, FL
;;; and GL the coordinate lambdas of phi in the same order, PF and PG the
;;; projections those lambdas apply.  S0 is
;;; `pw-antiderivative-linear' already instantiated at a, b (a second `dk-fact!'
;;; of it lands nothing new and would error).  Returns the primitive of the
;;; coordinate of chi.
(define (p3-coord-lin! lam proj mullaw rhs cf df f g fl gl pf pg s0)
  (let ((gf (list 'VNB-LAMBDA 'pax_ p3-cc
                  (list '+ (list '* cf (list f 'pax_))
                           (list '* df (list g 'pax_))))))
    (dk-have! (list 'IN gf (list 'FUN p3-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p3-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c f p3-cc 'RR z)
                 (fact 'fun-apply-type-c g p3-cc 'RR z)
                 (have! (list 'AND (list 'IN cf 'RR) (list 'IN (list f z) 'RR)))
                 (fact 'rr-mul-closed cf (list f z))
                 (have! (list 'AND (list 'IN df 'RR) (list 'IN (list g z) 'RR)))
                 (fact 'rr-mul-closed df (list g z))
                 (fact 'rr-add-in-rr (list '* cf (list f z)) (list '* df (list g z)))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p3-cc)
                (list '== (list gf 'pay_)
                      (list '+ (list '* cf (list f 'pay_))
                               (list '* df (list g 'pay_))))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (dk-lam-b!)
          (qrfl))))
    ;; the coordinate of chi is a function on [a,b] ...
    (dk-have! (list 'IN (lam 'pchi_ p3-cc) (list 'FUN p3-cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p3-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c 'pchi_ p3-cc 'CC z)
                 (fact 'real-part-in-rr (list 'pchi_ z))
                 (fact 'imag-part-in-rr (list 'pchi_ z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    ;; ... and it is that real linear combination of the coordinates of phi
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ p3-cc)
                (list '== (list (lam 'pchi_ p3-cc) 'pay_)
                      (list '+ (list '* cf (list (fl 'pphi_ p3-cc) 'pay_))
                               (list '* df (list (gl 'pphi_ p3-cc) 'pay_))))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr 'a 'b z)
          (fact 'fun-apply-type-c 'pphi_ p3-cc 'CC z)
          (fact 'real-part-in-rr (list 'pphi_ z))
          (fact 'imag-part-in-rr (list 'pphi_ z))
          (dk-apply! p3-cw-agree z)
          (fact mullaw 'pcw_ (list 'pphi_ z))
          ;; the law's right-hand side, rearranged into `cf * X + df * Y':
          ;; a ring identity once the law itself has been substituted in.  It
          ;; is proved on a `=' lane and then used as a rewrite, because the
          ;; goal here is a quasi-equality and `crs' decides `=' goals.
          (dk-have! (list '= (list proj (list '* 'pcw_ (list 'pphi_ z)))
                          (list '+ (list '* cf (list pf (list 'pphi_ z)))
                                   (list '* df (list pg (list 'pphi_ z)))))
            (lambda ()
              (subst (list '= (list proj (list '* 'pcw_ (list 'pphi_ z)))
                           (rhs (list 'pphi_ z))))
              (crs)))
          (dk-lam-b!)
          (subst (list '== (list 'pchi_ z) (list '* 'pcw_ (list 'pphi_ z))))
          (subst (list '= (list proj (list '* 'pcw_ (list 'pphi_ z)))
                       (list '+ (list '* cf (list pf (list 'pphi_ z)))
                                (list '* df (list pg (list 'pphi_ z))))))
          (qrfl))))
    (dk-split! (dk-apply! (dk-apply! (dk-apply! s0 cf df)
                                     f g (fl 'pphi_ p3-cc) (gl 'pphi_ p3-cc))
                          gf (lam 'pchi_ p3-cc)))
    gf))

(define p3-re-w '(real-part pcw_))
(define p3-im-w '(imag-part pcw_))

(define (p3-re-rhs z)
  (list '- (list '* p3-re-w (list 'real-part z))
           (list '* p3-im-w (list 'imag-part z))))
(define (p3-im-rhs z)
  (list '+ (list '* p3-re-w (list 'imag-part z))
           (list '* p3-im-w (list 'real-part z))))

(define (p3-vals-in-rr! f lam)
  (let ((u (dk-fact! 'pw-antiderivative-value-in-rr f lam 'a 'b)))
    (dk-apply! u 'a)
    (dk-apply! u 'b)))

(let* ((s0 (dk-fact! 'pw-antiderivative-linear 'a 'b))
       (g1 (p3-coord-lin! p3-relam 'real-part 'cc-re-mul p3-re-rhs
                          p3-re-w (list '- p3-im-w) 'pwf_ 'paw_
                          p3-relam p3-imlam 'real-part 'imag-part s0))
       ;; The imaginary lane takes its coefficients in the order (im w, re w)
       ;; against (re phi, im phi) -- the COMMUTED form of `cc-im-mul', which
       ;; `crs' rearranges on the `=' lane.  Written in the natural order
       ;; (re w, im w) its FIRST instantiation of S0 would coincide with the
       ;; real lane's, and `dk-apply!' reports a link already in context as
       ;; "the tactic landed no assumption".
       (g2 (p3-coord-lin! p3-imlam 'imag-part 'cc-im-mul p3-im-rhs
                          p3-im-w p3-re-w 'pwf_ 'paw_
                          p3-relam p3-imlam 'real-part 'imag-part s0)))
  (p3-vals-in-rr! 'pwf_ (p3-relam 'pphi_ p3-cc))
  (p3-vals-in-rr! 'paw_ (p3-imlam 'pphi_ p3-cc))
  (fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
  (fact 'cc-int-value 'a 'b 'pchi_ g1 g2)
  (fact 'cc-int-in-cc 'a 'b 'pphi_ 'pwf_ 'paw_)
  (fact 'rr-sub-in-rr '(pwf_ b) '(pwf_ a))
  (fact 'rr-sub-in-rr '(paw_ b) '(paw_ a))
  ;; the coordinates of CC-INT(phi) are the two endpoint differences
  (dk-split! (dk-fact! 'cc-re-im-of '(CC-INT pphi_ a b)
                       '(- (pwf_ b) (pwf_ a)) '(- (paw_ b) (paw_ a))))
  ;; w * CC-INT(phi), written out coordinatewise -- no i * i anywhere
  ;; `cc-mul-closed' has a CONJUNCTIVE antecedent, which `fact' will not split
  ;; (CLAUDE.md): the AND is landed first, or the citation lands the
  ;; implication SILENTLY.
  (have! '(AND (IN pcw_ CC) (IN (CC-INT pphi_ a b) CC)))
  (fact 'cc-mul-closed 'pcw_ '(CC-INT pphi_ a b))
  (fact 'cc-re-mul 'pcw_ '(CC-INT pphi_ a b))
  (fact 'cc-im-mul 'pcw_ '(CC-INT pphi_ a b))
  (fact 'cc-re-im-decompose '(* pcw_ (CC-INT pphi_ a b)))
  ;; the right-hand side, written out coordinatewise.  `cc-re-im-decompose'
  ;; names w * CC-INT(phi) by its own coordinates, `cc-re-mul' / `cc-im-mul'
  ;; expand those, and `cc-re-im-of' replaces the coordinates of CC-INT(phi)
  ;; by the two endpoint differences.  No product i * i occurs.
  (subst (list '= '(* pcw_ (CC-INT pphi_ a b))
               (list '+ '(real-part (* pcw_ (CC-INT pphi_ a b)))
                     (list '* '+i '(imag-part (* pcw_ (CC-INT pphi_ a b)))))))
  (subst (list '= '(real-part (* pcw_ (CC-INT pphi_ a b)))
               (p3-re-rhs '(CC-INT pphi_ a b))))
  (subst (list '= '(imag-part (* pcw_ (CC-INT pphi_ a b)))
               (p3-im-rhs '(CC-INT pphi_ a b))))
  (subst '(= (real-part (CC-INT pphi_ a b)) (- (pwf_ b) (pwf_ a))))
  (subst '(= (imag-part (CC-INT pphi_ a b)) (- (paw_ b) (paw_ a))))
  (subst (list '= '(CC-INT pchi_ a b)
               (list '+ (list '- (list g1 'b) (list g1 'a))
                     (list '* (list '- (list g2 'b) (list g2 'a)) '+i))))
  (dk-lam-b!)
  (crs))
(qed 'cc-int-complex-mul)
(topic! 'cc-int-complex-mul 'analysis)
(alias! 'cc-int-complex-mul
        "the complex integral is homogeneous under a complex scalar")

;;; =====================================================================
;;; (3) ADDITIVITY OF THE COMPLEX INTEGRAL OVER TWO ADJACENT INTERVALS.
;;;
;;; The route does NOT go through `pw-int-adjacent': each coordinate
;;; primitive, RESTRICTED to the half-interval, is a piecewise antiderivative
;;; of the coordinate of the RESTRICTED integrand (Remark 4.9 plus the
;;; integrand congruence, since `restrict(re o phi, [a,c])' and
;;; `re o restrict(phi, [a,c])' are different TERMS with the same values), so
;;; equation (44) applies three times and the identity telescopes.
;;; =====================================================================

(sp (make-wff
     (forall-guarded '(a b) '((IN a RR) (IN b RR))
       (list 'FORALL 'pcv_ (list 'IMPLIES '(IN pcv_ (OOINT a b))
         (list 'FORALL 'pphi_ (list 'FORALL 'pwf_ (list 'FORALL 'paw_
           (list 'IMPLIES (list 'IN 'pphi_ (list 'FUN p3-cc 'CC))
           (list 'IMPLIES
                 (list 'IS-PRIMITIVE 'pwf_ (p3-relam 'pphi_ p3-cc) 'a 'b)
           (list 'IMPLIES
                 (list 'IS-PRIMITIVE 'paw_ (p3-imlam 'pphi_ p3-cc) 'a 'b)
             (list '= '(CC-INT pphi_ a b)
                   (list '+ (list 'CC-INT (list 'RESTRICT 'pphi_ '(CCINT a pcv_))
                                  'a 'pcv_)
                            (list 'CC-INT (list 'RESTRICT 'pphi_ '(CCINT pcv_ b))
                                  'pcv_ 'b)))))))))))))) 
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'ooint-membership '(IN pcv_ (OOINT a b))))))
(dk-split! (dk-fact! 'primitive-endpoints 'pwf_ (p3-relam 'pphi_ p3-cc) 'a 'b))
(dk-split-all!)
(p3-endpoints!)
(dk-have! '(<= a pcv_) (lambda () (dk-ineq! '(IN a RR) '(IN pcv_ RR) '(< a pcv_))))
(dk-have! '(<= pcv_ b) (lambda () (dk-ineq! '(IN pcv_ RR) '(IN b RR) '(< pcv_ b))))
(p3-in-ccint! 'pcv_ 'a 'b (list '(IN pcv_ RR) '(<= a pcv_) '(<= pcv_ b)))
(fact 'rr-leq-reflexive 'pcv_)
;; the four endpoint memberships the value read-offs (`restrict-apply') need
(p3-in-ccint! 'a 'a 'pcv_ (list '(IN a RR) '(<= a a) '(<= a pcv_)))
(p3-in-ccint! 'pcv_ 'a 'pcv_ (list '(IN pcv_ RR) '(<= a pcv_) '(<= pcv_ pcv_)))
(p3-in-ccint! 'pcv_ 'pcv_ 'b (list '(IN pcv_ RR) '(<= pcv_ pcv_) '(<= pcv_ b)))
(p3-in-ccint! 'b 'pcv_ 'b (list '(IN b RR) '(<= pcv_ b) '(<= b b)))

;;; ONE HALF-INTERVAL, ONE COORDINATE.  LO, HI are its endpoints; F the
;;; coordinate primitive on [a,b]; LAMF the coordinate lambda; RINT is
;;; `pw-antiderivative-restrict' already instantiated at a, b, LO, HI -- it is
;;; instantiated ONCE PER INTERVAL, because a repeated instantiation lands
;;; nothing and `dk-apply!' reports that as a failure.  Returns the
;;; restriction of F, a piecewise antiderivative of the coordinate of the
;;; restricted integrand on [LO, HI].
(define (p3-adj-coord! lo hi f lamf rint)
  (let* ((dm (list 'CCINT lo hi))
         (rph (list 'RESTRICT 'pphi_ dm))
         (rf (list 'RESTRICT f dm))
         (src (list 'RESTRICT (lamf 'pphi_ p3-cc) dm))
         (tgt (lamf rph dm)))
    (dk-apply! rint f (lamf 'pphi_ p3-cc))
    (fact 'ccint-subset-ccint 'a 'b lo hi)
    (fact 'restrict-in-fun 'pphi_ p3-cc 'CC dm)
    (fact 'rr-is-set)
    (fact 'ccint-subset-rr lo hi)
    (fact 'subclass-of-set-is-set dm 'RR)
    (dk-have! (list 'IN tgt (list 'FUN dm 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (p3-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c rph dm 'CC z)
                 (fact 'real-part-in-rr (list rph z))
                 (fact 'imag-part-in-rr (list rph z))
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ dm)
                (list '== (list src 'pay_) (list tgt 'pay_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'subset-mem-fwd dm p3-cc z)
          (fact 'ccint-elt-in-rr lo hi z)
          (fact 'restrict-apply (lamf 'pphi_ p3-cc) dm z)
          (fact 'restrict-apply 'pphi_ dm z)
          (subst (list '== (list src z) (list (lamf 'pphi_ p3-cc) z)))
          (dk-lam-b!)
          (subst (list '== (list rph z) (list 'pphi_ z)))
          (qrfl))))
    (fact 'pw-antiderivative-integrand-congruence rf src tgt lo hi)
    rf))

(let* ((rs0 (dk-fact! 'pw-antiderivative-restrict 'a 'b))
       (ri1 (dk-apply! rs0 'a 'pcv_))
       (ri2 (dk-apply! rs0 'pcv_ 'b)))
  (let* ((f1 (p3-adj-coord! 'a 'pcv_ 'pwf_ p3-relam ri1))
         (g1 (p3-adj-coord! 'a 'pcv_ 'paw_ p3-imlam ri1))
         (f2 (p3-adj-coord! 'pcv_ 'b 'pwf_ p3-relam ri2))
         (g2 (p3-adj-coord! 'pcv_ 'b 'paw_ p3-imlam ri2)))
    (let ((u1 (dk-fact! 'pw-antiderivative-value-in-rr 'pwf_
                        (p3-relam 'pphi_ p3-cc) 'a 'b))
          (u2 (dk-fact! 'pw-antiderivative-value-in-rr 'paw_
                        (p3-imlam 'pphi_ p3-cc) 'a 'b)))
      (for-each (lambda (z) (dk-apply! u1 z) (dk-apply! u2 z)) '(a b pcv_)))
    (fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
    (fact 'cc-int-value 'a 'pcv_ (list 'RESTRICT 'pphi_ '(CCINT a pcv_)) f1 g1)
    (fact 'cc-int-value 'pcv_ 'b (list 'RESTRICT 'pphi_ '(CCINT pcv_ b)) f2 g2)
    (for-each
     (lambda (pr)
       (fact 'restrict-apply (car pr) (cadr pr) (caddr pr)))
     (list (list 'pwf_ '(CCINT a pcv_) 'a) (list 'pwf_ '(CCINT a pcv_) 'pcv_)
           (list 'paw_ '(CCINT a pcv_) 'a) (list 'paw_ '(CCINT a pcv_) 'pcv_)
           (list 'pwf_ '(CCINT pcv_ b) 'pcv_) (list 'pwf_ '(CCINT pcv_ b) 'b)
           (list 'paw_ '(CCINT pcv_ b) 'pcv_) (list 'paw_ '(CCINT pcv_ b) 'b)))
    (subst '(= (CC-INT pphi_ a b)
               (+ (- (pwf_ b) (pwf_ a)) (* (- (paw_ b) (paw_ a)) +i))))
    (subst (list '= (list 'CC-INT (list 'RESTRICT 'pphi_ '(CCINT a pcv_)) 'a 'pcv_)
                 (list '+ (list '- (list f1 'pcv_) (list f1 'a))
                       (list '* (list '- (list g1 'pcv_) (list g1 'a)) '+i))))
    (subst (list '= (list 'CC-INT (list 'RESTRICT 'pphi_ '(CCINT pcv_ b)) 'pcv_ 'b)
                 (list '+ (list '- (list f2 'b) (list f2 'pcv_))
                       (list '* (list '- (list g2 'b) (list g2 'pcv_)) '+i))))
    (for-each
     (lambda (eqn) (subst eqn))
     (list (list '== (list f1 'a) '(pwf_ a)) (list '== (list f1 'pcv_) '(pwf_ pcv_))
           (list '== (list g1 'a) '(paw_ a)) (list '== (list g1 'pcv_) '(paw_ pcv_))
           (list '== (list f2 'pcv_) '(pwf_ pcv_)) (list '== (list f2 'b) '(pwf_ b))
           (list '== (list g2 'pcv_) '(paw_ pcv_)) (list '== (list g2 'b) '(paw_ b))))
    (crs)))
(qed 'cc-int-adjacent)
(topic! 'cc-int-adjacent 'analysis)
(alias! 'cc-int-adjacent
        "the complex integral is additive over two adjacent intervals")
