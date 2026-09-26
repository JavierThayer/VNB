;;; rake-inequalities.scm -- the real-inequality leaves of the rake (batch 5,
;;; batch Q), PROVEN.  Nine asserted supports, and the bridge that four of them
;;; turned out to need.
;;;
;;; SCALAR (structure-library/scalar-inequalities.scm)
;;;   rr-young-2          (:25)  a*b <= (a^2+b^2)/2
;;;   rr-amgm-2           (:33)  4ab <= (a+b)^2
;;;   rr-qm-am-2          (:42)  (a+b)^2 <= 2(a^2+b^2)
;;;   rr-cauchy-schwarz-2 (:52)  (a1b1+a2b2)^2 <= (a1^2+a2^2)(b1^2+b2^2)
;;;   rr-bernoulli        (:64)  1 + n*x <= (1+x)^n  for x >= -1, n in NN
;;; ORDER (structure-library/order-predicates.scm)
;;;   rr-pos-shrink       (:96)  below every positive real sits a smaller one
;;; FINITE SUMS (theorem-library/analysis-inequalities.scm)
;;;   finsum-sq-nonneg    (:20)  0 <= SUM a(i)^2
;;;   finsum-le-termwise  (:30)  a <= b pointwise  =>  SUM a <= SUM b
;;;   finsum-abs-triangle (:41)  |SUM a| <= SUM |a|
;;;
;;; Every statement is copied LITERALLY from its support site.
;;;
;;; THE FOUR POLYNOMIAL ONES ARE ONE TACTIC CALL EACH, and the tactic is `sos'.
;;; Each warrant said so ("closed by (sos \"a - b\")") and nobody had run it.  The
;;; one wrinkle is rr-young-2's `/': `cvnb->poly' (comm-ring-simplify.scm) has no
;;; division case, so `(/ X 2)' is an opaque generator to the oracle and the
;;; difference is not a polynomial at all.  One `(mac 'binary-divide-def)' turns
;;; it into `X * recip(2)', and `recip(2)' IS ground arithmetic (arith-eval.scm
;;; has a `recip' case), so it normalises to the rational coefficient 1/2 and the
;;; certificate is 1/2*(a-b)^2.  `sos' is a trusted oracle: it contributes no
;;; leaf to a bill, only an `[oracles: sos]' note.
;;;
;;; rr-bernoulli IS AN INDUCTION STATED WITH THE INDUCTION VARIABLE SECOND
;;; (x first, n second), which `ni' cannot see -- it tests the goal's shape
;;; literally.  The companion `rr-bernoulli-ind' states it with n OUTERMOST and
;;; the support's own statement follows in three lines, the pattern batch 1
;;; recorded for `strictly-mono-ge-id'.
;;;
;;; THE BRIDGE THE THREE FINSUM LEAVES NEEDED, AND WHY IT DID NOT EXIST.  All
;;; three sum over `COMMUTATIVE-RING-ADDITIVE-AG(RR-NORMED-FIELD)', and BEFORE
;;; THIS FILE NOTHING IN THE TREE MENTIONED THAT TERM except the three supports
;;; themselves -- no carrier, no identity, no operation, not even that it is an
;;; abelian group.  The bridge cannot come from the view's own typing axiom:
;;; `commutative-ring-additive-ag-is-abelian-group' is guarded on
;;; IS-COMMUTATIVE-RING(r), and IS-COMMUTATIVE-RING(RR-NORMED-FIELD) is FALSE --
;;; the ring predicates pin length(s) = 6 and a normed field is a 7-tuple
;;; (structure-library/normed-field.scm:70-78, where the axioms asserting
;;; otherwise were removed in 2026-05-30 as inconsistent).
;;;
;;; What makes it work instead is that the two views have the SAME SOURCE SLOT
;;; LIST: `def-functor' builds the functoid `(LIST (c1 r) ... (cn r))', and
;;; COMMUTATIVE-RING-ADDITIVE-AG and NORMED-FIELD-ADDITIVE-AG (views.scm:84, :93)
;;; both read (CARR ADD ZERO NEG).  So the two constructors are QUASI-EQUAL at
;;; every argument -- `cra-ag-is-nf-ag', four lines, the trick batch M recorded
;;; for `cra-is-rag' -- and the normed-field view's typing axiom, whose guard
;;; `rr-is-normed-field' is PROVEN, transports across it.  The three slot
;;; read-offs are then theorem-library/normed-field-ring-view.scm's five-step
;;; recipe (slot, functoid unfold, nth-r, source slot, qrfl); `cra-ag-rr-carr'
;;; is the SAME-SYMBOL case (CARR read off CARR) and fires the instance macete
;;; `rr-normed-field@carr' BEFORE the `slot', which is what keeps the goal's
;;; right-hand side out of the rewrite.
;;;
;;; THE NONNEGATIVE REALS AS A SUBCLASS.  `finsum-in-subset'
;;; (theorem-library/rake-finsum-typing.scm) says a finite sum stays in any
;;; IDEN-containing, OPR-closed subclass of an abelian group, and `sm' there is an
;;; arbitrary CLASS term -- no sethood is asked.  So `{t_ in RR | 0 <= t_}' is a
;;; legal instance and `finsum-rr-nonneg' is that instance: no induction, no
;;; fold-length argument, no FIN-ENUM transfer.  finsum-sq-nonneg is then eight
;;; lines and finsum-le-termwise applies it to the DIFFERENCE family.
;;;
;;; ONE MECHANISM DOMINATES THE LAST TWO PROOFS, and it is a trap worth stating.
;;; The operation read-off `cra-ag-rr-opr-apply' is GUARDED on both arguments
;;; being real.  Applying it with `mac-h' to an assumption that carries a
;;; VNB-LAMBDA rewrites the occurrence UNDER THE BINDER too, and the spawned
;;; side-condition `a(z) in rr' is posted in the OUTER context, where z is FREE
;;; and nothing types it -- six unclosable leaves, the `pi-lambda-beta!' species
;;; of defect one level up.  Both proofs therefore never rewrite under a binder:
;;; each `finsum-add-ag' instance is combined with `finsum-congruence' oriented so
;;; that only the TOP-LEVEL `(OPR ag)(FINSUM .., FINSUM ..)' is opened, by a
;;; `have!' of its own instance equation, and the arithmetic is finished by `ineq'
;;; on named premises.
;;;
;;; THE THREE THAT ARE NOT HERE, and the route each needs.
;;; `cauchy-schwarz-finite' (analysis-inequalities.scm:53) is the discriminant
;;; argument: 0 <= SUM (a_i - t b_i)^2 for every real t, expanded by
;;; `finsum-add-ag' three times and `finsum-ring-distrib-left-gen' (to pull the
;;; scalars t and t^2 out of the two cross sums), gives A - 2tC + t^2 B >= 0 with
;;; A = SUM a^2, B = SUM b^2, C = SUM ab; `finsum-rr-nonneg' above supplies the
;;; left-hand side.  What is missing is the last step -- a nonnegative real
;;; quadratic has nonpositive discriminant -- which the tree does not have and
;;; which needs the B = 0 case split plus one division (t := C/B); that is a
;;; scalar lemma (`rr-quadratic-nonneg-discriminant') worth stating on its own,
;;; not a finsum fact.  `cauchy-schwarz-sqrt' (:74) and `minkowski-l2' (:90) sit
;;; on top of it and additionally need SQRT monotonicity and
;;; sqrt(x)*sqrt(y) = sqrt(xy) over the nonnegative reals.  `holder-finite'
;;; (:107) rests on the axiomatic RPOW and is out of reach until a^b is
;;; constructed.
;;;
;;; PLACEMENT.  lo = 409: `power-closed-at' (theorem-library/dyadic-weights.scm,
;;; 408) is the latest citation, and it is rr-bernoulli's only late one.  No
;;; proven theorem cites any of the nine, so nothing forces an upper bound:
;;; the window is [409, end).  Every other citation is far below -- the finsum
;;; layer tops out at rake-finsum-typing (229) and rake-finsum-laws (245).

;;; ---- file-local drivers (the `r5q-' prefix) --------------------------

;;; The 1-based indices of the ORDER-SHAPED assumptions, which is what `ineq'
;;; wants.  (A third copy of rr-order-basics.scm's `ro-idx'; it belongs in
;;; driver-kit.scm.)
(define (r5q-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (#t (loop (cdr l) (+ i 1) acc)))))
(define (r5q-ineq!) (apply ineq (r5q-idx)))

;;; `ineq' on premises named by FORMULA rather than by shape: a context equation
;;; between terms the oracle cannot certify in RR poisons the whole call
;;; (CLAUDE.md), and both proofs below hold such equations.
(define (r5q-index f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r5q-index: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r5q-ineq-on! . fs) (apply ineq (map r5q-index fs)))

;;; 1 + x is a real, and hence a complex -- what the `power' axioms want.
(define (r5q-onex! x)
  (fact 'rr-one-in)
  (have! (list 'AND '(IN 1 RR) (list 'IN x 'RR)))
  (fact 'rr-add-closed 1 x)
  (fact 'rr-subset-cc (list '+ 1 x)))

;;; A proof that does not close must say so here, not at the `qed'.
(define (r5q-check! name)
  (if (not (proof-done? *ps*))
      (error "rake-inequalities: proof did not close" name
             (expression->string (dk-goal)))))

;;; =====================================================================
;;; (1) THE FOUR POLYNOMIAL INEQUALITIES, by sum-of-squares certificate.
;;; =====================================================================

;;; Young at p=q=2.  b - a = 1/2 (a-b)^2 once the quotient is a coefficient.
(sp (make-wff
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* a b) (/ (+ (* a a) (* b b)) 2))))))))
(di)
(mac 'binary-divide-def)
(sos "a - b")
(r5q-check! 'rr-young-2)
(qed 'rr-young-2)
(topic! 'rr-young-2 'inequalities)

;;; AM-GM for two terms, square form.  (a+b)^2 - 4ab = (a-b)^2.
(sp (make-wff
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* 4 (* a b)) (* (+ a b) (+ a b)))))))))
(di)
(sos "a - b")
(r5q-check! 'rr-amgm-2)
(qed 'rr-amgm-2)
(topic! 'rr-amgm-2 'inequalities)

;;; QM-AM, square form.  2(a^2+b^2) - (a+b)^2 = (a-b)^2.
(sp (make-wff
  '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
     (<= (* (+ a b) (+ a b)) (* 2 (+ (* a a) (* b b))))))))))
(di)
(sos "a - b")
(r5q-check! 'rr-qm-am-2)
(qed 'rr-qm-am-2)
(topic! 'rr-qm-am-2 'inequalities)

;;; Cauchy-Schwarz for two terms.  The difference is the Lagrange identity.
(sp (make-wff
  '(FORALL a1 (IMPLIES (IN a1 RR) (FORALL a2 (IMPLIES (IN a2 RR)
     (FORALL b1 (IMPLIES (IN b1 RR) (FORALL b2 (IMPLIES (IN b2 RR)
       (<= (* (+ (* a1 b1) (* a2 b2)) (+ (* a1 b1) (* a2 b2)))
           (* (+ (* a1 a1) (* a2 a2)) (+ (* b1 b1) (* b2 b2))))))))))))))
(di)
(sos "a1*b2 - a2*b1")
(r5q-check! 'rr-cauchy-schwarz-2)
(qed 'rr-cauchy-schwarz-2)
(topic! 'rr-cauchy-schwarz-2 'inequalities)

;;; =====================================================================
;;; (2) rr-pos-shrink -- the last of the five archimedean supports.
;;;
;;; `rr-pos-halvable' (theorem-library/rr-halving.scm) is proven, and `dk-halve!'
;;; packages it: it lands POS-RR(d), d + d = eps, d in RR and 0 < d.  Then
;;; d < eps is one Farkas step.
;;; =====================================================================

(sp (make-wff
  '(FORALL eps (IMPLIES (POS-RR eps)
     (FORSOME d (AND (POS-RR d) (< d eps)))))))
(dk-peel!)
(fact 'rr-pos-rr-in-rr 'eps)
(define r5q-d (dk-halve! 'eps))
(ew r5q-d)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'POS-RR)
       (ass)
       (r5q-ineq!))))
(r5q-check! 'rr-pos-shrink)
(qed 'rr-pos-shrink)
(topic! 'rr-pos-shrink 'inequalities)

;;; =====================================================================
;;; (3) BERNOULLI, by induction on the exponent.
;;;
;;; The step is  (1+x)^(n+1) = (1+x)(1+x)^n >= (1+x)(1+nx) = 1 + (n+1)x + n x^2
;;; >= 1 + (n+1)x,  i.e. one scaling by the nonnegative 1+x, one ring identity
;;; and the nonnegativity of n x^2.  `power-closed-at' supplies the realness of
;;; the power -- every `ineq' atom must be certified in RR.
;;; =====================================================================

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL x (IMPLIES (IN x RR)
     (IMPLIES (<= -1 x) (<= (+ 1 (* n x)) (power (+ 1 x) n)))))))))
(define r5q-br (use-induction))

;;; base: (1+x)^0 = 1 and 1 + 0*x = 1.
(dk-focus! (cdr (assq 'base r5q-br)))
(dk-peel!)
(r5q-onex! 'x)
(mac 'power-zero)
(have! '(= (+ 1 (* 0 x)) 1) (lambda () (crs)))
(subst '(= (+ 1 (* 0 x)) 1))
(ineq)

;;; step.
(dk-focus! (cdr (assq 'step r5q-br)))
(define r5q-n  (cdr (assq 'var r5q-br)))
(define r5q-ih (cdr (assq 'ih  r5q-br)))
(dk-peel!)
(r5q-onex! 'x)
(have! (list 'AND (list 'IN '(+ 1 x) 'CC) (list 'IN r5q-n 'NN)))
(fact 'power-succ '(+ 1 x) r5q-n)
(subst (list '= (list 'power '(+ 1 x) (list 'succ r5q-n))
                (list '* '(+ 1 x) (list 'power '(+ 1 x) r5q-n))))
(fact 'nn-succ-plus-one r5q-n)
(subst (list '= (list 'succ r5q-n) (list '+ r5q-n 1)))

;;; typings
(fact 'nn-in-rr r5q-n)
(have! (list 'AND (list 'IN r5q-n 'RR) '(IN x RR)))
(fact 'rr-mul-closed r5q-n 'x)                       ; n*x in RR
(have! (list 'AND '(IN 1 RR) (list 'IN (list '* r5q-n 'x) 'RR)))
(fact 'rr-add-closed 1 (list '* r5q-n 'x))           ; 1 + n*x in RR
(fact 'power-closed-at r5q-n '(+ 1 x))               ; (1+x)^n in RR
(inst+ r5q-ih 'x)                                    ; the IH at x

;;; 0 <= 1 + x, then scale the IH by it
(have! '(<= 0 (+ 1 x)) (lambda () (r5q-ineq-on! '(<= -1 x))))
(have! (list 'AND '(<= 0 (+ 1 x))
                  (list '<= (list '+ 1 (list '* r5q-n 'x))
                            (list 'power '(+ 1 x) r5q-n))))
(fact 'rr-le-scale-nonneg '(+ 1 x) (list '+ 1 (list '* r5q-n 'x))
                          (list 'power '(+ 1 x) r5q-n))

;;; 0 <= n * (x*x)
(have! '(AND (IN x RR) (IN x RR)))
(fact 'rr-mul-closed 'x 'x)
(fact 'nn-zero-le r5q-n)
(fact 'rr-sq-nonneg 'x)
(have! (list 'AND (list 'IN r5q-n 'RR) '(IN (* x x) RR)))
(have! (list 'AND (list '<= 0 r5q-n) '(<= 0 (* x x))))
(fact 'rr-leq-mul-nonneg r5q-n '(* x x))

;;; the RR certificates the oracle wants for its atoms
(have! (list 'AND (list 'IN r5q-n 'RR) '(IN 1 RR)))
(fact 'rr-add-closed r5q-n 1)
(have! (list 'AND (list 'IN (list '+ r5q-n 1) 'RR) '(IN x RR)))
(fact 'rr-mul-closed (list '+ r5q-n 1) 'x)
(fact 'rr-mul-closed r5q-n '(* x x))
(have! (list 'AND '(IN (+ 1 x) RR) (list 'IN (list '+ 1 (list '* r5q-n 'x)) 'RR)))
(fact 'rr-mul-closed '(+ 1 x) (list '+ 1 (list '* r5q-n 'x)))
(have! (list 'AND '(IN (+ 1 x) RR) (list 'IN (list 'power '(+ 1 x) r5q-n) 'RR)))
(fact 'rr-mul-closed '(+ 1 x) (list 'power '(+ 1 x) r5q-n))

;;; 1 + (n+1)x <= (1+x)(1+nx), by the ring identity and 0 <= n x^2
(define r5q-h1
  (list '= (list '* '(+ 1 x) (list '+ 1 (list '* r5q-n 'x)))
           (list '+ (list '+ 1 (list '* (list '+ r5q-n 1) 'x))
                    (list '* r5q-n '(* x x)))))
(have! r5q-h1 (lambda () (crs)))
(have! (list '<= (list '+ 1 (list '* (list '+ r5q-n 1) 'x))
                 (list '* '(+ 1 x) (list '+ 1 (list '* r5q-n 'x))))
       (lambda () (subst r5q-h1)
                  (r5q-ineq-on! (list '<= 0 (list '* r5q-n '(* x x))))))
(r5q-ineq-on!
  (list '<= (list '+ 1 (list '* (list '+ r5q-n 1) 'x))
            (list '* '(+ 1 x) (list '+ 1 (list '* r5q-n 'x))))
  (list '<= (list '* '(+ 1 x) (list '+ 1 (list '* r5q-n 'x)))
            (list '* '(+ 1 x) (list 'power '(+ 1 x) r5q-n))))
(r5q-check! 'rr-bernoulli-ind)
(qed 'rr-bernoulli-ind)
(topic! 'rr-bernoulli-ind 'inequalities)
(alias! 'rr-bernoulli-ind "Bernoulli's inequality, induction variable outermost")

;;; the statement scalar-inequalities.scm carried, verbatim
(sp (make-wff
  '(FORALL x (IMPLIES (IN x RR) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (<= -1 x) (<= (+ 1 (* n x)) (power (+ 1 x) n)))))))))
(di)
(fact 'rr-bernoulli-ind 'n 'x)
(ass)
(r5q-check! 'rr-bernoulli)
(qed 'rr-bernoulli)
(topic! 'rr-bernoulli 'inequalities)

;;; =====================================================================
;;; (4) THE ADDITIVE ABELIAN GROUP OF RR, AS analysis-inequalities.scm
;;;     SPELLS IT.  See the header for why the view's own typing axiom is
;;;     unusable here and the same-slot-list quasi-equality is not.
;;; =====================================================================

(define r5q-ag '(COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD))
(define r5q-addlam '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN RR RR) (+ x_ y_)))
(define r5q-sm '(SEP t_ RR (<= 0 t_)))

;;; the carrier.  CARR is read off CARR: the first `slot' fires the INSTANCE value
;;; (carr(rr-normed-field) -> rr), the second the projection of the view's LIST.
;;; (The instance macete is never fired by name: the suite pins `slot' as the one
;;; door to an accessor reduction -- accessor-callsite-audit.)
(sp (make-wff (list '== (list 'CARR r5q-ag) 'RR)))
(mac 'commutative-ring-additive-ag)
(slot 'CARR)
(slot 'CARR)
(nth-r)
(qrfl)
(r5q-check! 'cra-ag-rr-carr)
(qed 'cra-ag-rr-carr)
(topic! 'cra-ag-rr-carr 'algebra)
(alias! 'cra-ag-rr-carr "the carrier of RR's additive group is RR")

(sp (make-wff (list '== (list 'IDEN r5q-ag) 0)))
(mac 'commutative-ring-additive-ag) (slot 'IDEN) (nth-r) (slot 'ZERO) (qrfl)
(r5q-check! 'cra-ag-rr-iden)
(qed 'cra-ag-rr-iden)
(topic! 'cra-ag-rr-iden 'algebra)

(sp (make-wff (list '== (list 'OPR r5q-ag) r5q-addlam)))
(mac 'commutative-ring-additive-ag) (slot 'OPR) (nth-r) (slot 'ADD) (qrfl)
(r5q-check! 'cra-ag-rr-opr)
(qed 'cra-ag-rr-opr)
(topic! 'cra-ag-rr-opr 'algebra)

;;; The two views have the same source slot list, so their functoids unfold to
;;; the same LIST -- four lines, and every normed-field fact transports.
(sp (make-wff '(FORALL r_ (== (COMMUTATIVE-RING-ADDITIVE-AG r_)
                              (NORMED-FIELD-ADDITIVE-AG r_)))))
(di)
(mac 'commutative-ring-additive-ag)
(mac 'normed-field-additive-ag)
(qrfl)
(r5q-check! 'cra-ag-is-nf-ag)
(qed 'cra-ag-is-nf-ag)
(topic! 'cra-ag-is-nf-ag 'algebra)
(alias! 'cra-ag-is-nf-ag
        "the commutative-ring and normed-field additive views coincide")

(sp (make-wff (list 'IS-ABELIAN-GROUP r5q-ag)))
(fact 'cra-ag-is-nf-ag 'RR-NORMED-FIELD)
(subst (list '== r5q-ag '(NORMED-FIELD-ADDITIVE-AG RR-NORMED-FIELD)))
(fact 'rr-is-normed-field)
(fact 'normed-field-additive-ag-is-abelian-group 'RR-NORMED-FIELD)
(ass)
(r5q-check! 'cra-ag-rr-is-abelian-group)
(qed 'cra-ag-rr-is-abelian-group)
(topic! 'cra-ag-rr-is-abelian-group 'algebra)

;;; the operation, APPLIED.  Guarded on both arguments, as the slot is a set
;;; function on CARTESIAN(RR,RR) and not a total constant.
(sp (make-wff (list 'FORALL 'u_ (list 'IMPLIES '(IN u_ RR)
                (list 'FORALL 'v_ (list 'IMPLIES '(IN v_ RR)
                  (list '== (list (list 'OPR r5q-ag) 'u_ 'v_) '(+ u_ v_))))))))
(dk-peel!)
(mac 'cra-ag-rr-opr)
(mac 'lam-slot-add-apply)
(qrfl)
(r5q-check! 'cra-ag-rr-opr-apply)
(qed 'cra-ag-rr-opr-apply)
(topic! 'cra-ag-rr-opr-apply 'algebra)
(alias! 'cra-ag-rr-opr-apply "the operation of RR's additive group is +")

;;; =====================================================================
;;; (5) THE NONNEGATIVE REALS AS A SUBCLASS OF THAT GROUP.
;;; =====================================================================

(sp (make-wff (list 'IN (list 'IDEN r5q-ag) r5q-sm)))
(mac 'cra-ag-rr-iden)
(for-each (lambda (n) (dk-focus! n)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'rr-zero-in) (ass))
                (ineq)))
          (dk-opened (lambda () (sep-mi))))
(r5q-check! 'rr-nonneg-has-zero)
(qed 'rr-nonneg-has-zero)
(topic! 'rr-nonneg-has-zero 'inequalities)

(sp (make-wff (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r5q-sm)
   (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r5q-sm)
     (list 'IN (list (list 'OPR r5q-ag) 'x_ 'y_) r5q-sm)))))))
(dk-peel!)
(sep-me (list 'IN 'x_ r5q-sm))
(sep-me (list 'IN 'y_ r5q-sm))
(mac 'cra-ag-rr-opr-apply)
(for-each (lambda (n) (dk-focus! n)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (have! '(AND (IN x_ RR) (IN y_ RR)))
                       (fact 'rr-add-closed 'x_ 'y_) (ass))
                (r5q-ineq-on! '(<= 0 x_) '(<= 0 y_))))
          (dk-opened (lambda () (sep-mi))))
(r5q-check! 'rr-nonneg-opr-closed)
(qed 'rr-nonneg-opr-closed)
(topic! 'rr-nonneg-opr-closed 'inequalities)

;;; =====================================================================
;;; (6) THE TWO GENERAL FINSUM FACTS OVER RR.
;;; =====================================================================

;;; a real finite sum is real
(sp (make-wff (list 'FORALL 'S_ (list 'IMPLIES '(IN S_ SET) (list 'IMPLIES '(IN (CARD S_) NN)
   (list 'FORALL 'f_ (list 'IMPLIES '(IN f_ (FUN S_ RR))
     (list 'IN (list 'FINSUM r5q-ag 'f_ 'S_) 'RR))))))))
(dk-peel!)
(fact 'cra-ag-rr-is-abelian-group)
(have! (list 'IN 'f_ (list 'FUN 'S_ (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(fact 'finsum-type r5q-ag 'S_ 'f_)
(mac 'cra-ag-rr-carr-rev)
(ass)
(r5q-check! 'finsum-rr-in-rr)
(qed 'finsum-rr-in-rr)
(topic! 'finsum-rr-in-rr 'plumbing)

;;; a finite sum of nonnegatives is nonnegative -- `finsum-in-subset' at the
;;; subclass {t in RR | 0 <= t}.  No induction anywhere.
(sp (make-wff
  (list 'FORALL 'S_ (list 'IMPLIES '(IN S_ SET) (list 'IMPLIES '(IN (CARD S_) NN)
    (list 'FORALL 'f_ (list 'IMPLIES '(IN f_ (FUN S_ RR))
      (list 'IMPLIES '(FORALL z_ (IMPLIES (IN z_ S_) (<= 0 (f_ z_))))
        (list '<= 0 (list 'FINSUM r5q-ag 'f_ 'S_))))))))))
(dk-peel!)
(fact 'cra-ag-rr-is-abelian-group)
(fact 'rr-nonneg-has-zero)
(fact 'rr-nonneg-opr-closed)
(have! (list 'IN 'f_ (list 'FUN 'S_ (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(have! (list 'FORALL 'z (list 'IMPLIES '(IN z S_) (list 'IN '(f_ z) r5q-sm)))
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c 'f_ 'S_ 'RR 'z)
    (inst+ (dk-pick (lambda (g) (and (pair? g) (eq? (car g) 'FORALL)
                                     (equal? (cadr g) 'z_)))
                    "the pointwise nonnegativity")
           'z)
    (for-each (lambda (n) (dk-focus! n) (ass))
              (dk-opened (lambda () (sep-mi))))))
(fact 'finsum-in-subset r5q-ag r5q-sm 'S_ 'f_)
(sep-me (list 'IN (list 'FINSUM r5q-ag 'f_ 'S_) r5q-sm))
(ass)
(r5q-check! 'finsum-rr-nonneg)
(qed 'finsum-rr-nonneg)
(topic! 'finsum-rr-nonneg 'inequalities)

;;; =====================================================================
;;; (7) THE THREE SUPPORTS OF analysis-inequalities.scm.
;;; =====================================================================

;;; ---- finsum-sq-nonneg -------------------------------------------------
(define r5q-sq-stmt
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= 0 (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                     (VNB-LAMBDA i S (* (a i) (a i))) S)))))))

(sp (make-wff r5q-sq-stmt))
(for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f)))
          (dk-peel!))
(let* ((sv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                           "S in SET")))
       (av  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
                           "a in FUN(S,RR)")))
       (lam (list 'VNB-LAMBDA 'i sv (list '* (list av 'i) (list av 'i)))))
  (have! (list 'IN lam (list 'FUN sv 'RR))
    (lambda ()
      (for-each (lambda (n) (dk-focus! n)
                  (if (equal? (dk-goal) (list 'IN sv 'SET))
                      (ass)
                      (let* ((landed (dk-peel!)) (iv (cadr (car landed))))
                        (fact 'fun-apply-type-c av sv 'RR iv)
                        (have! (list 'AND (list 'IN (list av iv) 'RR)
                                          (list 'IN (list av iv) 'RR)))
                        (fact 'rr-mul-closed (list av iv) (list av iv))
                        (ass))))
                (dk-opened (lambda () (lam-t))))))
  (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ sv)
                                 (list '<= 0 (list lam 'z_))))
    (lambda ()
      (dk-peel!)
      (fact 'fun-apply-type-c av sv 'RR 'z_)
      (lam-b)
      (fact 'rr-sq-nonneg (list av 'z_))
      (ass)))
  (fact 'finsum-rr-nonneg sv lam)
  (ass))
(r5q-check! 'finsum-sq-nonneg)
(qed 'finsum-sq-nonneg)
(topic! 'finsum-sq-nonneg 'inequalities)

;;; ---- finsum-le-termwise ------------------------------------------------
;;; SUM b = SUM a + SUM (b - a) and the second summand is nonnegative.  The
;;; equality is finsum-add-ag composed with finsum-congruence, oriented so that
;;; no guarded read-off is ever applied under the summand's binder.
(define r5q-lt-stmt
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR)) (FORALL b (IMPLIES (IN b (FUN S RR))
       (IMPLIES (FORALL i (IMPLIES (IN i S) (<= (a i) (b i))))
         (<= (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) a S)
             (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) b S))))))))))

(sp (make-wff r5q-lt-stmt))
(for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f)))
          (dk-peel!))
(define r5q-S
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                 "S in SET")))
(define r5q-funs
  (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
                    (dk-asms))))
(define r5q-a (car r5q-funs))
(define r5q-b (cadr r5q-funs))
(define r5q-c (list 'VNB-LAMBDA 'w_ r5q-S
                    (list '- (list r5q-b 'w_) (list r5q-a 'w_))))
(define r5q-ptw
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'IMPLIES)
                            (pair? (caddr (caddr f)))
                            (eq? (car (caddr (caddr f))) '<=)))
           "the pointwise a(i) <= b(i)"))
(fact 'cra-ag-rr-is-abelian-group)

;;; the difference family is a total real map
(have! (list 'IN r5q-c (list 'FUN r5q-S 'RR))
  (lambda ()
    (for-each (lambda (n) (dk-focus! n)
                (if (equal? (dk-goal) (list 'IN r5q-S 'SET))
                    (ass)
                    (let* ((landed (dk-peel!)) (iv (cadr (car landed))))
                      (fact 'fun-apply-type-c r5q-a r5q-S 'RR iv)
                      (fact 'fun-apply-type-c r5q-b r5q-S 'RR iv)
                      (have! (list 'AND (list 'IN (list r5q-b iv) 'RR)
                                        (list 'IN (list r5q-a iv) 'RR)))
                      (fact 'rr-sub-in-rr (list r5q-b iv) (list r5q-a iv))
                      (ass))))
              (dk-opened (lambda () (lam-t))))))

;;; each difference is nonnegative
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r5q-S)
                               (list '<= 0 (list r5q-c 'z_))))
  (lambda ()
    (dk-peel!)
    (lam-b)
    (fact 'fun-apply-type-c r5q-a r5q-S 'RR 'z_)
    (fact 'fun-apply-type-c r5q-b r5q-S 'RR 'z_)
    (have! (list 'AND (list 'IN (list r5q-b 'z_) 'RR)
                      (list 'IN (list r5q-a 'z_) 'RR)))
    (fact 'rr-sub-in-rr (list r5q-b 'z_) (list r5q-a 'z_))
    (inst+ r5q-ptw 'z_)
    (r5q-ineq-on! (list '<= (list r5q-a 'z_) (list r5q-b 'z_)))))
(fact 'finsum-rr-nonneg r5q-S r5q-c)
(fact 'finsum-rr-in-rr r5q-S r5q-c)
(fact 'finsum-rr-in-rr r5q-S r5q-a)
(fact 'finsum-rr-in-rr r5q-S r5q-b)

;;; a and the difference family are total maps into the carrier
(have! (list 'IN r5q-a (list 'FUN r5q-S (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(have! (list 'IN r5q-c (list 'FUN r5q-S (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(define r5q-addeq (dk-fact! 'finsum-add-ag r5q-ag r5q-S r5q-a r5q-c))
(define r5q-big (caddr (cadr r5q-addeq)))

;;; the combined family is a total real map
(have! (list 'IN r5q-big (list 'FUN r5q-S 'RR))
  (lambda ()
    (for-each (lambda (n) (dk-focus! n)
                (if (equal? (dk-goal) (list 'IN r5q-S 'SET))
                    (ass)
                    (let* ((landed (dk-peel!)) (iv (cadr (car landed))))
                      (fact 'fun-apply-type-c r5q-a r5q-S 'RR iv)
                      (fact 'fun-apply-type-c r5q-c r5q-S 'RR iv)
                      (mac 'cra-ag-rr-opr-apply)
                      (have! (list 'AND (list 'IN (list r5q-a iv) 'RR)
                                        (list 'IN (list r5q-c iv) 'RR)))
                      (fact 'rr-add-closed (list r5q-a iv) (list r5q-c iv))
                      (ass))))
              (dk-opened (lambda () (lam-t))))))
(fact 'finsum-rr-in-rr r5q-S r5q-big)

;;; b agrees with the combined family pointwise
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r5q-S)
                               (list '= (list r5q-b 'z_) (list r5q-big 'z_))))
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c r5q-a r5q-S 'RR 'z_)
    (fact 'fun-apply-type-c r5q-b r5q-S 'RR 'z_)
    (lam-b)
    (have! (list 'AND (list 'IN (list r5q-b 'z_) 'RR)
                      (list 'IN (list r5q-a 'z_) 'RR)))
    (fact 'rr-sub-in-rr (list r5q-b 'z_) (list r5q-a 'z_))
    (mac 'cra-ag-rr-opr-apply)
    (crs)))
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r5q-S)
                               (list 'IN (list r5q-b 'z_) (list 'CARR r5q-ag))))
  (lambda ()
    (dk-peel!)
    (mac 'cra-ag-rr-carr)
    (fact 'fun-apply-type-c r5q-b r5q-S 'RR 'z_)
    (ass)))
(define r5q-cong (dk-fact! 'finsum-congruence r5q-ag r5q-S r5q-b r5q-big))

;;; the group operation on the two finite sums is their sum -- opened at the
;;; TOP LEVEL only, never under the summand's binder
(define r5q-fa (list 'FINSUM r5q-ag r5q-a r5q-S))
(define r5q-fc (list 'FINSUM r5q-ag r5q-c r5q-S))
(define r5q-opeq (list '= (list (list 'OPR r5q-ag) r5q-fa r5q-fc)
                          (list '+ r5q-fa r5q-fc)))
(have! r5q-opeq (lambda () (mac 'cra-ag-rr-opr-apply) (rfl)))
(have! (list 'IN (list (list 'OPR r5q-ag) r5q-fa r5q-fc) 'RR)
  (lambda () (mac 'cra-ag-rr-opr-apply)
             (have! (list 'AND (list 'IN r5q-fa 'RR) (list 'IN r5q-fc 'RR)))
             (fact 'rr-add-closed r5q-fa r5q-fc)
             (ass)))
(r5q-ineq-on! r5q-cong r5q-addeq r5q-opeq (list '<= 0 r5q-fc))
(r5q-check! 'finsum-le-termwise)
(qed 'finsum-le-termwise)
(topic! 'finsum-le-termwise 'inequalities)

;;; ---- finsum-abs-triangle ------------------------------------------------
;;; -|a| <= a <= |a| pointwise gives SUM(-|a|) <= SUM a <= SUM |a| by the
;;; theorem just proved, and SUM(-|a|) + SUM|a| = 0 because the pointwise sum of
;;; the two families is the identity (finsum-add-ag + finsum-all-id).  The sign
;;; of SUM a then decides which of the two bounds is |SUM a|.
(define r5q-at-stmt
  '(FORALL S (IMPLIES (AND (IN S SET) (IN (CARD S) NN))
     (FORALL a (IMPLIES (IN a (FUN S RR))
       (<= (abs (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD) a S))
           (FINSUM (COMMUTATIVE-RING-ADDITIVE-AG RR-NORMED-FIELD)
                   (VNB-LAMBDA i S (abs (a i))) S)))))))

(sp (make-wff r5q-at-stmt))
(for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f)))
          (dk-peel!))
(define r5q-S2
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                 "S in SET")))
(define r5q-a2
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                  (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
                 "a in FUN(S,RR)")))
(define r5q-m (caddr (caddr (dk-goal))))          ; the statement's own summand
(define r5q-n2 (list 'VNB-LAMBDA 'w_ r5q-S2 (list '- (list 'abs (list r5q-a2 'w_)))))
(fact 'cra-ag-rr-is-abelian-group)

(define (r5q-fun-abs! lam negated?)
  (have! (list 'IN lam (list 'FUN r5q-S2 'RR))
    (lambda ()
      (for-each (lambda (nd) (dk-focus! nd)
                  (if (equal? (dk-goal) (list 'IN r5q-S2 'SET))
                      (ass)
                      (let* ((landed (dk-peel!)) (iv (cadr (car landed))))
                        (fact 'fun-apply-type-c r5q-a2 r5q-S2 'RR iv)
                        (fact 'rr-abs-closed (list r5q-a2 iv))
                        (if negated? (fact 'rr-neg-closed (list 'abs (list r5q-a2 iv))))
                        (ass))))
                (dk-opened (lambda () (lam-t)))))))
(r5q-fun-abs! r5q-m #f)
(r5q-fun-abs! r5q-n2 #t)

;;; a <= |a| and -|a| <= a, pointwise
(have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ r5q-S2)
        (list '<= (list r5q-a2 'i_) (list r5q-m 'i_))))
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c r5q-a2 r5q-S2 'RR 'i_)
    (lam-b)
    (fact 'rr-le-abs (list r5q-a2 'i_))
    (ass)))
(have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ r5q-S2)
        (list '<= (list r5q-n2 'i_) (list r5q-a2 'i_))))
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c r5q-a2 r5q-S2 'RR 'i_)
    (lam-b)
    (fact 'rr-neg-abs-le (list r5q-a2 'i_))
    (ass)))
;; finsum-le-termwise's antecedent is a CONJUNCTION, which `fact' will not split
(have! (list 'AND (list 'IN r5q-S2 'SET) (list 'IN (list 'CARD r5q-S2) 'NN)))
(fact 'finsum-le-termwise r5q-S2 r5q-a2 r5q-m)
(fact 'finsum-le-termwise r5q-S2 r5q-n2 r5q-a2)
(fact 'finsum-rr-in-rr r5q-S2 r5q-a2)
(fact 'finsum-rr-in-rr r5q-S2 r5q-m)
(fact 'finsum-rr-in-rr r5q-S2 r5q-n2)

;;; SUM(-|a|) + SUM(|a|) = 0
(have! (list 'IN r5q-n2 (list 'FUN r5q-S2 (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(have! (list 'IN r5q-m (list 'FUN r5q-S2 (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(define r5q-addeq3 (dk-fact! 'finsum-add-ag r5q-ag r5q-S2 r5q-n2 r5q-m))
(define r5q-big2 (caddr (cadr r5q-addeq3)))
(have! (list 'IN r5q-big2 (list 'FUN r5q-S2 'RR))
  (lambda ()
    (for-each (lambda (nd) (dk-focus! nd)
                (if (equal? (dk-goal) (list 'IN r5q-S2 'SET))
                    (ass)
                    (let* ((landed (dk-peel!)) (iv (cadr (car landed))))
                      (fact 'fun-apply-type-c r5q-n2 r5q-S2 'RR iv)
                      (fact 'fun-apply-type-c r5q-m r5q-S2 'RR iv)
                      (mac 'cra-ag-rr-opr-apply)
                      (have! (list 'AND (list 'IN (list r5q-n2 iv) 'RR)
                                        (list 'IN (list r5q-m iv) 'RR)))
                      (fact 'rr-add-closed (list r5q-n2 iv) (list r5q-m iv))
                      (ass))))
              (dk-opened (lambda () (lam-t))))))
(have! (list 'IN r5q-big2 (list 'FUN r5q-S2 (list 'CARR r5q-ag)))
  (lambda () (mac 'cra-ag-rr-carr) (ass)))
(fact 'finsum-rr-in-rr r5q-S2 r5q-big2)
(have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r5q-S2)
        (list '= (list r5q-big2 'z_) (list 'IDEN r5q-ag))))
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c r5q-a2 r5q-S2 'RR 'z_)
    (fact 'fun-apply-type-c r5q-n2 r5q-S2 'RR 'z_)
    (fact 'fun-apply-type-c r5q-m r5q-S2 'RR 'z_)
    (lam-b)
    (fact 'rr-abs-closed (list r5q-a2 'z_))
    (fact 'rr-neg-closed (list 'abs (list r5q-a2 'z_)))
    (mac 'cra-ag-rr-opr-apply)
    (mac 'cra-ag-rr-iden)
    (crs)))
(define r5q-allid (dk-fact! 'finsum-all-id r5q-ag r5q-S2 r5q-big2))

(define r5q-fn (list 'FINSUM r5q-ag r5q-n2 r5q-S2))
(define r5q-fm (list 'FINSUM r5q-ag r5q-m r5q-S2))
(define r5q-fa2 (list 'FINSUM r5q-ag r5q-a2 r5q-S2))
(define r5q-ideneq (list '= (list 'IDEN r5q-ag) 0))
(have! r5q-ideneq (lambda () (mac 'cra-ag-rr-iden) (rfl)))
(have! (list 'IN (list 'IDEN r5q-ag) 'RR)
  (lambda () (mac 'cra-ag-rr-iden) (fact 'rr-zero-in) (ass)))
(define r5q-opeq2 (list '= (list (list 'OPR r5q-ag) r5q-fn r5q-fm)
                           (list '+ r5q-fn r5q-fm)))
(have! r5q-opeq2 (lambda () (mac 'cra-ag-rr-opr-apply) (rfl)))
(have! (list 'IN (list (list 'OPR r5q-ag) r5q-fn r5q-fm) 'RR)
  (lambda () (mac 'cra-ag-rr-opr-apply)
             (have! (list 'AND (list 'IN r5q-fn 'RR) (list 'IN r5q-fm 'RR)))
             (fact 'rr-add-closed r5q-fn r5q-fm)
             (ass)))
(have! (list '= (list '+ r5q-fn r5q-fm) 0)
  (lambda () (r5q-ineq-on! r5q-addeq3 r5q-allid r5q-ideneq r5q-opeq2)))

;;; split on the sign of the sum
(fact 'rr-zero-in)
(have! (list 'AND '(IN 0 RR) (list 'IN r5q-fa2 'RR)))
(fact 'rr-leq-total 0 r5q-fa2)
(use-cases (list (list '<= 0 r5q-fa2) (list '<= r5q-fa2 0))
  (lambda ()
    (fact 'rr-abs-of-nonneg r5q-fa2)
    (subst (list '= (list 'abs r5q-fa2) r5q-fa2))
    (r5q-ineq-on! (list '<= r5q-fa2 r5q-fm)))
  (lambda ()
    (fact 'rr-abs-of-nonpos r5q-fa2)
    (subst (list '= (list 'abs r5q-fa2) (list '- r5q-fa2)))
    (r5q-ineq-on! (list '<= r5q-fn r5q-fa2)
                  (list '= (list '+ r5q-fn r5q-fm) 0))))
(r5q-check! 'finsum-abs-triangle)
(qed 'finsum-abs-triangle)
(topic! 'finsum-abs-triangle 'inequalities)
