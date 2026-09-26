;;; interval-taylor.scm -- TAYLOR'S FORMULA (2.18) FOR A FUNCTION ON ITS
;;; INTERVAL, AND ITS TWO COROLLARIES.
;;;
;;; The vocabulary is structure-library/interval-taylor.scm, whose header
;;; carries the notes' statement verbatim and the index-hygiene checks.  The
;;; route is the notes' own: the generalized mean value theorem (2.11, here
;;; `generalized-mvt-on-interval') applied to the auxiliary function (21) and
;;; to G.
;;;
;;; THE ONE PIECE OF MACHINERY WORTH NAMING is section (1).  The library's
;;; mean value theorems conclude with an EXISTENTIAL derivative value -- "there
;;; is a theta and a value l with has-deriv-at(f, theta, l) and ..." -- because
;;; the derivative is a relation here and not a function.  Every application of
;;; 2.11 in which one of the two derivatives is KNOWN (2.13 with g = id, 2.18
;;; with F, 2.19 with G = (b - x)^n) then has to pin that value down by
;;; uniqueness.  `gmvt-with-known-derivative' does it once: when f's derivative
;;; at every interior point is a given v(x), the conclusion is
;;;
;;;     v(xi) . (G(b) - G(a))  =  mu . (f(b) - f(a))
;;;
;;; with no existential on f's side.  It is 2.11 plus one citation of
;;; `has-deriv-at-unique'.  v is asked to be a member of FUN(OOINT(a,b), RR)
;;; and not left a bare family, because the proof INSTANTIATES at v(xi), and
;;; the definedness certificate (CLAUDE.md, "Definedness") never accepts an
;;; untyped application -- `f(a) with f in FUN(D, _) and a in D' is exactly the
;;; clause that applies.
;;;
;;; WHAT IS PROVEN HERE, in the order the file proves it.  (1) the generalized
;;; mean value theorem with one derivative known; (2) the read-offs of
;;; IS-TAYLOR-FAMILY; (3)-(6) the values of the summand, the sum and the
;;; auxiliary function, and their typings at a TRUNCATION order j <= n;
;;; (7)-(8) the sum of one summand and the sum at the right endpoint;
;;; (9)-(10) three general lemmas on IS-CONTINUOUS-ON and the continuity of
;;; one Taylor step on the line; (11) the recurrence F_{j+1} = F_j + the j-th
;;; summand; (12) F is CONTINUOUS on [a, b]; (13)-(14) the neighbourhood of an
;;; interior point, the local derivative of (b - z)^(k+1) and the value
;;; identity of the telescoping step; (15) the TELESCOPING DERIVATIVE of F;
;;; (16) Theorem 2.18 from the four properties of F; (17) THEOREM 2.18 with no
;;; hypothesis but the family; (18) COROLLARY 2.19, the Lagrange remainder.
;;;
;;; THE INDUCTIONS RUN ON THE TRUNCATION ORDER, the family FIXED:
;;; IS-TAYLOR-FAMILY is not downward closed in its order (d(n) lives on the
;;; OPEN interval, d(k) for k < n on the closed one), so an induction that
;;; lowers the order of the FAMILY cannot be stated, while one that lowers the
;;; number of SUMMANDS can.
;;;
;;; Helper prefix: it-.
;;;
;;; Dependencies: structure-library/interval-taylor.scm,
;;; structure-library/interval-calculus.scm,
;;; theorem-library/interval-calculus-laws.scm (ooint-*, has-deriv-at-unique,
;;; has-deriv-at-in-rr, has-deriv-at-local, has-deriv-at-sum,
;;; has-deriv-at-product, has-deriv-at-iff-diff-at, extend-const-*),
;;; interval-mvt.scm (generalized-mvt-on-interval), has-deriv-at-more.scm
;;; (has-deriv-at-real-mul -- the LAST file in the load order this one needs),
;;; ccint-basics.scm, taylor-proof.scm (factorial-real-pos,
;;; recip-factorial-in-rr, tgd-power-sub-diff, tgd-recip-factorial-succ,
;;; rr-power-pos, rr-cancel-mul-left, rr-recip-one), ms-continuity-algebra.scm
;;; (ms-cont-transfer-ptwise-eq), continuity-{sum,product,scale,transfer}.scm,
;;; differentiation.scm (diff-implies-continuous), metric-subspace-laws.scm
;;; (restrict-in-fun, restrict-apply, restrict-continuous-at),
;;; comparison-test-proof.scm (series-partial-sum-zero / -succ),
;;; rake-combinatorics.scm (power-zero-base), rr-recip-order.scm (rr-mul-pos),
;;; rake-analysis2.scm (fun-domain-in-set), fun-apply-type-proof.scm,
;;; rr-order-basics.scm (rr-pos-ne-zero, rr-min-pos).

;;; ---- file-local driver helpers ---------------------------------------

(define (it-head g) (and (pair? g) (car g)))

;;; unfold IS-TAYLOR-FAMILY in the context and split its seven conjuncts.
(define (it-open-family! d n a b)
  (dk-split-all!
   (dk-landed* (lambda () (mac-h 'IS-TAYLOR-FAMILY (list 'IS-TAYLOR-FAMILY d n a b))))))

;;; the family's per-index universal, discriminated on the predicate it names.
(define (it-family-univ)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-ON)))
           "the Taylor family universal"))

(define (it-mul-real! x y)
  (dk-have! (list 'AND (list 'IN x 'RR) (list 'IN y 'RR))
    (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'rr-mul-closed x y))

(define (it-add-real! x y)
  (dk-have! (list 'AND (list 'IN x 'RR) (list 'IN y 'RR))
    (lambda () (dk-conj-close! (lambda () (ass)))))
  (fact 'rr-add-closed x y))

(define (it-first pred lst)
  (cond ((null? lst) #f) ((pred (car lst)) (car lst)) (#t (it-first pred (cdr lst)))))

;;; an endpoint lies in the closed interval: a in RR, b in RR and a < b in
;;; context.
(define (it-endpoint-in-ccint! z)
  (dk-have! (list 'IN z '(CCINT a b))
    (lambda ()
      (mac 'ccint-membership)
      (dk-conj-close!
       (lambda ()
         (if (eq? (it-head (dk-goal)) 'IN)
             (ass)
             (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))))))

;;; the eigenvariable whose landed typing is (IN v CLASS), CLASS matched by
;;; PRED.  `dk-peel!' peels the WHOLE statement in one loop -- the four outer
;;; binders, the predicate hypothesis and the inner guarded universal -- so
;;; every eigenvariable of these proofs is read off ITS landing list, never
;;; from a counted `di' (CLAUDE.md: loop on the landing, not on a count).
(define (it-var-of lnd pred what)
  (let ((ty (it-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pred (caddr f)))) lnd)))
    (if (not ty)
        (error "it-var-of: no such typing landed" what (map expression->string lnd)))
    (cadr ty)))

;;; =====================================================================
;;; (1) THE GENERALIZED MEAN VALUE THEOREM WITH ONE DERIVATIVE KNOWN.
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([f, g, itv_],
     itv_ in fun(ooint(a,b), rr) implies
     f in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies
     forall([x in ooint(a,b)], has-deriv-at(f, x, itv_(x))) implies
     g in fun(ccint(a,b), rr) implies
     is-continuous-on(g, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([m], has-deriv-at(g, x, m))) implies
     forsome([xi in ooint(a,b)], forsome([m],
        has-deriv-at(g, xi, m) and
        itv_(xi) * (g(b) - g(a)) = m * (f(b) - f(a))))))"))
(dk-peel!)
(define it-known
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'itv_)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the known-derivative universal"))
;; 2.11 wants the existential form of f's differentiability.
(dk-have! '(FORALL x (IMPLIES (IN x (OOINT a b)) (FORSOME l (HAS-DERIV-AT f x l))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'fun-apply-type-c 'itv_ '(OOINT a b) 'RR z)
      (dk-apply! it-known z)
      (ew (list 'itv_ z))
      (ass))))
(let ((th (dk-skolem! (dk-fact! 'generalized-mvt-on-interval 'a 'b 'f 'g))))
  (dk-split-all!)
  (let* ((lv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the l existential")))
         (mv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the m existential"))))
    (dk-split-all!)
    (fact 'fun-apply-type-c 'itv_ '(OOINT a b) 'RR th)
    (dk-apply! it-known th)
    (fact 'has-deriv-at-unique 'f th lv (list 'itv_ th))
    (ew th)
    (dk-conj-close!
     (lambda ()
       (if (eq? (it-head (dk-goal)) 'IN)
           (ass)
           (begin
             (ew mv)
             (dk-conj-close!
              (lambda ()
                (if (eq? (it-head (dk-goal)) '=)
                    (begin (subst (list '= (list 'itv_ th) lv)) (ass))
                    (ass))))))))))
(qed 'gmvt-with-known-derivative)
(topic! 'gmvt-with-known-derivative 'analysis)
(alias! 'gmvt-with-known-derivative
        "the generalized mean value theorem when one derivative is known")

;;; =====================================================================
;;; (2) THE READ-OFFS OF IS-TAYLOR-FAMILY.
;;;
;;; `mac-h' CONSUMES the hypothesis it unfolds, so every consumer that needs
;;; two of these would have to unfold inside a lane; these seven make each
;;; conjunct a citation.  The three per-index ones detach the guarded universal
;;; as well, which is the form every caller wants.
;;; =====================================================================

;;; forall itd_, itn_, a, b.  IS-TAYLOR-FAMILY(itd_, itn_, a, b) implies BODY
(define (it-family-statement body)
  (let* ((s0 (list 'IMPLIES '(IS-TAYLOR-FAMILY itd_ itn_ a b) body))
         (s1 (list 'FORALL 'b s0))
         (s2 (list 'FORALL 'a s1))
         (s3 (list 'FORALL 'itn_ s2)))
    (list 'FORALL 'itd_ s3)))

(define (it-projection! concl name text)
  (sp (make-wff (it-family-statement concl)))
  (dk-peel!)
  (it-open-family! 'itd_ 'itn_ 'a 'b)
  (ass)
  (qed name)
  (topic! name 'analysis)
  (alias! name text))

(it-projection! '(IN itn_ NN) 'taylor-family-order-in-nn
                "the order of a Taylor family is a natural number")
(it-projection! '(<= 1 itn_) 'taylor-family-order-pos
                "the order of a Taylor family is at least one")
(it-projection! '(IN a RR) 'taylor-family-left-in-rr
                "the left endpoint of a Taylor family is a real")
(it-projection! '(IN b RR) 'taylor-family-right-in-rr
                "the right endpoint of a Taylor family is a real")
(it-projection! '(< a b) 'taylor-family-endpoints-lt
                "the endpoints of a Taylor family are in order")
(it-projection! '(IN (itd_ itn_) (FUN (OOINT a b) RR)) 'taylor-family-top-in-fun
                "the top derivative of a Taylor family is a function on the open interval")

;;; the three per-index read-offs.
;;; forall itk_ in NN. itk_ < itn_ implies BODY
(define (it-index-body body)
  (let* ((s0 (list 'IMPLIES '(< itk_ itn_) body))
         (s1 (list 'IMPLIES '(IN itk_ NN) s0)))
    (list 'FORALL 'itk_ s1)))

(define (it-index-projection! body name text)
  (sp (make-wff (it-family-statement (it-index-body body))))
  (let* ((lnd (dk-peel!))
         (z   (it-var-of lnd (lambda (c) (eq? c 'NN)) "the index")))
    (it-open-family! 'itd_ 'itn_ 'a 'b)
    (dk-split-all! (list (dk-apply! (it-family-univ) z)))
    ;; the third read-off's body is itself a universal, which `dk-peel!' has
    ;; already opened: instantiate the landed one at ITS eigenvariable.
    (if (eq? (it-head (dk-goal)) 'HAS-DERIV-AT)
        (dk-apply! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                              (dk-contains? fm 'HAS-DERIV-AT)))
                            "the pointwise derivative universal")
                   (it-var-of lnd (lambda (c) (and (pair? c) (eq? (car c) 'OOINT)))
                              "the interior point")))
    (ass))
  (qed name)
  (topic! name 'analysis)
  (alias! name text))

(it-index-projection! '(IN (itd_ itk_) (FUN (CCINT a b) RR))
                      'taylor-family-in-fun
                      "each derivative of a Taylor family is a function on the closed interval")
(it-index-projection! '(IS-CONTINUOUS-ON (itd_ itk_) (CCINT a b))
                      'taylor-family-continuous
                      "each derivative of a Taylor family is continuous on the closed interval")
(it-index-projection! '(FORALL itx_
                         (IMPLIES (IN itx_ (OOINT a b))
                           (HAS-DERIV-AT (itd_ itk_) itx_ ((itd_ (succ itk_)) itx_))))
                      'taylor-family-deriv
                      "each derivative of a Taylor family differentiates to the next")

;;; =====================================================================
;;; (3) THE VALUE OF THE AUXILIARY FUNCTION.  TAYLOR-AUX is the lambda on
;;; [a, b]; at a point of [a, b] it is the sum, by beta.
;;; =====================================================================
(sp (make-wff '(FORALL itd_ (FORALL itn_ (FORALL a (FORALL b (FORALL itz_
   (IMPLIES (IN itz_ (CCINT a b))
     (== ((TAYLOR-AUX itd_ itn_ a b) itz_) (TAYLOR-SUM itd_ itn_ b itz_))))))))))
(dk-peel!)
(mac 'TAYLOR-AUX)
(dk-lam-b!)
(qrfl)
(qed 'taylor-aux-value)
(topic! 'taylor-aux-value 'analysis)
(alias! 'taylor-aux-value
        "the Taylor auxiliary function takes the Taylor sum as its value")

;;; =====================================================================
;;; (4) THE CLEARING IDENTITY.  `crs' declines any term containing `recip'
;;; (CLAUDE.md), so the reciprocal is carried by a VARIABLE r with its defining
;;; equation s . r = 1 as a hypothesis, and the caller instantiates.  This is
;;; taylor-proof.scm's own move for the same obstacle.
;;;
;;; The two conclusions are (20) MULTIPLIED THROUGH by s = (n-1)! and (20)
;;; LITERALLY, with the division written as the reader desugars it.
;;; =====================================================================
(define (it-rr-forall vars body)
  (if (null? vars) body
      (list 'FORALL (car vars)
            (list 'IMPLIES (list 'IN (car vars) 'RR)
                  (it-rr-forall (cdr vars) body)))))

(sp (make-wff
     (it-rr-forall '(p q r s u w)
       (list 'IMPLIES '(= (* s r) 1)
         (list 'IMPLIES '(= (* (* (* p q) r) w) u)
           (list 'AND '(= (* u s) (* (* p q) w))
                      '(= u (* (* (* p r) q) w))))))))
(dk-peel!)
(dk-conj-close!
 (lambda ()
   (subst '(= u (* (* (* p q) r) w)))
   (if (dk-contains? (dk-goal) 's)
       (begin
         (have! '(= (* (* (* (* p q) r) w) s) (* (* (* p q) w) (* s r))) (lambda () (crs)))
         (subst '(= (* (* (* (* p q) r) w) s) (* (* (* p q) w) (* s r))))
         (subst '(= (* s r) 1))
         (crs))
       (crs))))
(qed 'taylor-clear-recip)
(topic! 'taylor-clear-recip 'analysis)
(alias! 'taylor-clear-recip
        "clearing a reciprocal coefficient from a product identity")

;;; =====================================================================
;;; (5) THE BOUNDED-POINTWISE PARTIAL SUM.  `series-partial-sum-in-rr-ptwise'
;;; (series-linearity.scm) asks for the summand to be real at EVERY k in NN; a
;;; Taylor family gives d(k) only for k <= n, so that theorem cannot be cited
;;; here.  This is the same induction under the guard `k < n', which is the
;;; hypothesis every FINITE family actually supplies.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'itn_ (list 'IMPLIES '(IN itn_ NN)
    (list 'FORALL 'itf_
      (list 'IMPLIES
        (list 'FORALL 'itk_ (list 'IMPLIES '(IN itk_ NN)
              (list 'IMPLIES '(< itk_ itn_) '(IN (itf_ itk_) RR))))
        '(IN (SERIES-PARTIAL-SUM itf_ itn_) RR)))))))
(let* ((br (use-induction)) (nv (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
  (dk-focus! (cdr (assq 'base br)))
  (dk-peel!)
  (mac 'series-partial-sum-zero)
  (fact 'rr-zero-in)
  (ass)
  (dk-focus! (cdr (assq 'step br)))
  (let* ((lnd (dk-peel!))
         (fv  (cadr (cadr (dk-goal))))
         (pw  (it-first (dk-head? 'FORALL) lnd)))
    (fact 'nn-succ-closed nv)
    (fact 'nn-in-rr nv)
    (fact 'nn-in-rr (list 'succ nv))
    (fact 'bt-lt-succ nv)
    (dk-have! (list 'FORALL 'itk_ (list 'IMPLIES '(IN itk_ NN)
                (list 'IMPLIES (list '< 'itk_ nv) (list 'IN (list fv 'itk_) 'RR))))
      (lambda ()
        (let* ((l2 (dk-peel!))
               (z  (it-var-of l2 (lambda (c) (eq? c 'NN)) "the index")))
          (fact 'nn-in-rr z)
          (dk-have! (list '< z (list 'succ nv))
            (lambda () (dk-ineq! (list '< z nv) (list '< nv (list 'succ nv))
                                 (list 'IN z 'RR) (list 'IN nv 'RR)
                                 (list 'IN (list 'succ nv) 'RR))))
          (dk-apply! pw z)
          (ass))))
    (dk-apply! ih fv)
    (dk-apply! pw nv)
    (mac 'series-partial-sum-succ)
    (have! (list 'AND (list 'IN (list 'SERIES-PARTIAL-SUM fv nv) 'RR)
                      (list 'IN (list fv nv) 'RR)))
    (fact 'rr-add-closed (list 'SERIES-PARTIAL-SUM fv nv) (list fv nv))
    (ass)))
(qed 'series-partial-sum-in-rr-below)
(topic! 'series-partial-sum-in-rr-below 'analysis)
(alias! 'series-partial-sum-in-rr-below
        "a family real below the bound has real partial sums up to the bound")

;;; =====================================================================
;;; (6) THE SUMMAND, THE SUM AND THE AUXILIARY FUNCTION.
;;; =====================================================================
(sp (make-wff '(FORALL itd_ (FORALL b (FORALL itv_ (FORALL itk_
   (IMPLIES (IN itk_ NN)
     (== ((TAYLOR-TERM itd_ b itv_) itk_)
         (* (* ((itd_ itk_) itv_) (power (- b itv_) itk_))
            (recip (FACTORIAL itk_)))))))))))
(dk-peel!)
(mac 'TAYLOR-TERM)
(dk-lam-b!)
(qrfl)
(qed 'taylor-term-value)
(topic! 'taylor-term-value 'analysis)
(alias! 'taylor-term-value "the value of the Taylor summand at an index")

;;; The unfold of TAYLOR-SUM as a citable THEOREM.  `mac' unfolds a functoid in
;;; a GOAL, `mac-h' cannot unfold one in an ASSUMPTION by the functoid's own
;;; name (CLAUDE.md); every proof below that has a partial sum in hand and wants
;;; the Taylor sum, or the other way round, cites this.
(sp (make-wff '(FORALL itd_ (FORALL itn_ (FORALL b (FORALL itv_
   (== (TAYLOR-SUM itd_ itn_ b itv_)
       (SERIES-PARTIAL-SUM (TAYLOR-TERM itd_ b itv_) itn_))))))))
(dk-peel!)
(mac 'TAYLOR-SUM)
(qrfl)
(qed 'taylor-sum-unfold)
(topic! 'taylor-sum-unfold 'analysis)
(alias! 'taylor-sum-unfold "the Taylor sum is the partial sum of the Taylor summands")

;;; THE TRUNCATION ORDER.  Both typing lemmas are stated at an order itj_ <=
;;; itn_ and not at itn_ itself: the three inductions below (the endpoint value,
;;; the continuity and the telescoping derivative) all run on the TRUNCATION
;;; order with the family FIXED -- IS-TAYLOR-FAMILY is not downward closed in
;;; its order (the top derivative d(n) lives on the OPEN interval, d(k) for
;;; k < n on the closed one), so an induction that lowers the order of the
;;; FAMILY cannot be stated, while one that lowers the number of SUMMANDS can.
(sp (make-wff (it-family-statement
  '(FORALL itj_ (IMPLIES (IN itj_ NN) (IMPLIES (<= itj_ itn_)
     (FORALL itz_ (IMPLIES (IN itz_ (CCINT a b))
       (IN (TAYLOR-SUM itd_ itj_ b itz_) RR)))))))))
(let* ((lnd (dk-peel!))
       (jv  (it-var-of lnd (lambda (c) (eq? c 'NN)) "the truncation order"))
       (zv  (it-var-of lnd (lambda (c) (and (pair? c) (eq? (car c) 'CCINT))) "the point")))
  (fact 'taylor-family-order-in-nn 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-left-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-right-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'nn-in-rr 'itn_)
  (fact 'nn-in-rr jv)
  (fact 'ccint-elt-in-rr 'a 'b zv)
  (fact 'rr-sub-in-rr 'b zv)
  (dk-have! (list 'FORALL 'itk_ (list 'IMPLIES '(IN itk_ NN)
              (list 'IMPLIES (list '< 'itk_ jv)
                (list 'IN (list (list 'TAYLOR-TERM 'itd_ 'b zv) 'itk_) 'RR))))
    (lambda ()
      (let* ((l2 (dk-peel!))
             (kv (it-var-of l2 (lambda (c) (eq? c 'NN)) "the index"))
             (dk (list 'itd_ kv))
             (pk (list 'power (list '- 'b zv) kv))
             (rk (list 'recip (list 'FACTORIAL kv))))
        (fact 'nn-in-rr kv)
        (dk-have! (list '< kv 'itn_)
          (lambda () (dk-ineq! (list '< kv jv) (list '<= jv 'itn_)
                               (list 'IN kv 'RR) (list 'IN jv 'RR) '(IN itn_ RR))))
        (fact 'taylor-family-in-fun 'itd_ 'itn_ 'a 'b kv)
        (fact 'fun-apply-type-c dk '(CCINT a b) 'RR zv)
        (fact 'power-closed-at kv (list '- 'b zv))
        (fact 'recip-factorial-in-rr kv)
        (it-mul-real! (list dk zv) pk)
        (it-mul-real! (list '* (list dk zv) pk) rk)
        (fact 'taylor-term-value 'itd_ 'b zv kv)
        (subst (list '== (list (list 'TAYLOR-TERM 'itd_ 'b zv) kv)
                     (list '* (list '* (list dk zv) pk) rk)))
        (ass))))
  (fact 'taylor-sum-unfold 'itd_ jv 'b zv)
  (subst (list '== (list 'TAYLOR-SUM 'itd_ jv 'b zv)
               (list 'SERIES-PARTIAL-SUM (list 'TAYLOR-TERM 'itd_ 'b zv) jv)))
  (fact 'series-partial-sum-in-rr-below jv (list 'TAYLOR-TERM 'itd_ 'b zv))
  (ass))
(qed 'taylor-sum-in-rr)
(topic! 'taylor-sum-in-rr 'analysis)
(alias! 'taylor-sum-in-rr "the Taylor sum of a Taylor family is a real")

(sp (make-wff (it-family-statement
  '(FORALL itj_ (IMPLIES (IN itj_ NN) (IMPLIES (<= itj_ itn_)
     (IN (TAYLOR-AUX itd_ itj_ a b) (FUN (CCINT a b) RR))))))))
(let* ((lnd (dk-peel!))
       (jv  (it-var-of lnd (lambda (c) (eq? c 'NN)) "the truncation order")))
  (fact 'taylor-family-order-pos 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-order-in-nn 'itd_ 'itn_ 'a 'b)
  (fact 'nn-in-rr 'itn_)
  (fact 'nn-zero-in)
  (dk-have! '(< 0 itn_) (lambda () (dk-ineq! '(<= 1 itn_) '(IN itn_ RR))))
  (fact 'taylor-family-in-fun 'itd_ 'itn_ 'a 'b 0)
  (fact 'fun-domain-in-set '(CCINT a b) 'RR '(itd_ 0))
  (mac 'TAYLOR-AUX)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (it-head (dk-goal)) 'FORALL)
         (let ((z (dk-di-var!)))
           (fact 'taylor-sum-in-rr 'itd_ 'itn_ 'a 'b jv z)
           (ass))
         (ass)))
   (dk-opened (lambda () (lam-t)))))
(qed 'taylor-aux-in-fun)
(topic! 'taylor-aux-in-fun 'analysis)
(alias! 'taylor-aux-in-fun
        "the Taylor auxiliary function is a function on the closed interval")

;;; =====================================================================
;;; (7) THE SUM OF ONE SUMMAND.  At order 1 the sum is d(0)(v): the single
;;; summand carries (b - v)^0 = 1 and recip(0!) = 1.  It is the base case of
;;; both inductions below.
;;; =====================================================================
(define it-tm1 '(TAYLOR-TERM itd_ b itv_))
(define it-d01 '((itd_ 0) itv_))

(sp (make-wff '(FORALL itd_ (FORALL b (IMPLIES (IN b RR)
   (FORALL itv_ (IMPLIES (IN itv_ RR)
     (IMPLIES (IN ((itd_ 0) itv_) RR)
       (= (TAYLOR-SUM itd_ (succ 0) b itv_) ((itd_ 0) itv_))))))))))
(dk-peel!)
(fact 'nn-zero-in)
(fact 'rr-sub-in-rr 'b 'itv_)
(fact 'rr-subset-cc '(- b itv_))
(fact 'rr-zero-in)
(dk-have! '(= (recip (succ 0)) 1)
  (lambda () (dk-have! '(= (succ 0) 1) (lambda () (arith)))
             (subst '(= (succ 0) 1)) (fact 'rr-recip-one) (ass)))
(dk-have! (list '= (list it-tm1 0) it-d01)
  (lambda ()
    (fact 'taylor-term-value 'itd_ 'b 'itv_ 0)
    (subst (list '== (list it-tm1 0)
                 (list '* (list '* it-d01 '(power (- b itv_) 0))
                       '(recip (FACTORIAL 0)))))
    (mac 'power-zero)
    (mac 'factorial-zero)
    (subst '(= (recip (succ 0)) 1))
    (crs)))
(dk-have! (list 'IN (list it-tm1 0) 'RR)
  (lambda () (subst (list '= (list it-tm1 0) it-d01)) (ass)))
(dk-have! (list 'IN (list 'SERIES-PARTIAL-SUM it-tm1 0) 'RR)
  (lambda () (mac 'series-partial-sum-zero) (ass)))
(fact 'taylor-sum-unfold 'itd_ '(succ 0) 'b 'itv_)
(subst (list '== '(TAYLOR-SUM itd_ (succ 0) b itv_)
             (list 'SERIES-PARTIAL-SUM it-tm1 '(succ 0))))
(fact 'series-partial-sum-succ it-tm1 0)
(subst (list '== (list 'SERIES-PARTIAL-SUM it-tm1 '(succ 0))
             (list '+ (list 'SERIES-PARTIAL-SUM it-tm1 0) (list it-tm1 0))))
(mac 'series-partial-sum-zero)
(subst (list '= (list it-tm1 0) it-d01))
(crs)
(qed 'taylor-sum-one)
(topic! 'taylor-sum-one 'analysis)
(alias! 'taylor-sum-one "the Taylor sum of order one is the value of the function")

;;; =====================================================================
;;; (8) THE SUM AT THE RIGHT ENDPOINT:  F(b) = f(b).
;;;
;;; At the base point tv_ = b every summand but the first carries
;;; (b - b)^k = 0^k = 0, so the sum collapses to d(0)(b).  This is the notes'
;;; unstated step "F(b) - F(a) = R_n(a, b)" (the other half is (19), which
;;; DEFINES R_n).  It is an induction on the number of summands, written with
;;; the order FIRST because `ni' tests the literal shape of the leading
;;; universal (CLAUDE.md).  The hypothesis is the POINTWISE typing of the
;;; family at b, not IS-TAYLOR-FAMILY: that is what the induction can carry,
;;; and every caller reads it off the family in one step.
;;; =====================================================================

(define (it-below-typing dv bv bound)
  (list 'FORALL 'itk_ (list 'IMPLIES '(IN itk_ NN)
        (list 'IMPLIES (list '<= 'itk_ bound)
              (list 'IN (list (list dv 'itk_) bv) 'RR)))))

(sp (make-wff
  (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
    (list 'FORALL 'itd_ (list 'FORALL 'b (list 'IMPLIES '(IN b RR)
      (list 'IMPLIES (it-below-typing 'itd_ 'b 'itm_)
        (list '= (list 'TAYLOR-SUM 'itd_ '(succ itm_) 'b 'b)
                 '((itd_ 0) b))))))))))
(let* ((br (use-induction)) (nv (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
  ;; ---- base:  the sum of ONE summand at b is d(0)(b) ----
  (dk-focus! (cdr (assq 'base br)))
  (let* ((lnd (dk-peel!))
         (gl  (dk-goal))
         (dv  (cadr (cadr gl)))
         (bv  (cadddr (cadr gl)))
         (ty  (it-first (dk-head? 'FORALL) lnd)))
    (fact 'nn-zero-in)
    (fact 'nn-le-refl 0)
    (dk-apply! ty 0)
    (fact 'taylor-sum-one dv bv bv)
    (ass))
  ;; ---- step:  the new summand carries (b - b)^(succ m) = 0 ----
  (dk-focus! (cdr (assq 'step br)))
  (let* ((lnd (dk-peel!))
         (gl  (dk-goal))
         (dv  (cadr (cadr gl)))
         (bv  (cadddr (cadr gl)))
         (ty  (it-first (dk-head? 'FORALL) lnd))
         (tm  (list 'TAYLOR-TERM dv bv bv))
         (d0  (list (list dv 0) bv))
         (sm  (list 'succ nv))
         (dsm (list (list dv sm) bv))
         (rsm (list 'recip (list 'FACTORIAL sm)))
         (sps (lambda (k) (list 'SERIES-PARTIAL-SUM tm k))))
    (fact 'nn-succ-closed nv)
    (fact 'nn-le-refl sm)
    (fact 'nn-le-succ nv)
    (fact 'nn-zero-in)
    (fact 'nn-zero-le sm)
    (dk-apply! ty 0)
    (dk-apply! ty sm)
    (fact 'recip-factorial-in-rr sm)
    (fact 'rr-sub-in-rr bv bv)
    (fact 'rr-zero-in)
    ;; the typing hypothesis weakened to k <= m, which the induction wants
    (dk-have! (it-below-typing dv bv nv)
      (lambda ()
        (let* ((l2 (dk-peel!))
               (kv (it-var-of l2 (lambda (c) (eq? c 'NN)) "the index")))
          (fact 'nn-le-trans-guarded kv nv sm)
          (dk-apply! ty kv)
          (ass))))
    (dk-apply! ih dv bv)
    (dk-have! (list '= (sps sm) d0)
      (lambda ()
        (fact 'taylor-sum-unfold dv sm bv bv)
        (subst (list '== (sps sm) (list 'TAYLOR-SUM dv sm bv bv)))
        (ass)))
    (dk-have! (list 'IN (sps sm) 'RR)
      (lambda () (subst (list '= (sps sm) d0)) (ass)))
    (dk-have! (list '= (list '- bv bv) 0) (lambda () (crs)))
    (dk-have! (list '= (list tm sm) 0)
      (lambda ()
        (fact 'taylor-term-value dv bv bv sm)
        (subst (list '== (list tm sm)
                     (list '* (list '* dsm (list 'power (list '- bv bv) sm)) rsm)))
        (subst (list '= (list '- bv bv) 0))
        (fact 'power-zero-base nv)
        (subst (list '= (list 'power 0 sm) 0))
        (crs)))
    (dk-have! (list 'IN (list tm sm) 'RR)
      (lambda () (subst (list '= (list tm sm) 0)) (ass)))
    (fact 'taylor-sum-unfold dv (list 'succ sm) bv bv)
    (subst (list '== (list 'TAYLOR-SUM dv (list 'succ sm) bv bv) (sps (list 'succ sm))))
    (fact 'series-partial-sum-succ tm sm)
    (subst (list '== (sps (list 'succ sm)) (list '+ (sps sm) (list tm sm))))
    (subst (list '= (sps sm) d0))
    (subst (list '= (list tm sm) 0))
    (crs)))
(qed 'taylor-sum-at-endpoint)
(topic! 'taylor-sum-at-endpoint 'analysis)
(alias! 'taylor-sum-at-endpoint
        "the Taylor sum towards b, evaluated at b, is the value of the function")

;;; the same fact read off a Taylor family: every d(k) with k <= m is a
;;; function on [a, b], so its value at b is real.
(sp (make-wff (it-family-statement
  '(FORALL itm_ (IMPLIES (IN itm_ NN) (IMPLIES (<= (succ itm_) itn_)
     (= (TAYLOR-SUM itd_ (succ itm_) b b) ((itd_ 0) b))))))))
(let* ((lnd (dk-peel!))
       (mv  (it-var-of lnd (lambda (c) (eq? c 'NN)) "the order")))
  (fact 'taylor-family-order-in-nn 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-right-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-endpoints-lt 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-left-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'nn-succ-closed mv)
  (fact 'nn-in-rr mv)
  (fact 'nn-in-rr (list 'succ mv))
  (fact 'nn-in-rr 'itn_)
  (fact 'bt-lt-succ mv)
  (it-endpoint-in-ccint! 'b)
  (dk-have! (it-below-typing 'itd_ 'b mv)
    (lambda ()
      (let* ((l2 (dk-peel!))
             (kv (it-var-of l2 (lambda (c) (eq? c 'NN)) "the index")))
        (fact 'nn-in-rr kv)
        (dk-have! (list '< kv 'itn_)
          (lambda () (dk-ineq! (list '<= kv mv) (list '< mv (list 'succ mv))
                               (list '<= (list 'succ mv) 'itn_)
                               (list 'IN kv 'RR) (list 'IN mv 'RR)
                               (list 'IN (list 'succ mv) 'RR) '(IN itn_ RR))))
        (fact 'taylor-family-in-fun 'itd_ 'itn_ 'a 'b kv)
        (fact 'fun-apply-type-c (list 'itd_ kv) '(CCINT a b) 'RR 'b)
        (ass))))
  (fact 'taylor-sum-at-endpoint mv 'itd_ 'b)
  (ass))
(qed 'taylor-family-sum-at-endpoint)
(topic! 'taylor-family-sum-at-endpoint 'analysis)
(alias! 'taylor-family-sum-at-endpoint
        "the Taylor sum of a family towards b, at b, is the value of the function")

;;; =====================================================================
;;; (9) CONTINUITY ON A SUBSET OF THE LINE: THREE GENERAL LEMMAS.
;;;
;;; IS-CONTINUOUS-ON(f, D) is continuity as a map off SUBSPACE-MS(RR-MS, D),
;;; and the library's continuity ALGEBRA (`sum-continuous-at',
;;; `product-continuous-at', `scale-continuous-at') lives on RR-MS, i.e. on
;;; TOTAL functions.  These three lemmas are the whole bridge, and nothing of
;;; Taylor's formula is in them:
;;;
;;;   cont-on-in-fun              -- the typing conjunct, as a citation;
;;;   cont-on-transfer-ptwise-eq  -- the IS-CONTINUOUS-ON twin of
;;;                                  `cont-transfer-ptwise-eq';
;;;   cont-on-of-total            -- a function on D agreeing with a function
;;;                                  continuous on the LINE is continuous on D.
;;;
;;; The third is the general form of `pw-restrict-continuous-on'
;;; (pw-antiderivative-laws.scm), which says the same for D = CCINT(a, b); it
;;; is proven here from `restrict-continuous-at' so that this file does not
;;; depend on the piecewise-antiderivative development.
;;; =====================================================================

(sp (make-wff '(FORALL f (FORALL itdm_
   (IMPLIES (IS-CONTINUOUS-ON f itdm_) (IN f (FUN itdm_ RR)))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-CONTINUOUS-ON '(IS-CONTINUOUS-ON f itdm_)))))
(ass)
(qed 'cont-on-in-fun)
(topic! 'cont-on-in-fun 'analysis)
(alias! 'cont-on-in-fun "a function continuous on a set is a function on that set")

(define it-sub '(SUBSPACE-MS RR-MS itdm_))

(sp (make-wff '(FORALL itdm_ (IMPLIES (SUBSET itdm_ RR)
   (FORALL f (FORALL itg_
     (IMPLIES (IN f (FUN itdm_ RR))
     (IMPLIES (IS-CONTINUOUS-ON itg_ itdm_)
     (IMPLIES (FORALL itz_ (IMPLIES (IN itz_ itdm_) (= (f itz_) (itg_ itz_))))
              (IS-CONTINUOUS-ON f itdm_))))))))))
(define it-tr-landed (dk-peel!))
(define it-tr-agree
  (dk-pick (lambda (fm) (and (member fm it-tr-landed) (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'f) (dk-contains? fm 'itg_)))
           "the pointwise agreement"))
(fact 'rr-is-metric-space)
(dk-have! '(SUBSET itdm_ (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'subspace-pts 'RR-MS 'itdm_)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-CONTINUOUS-ON '(IS-CONTINUOUS-ON itg_ itdm_)))))
(define it-tr-cont
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
           "the pointwise continuity of the known map"))
(mac 'IS-CONTINUOUS-ON)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (it-head (dk-goal)) 'FORALL))
       (ass)
       (let ((z (dk-di-var!)))
         (dk-apply! it-tr-cont z)
         (dk-have! (list 'IN 'f (list 'FUN (list 'PTS it-sub) '(PTS RR-MS)))
           (lambda ()
             (subst (list '== (list 'PTS it-sub) 'itdm_))
             (slot 'PTS)
             (ass)))
         (dk-have! (list 'FORALL 'msz_ (list 'IMPLIES (list 'IN 'msz_ (list 'PTS it-sub))
                     '(= (f msz_) (itg_ msz_))))
           (lambda ()
             (let ((y (dk-di-var!)))
               (dk-have! (list 'IN y 'itdm_)
                 (lambda () (subst (list '== 'itdm_ (list 'PTS it-sub))) (ass)))
               (dk-apply! it-tr-agree y)
               (ass))))
         (fact 'ms-cont-transfer-ptwise-eq it-sub 'RR-MS 'itg_ 'f z)
         (ass)))))
(qed 'cont-on-transfer-ptwise-eq)
(topic! 'cont-on-transfer-ptwise-eq 'analysis)
(alias! 'cont-on-transfer-ptwise-eq
        "a function agreeing pointwise with one continuous on a set is continuous on it")

(sp (make-wff '(FORALL itdm_ (IMPLIES (SUBSET itdm_ RR)
   (FORALL itg_ (IMPLIES (IN itg_ (FUN RR RR))
     (IMPLIES (FORALL ity_ (IMPLIES (IN ity_ RR)
                 (IS-CONTINUOUS-AT RR-MS RR-MS itg_ ity_)))
       (FORALL f (IMPLIES (IN f (FUN itdm_ RR))
         (IMPLIES (FORALL itz_ (IMPLIES (IN itz_ itdm_) (= (f itz_) (itg_ itz_))))
                  (IS-CONTINUOUS-ON f itdm_)))))))))))
(define it-tt-landed (dk-peel!))
(define it-tt-cont
  (dk-pick (lambda (fm) (and (member fm it-tt-landed) (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
           "the pointwise continuity on the line"))
(define it-tt-agree
  (dk-pick (lambda (fm) (and (member fm it-tt-landed) (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'f) (dk-contains? fm 'itg_)))
           "the pointwise agreement"))
(fact 'rr-is-metric-space)
(dk-have! '(SUBSET itdm_ (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'subspace-pts 'RR-MS 'itdm_)
(fact 'restrict-in-fun 'itg_ 'RR 'RR 'itdm_)
(dk-have! (list 'IS-CONTINUOUS-ON (list 'RESTRICT 'itg_ 'itdm_) 'itdm_)
  (lambda ()
    (mac 'IS-CONTINUOUS-ON)
    (dk-conj-close!
     (lambda ()
       (if (not (eq? (it-head (dk-goal)) 'FORALL))
           (ass)
           (let ((z (dk-di-var!)))
             (fact 'subset-mem-fwd 'itdm_ 'RR z)
             (dk-apply! it-tt-cont z)
             (fact 'restrict-continuous-at 'RR-MS 'itdm_ 'RR-MS 'itg_ z)
             (ass)))))))
(dk-have! (list 'FORALL 'itz_ (list 'IMPLIES '(IN itz_ itdm_)
            (list '= '(f itz_) (list (list 'RESTRICT 'itg_ 'itdm_) 'itz_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'restrict-apply 'itg_ 'itdm_ z)
      (subst (list '== (list (list 'RESTRICT 'itg_ 'itdm_) z) (list 'itg_ z)))
      (dk-apply! it-tt-agree z)
      (ass))))
(fact 'cont-on-transfer-ptwise-eq 'itdm_ 'f (list 'RESTRICT 'itg_ 'itdm_))
(ass)
(qed 'cont-on-of-total)
(topic! 'cont-on-of-total 'analysis)
(alias! 'cont-on-of-total
        "a function agreeing with a continuous function of the line is continuous on its set")

;;; =====================================================================
;;; (10) THE CONTINUITY OF ONE TAYLOR STEP, ON THE LINE.
;;;
;;; w |-> g(w) + f(w) (b - w)^(k+1) c, for f and g continuous at y.  The
;;; continuity of w |-> (b - w)^(k+1) is the one brick with no model: it comes
;;; from `tgd-power-sub-diff' (theorem-library/taylor-proof.scm, which
;;; differentiates that very lambda) through `diff-implies-continuous'.  The
;;; rest is the algebra, assembled FORWARD and carried to the literal lambda by
;;; `cont-transfer-ptwise-eq' -- the algebra's lambdas nest, the statement's
;;; does not.
;;; =====================================================================
(define it-pl '(VNB-LAMBDA z RR (power (- b z) (succ itk_))))
(define it-prod (list 'VNB-LAMBDA 'x 'RR (list '* '(itf_ x) (list it-pl 'x))))
(define it-sc (list 'VNB-LAMBDA 'x 'RR (list '* 'itc_ (list it-prod 'x))))
(define it-sum (list 'VNB-LAMBDA 'x 'RR (list '+ '(itg_ x) (list it-sc 'x))))
(define it-tgt
  '(VNB-LAMBDA itw_ RR
     (+ (itg_ itw_) (* (* (itf_ itw_) (power (- b itw_) (succ itk_))) itc_))))

;;; the brick: w |-> (b - w)^(k+1) is continuous at every real.
(sp (make-wff '(FORALL b (IMPLIES (IN b RR)
   (FORALL itk_ (IMPLIES (IN itk_ NN)
     (FORALL ity_ (IMPLIES (IN ity_ RR)
       (IS-CONTINUOUS-AT RR-MS RR-MS
         (VNB-LAMBDA z RR (power (- b z) (succ itk_))) ity_)))))))))
(dk-peel!)
(fact 'nn-succ-closed 'itk_)
(fact 'nn-in-rr '(succ itk_))
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 'b 'ity_)
(fact 'power-closed-at 'itk_ '(- b ity_))
(it-mul-real! '(succ itk_) '(power (- b ity_) itk_))
(dk-have! '(IN (- 1) RR) (lambda () (in-rr)))
(it-mul-real! '(* (succ itk_) (power (- b ity_) itk_)) '(- 1))
(fact 'tgd-power-sub-diff 'itk_ 'b 'ity_)
(fact 'diff-implies-continuous it-pl 'ity_
      '(* (* (succ itk_) (power (- b ity_) itk_)) (- 1)))
(ass)
(qed 'power-sub-succ-continuous)
(topic! 'power-sub-succ-continuous 'analysis)
(alias! 'power-sub-succ-continuous
        "(b - z) raised to a successor power is continuous in z")

(sp (make-wff
  '(FORALL b (IMPLIES (IN b RR)
    (FORALL itc_ (IMPLIES (IN itc_ RR)
      (FORALL itk_ (IMPLIES (IN itk_ NN)
        (FORALL itg_ (IMPLIES (IN itg_ (FUN RR RR))
          (FORALL itf_ (IMPLIES (IN itf_ (FUN RR RR))
            (FORALL ity_ (IMPLIES (IN ity_ RR)
              (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS itg_ ity_)
              (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS itf_ ity_)
                (IS-CONTINUOUS-AT RR-MS RR-MS
                  (VNB-LAMBDA itw_ RR
                    (+ (itg_ itw_)
                       (* (* (itf_ itw_) (power (- b itw_) (succ itk_))) itc_)))
                  ity_)))))))))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'itk_)
(fact 'power-sub-succ-continuous 'b 'itk_ 'ity_)
(fact 'product-continuous-at 'itf_ it-pl 'ity_)
(fact 'scale-continuous-at 'itc_ it-prod 'ity_)
(fact 'sum-continuous-at 'itg_ it-sc 'ity_)
(dk-have! (list 'IN it-tgt '(FUN RR RR))
  (lambda ()
    (fact 'rr-is-set)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (it-head (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'fun-apply-type-c 'itf_ 'RR 'RR z)
             (fact 'fun-apply-type-c 'itg_ 'RR 'RR z)
             (fact 'rr-sub-in-rr 'b z)
             (fact 'power-closed-at '(succ itk_) (list '- 'b z))
             (it-mul-real! (list 'itf_ z) (list 'power (list '- 'b z) '(succ itk_)))
             (it-mul-real! (list '* (list 'itf_ z) (list 'power (list '- 'b z) '(succ itk_)))
                           'itc_)
             (it-add-real! (list 'itg_ z)
                           (list '* (list '* (list 'itf_ z)
                                          (list 'power (list '- 'b z) '(succ itk_)))
                                 'itc_))
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
            (list '= (list it-tgt 'x) (list it-sum 'x))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'fun-apply-type-c 'itf_ 'RR 'RR z)
      (fact 'fun-apply-type-c 'itg_ 'RR 'RR z)
      (fact 'rr-sub-in-rr 'b z)
      (fact 'power-closed-at '(succ itk_) (list '- 'b z))
      (dk-lam-b!)
      (crs))))
(fact 'cont-transfer-ptwise-eq it-tgt it-sum 'ity_)
(ass)
(qed 'taylor-step-continuous)
(topic! 'taylor-step-continuous 'analysis)
(alias! 'taylor-step-continuous
        "one Taylor step is continuous wherever its two functions are")

;;; =====================================================================
;;; (11) THE RECURRENCE OF THE AUXILIARY FUNCTION.
;;;
;;;     F_{j+1}(z) = F_j(z) + d(j)(z) (b - z)^j / j!
;;;
;;; -- the partial-sum recurrence, read through TAYLOR-AUX.  Both inductions
;;; below take their step from it.
;;; =====================================================================
(sp (make-wff (it-family-statement
  '(FORALL itj_ (IMPLIES (IN itj_ NN) (IMPLIES (<= (succ itj_) itn_)
     (FORALL itz_ (IMPLIES (IN itz_ (CCINT a b))
       (= ((TAYLOR-AUX itd_ (succ itj_) a b) itz_)
          (+ ((TAYLOR-AUX itd_ itj_ a b) itz_)
             (* (* ((itd_ itj_) itz_) (power (- b itz_) itj_))
                (recip (FACTORIAL itj_)))))))))))))
(let* ((lnd (dk-peel!))
       (jv  (it-var-of lnd (lambda (c) (eq? c 'NN)) "the index"))
       (zv  (it-var-of lnd (lambda (c) (and (pair? c) (eq? (car c) 'CCINT))) "the point"))
       (sj  (list 'succ jv))
       (tm  (list 'TAYLOR-TERM 'itd_ 'b zv))
       (prd (list '* (list '* (list (list 'itd_ jv) zv)
                           (list 'power (list '- 'b zv) jv))
                  (list 'recip (list 'FACTORIAL jv)))))
  (fact 'taylor-family-order-in-nn 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-left-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'taylor-family-right-in-rr 'itd_ 'itn_ 'a 'b)
  (fact 'nn-succ-closed jv)
  (fact 'nn-in-rr jv)
  (fact 'nn-in-rr sj)
  (fact 'nn-in-rr 'itn_)
  (fact 'bt-lt-succ jv)
  (dk-have! (list '<= jv 'itn_)
    (lambda () (dk-ineq! (list '< jv sj) (list '<= sj 'itn_)
                         (list 'IN jv 'RR) (list 'IN sj 'RR) '(IN itn_ RR))))
  (dk-have! (list '< jv 'itn_)
    (lambda () (dk-ineq! (list '< jv sj) (list '<= sj 'itn_)
                         (list 'IN jv 'RR) (list 'IN sj 'RR) '(IN itn_ RR))))
  (fact 'ccint-elt-in-rr 'a 'b zv)
  (fact 'rr-sub-in-rr 'b zv)
  (fact 'taylor-family-in-fun 'itd_ 'itn_ 'a 'b jv)
  (fact 'fun-apply-type-c (list 'itd_ jv) '(CCINT a b) 'RR zv)
  (fact 'power-closed-at jv (list '- 'b zv))
  (fact 'recip-factorial-in-rr jv)
  (it-mul-real! (list (list 'itd_ jv) zv) (list 'power (list '- 'b zv) jv))
  (it-mul-real! (list '* (list (list 'itd_ jv) zv) (list 'power (list '- 'b zv) jv))
                (list 'recip (list 'FACTORIAL jv)))
  (fact 'taylor-term-value 'itd_ 'b zv jv)
  (dk-have! (list 'IN (list tm jv) 'RR)
    (lambda () (subst (list '== (list tm jv) prd)) (ass)))
  (fact 'taylor-sum-in-rr 'itd_ 'itn_ 'a 'b jv zv)
  (fact 'taylor-sum-unfold 'itd_ jv 'b zv)
  (dk-have! (list 'IN (list 'SERIES-PARTIAL-SUM tm jv) 'RR)
    (lambda ()
      (subst (list '== (list 'SERIES-PARTIAL-SUM tm jv)
                   (list 'TAYLOR-SUM 'itd_ jv 'b zv)))
      (ass)))
  (fact 'taylor-aux-value 'itd_ sj 'a 'b zv)
  (fact 'taylor-aux-value 'itd_ jv 'a 'b zv)
  (subst (list '== (list (list 'TAYLOR-AUX 'itd_ sj 'a 'b) zv)
               (list 'TAYLOR-SUM 'itd_ sj 'b zv)))
  (subst (list '== (list (list 'TAYLOR-AUX 'itd_ jv 'a 'b) zv)
               (list 'TAYLOR-SUM 'itd_ jv 'b zv)))
  (fact 'taylor-sum-unfold 'itd_ sj 'b zv)
  (subst (list '== (list 'TAYLOR-SUM 'itd_ sj 'b zv)
               (list 'SERIES-PARTIAL-SUM tm sj)))
  (subst (list '== (list 'TAYLOR-SUM 'itd_ jv 'b zv)
               (list 'SERIES-PARTIAL-SUM tm jv)))
  (fact 'series-partial-sum-succ tm jv)
  (subst (list '== (list 'SERIES-PARTIAL-SUM tm sj)
               (list '+ (list 'SERIES-PARTIAL-SUM tm jv) (list tm jv))))
  (subst (list '== prd (list tm jv)))
  (crs))
(qed 'taylor-aux-step)
(topic! 'taylor-aux-step 'analysis)
(alias! 'taylor-aux-step
        "the auxiliary function of order j+1 is the one of order j plus the j-th summand")

;;; =====================================================================
;;; (12) THE SECOND OF THE NOTES' UNSTATED STEPS: F IS CONTINUOUS ON [a, b].
;;;
;;; Induction on the TRUNCATION ORDER, the family fixed (see (7)).  The base
;;; is the one-summand sum; the step extends F_j and d(j) to the whole line by
;;; EXTEND-CONST -- the move interval-mvt.scm makes for every mean value
;;; theorem -- so that the LINE's continuity algebra applies, and brings the
;;; result back to [a, b] with `cont-on-of-total'.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
    (list 'FORALL 'itd_ (list 'FORALL 'itn_ (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IS-TAYLOR-FAMILY itd_ itn_ a b)
        (list 'IMPLIES '(<= (succ itm_) itn_)
          '(IS-CONTINUOUS-ON (TAYLOR-AUX itd_ (succ itm_) a b)
                             (CCINT a b))))))))))))
(let* ((br (use-induction)) (nv (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
  ;; ---- base:  F_1 = d(0) on [a, b] ----
  (dk-focus! (cdr (assq 'base br)))
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (aux (cadr gl))
         (dv  (cadr aux))
         (av  (cadddr aux))
         (bv  (list-ref aux 4))
         (cc  (list 'CCINT av bv))
         (fam (dk-pick (dk-head? 'IS-TAYLOR-FAMILY) "the Taylor family"))
         (ov  (caddr fam))
         (d0  (list dv 0)))
    (fact 'taylor-family-order-in-nn dv ov av bv)
    (fact 'taylor-family-order-pos dv ov av bv)
    (fact 'taylor-family-left-in-rr dv ov av bv)
    (fact 'taylor-family-right-in-rr dv ov av bv)
    (fact 'nn-in-rr ov)
    (fact 'nn-zero-in)
    (fact 'nn-succ-closed 0)
    (dk-have! (list '< 0 ov) (lambda () (dk-ineq! (list '<= 1 ov) (list 'IN ov 'RR))))
    (fact 'taylor-family-in-fun dv ov av bv 0)
    (fact 'taylor-family-continuous dv ov av bv 0)
    (fact 'taylor-aux-in-fun dv ov av bv '(succ 0))
    (fact 'ccint-subset-rr av bv)
    (dk-have! (list 'FORALL 'itz_ (list 'IMPLIES (list 'IN 'itz_ cc)
                (list '= (list aux 'itz_) (list d0 'itz_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr av bv z)
          (fact 'fun-apply-type-c d0 cc 'RR z)
          (fact 'taylor-aux-value dv '(succ 0) av bv z)
          (subst (list '== (list aux z) (list 'TAYLOR-SUM dv '(succ 0) bv z)))
          (fact 'taylor-sum-one dv bv z)
          (ass))))
    (fact 'cont-on-transfer-ptwise-eq cc aux d0)
    (ass))
  ;; ---- step:  F_{j+1} = F_j + the new summand, on the line ----
  (dk-focus! (cdr (assq 'step br)))
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (hi  (cadr gl))
         (dv  (cadr hi))
         (av  (cadddr hi))
         (bv  (list-ref hi 4))
         (cc  (list 'CCINT av bv))
         (fam (dk-pick (dk-head? 'IS-TAYLOR-FAMILY) "the Taylor family"))
         (ov  (caddr fam))
         (sn  (list 'succ nv))
         (ssn (list 'succ sn))
         (lo  (list 'TAYLOR-AUX dv sn av bv))
         (dsn (list dv sn))
         (rsn (list 'recip (list 'FACTORIAL sn)))
         (e1  (list 'EXTEND-CONST lo av bv))
         (e2  (list 'EXTEND-CONST dsn av bv))
         (wl  (list 'VNB-LAMBDA 'itw_ 'RR
                    (list '+ (list e1 'itw_)
                          (list '* (list '* (list e2 'itw_)
                                         (list 'power (list '- bv 'itw_) sn))
                                rsn)))))
    (fact 'taylor-family-order-in-nn dv ov av bv)
    (fact 'taylor-family-left-in-rr dv ov av bv)
    (fact 'taylor-family-right-in-rr dv ov av bv)
    (fact 'taylor-family-endpoints-lt dv ov av bv)
    ;; `extend-const-continuous-at' is guarded on a <= b
    (dk-have! (list '<= av bv)
      (lambda () (dk-ineq! (list 'IN av 'RR) (list 'IN bv 'RR) (list '< av bv))))
    (fact 'nn-in-rr ov)
    (fact 'nn-succ-closed nv)
    (fact 'nn-succ-closed sn)
    (fact 'nn-in-rr sn)
    (fact 'nn-in-rr ssn)
    (fact 'bt-lt-succ sn)
    (dk-have! (list '<= sn ov)
      (lambda () (dk-ineq! (list '< sn ssn) (list '<= ssn ov)
                           (list 'IN sn 'RR) (list 'IN ssn 'RR) (list 'IN ov 'RR))))
    (dk-have! (list '< sn ov)
      (lambda () (dk-ineq! (list '< sn ssn) (list '<= ssn ov)
                           (list 'IN sn 'RR) (list 'IN ssn 'RR) (list 'IN ov 'RR))))
    (dk-apply! ih dv ov av bv)
    (fact 'taylor-family-continuous dv ov av bv sn)
    (fact 'cont-on-in-fun lo cc)
    (fact 'cont-on-in-fun dsn cc)
    (fact 'extend-const-in-fun av bv lo)
    (fact 'extend-const-in-fun av bv dsn)
    (fact 'recip-factorial-in-rr sn)
    (fact 'taylor-aux-in-fun dv ov av bv ssn)
    (fact 'ccint-subset-rr av bv)
    (fact 'rr-is-set)
    (dk-have! (list 'FORALL 'ity_ (list 'IMPLIES '(IN ity_ RR)
                (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS wl 'ity_)))
      (lambda ()
        (let ((y (dk-di-var!)))
          (fact 'extend-const-continuous-at av bv lo y)
          (fact 'extend-const-continuous-at av bv dsn y)
          (fact 'taylor-step-continuous bv rsn nv e1 e2 y)
          (ass))))
    (dk-have! (list 'IN wl '(FUN RR RR))
      (lambda ()
        (fact 'rr-is-set)
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (it-head (dk-goal)) 'FORALL)
               (let ((z (dk-di-var!)))
                 (fact 'fun-apply-type-c e1 'RR 'RR z)
                 (fact 'fun-apply-type-c e2 'RR 'RR z)
                 (fact 'rr-sub-in-rr bv z)
                 (fact 'power-closed-at sn (list '- bv z))
                 (it-mul-real! (list e2 z) (list 'power (list '- bv z) sn))
                 (it-mul-real! (list '* (list e2 z) (list 'power (list '- bv z) sn)) rsn)
                 (it-add-real! (list e1 z)
                               (list '* (list '* (list e2 z)
                                              (list 'power (list '- bv z) sn))
                                     rsn))
                 (ass))
               (ass)))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'FORALL 'itz_ (list 'IMPLIES (list 'IN 'itz_ cc)
                (list '= (list hi 'itz_) (list wl 'itz_))))
      (lambda ()
        (let ((z (dk-di-var!)))
          (fact 'ccint-elt-in-rr av bv z)
          (fact 'fun-apply-type-c lo cc 'RR z)
          (fact 'fun-apply-type-c dsn cc 'RR z)
          (fact 'rr-sub-in-rr bv z)
          (fact 'power-closed-at sn (list '- bv z))
          (fact 'extend-const-ccint-fixes av bv z lo)
          (fact 'extend-const-ccint-fixes av bv z dsn)
          (fact 'taylor-aux-step dv ov av bv sn z)
          (subst (list '= (list hi z)
                       (list '+ (list lo z)
                             (list '* (list '* (list dsn z)
                                            (list 'power (list '- bv z) sn))
                                   rsn))))
          (dk-lam-b!)
          (subst (list '== (list e1 z) (list lo z)))
          (subst (list '== (list e2 z) (list dsn z)))
          (crs))))
    (fact 'cont-on-of-total cc wl hi)
    (ass)))
(qed 'taylor-aux-continuous-on)
(topic! 'taylor-aux-continuous-on 'analysis)
(alias! 'taylor-aux-continuous-on
        "the Taylor auxiliary function is continuous on the closed interval")

;;; =====================================================================
;;; (13) THE NEIGHBOURHOOD OF AN INTERIOR POINT.
;;;
;;; Every rule of the local derivative (has-deriv-at-sum, -product,
;;; -real-mul, -local) asks for a radius icr_ > 0 and speaks only inside
;;; OOINT(x - icr_, x + icr_).  For a point of OOINT(a, b) the radius is
;;; min(x - a, b - x), which `rr-min-pos' produces existentially.
;;; =====================================================================
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
   (FORALL b (IMPLIES (IN b RR)
     (FORALL itx_ (IMPLIES (IN itx_ (OOINT a b))
       (FORSOME itr_
         (AND (POS-RR itr_)
              (SUBSET (OOINT (- itx_ itr_) (+ itx_ itr_)) (OOINT a b))))))))))))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'ooint-membership '(IN itx_ (OOINT a b))))))
(fact 'rr-sub-in-rr 'itx_ 'a)
(fact 'rr-sub-in-rr 'b 'itx_)
(dk-have! '(< 0 (- itx_ a)) (lambda () (dk-ineq! '(< a itx_) '(IN a RR) '(IN itx_ RR))))
(dk-have! '(< 0 (- b itx_)) (lambda () (dk-ineq! '(< itx_ b) '(IN b RR) '(IN itx_ RR))))
(let ((w (dk-skolem! (dk-fact! 'rr-min-pos '(- itx_ a) '(- b itx_)))))
  (dk-split-all!)
  (fact 'rr-pos-rr-of-lt w)
  (fact 'rr-sub-in-rr 'itx_ w)
  (fact 'rr-add-in-rr 'itx_ w)
  (ew w)
  (dk-conj-close!
   (lambda ()
     (if (eq? (it-head (dk-goal)) 'POS-RR)
         (ass)
         (let ((z (subset-by-element!)))
           (dk-split-all! (dk-landed* (lambda ()
             (mac-h 'ooint-membership
                    (list 'IN z (list 'OOINT (list '- 'itx_ w) (list '+ 'itx_ w)))))))
           (mac 'ooint-membership)
           (dk-conj-close!
            (lambda ()
              (if (eq? (it-head (dk-goal)) 'IN)
                  (ass)
                  (dk-ineq! (list '< (list '- 'itx_ w) z)
                            (list '< z (list '+ 'itx_ w))
                            (list '<= w '(- itx_ a))
                            (list '<= w '(- b itx_))
                            (list 'IN z 'RR) (list 'IN w 'RR)
                            '(IN itx_ RR) '(IN a RR) '(IN b RR))))))))))
(qed 'ooint-interior-radius)
(topic! 'ooint-interior-radius 'topology)
(alias! 'ooint-interior-radius
        "an interior point of an interval has a symmetric neighbourhood inside it")

;;; =====================================================================
;;; (14) THE LOCAL DERIVATIVE OF (b - z)^(k+1), AND THE VALUE IDENTITY OF
;;; THE TELESCOPING STEP.
;;;
;;; taylor-proof.scm differentiates that lambda for the TOTAL theory
;;; (`tgd-power-sub-diff'); `has-deriv-at-iff-diff-at' carries it across.
;;; =====================================================================
(sp (make-wff '(FORALL b (IMPLIES (IN b RR)
   (FORALL itk_ (IMPLIES (IN itk_ NN)
     (FORALL itx_ (IMPLIES (IN itx_ RR)
       (HAS-DERIV-AT (VNB-LAMBDA z RR (power (- b z) (succ itk_))) itx_
                     (* (* (succ itk_) (power (- b itx_) itk_)) (- 1)))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'itk_)
(dk-have! (list 'IN it-pl '(FUN RR RR))
  (lambda ()
    (fact 'rr-is-set)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (it-head (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'rr-sub-in-rr 'b z)
             (fact 'power-closed-at '(succ itk_) (list '- 'b z))
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
(fact 'tgd-power-sub-diff 'itk_ 'b 'itx_)
(fact 'has-deriv-at-iff-diff-at it-pl 'itx_
      '(* (* (succ itk_) (power (- b itx_) itk_)) (- 1)))
(prop)
(qed 'power-sub-succ-has-deriv)
(topic! 'power-sub-succ-has-deriv 'analysis)
(alias! 'power-sub-succ-has-deriv
        "the local derivative of (b - z) raised to a successor power")

;;; V_j + recip((j+1)!) . (d(j+2)(x) (b-x)^(j+1) + ((j+1)(b-x)^j)(-1) d(j+1)(x))
;;;   =  V_{j+1},  once recip(j!) is written (j+1) recip((j+1)!).
(sp (make-wff (it-rr-forall '(d1 d2 p q r s)
   '(= (+ (* (* d1 p) (* s r))
          (* r (+ (* d2 q) (* (* (* s p) (- 1)) d1))))
       (* (* d2 q) r)))))
(dk-peel!)
(crs)
(qed 'taylor-step-identity)
(topic! 'taylor-step-identity 'analysis)
(alias! 'taylor-step-identity "the value identity of the telescoping Taylor step")

;;; =====================================================================
;;; (15) THE THIRD AND LAST OF THE NOTES' UNSTATED STEPS: THE TELESCOPING
;;; DERIVATIVE OF F.
;;;
;;;     F_{j+1}'(x) = d(j+1)(x) (b - x)^j / j!
;;;
;;; The notes compute F'(x) by writing the derivative of each summand as a
;;; DIFFERENCE of two consecutive terms and cancelling; here the same
;;; cancellation is the induction step, and the whole of it is
;;; `taylor-step-identity' -- the product rule supplies
;;;   (d(j+1) . (b - .)^(j+1))'(x) = d(j+2)(x)(b-x)^(j+1) - (j+1) d(j+1)(x)(b-x)^j
;;; and the second half is exactly j+1 times F_{j+1}'(x), which the induction
;;; hypothesis has just produced with the opposite sign.
;;;
;;; Every rule is applied on ONE neighbourhood of x inside (a, b), the radius
;;; of (13); the functions PR and T of the step are lambdas on [a, b], so
;;; their restrictions to that neighbourhood are functions on it.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
    (list 'FORALL 'itd_ (list 'FORALL 'itn_ (list 'FORALL 'a (list 'FORALL 'b
      (list 'IMPLIES '(IS-TAYLOR-FAMILY itd_ itn_ a b)
        (list 'IMPLIES '(<= (succ itm_) itn_)
          '(FORALL itx_ (IMPLIES (IN itx_ (OOINT a b))
             (HAS-DERIV-AT (TAYLOR-AUX itd_ (succ itm_) a b) itx_
               (* (* ((itd_ (succ itm_)) itx_) (power (- b itx_) itm_))
                  (recip (FACTORIAL itm_))))))))))))))))
(let* ((br (use-induction)) (nv (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
  ;; ---- base:  F_1 = d(0) near x, so F_1'(x) = d(1)(x) ----
  (dk-focus! (cdr (assq 'base br)))
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (aux (cadr gl))
         (xv  (caddr gl))
         (dv  (cadr aux))
         (av  (cadddr aux))
         (bv  (list-ref aux 4))
         (cc  (list 'CCINT av bv))
         (fam (dk-pick (dk-head? 'IS-TAYLOR-FAMILY) "the Taylor family"))
         (ov  (caddr fam))
         (d0  (list dv 0))
         (d1  (list (list dv '(succ 0)) xv)))
    (fact 'taylor-family-order-in-nn dv ov av bv)
    (fact 'taylor-family-order-pos dv ov av bv)
    (fact 'taylor-family-left-in-rr dv ov av bv)
    (fact 'taylor-family-right-in-rr dv ov av bv)
    (fact 'nn-in-rr ov)
    (fact 'nn-zero-in)
    (fact 'nn-succ-closed 0)
    (dk-have! (list '< 0 ov) (lambda () (dk-ineq! (list '<= 1 ov) (list 'IN ov 'RR))))
    (fact 'taylor-family-in-fun dv ov av bv 0)
    (fact 'taylor-aux-in-fun dv ov av bv '(succ 0))
    (fact 'ooint-elt-in-rr av bv xv)
    (fact 'rr-sub-in-rr bv xv)
    (fact 'rr-subset-cc (list '- bv xv))
    (dk-apply! (dk-fact! 'taylor-family-deriv dv ov av bv 0) xv)
    (fact 'has-deriv-at-in-rr d0 xv d1)
    (fact 'ooint-subset-ccint av bv)
    (let ((r (dk-skolem! (dk-fact! 'ooint-interior-radius av bv xv))))
      (dk-split-all!)
      (fact 'rr-pos-rr-in-rr r)
      (fact 'rr-sub-in-rr xv r)
      (fact 'rr-add-in-rr xv r)
      (let ((nb (list 'OOINT (list '- xv r) (list '+ xv r))))
        (fact 'subset-trans nb (list 'OOINT av bv) cc)
        (fact 'restrict-in-fun aux cc 'RR nb)
        (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ nb)
                    (list '== (list aux 'hbx_) (list d0 'hbx_))))
          (lambda ()
            (let ((w (dk-di-var!)))
              (fact 'subset-mem-fwd nb cc w)
              (fact 'ccint-elt-in-rr av bv w)
              (fact 'fun-apply-type-c d0 cc 'RR w)
              (fact 'taylor-aux-value dv '(succ 0) av bv w)
              (subst (list '== (list aux w) (list 'TAYLOR-SUM dv '(succ 0) bv w)))
              (fact 'taylor-sum-one dv bv w)
              (subst (list '= (list 'TAYLOR-SUM dv '(succ 0) bv w) (list d0 w)))
              (qrfl))))
        (fact 'has-deriv-at-local r aux d0 xv d1)
        (dk-have! '(= (recip (succ 0)) 1)
          (lambda () (dk-have! '(= (succ 0) 1) (lambda () (arith)))
                     (subst '(= (succ 0) 1)) (fact 'rr-recip-one) (ass)))
        (mac 'power-zero)
        (mac 'factorial-zero)
        (subst '(= (recip (succ 0)) 1))
        (dk-have! (list '= (list '* (list '* d1 1) 1) d1) (lambda () (crs)))
        (subst (list '= (list '* (list '* d1 1) 1) d1))
        (ass))))
  ;; ---- step:  the product rule on the new summand, then the cancellation ----
  (dk-focus! (cdr (assq 'step br)))
  (dk-peel!)
  (let* ((gl  (dk-goal))
         (hi  (cadr gl))
         (xv  (caddr gl))
         (dv  (cadr hi))
         (av  (cadddr hi))
         (bv  (list-ref hi 4))
         (cc  (list 'CCINT av bv))
         (fam (dk-pick (dk-head? 'IS-TAYLOR-FAMILY) "the Taylor family"))
         (ov  (caddr fam))
         (sn  (list 'succ nv))
         (ssn (list 'succ sn))
         (lo  (list 'TAYLOR-AUX dv sn av bv))
         (dsn (list dv sn))
         (dss (list dv ssn))
         (rsn (list 'recip (list 'FACTORIAL sn)))
         (rnv (list 'recip (list 'FACTORIAL nv)))
         (pnv (list 'power (list '- bv xv) nv))
         (psn (list 'power (list '- bv xv) sn))
         (d1  (list dsn xv))
         (d2  (list dss xv))
         (mm  (list '* (list '* sn pnv) '(- 1)))
         (vlo (list '* (list '* d1 pnv) rnv))
         (vhi (list '* (list '* d2 psn) rsn))
         (pr  (list 'VNB-LAMBDA 'itw_ cc
                    (list '* (list dsn 'itw_) (list 'power (list '- bv 'itw_) sn))))
         (tl  (list 'VNB-LAMBDA 'itw_ cc
                    (list '* (list '* (list dsn 'itw_)
                                   (list 'power (list '- bv 'itw_) sn))
                          rsn)))
         (pl  (list 'VNB-LAMBDA 'z 'RR (list 'power (list '- bv 'z) sn))))
    (fact 'taylor-family-order-in-nn dv ov av bv)
    (fact 'taylor-family-left-in-rr dv ov av bv)
    (fact 'taylor-family-right-in-rr dv ov av bv)
    (fact 'nn-in-rr ov)
    (fact 'nn-succ-closed nv)
    (fact 'nn-succ-closed sn)
    (fact 'nn-in-rr nv)
    (fact 'nn-in-rr sn)
    (fact 'nn-in-rr ssn)
    (fact 'bt-lt-succ sn)
    (fact 'rr-one-in)
    (dk-have! '(IN (- 1) RR) (lambda () (in-rr)))
    (dk-have! (list '<= sn ov)
      (lambda () (dk-ineq! (list '< sn ssn) (list '<= ssn ov)
                           (list 'IN sn 'RR) (list 'IN ssn 'RR) (list 'IN ov 'RR))))
    (dk-have! (list '< sn ov)
      (lambda () (dk-ineq! (list '< sn ssn) (list '<= ssn ov)
                           (list 'IN sn 'RR) (list 'IN ssn 'RR) (list 'IN ov 'RR))))
    (fact 'ooint-elt-in-rr av bv xv)
    (fact 'rr-sub-in-rr bv xv)
    (fact 'power-closed-at nv (list '- bv xv))
    (fact 'power-closed-at sn (list '- bv xv))
    (fact 'recip-factorial-in-rr nv)
    (fact 'recip-factorial-in-rr sn)
    (fact 'taylor-family-in-fun dv ov av bv sn)
    ;; the interior point is a point of the CLOSED interval, which is where
    ;; d(j+1) is defined
    (fact 'ooint-subset-ccint av bv)
    (fact 'subset-mem-fwd (list 'OOINT av bv) cc xv)
    (fact 'fun-apply-type-c dsn cc 'RR xv)
    (fact 'fun-domain-in-set cc 'RR dsn)
    (dk-apply! (dk-fact! 'taylor-family-deriv dv ov av bv sn) xv)
    (fact 'has-deriv-at-in-rr dsn xv d2)
    (fact 'power-sub-succ-has-deriv bv nv xv)
    (it-mul-real! sn pnv)
    (it-mul-real! (list '* sn pnv) '(- 1))
    (fact 'taylor-aux-in-fun dv ov av bv sn)
    (fact 'taylor-aux-in-fun dv ov av bv ssn)
    (dk-apply! (dk-apply! ih dv ov av bv) xv)
    (fact 'ooint-subset-ccint av bv)
    ;; The two lambdas of the step are functions on [a, b].  Each closure lands
    ;; EXACTLY the typings its own body needs and stops: a landing that closes
    ;; the leaf moves the focus to the sibling, and a further step would run
    ;; there (CLAUDE.md, focus drift).
    (dk-have! (list 'IN pr (list 'FUN cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (it-head (dk-goal)) 'FORALL)
               (let ((z (dk-di-var!)))
                 (fact 'ccint-elt-in-rr av bv z)
                 (fact 'fun-apply-type-c dsn cc 'RR z)
                 (fact 'rr-sub-in-rr bv z)
                 (fact 'power-closed-at sn (list '- bv z))
                 (it-mul-real! (list dsn z) (list 'power (list '- bv z) sn))
                 (ass))
               (ass)))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'IN tl (list 'FUN cc 'RR))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (it-head (dk-goal)) 'FORALL)
               (let ((z (dk-di-var!)))
                 (fact 'ccint-elt-in-rr av bv z)
                 (fact 'fun-apply-type-c dsn cc 'RR z)
                 (fact 'rr-sub-in-rr bv z)
                 (fact 'power-closed-at sn (list '- bv z))
                 (it-mul-real! (list dsn z) (list 'power (list '- bv z) sn))
                 (it-mul-real! (list '* (list dsn z) (list 'power (list '- bv z) sn))
                               rsn)
                 (ass))
               (ass)))
         (dk-opened (lambda () (lam-t))))))
    (let ((r (dk-skolem! (dk-fact! 'ooint-interior-radius av bv xv))))
      (dk-split-all!)
      (fact 'rr-pos-rr-in-rr r)
      (fact 'rr-sub-in-rr xv r)
      (fact 'rr-add-in-rr xv r)
      (let ((nb (list 'OOINT (list '- xv r) (list '+ xv r))))
        (fact 'subset-trans nb (list 'OOINT av bv) cc)
        (fact 'restrict-in-fun pr cc 'RR nb)
        (fact 'restrict-in-fun tl cc 'RR nb)
        (fact 'restrict-in-fun hi cc 'RR nb)
        ;; PR(w) = d(j+1)(w) . (b - w)^(j+1)
        (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ nb)
                    (list '== (list pr 'hbx_)
                          (list '* (list dsn 'hbx_) (list pl 'hbx_)))))
          (lambda ()
            (let ((w (dk-di-var!)))
              (fact 'subset-mem-fwd nb cc w)
              (fact 'ccint-elt-in-rr av bv w)
              (dk-lam-b!)
              (qrfl))))
        ;; T(w) = recip((j+1)!) . PR(w)
        (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ nb)
                    (list '== (list tl 'hbx_) (list '* rsn (list pr 'hbx_)))))
          (lambda ()
            (let ((w (dk-di-var!)))
              (fact 'subset-mem-fwd nb cc w)
              (fact 'ccint-elt-in-rr av bv w)
              (fact 'fun-apply-type-c dsn cc 'RR w)
              (fact 'rr-sub-in-rr bv w)
              (fact 'power-closed-at sn (list '- bv w))
              (dk-lam-b!)
              (let ((l (list '* (list '* (list dsn w)
                                     (list 'power (list '- bv w) sn)) rsn))
                    (rr_ (list '* rsn (list '* (list dsn w)
                                            (list 'power (list '- bv w) sn)))))
                (dk-have! (list '= l rr_) (lambda () (crs)))
                (subst (list '= l rr_))
                (qrfl)))))
        ;; F_{j+2}(w) = F_{j+1}(w) + T(w)
        (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ nb)
                    (list '== (list hi 'hbx_)
                          (list '+ (list lo 'hbx_) (list tl 'hbx_)))))
          (lambda ()
            (let ((w (dk-di-var!)))
              (fact 'subset-mem-fwd nb cc w)
              (fact 'ccint-elt-in-rr av bv w)
              (fact 'taylor-aux-step dv ov av bv sn w)
              (dk-lam-b!)
              (subst (list '= (list hi w)
                           (list '+ (list lo w)
                                 (list '* (list '* (list dsn w)
                                                (list 'power (list '- bv w) sn))
                                       rsn))))
              (qrfl))))
        ;; the product rule, then the constant multiple, then the sum
        (let* ((p1  (dk-fact! 'has-deriv-at-product r dsn pl pr xv d2 mm))
               (p1b (dk-landed-1 (lambda () (lam-b-h p1))))
               (mpr (cadddr p1b)))
          (dk-fact! 'has-deriv-at-real-mul r pr tl rsn xv mpr)
          (dk-fact! 'has-deriv-at-sum r lo tl hi xv vlo (list '* rsn mpr))
          (fact 'tgd-recip-factorial-succ nv)
          (dk-have! (list '= (list '+ vlo (list '* rsn mpr)) vhi)
            (lambda ()
              (subst (list '= rnv (list '* sn rsn)))
              (fact 'taylor-step-identity d1 d2 pnv psn rsn sn)
              (ass)))
          (subst (list '= vhi (list '+ vlo (list '* rsn mpr))))
          (ass))))))
(qed 'taylor-aux-has-deriv)
(topic! 'taylor-aux-has-deriv 'analysis)
(alias! 'taylor-aux-has-deriv
        "the telescoping derivative of the Taylor auxiliary function")

;;; =====================================================================
;;; (16) THEOREM 2.18, in the notes' form, from the auxiliary function's four
;;; properties.
;;;
;;; WHAT IS ASSUMED HERE AND WHAT IS NOT.  The three hypotheses this theorem
;;; makes about TAYLOR-AUX -- its continuity on [a, b], its derivative on
;;; (a, b) and the value of the sum at the right endpoint -- are the notes'
;;; unstated steps "F is continuous", the telescoping computation of F'(x),
;;; and "F(b) - F(a) = R_n(a, b)".  They are PROVEN above, in (12), (15) and
;;; (8), and (17) below is this theorem with all three discharged; the
;;; conditional form is kept because it is the useful one when a caller has a
;;; different auxiliary function in hand.  Nothing here is a SUPPORT and the
;;; bill is `modulo 0'.
;;;
;;; n = succ(m).  The notes' n >= 1 is written as a successor so that `power'
;;; and `FACTORIAL' receive n - 1 = m as a natural number; RR subtraction does
;;; not deliver one, and `succ' off NN is uninterpreted.
;;;
;;; BOTH FORMS OF (20) ARE CONCLUDED.  The first is (20) multiplied through by
;;; (n-1)!, the form free of division that docs/real-calculus-statements.tex
;;; proposes; the second is (20) LITERALLY, with the division exactly where the
;;; notes divide.  THE GUARD THAT MAKES THE DIVISOR NON-ZERO IS NOT A
;;; HYPOTHESIS AND DOES NOT NEED TO BE: the notes divide by (n-1)! and by
;;; nothing else -- there is no G'(xi) in a denominator -- and (n-1)! is a
;;; positive real for every m in NN (`factorial-real-pos'), so `recip' of it is
;;; defined outright.  The division is written `* recip(FACTORIAL(m))', which
;;; is what the reader desugars `/ FACTORIAL(m)' to.
;;; =====================================================================

(define it-nn '(succ itm_))
(define it-aux (list 'TAYLOR-AUX 'itd_ it-nn 'a 'b))
(define it-top (list 'itd_ it-nn))
(define it-fac '(FACTORIAL itm_))
(define it-rcp (list 'recip it-fac))
(define (it-val x)
  (list '* (list '* (list it-top x) (list 'power (list '- 'b x) 'itm_)) it-rcp))
(define it-vlam (list 'VNB-LAMBDA 'itw_ '(OOINT a b) (it-val 'itw_)))
(define it-sum-at (lambda (x) (list 'TAYLOR-SUM 'itd_ it-nn 'b x)))
(define it-rem (list 'TAYLOR-REM 'itd_ it-nn 'a 'b))

(define (it-imp-chain hyps concl)
  (if (null? hyps) concl (list 'IMPLIES (car hyps) (it-imp-chain (cdr hyps) concl))))

(define it-eq1
  (list '= (list '* (list '* 'itmu_ it-rem) it-fac)
           (list '* (list '* (list it-top 'itxi_) (list 'power '(- b itxi_) 'itm_))
                 '(- (itg_ b) (itg_ a)))))
(define it-eq2
  (list '= (list '* 'itmu_ it-rem)
           (list '* (list '* (list '* (list it-top 'itxi_) it-rcp)
                          (list 'power '(- b itxi_) 'itm_))
                 '(- (itg_ b) (itg_ a)))))
(define it-concl
  (list 'FORSOME 'itxi_
    (list 'AND '(IN itxi_ (OOINT a b))
      (list 'FORSOME 'itmu_
        (list 'AND (list 'HAS-DERIV-AT 'itg_ 'itxi_ 'itmu_)
              (list 'AND it-eq1 it-eq2))))))
(define it-g-block
  (list 'FORALL 'itg_
    (it-imp-chain
     (list '(IN itg_ (FUN (CCINT a b) RR))
           (list 'IS-CONTINUOUS-ON 'itg_ '(CCINT a b))
           (list 'FORALL 'itx_ (list 'IMPLIES '(IN itx_ (OOINT a b))
                 (list 'FORSOME 'itl_ (list 'HAS-DERIV-AT 'itg_ 'itx_ 'itl_)))))
     it-concl)))
(define it-statement
  (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
    (list 'FORALL 'b (list 'IMPLIES '(IN b RR)
      (list 'FORALL 'itd_
        (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
          (it-imp-chain
           (list (list 'IS-TAYLOR-FAMILY 'itd_ it-nn 'a 'b)
                 (list 'IS-CONTINUOUS-ON it-aux '(CCINT a b))
                 (list 'FORALL 'itx_ (list 'IMPLIES '(IN itx_ (OOINT a b))
                       (list 'HAS-DERIV-AT it-aux 'itx_ (it-val 'itx_))))
                 (list '= (it-sum-at 'b) '((itd_ 0) b)))
           it-g-block)))))))))

(sp (make-wff it-statement))

(dk-peel!)
(define it-h2
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL) (dk-contains? fm 'TAYLOR-AUX)))
           "the derivative hypothesis on the auxiliary function"))
(fact 'taylor-family-endpoints-lt 'itd_ it-nn 'a 'b)
(fact 'nn-succ-closed 'itm_)
(fact 'nn-le-refl it-nn)
(fact 'taylor-aux-in-fun 'itd_ it-nn 'a 'b it-nn)
(fact 'taylor-family-top-in-fun 'itd_ it-nn 'a 'b)
(fact 'recip-factorial-in-rr 'itm_)
(dk-split! (dk-fact! 'factorial-real-pos 'itm_))
(fact 'fun-domain-in-set '(OOINT a b) 'RR it-top)
;; the derivative VALUE as a function on the open interval
(dk-have! (list 'IN it-vlam '(FUN (OOINT a b) RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (it-head (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'ooint-elt-in-rr 'a 'b z)
             (fact 'fun-apply-type-c it-top '(OOINT a b) 'RR z)
             (fact 'rr-sub-in-rr 'b z)
             (fact 'power-closed-at 'itm_ (list '- 'b z))
             (it-mul-real! (list it-top z) (list 'power (list '- 'b z) 'itm_))
             (it-mul-real! (list '* (list it-top z) (list 'power (list '- 'b z) 'itm_)) it-rcp)
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
;; the derivative hypothesis in the shape gmvt-with-known-derivative wants
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x (OOINT a b))
            (list 'HAS-DERIV-AT it-aux 'x (list it-vlam 'x))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (dk-apply! it-h2 z)
      (dk-lam-b!)
      (ass))))
;; the endpoint values of the auxiliary function
(it-endpoint-in-ccint! 'a)
(it-endpoint-in-ccint! 'b)
(fact 'taylor-aux-value 'itd_ it-nn 'a 'b 'a)
(fact 'taylor-aux-value 'itd_ it-nn 'a 'b 'b)
(fact 'fun-apply-type-c it-aux '(CCINT a b) 'RR 'a)
(fact 'fun-apply-type-c it-aux '(CCINT a b) 'RR 'b)
(fact 'rr-sub-in-rr (list it-aux 'b) (list it-aux 'a))
(dk-have! (list 'IN it-rem 'RR)
  (lambda ()
    (mac 'TAYLOR-REM)
    (subst (list '= '((itd_ 0) b) (it-sum-at 'b)))
    (subst (list '== (it-sum-at 'b) (list it-aux 'b)))
    (subst (list '== (it-sum-at 'a) (list it-aux 'a)))
    (ass)))
;; 2.11 with the known derivative
(let ((xi (dk-skolem! (dk-fact! 'gmvt-with-known-derivative 'a 'b it-aux 'itg_ it-vlam))))
  (dk-split-all!)
  (let ((mu (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the derivative existential"))))
    (dk-split-all!)
    (let* ((pv (list it-top xi))
           (qv (list 'power (list '- 'b xi) 'itm_))
           (wv '(- (itg_ b) (itg_ a)))
           (uv (list '* 'itmu_ it-rem)))
      (fact 'ooint-elt-in-rr 'a 'b xi)
      (fact 'fun-apply-type-c it-top '(OOINT a b) 'RR xi)
      (fact 'rr-sub-in-rr 'b xi)
      (fact 'power-closed-at 'itm_ (list '- 'b xi))
      (fact 'has-deriv-at-in-rr 'itg_ xi mu)
      (fact 'fun-apply-type-c 'itg_ '(CCINT a b) 'RR 'a)
      (fact 'fun-apply-type-c 'itg_ '(CCINT a b) 'RR 'b)
      (fact 'rr-sub-in-rr '(itg_ b) '(itg_ a))
      (it-mul-real! mu it-rem)
      (dk-have! (list 'AND (list 'IN it-fac 'RR) (list 'NOT (list '= it-fac 0)))
        (lambda ()
          (fact 'rr-pos-ne-zero it-fac)
          (dk-conj-close! (lambda () (ass)))))
      (fact 'rr-recip-inverse it-fac)
      ;; the beta value of the known derivative at xi
      (dk-have! (list '== (list it-vlam xi) (it-val xi)) (lambda () (dk-lam-b!) (qrfl)))
      ;; the premise of the clearing identity
      (dk-have! (list '= (list '* (list '* (list '* pv qv) it-rcp) wv)
                      (list '* mu it-rem))
        (lambda ()
          (mac 'TAYLOR-REM)
          (subst (list '= '((itd_ 0) b) (it-sum-at 'b)))
          (subst (list '== (it-sum-at 'b) (list it-aux 'b)))
          (subst (list '== (it-sum-at 'a) (list it-aux 'a)))
          (subst (list '= (it-val xi) (list it-vlam xi)))
          (ass)))
      (dk-split-all!
       (list (dk-fact! 'taylor-clear-recip pv qv it-rcp it-fac (list '* mu it-rem) wv)))
      (ew xi)
      (dk-conj-close!
       (lambda ()
         (if (eq? (it-head (dk-goal)) 'IN)
             (ass)
             (begin (ew mu) (dk-conj-close! (lambda () (ass))))))))))
(qed 'taylor-formula-on-interval-from-aux)
(topic! 'taylor-formula-on-interval-from-aux 'analysis)
(alias! 'taylor-formula-on-interval-from-aux
        "Taylor's formula from the four properties of the auxiliary function")

;;; =====================================================================
;;; (17) THEOREM 2.18 ITSELF.  The three remaining hypotheses of (16) are
;;; now theorems -- (12) the continuity, (15) the derivative, (8) the value
;;; at b -- so the statement is the notes' own: a Taylor family of order n
;;; on [a, b] and any G continuous on [a, b] and differentiable on (a, b).
;;; Nothing else is assumed, and the bill is `modulo 0'.
;;; =====================================================================
(define it-statement-plain
  (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
    (list 'FORALL 'b (list 'IMPLIES '(IN b RR)
      (list 'FORALL 'itd_
        (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
          (it-imp-chain
           (list (list 'IS-TAYLOR-FAMILY 'itd_ it-nn 'a 'b))
           it-g-block)))))))))

(sp (make-wff it-statement-plain))
(dk-peel!)
(fact 'nn-succ-closed 'itm_)
(fact 'nn-le-refl it-nn)
(fact 'taylor-aux-continuous-on 'itm_ 'itd_ it-nn 'a 'b)
(fact 'taylor-aux-has-deriv 'itm_ 'itd_ it-nn 'a 'b)
(fact 'taylor-family-sum-at-endpoint 'itd_ it-nn 'a 'b 'itm_)
(fact 'taylor-formula-on-interval-from-aux 'a 'b 'itd_ 'itm_ 'itg_)
(ass)
(qed 'taylor-formula-on-interval)
(topic! 'taylor-formula-on-interval 'analysis)
(alias! 'taylor-formula-on-interval
        "Taylor's formula with a general remainder for a function on a closed interval")

;;; =====================================================================
;;; (18) COROLLARY 2.19 -- THE LAGRANGE FORM OF THE REMAINDER.
;;;
;;; The notes: "Letting G(x) = (b - x)^n, we obtain G(b) - G(a) = -(b-a)^n
;;; and G'(x) = -n (b-x)^(n-1); therefore
;;;
;;;  (23)     R_n(a, b) = f^(n)(xi) / n! . (b - a)^n."
;;;
;;; G is the function (b - x)^n ON [a, b] -- the notes' functions live on
;;; their interval -- so it is the lambda on CCINT(a, b); its continuity and
;;; its derivative come from the TOTAL lambda of the same body, which
;;; `power-sub-succ-continuous' and `power-sub-succ-has-deriv' settle, through
;;; `cont-on-of-total' and `has-deriv-at-local'.
;;;
;;; THE CANCELLATION the notes perform in one line -- dividing by
;;; -n (b - xi)^(n-1), which is what G'(xi) is -- is here: the factor
;;; n (b - xi)^(n-1) is POSITIVE (xi < b), so it is non-zero and
;;; `rr-cancel-mul-left' removes it.  `tgd-recip-factorial-succ' turns
;;; recip((n-1)!) into n . recip(n!), which is what puts the n! of (23) in
;;; place.
;;; =====================================================================
(define it-gl (list 'VNB-LAMBDA 'itw_ '(CCINT a b) (list 'power '(- b itw_) it-nn)))
(define it-pln (list 'VNB-LAMBDA 'z 'RR (list 'power '(- b z) it-nn)))
(define (it-gd x) (list '* (list '* it-nn (list 'power (list '- 'b x) 'itm_)) '(- 1)))
(define it-lag-deriv
  (list 'FORALL 'itx_ (list 'IMPLIES '(IN itx_ (OOINT a b))
        (list 'HAS-DERIV-AT it-gl 'itx_ (it-gd 'itx_)))))

(sp (make-wff
  (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
    (list 'FORALL 'b (list 'IMPLIES '(IN b RR)
      (list 'FORALL 'itd_
        (list 'FORALL 'itm_ (list 'IMPLIES '(IN itm_ NN)
          (list 'IMPLIES (list 'IS-TAYLOR-FAMILY 'itd_ it-nn 'a 'b)
            (list 'FORSOME 'itxi_
              (list 'AND '(IN itxi_ (OOINT a b))
                    (list '= it-rem
                          (list '* (list '* (list it-top 'itxi_)
                                         (list 'recip (list 'FACTORIAL it-nn)))
                                (list 'power '(- b a) it-nn)))))))))))))))
(dk-peel!)
(fact 'taylor-family-order-pos 'itd_ it-nn 'a 'b)
(fact 'taylor-family-endpoints-lt 'itd_ it-nn 'a 'b)
(fact 'nn-succ-closed 'itm_)
(fact 'nn-in-rr it-nn)
(fact 'nn-in-rr 'itm_)
(fact 'nn-le-refl it-nn)
(fact 'nn-zero-in)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'bt-lt-succ 'itm_)
(dk-have! '(IN (- 1) RR) (lambda () (in-rr)))
(dk-have! (list '< 0 it-nn)
  (lambda () (dk-ineq! (list '< 'itm_ it-nn) '(IN itm_ RR) (list 'IN it-nn 'RR)
                       (list '<= 1 it-nn))))
(fact 'taylor-family-in-fun 'itd_ it-nn 'a 'b 0)
(fact 'fun-domain-in-set '(CCINT a b) 'RR '(itd_ 0))
(fact 'ccint-subset-rr 'a 'b)
(fact 'ooint-subset-ccint 'a 'b)
(fact 'rr-is-set)
(fact 'recip-factorial-in-rr it-nn)
(fact 'rr-sub-in-rr 'b 'a)
(fact 'power-closed-at it-nn '(- b a))
(it-endpoint-in-ccint! 'a)
(it-endpoint-in-ccint! 'b)
;; the remainder is a real
(fact 'fun-apply-type-c '(itd_ 0) '(CCINT a b) 'RR 'b)
(fact 'taylor-sum-in-rr 'itd_ it-nn 'a 'b it-nn 'a)
(fact 'rr-sub-in-rr '((itd_ 0) b) (list 'TAYLOR-SUM 'itd_ it-nn 'b 'a))
(dk-have! (list 'IN it-rem 'RR)
  (lambda () (mac 'TAYLOR-REM) (ass)))
;; G on [a, b] and its total twin
(dk-have! (list 'IN it-gl '(FUN (CCINT a b) RR))
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (it-head (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'ccint-elt-in-rr 'a 'b z)
             (fact 'rr-sub-in-rr 'b z)
             (fact 'power-closed-at it-nn (list '- 'b z))
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'IN it-pln '(FUN RR RR))
  (lambda ()
    (fact 'rr-is-set)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (it-head (dk-goal)) 'FORALL)
           (let ((z (dk-di-var!)))
             (fact 'rr-sub-in-rr 'b z)
             (fact 'power-closed-at it-nn (list '- 'b z))
             (ass))
           (ass)))
     (dk-opened (lambda () (lam-t))))))
(dk-have! (list 'FORALL 'ity_ (list 'IMPLIES '(IN ity_ RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS it-pln 'ity_)))
  (lambda ()
    (let ((y (dk-di-var!)))
      (fact 'power-sub-succ-continuous 'b 'itm_ y)
      (ass))))
(dk-have! (list 'FORALL 'itz_ (list 'IMPLIES '(IN itz_ (CCINT a b))
            (list '= (list it-gl 'itz_) (list it-pln 'itz_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (fact 'rr-sub-in-rr 'b z)
      (fact 'power-closed-at it-nn (list '- 'b z))
      (dk-lam-b!)
      (rfl))))
(fact 'cont-on-of-total '(CCINT a b) it-pln it-gl)
;; G'(x) = -n (b - x)^(n-1) at every interior point
(dk-have! it-lag-deriv
  (lambda ()
    (let ((x (dk-di-var!)))
      (fact 'ooint-elt-in-rr 'a 'b x)
      (fact 'power-sub-succ-has-deriv 'b 'itm_ x)
      (let ((r (dk-skolem! (dk-fact! 'ooint-interior-radius 'a 'b x))))
        (dk-split-all!)
        (fact 'rr-pos-rr-in-rr r)
        (fact 'rr-sub-in-rr x r)
        (fact 'rr-add-in-rr x r)
        (let ((nb (list 'OOINT (list '- x r) (list '+ x r))))
          (fact 'subset-trans nb '(OOINT a b) '(CCINT a b))
          (fact 'restrict-in-fun it-gl '(CCINT a b) 'RR nb)
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ nb)
                      (list '== (list it-gl 'hbx_) (list it-pln 'hbx_))))
            (lambda ()
              (let ((w (dk-di-var!)))
                (fact 'subset-mem-fwd nb '(CCINT a b) w)
                (fact 'ccint-elt-in-rr 'a 'b w)
                (dk-lam-b!)
                (qrfl))))
          (fact 'has-deriv-at-local r it-gl it-pln x (it-gd x))
          (ass))))))
(dk-have! (list 'FORALL 'itx_ (list 'IMPLIES '(IN itx_ (OOINT a b))
            (list 'FORSOME 'itl_ (list 'HAS-DERIV-AT it-gl 'itx_ 'itl_))))
  (lambda ()
    (let ((x (dk-di-var!)))
      (dk-apply! it-lag-deriv x)
      (ew (it-gd x))
      (ass))))
;; 2.18 at G
(let ((xi (dk-skolem! (dk-fact! 'taylor-formula-on-interval 'a 'b 'itd_ 'itm_ it-gl))))
  (dk-split-all!)
  (let ((mu (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the derivative existential"))))
    (dk-split-all!)
    (let* ((dn  (list it-top xi))
           (pp  (list 'power (list '- 'b xi) 'itm_))
           (qq  (list 'power '(- b a) it-nn))
           (rm  '(recip (FACTORIAL itm_)))
           (rf  (list 'recip (list 'FACTORIAL it-nn)))
           (cc_ (list '* it-nn pp))
           (rr_ it-rem)
           (gb  (list it-gl 'b))
           (ga  (list it-gl 'a))
           (eqv (list '= (list '* cc_ (list '* '(- 1) rr_))
                      (list '* cc_ (list '* (list '* dn rf) (list '- 0 qq))))))
      (fact 'ooint-elt-in-rr 'a 'b xi)
      (fact 'rr-sub-in-rr 'b xi)
      (fact 'power-closed-at 'itm_ (list '- 'b xi))
      (fact 'recip-factorial-in-rr 'itm_)
      (fact 'taylor-family-top-in-fun 'itd_ it-nn 'a 'b)
      (fact 'fun-apply-type-c it-top '(OOINT a b) 'RR xi)
      (it-mul-real! it-nn pp)
      (dk-apply! it-lag-deriv xi)
      (fact 'has-deriv-at-unique it-gl xi mu (it-gd xi))
      ;; the endpoint values of G
      (dk-have! (list '= gb 0)
        (lambda ()
          (dk-lam-b!)
          (dk-have! '(= (- b b) 0) (lambda () (crs)))
          (subst '(= (- b b) 0))
          (fact 'power-zero-base 'itm_)
          (subst (list '= (list 'power 0 it-nn) 0))
          (rfl)))
      (dk-have! (list '= ga qq) (lambda () (dk-lam-b!) (rfl)))
      ;; the cancellable form of (20)
      (dk-have! eqv
        (lambda ()
          (dk-have! (list '= (list '* cc_ (list '* '(- 1) rr_))
                          (list '* (it-gd xi) rr_))
            (lambda () (crs)))
          (subst (list '= (list '* cc_ (list '* '(- 1) rr_))
                       (list '* (it-gd xi) rr_)))
          (subst (list '= (it-gd xi) mu))
          (subst (list '= (list '* mu rr_)
                       (list '* (list '* (list '* dn rm) pp) (list '- gb ga))))
          (subst (list '= gb 0))
          (subst (list '= ga qq))
          (fact 'tgd-recip-factorial-succ 'itm_)
          (subst (list '= rm (list '* it-nn rf)))
          (crs)))
      ;; the factor n (b - xi)^(n-1) is positive, hence non-zero
      ;; `mac-h' CONSUMES the membership, which the conclusion still needs:
      ;; the projection is taken on a lane (CLAUDE.md, dk-project!).
      (dk-have! (list '< xi 'b)
        (lambda ()
          (dk-split-all! (dk-landed* (lambda ()
            (mac-h 'ooint-membership (list 'IN xi '(OOINT a b))))))
          (ass)))
      (dk-have! (list '< 0 (list '- 'b xi))
        (lambda () (dk-ineq! (list '< xi 'b) '(IN b RR) (list 'IN xi 'RR))))
      (fact 'rr-power-pos (list '- 'b xi) 'itm_)
      (fact 'rr-mul-pos it-nn pp)
      (fact 'rr-pos-ne-zero cc_)
      (it-mul-real! '(- 1) rr_)
      (it-mul-real! dn rf)
      (dk-have! (list 'IN (list '- 0 qq) 'RR)
        (lambda () (fact 'rr-sub-in-rr 0 qq) (ass)))
      (it-mul-real! (list '* dn rf) (list '- 0 qq))
      (fact 'rr-cancel-mul-left cc_ (list '* '(- 1) rr_)
            (list '* (list '* dn rf) (list '- 0 qq)))
      (ew xi)
      (dk-conj-close!
       (lambda ()
         (if (eq? (it-head (dk-goal)) 'IN)
             (ass)
             (begin
               (dk-have! (list '= rr_ (list '* '(- 1) (list '* '(- 1) rr_)))
                 (lambda () (crs)))
               (subst (list '= rr_ (list '* '(- 1) (list '* '(- 1) rr_))))
               (subst (list '= (list '* '(- 1) rr_)
                            (list '* (list '* dn rf) (list '- 0 qq))))
               (crs))))))))
(qed 'taylor-lagrange-on-interval)
(topic! 'taylor-lagrange-on-interval 'analysis)
(alias! 'taylor-lagrange-on-interval
        "Taylor's formula with the Lagrange remainder for a function on a closed interval")
