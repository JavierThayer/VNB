;;; line-int-laws.scm -- THE LAWS OF THE INTEGRAL ALONG A ROAD, for a road and a
;;; CONTINUOUS f, with no primitive in the statement.
;;; Batch 24-A, 2026-09-23.
;;;
;;; THE SOURCE.  complex-analysis.pdf 3.1: (44) the integral of a C-valued f
;;; on [a, b] is defined componentwise, and "it follows easily that (44) is
;;; complex linear in f"; (45) |int f| <= int |f|; (47) the line integral
;;; int_gamma f(z) dz = int_a^b f(gamma(t)) gamma'(t) dt; (54) the same bound
;;; along a path; "reversing the path gamma changes the sign of the integral";
;;; Lemma 3.4 / Prop 3.1 (path additivity), here in the form "the road split
;;; at c in (a, b)".  Dieudonne IX.6 / (9.6.1) for the opposite road.
;;;
;;; THE STATE BEFORE.  Every law of CC-INT and LINE-INT in the tree
;;; (cc-int-value, cc-int-sum, cc-int-complex-mul, cc-int-adjacent,
;;; cc-int-abs-bound, line-int-opposite, ...) takes as ANTECEDENTS the
;;; existence of primitives of the two coordinates of the integrand.  Since
;;; batch 23 `line-int-exists' (regulated-algebra.scm) proves them for a ROAD
;;; and an f continuous on a set U containing the trace.  Each theorem below
;;; is stated under exactly the hypotheses of `line-int-exists'; its proof
;;; cites `line-int-exists', skolemises the two primitives, and cites the old
;;; law.
;;;
;;; THE FILE IN ORDER.
;;;   (1) line-int-value (any primitives of the two coordinates; no road
;;;       hypothesis needed).
;;;   (2) line-int-sum, line-int-scalar (c in CC): linearity in f.
;;;   (3) line-int-opposite-road.
;;;   (4) road-restrict: the restriction of a road to [c, d] is a road.
;;;   (5) cc-int-congruence: CC-INT sees only the values on [a, b].
;;;   (6) line-int-adjacent: the road split at c in (a, b).
;;;   (7) right-/left-limit-within-magnitude, regulated-on-magnitude.
;;;   (8) line-int-abs-bound: the estimate (54).
;;;
;;; Helper prefix: lil-.  Theorem binders li..._ (no predicate body uses one);
;;; the continuity clause keeps `line-int-exists''s binder rgy_ so that its
;;; citation detaches literally.

;;; ---- file-local driver helpers ---------------------------------------

(define (lil-head g) (and (pair? g) (car g)))
(define lil-nfc '(NF-METRIC-SPACE CC-NORMED-FIELD))
(define lil-cc '(CCINT a b))

;;; the leaf a lane started on: the branch is done when IT is grounded (a
;;; tactic that closes the branch moves the focus to a sibling, and a closer
;;; fired then lands on the sibling -- the focus-drift species).
(define lil-leaf #f)
(define (lil-goal-open?) (not (sequent-node-grounded? lil-leaf)))
(define (lil-lane thunk)
  (lambda () (fluid-let ((lil-leaf (proof-state-focus *ps*))) (thunk))))

(define (lil-set-setup!)
  (fact 'rr-is-set)
  (fact 'ccint-subset-rr 'a 'b)
  (fact 'subclass-of-set-is-set lil-cc 'RR))

(define (lil-and! a b)
  (dk-have! (list 'AND a b) (lambda () (dk-conj-close! (lambda () (ass))))))

;;; the road's read-offs: a, b typed, pgam and dgam typed, the trace in u
;;; pointwise (the formula lil-pgu picks).
(define (lil-road-basic!)
  (fact 'is-road-is-path 'pgam 'dgam 'a 'b)
  (fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
  (fact 'is-path-in-fun 'pgam 'a 'b)
  (dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
  (dk-split-all!)
  (lil-set-setup!))

(define (lil-road-setup!)
  (lil-road-basic!)
  (dk-have! (list 'FORALL 'lim_ (list 'IMPLIES (list 'IN 'lim_ lil-cc) '(IN (pgam lim_) u)))
    (lambda ()
      (let ((y (dk-di-var!)))
        (fact 'trace-value-in 'pgam 'a 'b y)
        (fact 'subset-mem-fwd '(TRACE pgam a b) 'u (list 'pgam y))
        (ass)))))

(define (lil-pgu)
  (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORALL) (dk-contains? fm 'lim_)
                             (dk-contains? fm '(pgam lim_))))
           "the trace lies in u"))

;;; a point y of [a, b]: gamma(y), dgamma(y), fn(gamma(y)) and the product
;;; typed, for each function symbol in FNS (each in fun(u, cc)).
(define (lil-pt! y fns)
  (fact 'fun-apply-type-c 'pgam lil-cc 'CC y)
  (fact 'fun-apply-type-c 'dgam lil-cc 'CC y)
  (if (not (dk-ctx-form (list 'IN (list 'pgam y) 'u))) (dk-apply! (lil-pgu) y))
  (for-each
   (lambda (fn)
     (let ((fy (list fn (list 'pgam y))))
       (fact 'fun-apply-type-c fn 'u 'CC (list 'pgam y))
       (lil-and! (list 'IN fy 'CC) (list 'IN (list 'dgam y) 'CC))
       (fact 'cc-mul-closed fy (list 'dgam y))))
   fns))

;;; the two primitives of line-int-exists for FN, skolemised: (w1 w2).
(define (lil-prims! fn)
  (let* ((ex (dk-fact! 'line-int-exists 'u fn 'pgam 'dgam 'a 'b))
         (w1 (dk-skolem! ex))
         (w2 (dk-skolem! (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORSOME)
                                                   (dk-contains? fm w1)))
                                  "the second primitive"))))
    (dk-split-all!)
    (list w1 w2)))

;;; beta on the goal if it holds a redex; close by ass when still open.
(define (lil-beta-close! leaf)
  (if (dk--redex? (dk-goal)) (dk-lam-b!))
  (if (not (sequent-node-grounded? leaf)) (ass)))

;;; the pointwise agreement antecedent AGREE of an instance (a FORALL over
;;; [a, b] of an ==), proved by: di, POINT!, beta, then CLOSE! on the reduced
;;; goal with the point.
(define (lil-agree! point! close!)
  (lil-lane (lambda ()
    (let ((y (dk-di-var!)))
      (point! y)
      (if (dk--redex? (dk-goal)) (dk-lam-b!))
      (if (lil-goal-open?) (close! y))))))

;;; cite NAME at TERMS; a conjunctive antecedent left standing (`fact' does not
;;; split one) is proved from context on a lane and detached.  Returns the
;;; deepest landing.
(define (lil-cite! name . terms)
  (let ((r (apply dk-fact! name terms)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES) (eq? (lil-head (cadr r)) 'AND))
        (detach-with! r (lambda () (dk-conj-close! (lambda () (ass)))))
        r)))

(define (lil-line-int-typing! fn)
  (fact 'line-int-integrand-in-fun 'a 'b 'pgam 'dgam fn 'u))

;;; =====================================================================
;;; (1) THE VALUE: the integral along gamma is G1(b) - G1(a) + (G2(b) -
;;; G2(a)) i for ANY primitives G1, G2 of the two coordinates of
;;; t |-> f(gamma(t)) gamma'(t) -- (44) with (47).  No hypothesis on gamma or
;;; f is needed beyond the two primitives; the integrand is stated
;;; beta-reduced.  From `cc-int-value' after
;;; `pw-antiderivative-integrand-congruence' (beta under the binder).
;;; =====================================================================

(sp (make-wff
  "forall([f, pgam, dgam, a, b, lig1_, lig2_],
     is-primitive(lig1_, vnb-lambda(pat_, ccint(a, b), real-part(f(pgam(pat_)) * dgam(pat_))), a, b) implies
     is-primitive(lig2_, vnb-lambda(pat_, ccint(a, b), imag-part(f(pgam(pat_)) * dgam(pat_))), a, b) implies
     line-int(f, pgam, dgam, a, b) = lig1_(b) - lig1_(a) + (lig2_(b) - lig2_(a)) * 1i)"))
(define lil-v-ls (dk-peel!))
(define lil-v-p1 (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-PRIMITIVE) (eq? (cadr fm) 'lig1_)))
                          "the first primitive"))
(define lil-v-p2 (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-PRIMITIVE) (eq? (cadr fm) 'lig2_)))
                          "the second primitive"))
(dk-split! (dk-fact! 'primitive-endpoints 'lig1_ (caddr lil-v-p1) 'a 'b))
(dk-split-all!)
(lil-set-setup!)
(fact 'primitive-integrand-in-fun 'lig1_ (caddr lil-v-p1) 'a 'b)
(fact 'primitive-integrand-in-fun 'lig2_ (caddr lil-v-p2) 'a 'b)
(mac 'LINE-INT)
(define lil-v-phi (cadr (cadr (dk-goal))))
(define lil-v-inst (dk-fact! 'cc-int-value 'a 'b lil-v-phi 'lig1_ 'lig2_))
;;; the two antecedents of the instance: is-primitive(lig_k, x |-> re/im(PHI(x)), a, b).
(define (lil-v-cong! ante red)
  (dk-have! ante
    (lambda ()
      (let ((ap (caddr ante)))
        ;; the applied-lambda integrand is a function on [a, b] into RR
        (dk-have! (list 'IN ap (list 'FUN lil-cc 'RR))
          (lambda ()
            (for-each
             (lambda (leaf)
               (if (not (sequent-node-grounded? leaf))
                   (begin
                     (dk-focus! leaf)
                     (if (not (eq? (lil-head (dk-goal)) 'FORALL))
                         (ass)
                         (let ((y (dk-di-var!)))
                           (dk-lam-b-h! (dk-fact! 'fun-apply-type-c red lil-cc 'RR y))
                           (lil-beta-close! leaf))))))
             (dk-opened (lambda () (lam-t))))))
        (let ((r (dk-fact! 'pw-antiderivative-integrand-congruence (cadr ante) red ap 'a 'b)))
          (detach-with! r (lil-agree! (lambda (y) #t) (lambda (y) (qrfl))))
          (ass))))))
(lil-v-cong! (cadr lil-v-inst) (caddr lil-v-p1))
(define lil-v-inst2 (dk-landed-1 (lambda () (detach! lil-v-inst))))
(lil-v-cong! (cadr lil-v-inst2) (caddr lil-v-p2))
(detach! lil-v-inst2)
(ass)
(qed 'line-int-value)

;;; ---- the hypotheses of `line-int-exists', verbatim ----------------------

(define lil-cont "forall([rgy_ in u], is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u),
                                        nf-metric-space(cc-normed-field), ")

(define (lil-fhyps fn) (string-append fn " in fun(u, cc) implies " lil-cont fn ", rgy_)) implies "))

(define lil-road "is-road(pgam, dgam, a, b) implies subset(trace(pgam, a, b), u) implies ")

;;; the goal of a LINE-INT equation, unfolded: the lambdas of its CC-INT terms,
;;; in order of appearance.
(define (lil-cc-int-lams g)
  (cond ((not (pair? g)) '())
        ((eq? (car g) 'CC-INT) (list (cadr g)))
        (#t (append-map lil-cc-int-lams g))))

;;; =====================================================================
;;; (2) LINEARITY IN f: "(44) is complex linear in f" with (47).  The
;;; combination h is GIVEN, with its pointwise agreement on U.  From
;;; `cc-int-sum' / `cc-int-complex-mul' with the primitives of
;;; `line-int-exists'.
;;; =====================================================================

(sp (make-wff (string-append
  "forall([u, f, g, pgam, dgam, a, b], subset(u, cc) implies "
  (lil-fhyps "f") (lil-fhyps "g") lil-road
  "forall([lih_], lih_ in fun(u, cc) implies forall([liz_ in u], lih_(liz_) == f(liz_) + g(liz_)) implies
     line-int(lih_, pgam, dgam, a, b) = line-int(f, pgam, dgam, a, b) + line-int(g, pgam, dgam, a, b)))")))
(dk-peel!)
(lil-road-setup!)
(define lil-s-f (lil-prims! 'f))
(define lil-s-g (lil-prims! 'g))
(define lil-s-agree (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORALL) (dk-contains? fm 'lih_)))
                             "the agreement of h"))
(lil-line-int-typing! 'f)
(lil-line-int-typing! 'g)
(lil-line-int-typing! 'lih_)
(mac 'LINE-INT)
(define lil-s-lams (lil-cc-int-lams (dk-goal)))
(define lil-s-inst (dk-fact! 'cc-int-sum 'a 'b (cadr lil-s-lams) (caddr lil-s-lams) (car lil-s-lams)))
(define lil-s-rest
  (detach-with! lil-s-inst
    (lil-agree! (lambda (y) (lil-pt! y '(f g lih_)))
      (lambda (y)
        (let* ((py (list 'pgam y)) (dy (list 'dgam y))
               (fy (list 'f py)) (gy (list 'g py)))
          (dk-apply! lil-s-agree py)
          (subst (list '= (list 'lih_ py) (list '+ fy gy)))
          (lil-cite! 'cc-add-closed fy gy)
          (lil-cite! 'cc-mul-comm (list '+ fy gy) dy)
          (subst (list '= (list '* (list '+ fy gy) dy) (list '* dy (list '+ fy gy))))
          (lil-cite! 'cc-distributive dy fy gy)
          (subst (list '= (list '* dy (list '+ fy gy)) (list '+ (list '* dy fy) (list '* dy gy))))
          (lil-cite! 'cc-mul-comm dy fy)
          (lil-cite! 'cc-mul-comm dy gy)
          (subst (list '= (list '* dy fy) (list '* fy dy)))
          (subst (list '= (list '* dy gy) (list '* gy dy)))
          (if (lil-goal-open?) (qrfl)))))))
(dk-apply! lil-s-rest (car lil-s-f) (cadr lil-s-f) (car lil-s-g) (cadr lil-s-g))
(ass)
(qed 'line-int-sum)

(sp (make-wff (string-append
  "forall([u, f, pgam, dgam, a, b], subset(u, cc) implies "
  (lil-fhyps "f") lil-road
  "forall([lic_ in cc, lih_], lih_ in fun(u, cc) implies forall([liz_ in u], lih_(liz_) == lic_ * f(liz_)) implies
     line-int(lih_, pgam, dgam, a, b) = lic_ * line-int(f, pgam, dgam, a, b)))")))
(dk-peel!)
(lil-road-setup!)
(define lil-c-f (lil-prims! 'f))
(define lil-c-agree (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORALL) (dk-contains? fm 'lih_)))
                             "the agreement of h"))
(lil-line-int-typing! 'f)
(lil-line-int-typing! 'lih_)
(mac 'LINE-INT)
(define lil-c-lams (lil-cc-int-lams (dk-goal)))
(define lil-c-inst (dk-fact! 'cc-int-complex-mul 'a 'b (cadr lil-c-lams) (car lil-c-lams) 'lic_))
(define lil-c-rest
  (detach-with! lil-c-inst
    (lil-agree! (lambda (y) (lil-pt! y '(f lih_)))
      (lambda (y)
        (let* ((py (list 'pgam y)) (dy (list 'dgam y)) (fy (list 'f py)))
          (dk-apply! lil-c-agree py)
          (subst (list '= (list 'lih_ py) (list '* 'lic_ fy)))
          (lil-cite! 'cc-mul-assoc 'lic_ fy dy)
          (subst (list '= (list '* (list '* 'lic_ fy) dy) (list '* 'lic_ (list '* fy dy))))
          (if (lil-goal-open?) (qrfl)))))))
(dk-apply! lil-c-rest (car lil-c-f) (cadr lil-c-f))
(ass)
(qed 'line-int-scalar)

;;; =====================================================================
;;; (3) THE OPPOSITE ROAD: "reversing the path gamma changes the sign of the
;;; integral" (Dieudonne (9.6.1)); `line-int-opposite' with the primitives
;;; of `line-int-exists'.  The opposite road and its derivative are GIVEN by
;;; their pointwise agreement on [a, b] (`opposite-is-road' shows they form a
;;; road).
;;; =====================================================================

(sp (make-wff (string-append
  "forall([u, f, pgam, dgam, a, b], subset(u, cc) implies "
  (lil-fhyps "f") lil-road
  "forall([lirg_, lird_], lirg_ in fun(ccint(a, b), cc) implies lird_ in fun(ccint(a, b), cc) implies
     forall([pay_ in ccint(a, b)], lirg_(pay_) == pgam(a + b - pay_)) implies
     forall([pay_ in ccint(a, b)], lird_(pay_) == -1 * dgam(a + b - pay_)) implies
     line-int(f, lirg_, lird_, a, b) = -1 * line-int(f, pgam, dgam, a, b)))")))
(dk-peel!)
(lil-road-setup!)
(define lil-o-f (lil-prims! 'f))
(define lil-o-r1 (dk-fact! 'line-int-opposite 'a 'b 'pgam 'dgam 'f 'u))
(define lil-o-r2 (dk-apply! lil-o-r1 'lirg_ 'lird_))
(dk-apply! lil-o-r2 (car lil-o-f) (cadr lil-o-f))
(ass)
(qed 'line-int-opposite-road)

;;; =====================================================================
;;; (4) THE RESTRICTION OF A ROAD TO A SUBINTERVAL [c, d] of [a, b] IS A
;;; ROAD.  Coordinatewise: `pw-antiderivative-restrict' for the two
;;; primitives (moved from restrict(G, [c, d]) to the lambdas of IS-ROAD by
;;; `pw-antiderivative-real-mul' at the scalar 1, which serves as the
;;; congruence of primitives), `regulated-on-restrict' for the two regulated
;;; derivatives, `primitive-continuous' + `is-path-of-coords' for the path.
;;; =====================================================================

;;; run the implication chain R to its end: an antecedent in context is
;;; detached, any other is proved on a lane by (PROVE! ante), a thunk maker.
(define (lil-chain! r prove!)
  (let loop ((r r))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (if (dk-ctx-form (cadr r))
            (loop (dk-landed-1 (lambda () (detach! r))))
            (loop (detach-with! r (lil-lane (prove! (cadr r))))))
        r)))

(define lil-e '(CCINT licv_ lidv_))
(define lil-rg (list 'RESTRICT 'pgam lil-e))
(define lil-rd (list 'RESTRICT 'dgam lil-e))

;;; a point y of [c, d]: y in [a, b], gamma(y), dgamma(y) and their
;;; restrictions typed, their coordinates typed, the restrict read-offs landed.
(define (lil-rpt! y)
  (fact 'subset-mem-fwd lil-e lil-cc y)
  (fact 'fun-apply-type-c 'pgam lil-cc 'CC y)
  (fact 'fun-apply-type-c 'dgam lil-cc 'CC y)
  (fact 'fun-apply-type-c lil-rg lil-e 'CC y)
  (fact 'fun-apply-type-c lil-rd lil-e 'CC y)
  (for-each (lambda (proj)
              (for-each (lambda (fn) (fact (if (eq? proj 'real-part) 'real-part-in-rr 'imag-part-in-rr)
                                           (list fn y)))
                        '(pgam dgam)))
            '(real-part imag-part))
  (fact 'restrict-apply 'pgam lil-e y)
  (fact 'restrict-apply 'dgam lil-e y))


;;; typing of a lambda over SET into RR, the pointwise leaf by POINT! then
;;; beta then REST! (a thunk run while the leaf is open).
(define (lil-lam-type! claim point! rest!)
  (dk-have! claim
    (lambda ()
      (for-each
       (lambda (leaf)
         (if (not (sequent-node-grounded? leaf))
             (begin
               (dk-focus! leaf)
               (if (not (eq? (lil-head (dk-goal)) 'FORALL))
                   (ass)
                   (fluid-let ((lil-leaf leaf))
                     (let ((y (dk-di-var!)))
                       (point! y)
                       (if (dk--redex? (dk-goal)) (dk-lam-b!))
                       (if (lil-goal-open?) (rest! y))))))))
       (dk-opened (lambda () (lam-t)))))))

(define (lil-restrict-coord! proj)
  (let* ((ant (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-PRIMITIVE)
                                         (dk-contains? fm (list proj '(pgam pat_)))
                                         (not (dk-contains? fm 'RESTRICT))))
                       "the road's primitive"))
         (g  (list-ref ant 1))
         (dd (list-ref ant 2))
         (bg (list 'VNB-LAMBDA 'liv_ lil-e (list proj (list lil-rg 'liv_))))
         (bd (list 'VNB-LAMBDA 'liv_ lil-e (list proj (list lil-rd 'liv_))))
         (rw (lambda (y fn)          ; rewrite RESTRICT(fn, E)(y) to fn(y)
               (subst (list '= (list (list 'RESTRICT fn lil-e) y) (list fn y))))))
    (for-each
     (lambda (lam fn)
       (lil-lam-type! (list 'IN lam (list 'FUN lil-e 'RR)) lil-rpt!
         (lambda (y) (rw y fn) (if (lil-goal-open?) (ass)))))
     (list bg bd) '(pgam dgam))
    ;; the primitive
    (fact 'pw-antiderivative-restrict 'a 'b 'licv_ 'lidv_ g dd)
    (let* ((r2 (dk-fact! 'pw-antiderivative-real-mul 'licv_ 'lidv_
                         (list 'RESTRICT g lil-e) (list 'RESTRICT dd lil-e) 1))
           (r3 (inst*! r2 bg bd))
           (res (lil-chain! r3
                  (lambda (ante)
                    (lambda ()
                      (let* ((y (dk-di-var!))
                             (big (if (dk-contains? ante bg) g dd))
                             (fn (if (dk-contains? ante bg) 'pgam 'dgam))
                             (x (list proj (list fn y))))
                        (lil-rpt! y)
                        (fact 'restrict-apply big lil-e y)
                        (subst (list '= (list (list 'RESTRICT big lil-e) y) (list big y)))
                        (dk-lam-b!)
                        (if (lil-goal-open?) (rw y fn))
                        (if (lil-goal-open?)
                            (begin
                              (have! (list '= (list '* 1 x) x) (lambda () (crs)))
                              (subst (list '= (list '* 1 x) x))))
                        (if (lil-goal-open?) (qrfl))))))))
      (dk-split-all! (list res)))
    ;; the regulated derivative
    (lil-chain! (dk-fact! 'regulated-on-restrict dd 'a 'b 'licv_ 'lidv_ bd)
      (lambda (ante)
        (lambda ()
          (let ((y (dk-di-var!)))
            (lil-rpt! y)
            (dk-lam-b!)
            (if (lil-goal-open?) (rw y 'dgam))
            (if (lil-goal-open?) (rfl))))))
    (fact 'primitive-continuous bg bd 'licv_ 'lidv_)
    bg))

(sp (make-wff
  "forall([pgam, dgam, a, b, licv_ in rr, lidv_ in rr], is-road(pgam, dgam, a, b) implies
     a <= licv_ implies licv_ < lidv_ implies lidv_ <= b implies
     is-road(restrict(pgam, ccint(licv_, lidv_)), restrict(dgam, ccint(licv_, lidv_)), licv_, lidv_))"))
(dk-peel!)
(lil-road-basic!)
(fact 'ccint-subset-ccint 'a 'b 'licv_ 'lidv_)
(fact 'ccint-subset-rr 'licv_ 'lidv_)
(fact 'subclass-of-set-is-set lil-e 'RR)
(fact 'restrict-in-fun 'pgam lil-cc 'CC lil-e)
(fact 'restrict-in-fun 'dgam lil-cc 'CC lil-e)
(fact 'rr-one-in)
(fact 'is-road-re-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-im-antiderivative 'pgam 'dgam 'a 'b)
(fact 'is-road-re-regulated 'pgam 'dgam 'a 'b)
(fact 'is-road-im-regulated 'pgam 'dgam 'a 'b)
(define lil-r-bgr (lil-restrict-coord! 'real-part))
(define lil-r-bgi (lil-restrict-coord! 'imag-part))
(lil-chain! (dk-fact! 'is-path-of-coords 'licv_ 'lidv_ lil-rg lil-r-bgr lil-r-bgi)
  (lambda (ante)
    (lambda ()
      (let ((y (dk-di-var!)))
        (lil-rpt! y)
        (fact 'real-part-in-rr (list lil-rg y))
        (fact 'imag-part-in-rr (list lil-rg y))
        (dk-lam-b!)
        (if (lil-goal-open?) (rfl))))))
(mac 'IS-ROAD)
(dk-conj-close! (lambda () (ass)))
(qed 'road-restrict)

;;; =====================================================================
;;; (5) CC-INT DEPENDS ONLY ON THE VALUES ON [a, b]: pphi_ with primitives
;;; of its coordinates and ppsi_ agreeing with it pointwise on [a, b] have
;;; the same integral.  From `pw-antiderivative-integrand-congruence' (the
;;; primitives serve ppsi_) and `cc-int-value' twice.
;;; =====================================================================

(sp (make-wff
  "forall([pphi_, ppsi_, a, b, lig1_, lig2_],
     is-primitive(lig1_, vnb-lambda(pat_, ccint(a, b), real-part(pphi_(pat_))), a, b) implies
     is-primitive(lig2_, vnb-lambda(pat_, ccint(a, b), imag-part(pphi_(pat_))), a, b) implies
     ppsi_ in fun(ccint(a, b), cc) implies
     forall([liy_ in ccint(a, b)], pphi_(liy_) == ppsi_(liy_)) implies
     cc-int(pphi_, a, b) = cc-int(ppsi_, a, b))"))
(dk-peel!)
(define lil-g-agree (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORALL) (dk-contains? fm 'ppsi_)))
                             "the agreement"))
(define (lil-g-prim w)
  (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-PRIMITIVE) (eq? (cadr fm) w)))
           "a primitive"))
(dk-split! (dk-fact! 'primitive-endpoints 'lig1_ (caddr (lil-g-prim 'lig1_)) 'a 'b))
(dk-split-all!)
(lil-set-setup!)
(for-each
 (lambda (proj inr w)
   (let* ((rp (caddr (lil-g-prim w)))
          (rs (list 'VNB-LAMBDA 'pat_ lil-cc (list proj '(ppsi_ pat_)))))
     (lil-lam-type! (list 'IN rs (list 'FUN lil-cc 'RR))
       (lambda (y) (fact 'fun-apply-type-c 'ppsi_ lil-cc 'CC y) (fact inr (list 'ppsi_ y)))
       (lambda (y) (ass)))
     (lil-chain! (dk-fact! 'pw-antiderivative-integrand-congruence w rp rs 'a 'b)
       (lambda (ante)
         (lambda ()
           (let ((y (dk-di-var!)))
             (fact 'fun-apply-type-c 'ppsi_ lil-cc 'CC y)
             (dk-apply! lil-g-agree y)
             (dk-lam-b!)
             (if (lil-goal-open?) (subst (list '= (list 'pphi_ y) (list 'ppsi_ y))))
             (if (lil-goal-open?) (qrfl))))))))
 '(real-part imag-part) '(real-part-in-rr imag-part-in-rr) '(lig1_ lig2_))
(define lil-g-e1 (dk-fact! 'cc-int-value 'a 'b 'pphi_ 'lig1_ 'lig2_))
(define lil-g-e2 (lil-chain! (dk-fact! 'cc-int-value 'a 'b 'ppsi_ 'lig1_ 'lig2_)
                   (lambda (ante) (error "cc-int-congruence: antecedent not in context" ante))))
(define lil-g-leaf (proof-state-focus *ps*))
(subst lil-g-e1)
(subst lil-g-e2)
(if (not (sequent-node-grounded? lil-g-leaf)) (rfl))
(qed 'cc-int-congruence)

;;; =====================================================================
;;; (6) THE ROAD SPLIT AT c IN (a, b): the integral along gamma is the sum
;;; of the integrals along its restrictions to [a, c] and [c, b] (each a
;;; road by (4)) -- path additivity, Prop 3.1 / Lemma 3.4 of the notes, in
;;; the split form.  From `cc-int-adjacent' with the primitives of
;;; `line-int-exists', and (5) on each piece.
;;; =====================================================================

(sp (make-wff (string-append
  "forall([u, f, pgam, dgam, a, b], subset(u, cc) implies "
  (lil-fhyps "f") lil-road
  "forall([licv_ in ooint(a, b)],
     line-int(f, pgam, dgam, a, b) =
       line-int(f, restrict(pgam, ccint(a, licv_)), restrict(dgam, ccint(a, licv_)), a, licv_) +
       line-int(f, restrict(pgam, ccint(licv_, b)), restrict(dgam, ccint(licv_, b)), licv_, b)))")))
(dk-peel!)
(lil-road-setup!)
(define lil-a-w (lil-prims! 'f))
(lil-line-int-typing! 'f)
(mac 'LINE-INT)
(define lil-a-lams (lil-cc-int-lams (dk-goal)))
(define lil-a-phi (car lil-a-lams))
(define lil-a-e (dk-fact! 'cc-int-adjacent 'a 'b 'licv_ lil-a-phi (car lil-a-w) (cadr lil-a-w)))
(fact 'ooint-elt-in-rr 'a 'b 'licv_)
(dk-have! '(AND (< a licv_) (< licv_ b))
  (lambda ()
    (dk-split-all! (dk-landed* (lambda () (mac-h 'ooint-membership '(IN licv_ (OOINT a b))))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all!)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'rr-lt-implies-le 'a 'licv_)
(fact 'rr-lt-implies-le 'licv_ 'b)

;;; a point y of the piece EK: y in [a, b], and everything evaluated there typed.
(define (lil-ept! y ek)
  (fact 'subset-mem-fwd ek lil-cc y)
  (lil-pt! y '(f))
  (fact 'real-part-in-rr (list '* (list 'f (list 'pgam y)) (list 'dgam y)))
  (fact 'imag-part-in-rr (list '* (list 'f (list 'pgam y)) (list 'dgam y))))

(define (lil-rw-restrict! fn ek y)
  (fact 'restrict-apply fn ek y)
  (subst (list '= (list (list 'RESTRICT fn ek) y) (list fn y))))

(define (lil-beta-if!) (if (and (lil-goal-open?) (dk--redex? (dk-goal))) (dk-lam-b!)))

;;; the piece [LO, HI] with its integrand PHIK: returns the landed equation
;;; cc-int(restrict(PHI, EK), LO, HI) = cc-int(PHIK, LO, HI).
(define (lil-piece! lo hi phik)
  (let* ((ek (list 'CCINT lo hi))
         (rpk (list 'RESTRICT lil-a-phi ek)))
    (fact 'ccint-subset-ccint 'a 'b lo hi)
    (fact 'ccint-subset-rr lo hi)
    (fact 'subclass-of-set-is-set ek 'RR)
    ;; the primitives of the two coordinates of restrict(PHI, EK)
    (let ((ws
           (map
            (lambda (proj w)
              (let* ((ap (caddr (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-PRIMITIVE)
                                                             (eq? (cadr fm) w)))
                                         "a primitive of the road integrand")))
                     (tg (list 'VNB-LAMBDA 'pat_ ek (list proj (list rpk 'pat_)))))
                (fact 'pw-antiderivative-restrict 'a 'b lo hi w ap)
                (lil-lam-type! (list 'IN tg (list 'FUN ek 'RR))
                  (lambda (y) (lil-ept! y ek))
                  (lambda (y)
                    (lil-rw-restrict! lil-a-phi ek y)
                    (lil-beta-if!)
                    (if (lil-goal-open?) (ass))))
                (lil-chain! (dk-fact! 'pw-antiderivative-integrand-congruence
                                      (list 'RESTRICT w ek) (list 'RESTRICT ap ek) tg lo hi)
                  (lambda (ante)
                    (lambda ()
                      (let ((y (dk-di-var!)))
                        (lil-ept! y ek)
                        (lil-rw-restrict! ap ek y)
                        (lil-beta-if!)
                        (if (lil-goal-open?) (lil-rw-restrict! lil-a-phi ek y))
                        (lil-beta-if!)
                        (if (lil-goal-open?) (qrfl))))))
                (list 'RESTRICT w ek)))
            '(real-part imag-part) lil-a-w)))
      ;; PHIK is a function on EK into CC
      (dk-have! (list 'IN phik (list 'FUN ek 'CC))
        (lambda ()
          (for-each
           (lambda (leaf)
             (if (not (sequent-node-grounded? leaf))
                 (begin
                   (dk-focus! leaf)
                   (if (not (eq? (lil-head (dk-goal)) 'FORALL))
                       (ass)
                       (fluid-let ((lil-leaf leaf))
                        (let ((y (dk-di-var!)))
                         (lil-ept! y ek)
                         (lil-beta-if!)
                         (if (lil-goal-open?) (lil-rw-restrict! 'pgam ek y))
                         (if (lil-goal-open?) (lil-rw-restrict! 'dgam ek y))
                         (if (lil-goal-open?) (ass))))))))
           (dk-opened (lambda () (lam-t))))))
      (lil-chain! (dk-fact! 'cc-int-congruence rpk phik lo hi (car ws) (cadr ws))
        (lambda (ante)
          (lambda ()
            (let ((y (dk-di-var!)))
              (lil-ept! y ek)
              (lil-rw-restrict! lil-a-phi ek y)
              (lil-beta-if!)
              (if (lil-goal-open?) (lil-rw-restrict! 'pgam ek y))
              (if (lil-goal-open?) (lil-rw-restrict! 'dgam ek y))
              (if (lil-goal-open?) (qrfl)))))))))

(define lil-a-q1 (lil-piece! 'a 'licv_ (cadr lil-a-lams)))
(define lil-a-q2 (lil-piece! 'licv_ 'b (caddr lil-a-lams)))
(subst (list '= (caddr lil-a-q1) (cadr lil-a-q1)))
(subst (list '= (caddr lil-a-q2) (cadr lil-a-q2)))
(ass)
(qed 'line-int-adjacent)

;;; =====================================================================
;;; (7) THE MODULUS OF A REGULATED C-VALUED FUNCTION IS REGULATED.  For
;;; real f, g with one-sided limits l, m within a set, |f + g i| has the
;;; one-sided limit |l + m i|: with P = f(t) + g(t) i and L = l + m i,
;;;   | |P| - |L| | <= |P - L| <= |Re(P - L)| + |Im(P - L)|
;;;                 =  |f(t) - l| + |g(t) - m|
;;; (`cc-magnitude-le-add' both ways, `cc-magnitude-sub-sym',
;;; `cc-magnitude-le-re-im', `cc-re-sub' / `cc-im-sub', `cc-re-im-of').
;;; Needed for (8): the tree's estimate `cc-int-abs-bound' takes a primitive
;;; of |phi| as an antecedent, and (8.7.2) supplies it once |phi| is regulated.
;;; The window machinery is regulated-algebra.scm's (rga-delta!, rga-min!,
;;; rga-window!), copied: it is file-local there.
;;; =====================================================================

(define (lil-abs-lt! y c prems)
  (dk-have! (list '< (list '- c) y) (lambda () (apply dk-ineq! prems)))
  (dk-have! (list '< y c) (lambda () (apply dk-ineq! prems)))
  (fact 'rr-abs-lt-of-parts y c)
  (ass))

(define (lil-delta! cl e)
  (let* ((d (dk-skolem! (dk-apply! cl e)))
         (c (dk-pick (lambda (g) (and (eq? (lil-head g) 'FORALL) (dk-contains? g d)))
                     "a delta clause")))
    (fact 'rr-pos-rr-in-rr d)
    (fact 'rr-lt-of-pos-rr d)
    (cons d c)))

(define (lil-min2! d1 d2)
  (let ((w (dk-skolem! (dk-fact! 'rr-min-pos d1 d2))))
    (dk-split-all!)
    w))

(define (lil-window right? x t r)
  (if right?
      (list (list '< x t) (list '< t (list '+ x r)))
      (list (list '< (list '- x r) t) (list '< t x))))

(define (lil-open-lim! pred fa la)
  (let ((ps (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred fa 'liw_ 'lix_ la)))))))
    (car (filter (dk-head? 'FORALL) ps))))

(define lil-l '(+ lil_ (* lik_ +i)))

;;; the facts about a point P = A + B i with A, B real: P in cc, Re P = A,
;;; Im P = B.
(define (lil-cc-point! a b)
  (let ((p (list '+ a (list '* b '+i))))
    (fact 'rr-subset-cc a)
    (fact 'rr-subset-cc b)
    (fact 'cc-i-in)
    (lil-cite! 'cc-mul-closed b '+i)
    (lil-cite! 'cc-add-closed a (list '* b '+i))
    (have! (list '= p p) (lambda () (rfl)))
    (dk-split-all! (list (dk-fact! 'cc-re-im-of p a b)))
    p))

(define (lil-mag-lim! right?)
  (dk-peel!)
  (let* ((pred (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN))
         (agree (dk-pick (lambda (g) (and (eq? (lil-head g) 'FORALL) (dk-contains? g 'lih_)))
                         "the pointwise agreement"))
         (cf (lil-open-lim! pred 'f 'lil_))
         (cg (lil-open-lim! pred 'g 'lik_))
         (l (lil-cc-point! 'lil_ 'lik_))
         (ml (list 'magnitude l)))
    (fact 'cc-magnitude-closed l)
    (mac pred)
    (dk-conj-close!
     (lambda ()
       (if (not (eq? (lil-head (dk-goal)) 'FORALL))
           (ass)
           (let* ((pe (dk-peel!))
                  (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
                  (h  (dk-halve! e))
                  (dc1 (lil-delta! cf h))
                  (dc2 (lil-delta! cg h))
                  (w  (lil-min2! (car dc1) (car dc2))))
             (fact 'rr-pos-rr-in-rr e)
             (fact 'rr-pos-rr-of-lt w)
             (ew w)
             (dk-conj-close!
              (lambda ()
                (if (eq? (lil-head (dk-goal)) 'POS-RR)
                    (ass)
                    (let* ((ls (dk-peel!))
                           (t (cadr (car (filter (lambda (g) (and (eq? (lil-head g) 'IN)
                                                                  (eq? (caddr g) 'liw_)))
                                                 ls))))
                           (base (append (list '(IN lix_ RR) (list 'IN t 'RR)
                                               (list 'IN (car dc1) 'RR) (list 'IN (car dc2) 'RR)
                                               (list 'IN w 'RR) (list '< 0 w)
                                               (list '<= w (car dc1)) (list '<= w (car dc2)))
                                         (lil-window right? 'lix_ t w))))
                      (fact 'subset-mem-fwd 'liw_ 'RR t)
                      (for-each
                       (lambda (dc)
                         (for-each (lambda (g) (if (not (dk-ctx-form g))
                                                   (dk-have! g (lambda () (apply dk-ineq! base)))))
                                   (lil-window right? 'lix_ t (car dc)))
                         (dk-apply! (cdr dc) t))
                       (list dc1 dc2))
                      (let* ((ft (list 'f t)) (gt (list 'g t))
                             (p (begin (fact 'fun-apply-type-c 'f 'liw_ 'RR t)
                                       (fact 'fun-apply-type-c 'g 'liw_ 'RR t)
                                       (lil-cc-point! ft gt)))
                             (pl (list '- p l))
                             (mp (list 'magnitude p))
                             (mpl (list 'magnitude pl))
                             (a1 (list 'abs (list 'real-part pl)))
                             (a2 (list 'abs (list 'imag-part pl))))
                        (lil-cite! 'cc-sub-in-cc p l)
                        (fact 'cc-magnitude-closed p)
                        (fact 'cc-magnitude-closed pl)
                        (fact 'real-part-in-rr pl)
                        (fact 'imag-part-in-rr pl)
                        (fact 'rr-abs-closed (list 'real-part pl))
                        (fact 'rr-abs-closed (list 'imag-part pl))
                        (lil-cite! 'cc-re-sub p l)
                        (lil-cite! 'cc-im-sub p l)
                        (fact 'cc-magnitude-le-re-im pl)
                        (fact 'cc-magnitude-le-add p l)
                        (fact 'cc-magnitude-le-add l p)
                        (fact 'cc-magnitude-sub-sym p l)
                        (dk-have! (list '<= ml (list '+ mpl mp))
                          (lil-lane (lambda ()
                            (subst (list '= mpl (list 'magnitude (list '- l p))))
                            (if (lil-goal-open?) (ass)))))
                        (for-each
                         (lambda (proj a fv lv)
                           (dk-have! (list '< a h)
                             (lil-lane (lambda ()
                               (subst (list '= (list proj pl) (list '- (list proj p) (list proj l))))
                               (subst (list '= (list proj p) fv))
                               (subst (list '= (list proj l) lv))
                               (if (lil-goal-open?) (ass))))))
                         '(real-part imag-part) (list a1 a2) (list ft gt) '(lil_ lik_))
                        (dk-apply! agree t)
                        (subst (list '= (list 'lih_ t) mp))
                        (fact 'rr-sub-in-rr mp ml)
                        (lil-abs-lt! (list '- mp ml) e
                          (list (list 'IN mp 'RR) (list 'IN ml 'RR) (list 'IN mpl 'RR)
                                (list 'IN a1 'RR) (list 'IN a2 'RR)
                                (list 'IN e 'RR) (list 'IN h 'RR)
                                (list '<= mp (list '+ mpl ml)) (list '<= ml (list '+ mpl mp))
                                (list '<= mpl (list '+ a1 a2))
                                (list '< a1 h) (list '< a2 h) (list '= (list '+ h h) e))))))))))))))

(define (lil-mag-lim-stmt right?)
  (let ((p (if right? "is-right-limit-within" "is-left-limit-within")))
    (string-append
     "forall([f, g, lih_, liw_, lix_, lil_, lik_], "
     p "(f, liw_, lix_, lil_) implies " p "(g, liw_, lix_, lik_) implies lih_ in fun(liw_, rr) implies
      forall([liz_ in liw_], lih_(liz_) == magnitude(f(liz_) + g(liz_) * 1i)) implies "
     p "(lih_, liw_, lix_, magnitude(lil_ + lik_ * 1i)))")))

(sp (make-wff (lil-mag-lim-stmt #t)))
(lil-mag-lim! #t)
(qed 'right-limit-within-magnitude)

(sp (make-wff (lil-mag-lim-stmt #f)))
(lil-mag-lim! #f)
(qed 'left-limit-within-magnitude)

(define (lil-open-reg! fn)
  (let ((ps (dk-split-all! (dk-landed* (lambda ()
              (mac-h 'IS-REGULATED-ON (list 'IS-REGULATED-ON fn 'a 'b)))))))
    (cons (car (filter (lambda (g) (and (eq? (lil-head g) 'FORALL)
                                        (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN)))
                       ps))
          (car (filter (lambda (g) (and (eq? (lil-head g) 'FORALL)
                                        (dk-contains? g 'IS-LEFT-LIMIT-WITHIN)))
                       ps)))))

(sp (make-wff
  "forall([f, g, lih_, a, b], is-regulated-on(f, a, b) implies is-regulated-on(g, a, b) implies
     lih_ in fun(ccint(a, b), rr) implies
     forall([liz_ in ccint(a, b)], lih_(liz_) == magnitude(f(liz_) + g(liz_) * 1i)) implies
     is-regulated-on(lih_, a, b))"))
(dk-peel!)
(define lil-m-rf (lil-open-reg! 'f))
(define lil-m-rg (lil-open-reg! 'g))
(mac 'IS-REGULATED-ON)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (lil-head gl) 'FORALL)
         (let* ((right? (dk-contains? gl 'IS-RIGHT-LIMIT-WITHIN))
                (sel (if right? car cdr))
                (x (dk-di-var!)))
           (dk-peel!)
           (let* ((l (dk-skolem! (dk-apply! (sel lil-m-rf) x)))
                  (m (dk-skolem! (dk-apply! (sel lil-m-rg) x))))
             (ew (list 'magnitude (list '+ l (list '* m '+i))))
             (fact (if right? 'right-limit-within-magnitude 'left-limit-within-magnitude)
                   'f 'g 'lih_ '(CCINT a b) x l m)
             (ass)))
         (ass)))))
(qed 'regulated-on-magnitude)

;;; =====================================================================
;;; (8) THE ESTIMATE (54) of the notes:
;;;     | int_gamma f(z) dz | <= int_a^b |f(gamma(t))| |gamma'(t)| dt,
;;; the integrand on the right GIVEN as a function on [a, b] with its
;;; pointwise value (the notes' (45) applied to (47)).  The notes' length
;;; form (53) is not available: the tree defines no length of a road.  From
;;; `cc-int-abs-bound' with the primitives of `line-int-exists' and a
;;; primitive of |f(gamma) gamma'| from (8.7.2), which applies because that
;;; function is regulated by (7) and `road-integrand-regulated'.
;;; =====================================================================

;;; y a point of [a, b]: close  X == magnitude(f(gamma(y)) dgamma(y))  where
;;; the goal's left side is liab_(y), by the agreement AG and |zw| = |z||w|.
(define (lil-mag-close! ag y)
  (let* ((fy (list 'f (list 'pgam y))) (dy (list 'dgam y)) (q (list '* fy dy)))
    (dk-apply! ag y)
    (subst (list '= (list 'liab_ y) (list '* (list 'magnitude fy) (list 'magnitude dy))))
    (lil-cite! 'cc-magnitude-mul fy dy)
    (if (lil-goal-open?)
        (subst (list '= (list 'magnitude q) (list '* (list 'magnitude fy) (list 'magnitude dy)))))
    (if (lil-goal-open?) (qrfl))))

(sp (make-wff (string-append
  "forall([u, f, pgam, dgam, a, b], subset(u, cc) implies "
  (lil-fhyps "f") lil-road
  "forall([liab_], liab_ in fun(ccint(a, b), rr) implies
     forall([liy_ in ccint(a, b)], liab_(liy_) == magnitude(f(pgam(liy_))) * magnitude(dgam(liy_))) implies
     magnitude(line-int(f, pgam, dgam, a, b)) <= pw-int(liab_, a, b)))")))
(dk-peel!)
(lil-road-setup!)
(define lil-b-w (lil-prims! 'f))
(define lil-b-ag (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'FORALL) (dk-contains? fm 'liab_)))
                          "the value of the bound"))
(lil-line-int-typing! 'f)
(dk-split-all! (list (dk-fact! 'road-integrand-regulated 'u 'f 'pgam 'dgam 'a 'b)))
(define (lil-b-reg proj)
  (cadr (dk-pick (lambda (fm) (and (eq? (lil-head fm) 'IS-REGULATED-ON)
                                   (dk-contains? fm (list proj '(* (f (pgam pat_)) (dgam pat_))))))
                 "a regulated coordinate of the integrand")))
(lil-chain! (dk-fact! 'regulated-on-magnitude (lil-b-reg 'real-part) (lil-b-reg 'imag-part) 'liab_ 'a 'b)
  (lambda (ante)
    (lambda ()
      (let* ((y (dk-di-var!))
             (q (list '* (list 'f (list 'pgam y)) (list 'dgam y)))
             (rq (list 'real-part q)) (iq (list 'imag-part q)))
        (lil-pt! y '(f))
        (fact 'real-part-in-rr q)
        (fact 'imag-part-in-rr q)
        (dk-lam-b!)
        (fact 'cc-re-im-decompose q)
        (fact 'rr-subset-cc iq)
        (fact 'cc-i-in)
        (lil-cite! 'cc-mul-comm iq '+i)
        (subst (list '= (list '* iq '+i) (list '* '+i iq)))
        (subst (list '= (list '+ rq (list '* '+i iq)) q))
        (lil-mag-close! lil-b-ag y)))))
(define lil-b-pb (dk-skolem! (dk-fact! 'regulated-on-has-primitive 'a 'b 'liab_)))
(mac 'LINE-INT)
(define lil-b-phi (car (lil-cc-int-lams (dk-goal))))
(lil-chain! (dk-fact! 'cc-int-abs-bound lil-b-phi (car lil-b-w) (cadr lil-b-w) 'liab_ lil-b-pb 'a 'b)
  (lambda (ante)
    (lambda ()
      (let ((y (dk-di-var!)))
        (lil-pt! y '(f))
        (dk-lam-b!)
        (lil-mag-close! lil-b-ag y)))))
(ass)
(qed 'line-int-abs-bound)
