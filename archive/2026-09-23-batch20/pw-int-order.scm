;;; pw-int-order.scm -- ORDER PROPERTIES OF THE PIECEWISE INTEGRAL.
;;;
;;; (1) THE GENERAL BRICK.  `nondecreasing-off-finite-set': a function on the
;;;     line whose derivative is >= 0 at every interior point OUTSIDE A FINITE
;;;     SET is nondecreasing across the interval.  This is the monotone twin of
;;;     `pw-zero-deriv-off-finite-set' (theorem-library/pw-antiderivative-laws,
;;;     batch 16-A) and is proved the same way: `finite-set-induction' over the
;;;     class of exceptional sets, with the function and the two endpoints
;;;     QUANTIFIED INSIDE the class, so that the step can use the induction
;;;     hypothesis on (u, x) and on (x, v) for the same function.  The base case
;;;     is the mean value theorem in its lower-bound form (`mvt-lower-bound' at
;;;     m = 0); the step glues the two halves with `rr-leq-transitive' where the
;;;     16-A proof glued them with `eq-trans'.
;;;
;;; (2) THE SAME FOR A FUNCTION ON ITS INTERVAL (`pw-nondecreasing-on-interval'),
;;;     through EXTEND-CONST, exactly as `deriv-zero-constant-on-interval' does
;;;     it: the extension is continuous on the line, its derivative inside the
;;;     interval is the function's own (`extend-const-deriv-fwd'), and the two
;;;     endpoint values are unchanged (`extend-const-fixes').
;;;
;;; (3) `pw-int-nonneg': a PW-antiderivative of a NONNEGATIVE integrand has
;;;     PW-INT >= 0 -- (2) applied to the antiderivative, then `pw-int-value'.
;;;
;;; (4) `pw-int-monotone': phi <= psi pointwise on [a,b], both with
;;;     PW-antiderivatives, gives PW-INT(phi) <= PW-INT(psi).  The difference is
;;;     assembled with 16-A's `pw-antiderivative-sum' and 17-A's
;;;     `pw-antiderivative-real-mul' (at the scalar -1), so no new
;;;     differentiation lemma is needed: psi - phi is a PW-antiderivable
;;;     integrand whose PW-INT is PW-INT(psi) - PW-INT(phi), and (3) applies.
;;;
;;; (5) `pw-int-abs-bound': |PW-INT(phi)| <= PW-INT(|phi|), the real half of the
;;;     notes' estimate (45).  Both bounds come from (4): phi <= |phi| and
;;;     -phi <= |phi| pointwise.  |phi| is given as a FUNCTION on [a,b] with the
;;;     pointwise equation `pabs_(t) == abs(phi(t))' and its own PW-antiderivative
;;;     -- PW-INT is an IOTA, so the statement would be UNDERDETERMINED (a strict
;;;     `=' on an undefined term) without that existence hypothesis: `abs' of a
;;;     piecewise-continuous function need not have an antiderivative for any
;;;     reason this library knows.
;;;
;;; WINDOW.  The latest citations are `pw-antiderivative-real-mul' and
;;; `pw-int-adjacent' (theorem-library/pw-int-laws-2.scm, batch 17-A), so the
;;; slot is immediately after that file.  Nothing here cites road-laws.
;;;
;;; Helper prefix: pio-.

;;; ---- file-local driver helpers --------------------------------------

(define (pio-head g) (and (pair? g) (car g)))

;;; the membership of an open interval, landed as its three conjuncts.
(define (pio-ooint-in! y lo hi)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'ooint-membership (list 'IN y (list 'OOINT lo hi)))))))

(define (pio-conj-ineq! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal))
         (ass)
         (apply dk-ineq! prems)))))

(define (pio-in-ccint! z lo hi prems)
  (dk-have! (list 'IN z (list 'CCINT lo hi))
    (lambda () (mac 'ccint-membership) (pio-conj-ineq! prems))))

(define (pio-in-ooint! z lo hi prems)
  (dk-have! (list 'IN z (list 'OOINT lo hi))
    (lambda () (mac 'ooint-membership) (pio-conj-ineq! prems))))

;;; the derivative-existential universal of the current goal-body, named by the
;;; exceptional set it mentions.
(define (pio-deriv-univ sv)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-DIFF-AT)
                             (dk-contains? fm 'OOINT)
                             (dk-contains? fm sv)))
           "the derivative universal"))

;;; =====================================================================
;;; (0) THE BASE CASE: NO EXCEPTIONAL SET, ON THE LINE.
;;;     The mean value theorem in its lower-bound form at m = 0.
;;; =====================================================================
(sp (make-wff '(FORALL pah_ (IMPLIES (IN pah_ (FUN RR RR))
     (IMPLIES (FORALL pax_ (IMPLIES (IN pax_ RR)
                             (IS-CONTINUOUS-AT RR-MS RR-MS pah_ pax_)))
       (FORALL pau_ (IMPLIES (IN pau_ RR)
         (FORALL pav_ (IMPLIES (IN pav_ RR)
           (IMPLIES (< pau_ pav_)
             (IMPLIES (FORALL pat_ (IMPLIES (IN pat_ (OOINT pau_ pav_))
                        (FORSOME pal_ (AND (IS-DIFF-AT pah_ pat_ pal_)
                                           (<= 0 pal_)))))
                      (<= (pah_ pau_) (pah_ pav_)))))))))))))
(dk-peel!)
(define pio-nt-cont
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-CONTINUOUS-AT)))
           "the continuity universal"))
(define pio-nt-diff
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'IS-DIFF-AT)))
           "the derivative universal"))
(dk-real! 0)
(dk-have! '(FORALL x (IMPLIES (IN x (CCINT pau_ pav_))
              (IS-CONTINUOUS-AT RR-MS RR-MS pah_ x)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'pau_ 'pav_ z)
      (dk-apply! pio-nt-cont z)
      (ass))))
(dk-have! '(FORALL x (IMPLIES (AND (IN x RR) (AND (< pau_ x) (< x pav_)))
              (FORSOME pal_ (AND (IS-DIFF-AT pah_ x pal_) (<= 0 pal_)))))
  (lambda ()
    (dk-peel!)
    (dk-split-all!)
    (pio-in-ooint! 'x 'pau_ 'pav_ (list '(IN x RR) '(< pau_ x) '(< x pav_)))
    (dk-apply! pio-nt-diff 'x)
    (ass)))
;; `mvt-lower-bound' has a CONJUNCTIVE first antecedent, which `fact' will not
;; split: read it off the instance and prove it on a lane.
(let* ((ch (dk-fact! 'mvt-lower-bound 'pah_ 'pau_ 'pav_ 0))
       (c1 (detach-with! ch (lambda () (dk-conj-close! (lambda () (ass))))))
       (c2 (dk-landed-1 (lambda () (detach! c1)))))
  (dk-landed-1 (lambda () (detach! c2))))
(fact 'fun-apply-type-c 'pah_ 'RR 'RR 'pau_)
(fact 'fun-apply-type-c 'pah_ 'RR 'RR 'pav_)
(dk-ineq! (list '<= (list '* 0 '(- pav_ pau_)) (list '- (list 'pah_ 'pav_)
                                                        (list 'pah_ 'pau_)))
          '(IN (pah_ pau_) RR) '(IN (pah_ pav_) RR)
          '(IN pau_ RR) '(IN pav_ RR))
(qed 'nondecreasing-total)
(topic! 'nondecreasing-total 'analysis)
(alias! 'nondecreasing-total
        "a function on the line with nonnegative derivative inside an interval does not decrease across it")

;;; =====================================================================
;;; (1) NONDECREASING OFF A FINITE SET, by finite-set-induction.
;;; =====================================================================

(define (pio-fin-body sv)
  (list 'FORALL 'pah_
   (list 'IMPLIES '(IN pah_ (FUN RR RR))
   (list 'IMPLIES '(FORALL pax_ (IMPLIES (IN pax_ RR)
                     (IS-CONTINUOUS-AT RR-MS RR-MS pah_ pax_)))
   (list 'FORALL 'pau_
   (list 'IMPLIES '(IN pau_ RR)
   (list 'FORALL 'pav_
   (list 'IMPLIES '(IN pav_ RR)
   (list 'IMPLIES '(< pau_ pav_)
   (list 'IMPLIES
     (list 'FORALL 'pat_
       (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT 'pau_ 'pav_))
         (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
               '(FORSOME pal_ (AND (IS-DIFF-AT pah_ pat_ pal_) (<= 0 pal_))))))
     '(<= (pah_ pau_) (pah_ pav_))))))))))))

(define pio-cls (list 'COMP 'pcs_ (pio-fin-body 'pcs_)))

(define pio-fin-stmt
  (list 'FORALL 'pas_
    (list 'IMPLIES '(IN pas_ SET)
      (list 'IMPLIES '(IN (CARD pas_) NN) (pio-fin-body 'pas_)))))

(define pio-base-claim (list 'IN 'EMPTY-SET pio-cls))

(define pio-step-claim
  (list 'FORALL 'pcs_
    (list 'IMPLIES
      (list 'AND '(IN pcs_ SET)
            (list 'AND '(IN (CARD pcs_) NN) (list 'IN 'pcs_ pio-cls)))
      (list 'FORALL 'pcx_
        (list 'IMPLIES (list 'AND '(IN pcx_ SET) '(NOT (IN pcx_ pcs_)))
              (list 'IN '(UNION pcs_ (PAIR pcx_ pcx_)) pio-cls))))))

;;; the eigenvariables of the class body, READ OFF THE GOAL after the peel.
(define (pio-body-vars)
  (let ((g (dk-goal)))
    (list (car (cadr g)) (cadr (cadr g)) (cadr (caddr g)))))

;;; peel `forall t in OOINT(lo,hi). not(t in S) => ...' and return the
;;; eigenvariable, read off the MEMBERSHIP that landed.
(define (pio-peel-point! oo)
  (let* ((ls (dk-peel!))
         (m  (car (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                           (equal? (caddr f) oo)))
                          ls))))
    (cadr m)))

(define (pio-base!)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (eq? (pio-head (dk-goal)) 'IN)
         (begin (fact 'empty-set-is-set) (ass))
         (begin
           (dk-peel!)
           (let* ((vs (pio-body-vars))
                  (hv (car vs)) (uv (cadr vs)) (vv (caddr vs))
                  (dd (pio-deriv-univ 'EMPTY-SET)))
             (dk-have! (list 'FORALL 'pat_
                         (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT uv vv))
                               (list 'FORSOME 'pal_
                                 (list 'AND (list 'IS-DIFF-AT hv 'pat_ 'pal_)
                                            '(<= 0 pal_)))))
               (lambda ()
                 (let ((tv (pio-peel-point! (list 'OOINT uv vv))))
                   (fact 'empty-set-has-no-members tv)
                   (dk-apply! dd tv)
                   (ass))))
             (fact 'nondecreasing-total hv uv vv)
             (ass)))))
   (dk-opened (lambda () (comp-mi)))))

;;; t is not in S u {x}, given `not (t in S)' and `not (t = x)'.
(define (pio-not-in-union! t sv xv)
  (fact 'pw-not-in-insert xv sv t))

(define (pio-step-body! ih sv xv)
  (dk-peel!)
  (let* ((vs (pio-body-vars))
         (hv (car vs)) (uv (cadr vs)) (vv (caddr vs))
         (dd (pio-deriv-univ 'UNION))
         (half!
          (lambda (lo hi prems flip)
            (dk-have! (list 'FORALL 'pat_
                        (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT lo hi))
                          (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
                                (list 'FORSOME 'pal_
                                  (list 'AND (list 'IS-DIFF-AT hv 'pat_ 'pal_)
                                             '(<= 0 pal_))))))
              (lambda ()
                (let ((tv (pio-peel-point! (list 'OOINT lo hi))))
                  (pio-ooint-in! tv lo hi)
                  (pio-in-ooint! tv uv vv (prems tv))
                  (dk-split-all!
                   (list (if flip (dk-fact! 'pw-lt-ne xv tv)
                                  (dk-fact! 'pw-lt-ne tv xv))))
                  (pio-not-in-union! tv sv xv)
                  (dk-apply! dd tv)
                  (ass)))))))
    (use-em (list 'IN xv (list 'OOINT uv vv))
      ;; ---- the inserted point IS interior: halve the interval ------------
      (lambda ()
        (pio-ooint-in! xv uv vv)
        (half! uv xv
               (lambda (tv) (list (list 'IN tv 'RR) (list 'IN xv 'RR)
                                  (list '< uv tv) (list '< tv xv) (list '< xv vv)))
               #f)
        (let ((ihh (dk-apply! ih hv)))
          (dk-apply! ihh uv xv)
          (half! xv vv
                 (lambda (tv) (list (list 'IN tv 'RR) (list 'IN xv 'RR)
                                    (list '< uv xv) (list '< xv tv) (list '< tv vv)))
                 #t)
          (dk-apply! ihh xv vv))
        (fact 'fun-apply-type-c hv 'RR 'RR uv)
        (fact 'fun-apply-type-c hv 'RR 'RR xv)
        (fact 'fun-apply-type-c hv 'RR 'RR vv)
        (dk-le-trans! (list hv uv) (list hv xv) (list hv vv))
        (ass))
      ;; ---- the inserted point is OUTSIDE: nothing changes ----------------
      (lambda ()
        (dk-have! (list 'FORALL 'pat_
                    (list 'IMPLIES (list 'IN 'pat_ (list 'OOINT uv vv))
                      (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
                            (list 'FORSOME 'pal_
                              (list 'AND (list 'IS-DIFF-AT hv 'pat_ 'pal_)
                                         '(<= 0 pal_))))))
          (lambda ()
            (let ((tv (pio-peel-point! (list 'OOINT uv vv))))
              (dk-have! (list 'NOT (list '= tv xv))
                (lambda ()
                  (di)
                  (dk-have! (list 'IN xv (list 'OOINT uv vv))
                    (lambda () (subst (list '= xv tv)) (ass)))
                  (ai (list 'NOT (list 'IN xv (list 'OOINT uv vv))))))
              (pio-not-in-union! tv sv xv)
              (dk-apply! dd tv)
              (ass))))
        (dk-apply! ih hv uv vv)
        (ass)))))

(define (pio-step!)
  (dk-peel!)
  (dk-split-all!)
  (let* ((g  (dk-goal))
         (un (cadr g))
         (sv (cadr un))
         (xv (cadr (caddr un))))
    (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
    (fact 'pairing xv xv)
    (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'PAIR xv xv) 'SET)))
    (fact 'union-set-closure sv (list 'PAIR xv xv))
    (fact 'pairing-membership xv xv)
    (let ((ih (dk-landed-find (lambda () (comp-me (list 'IN sv pio-cls)))
                              (dk-head? 'FORALL))))
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (pio-head (dk-goal)) 'IN)
             (ass)
             (pio-step-body! ih sv xv)))
       (dk-opened (lambda () (comp-mi)))))))

(sp (make-wff pio-fin-stmt))
(dk-peel!)
(have! pio-base-claim (lambda () (pio-base!)))
(have! pio-step-claim (lambda () (pio-step!)))
(have! (list 'AND pio-base-claim pio-step-claim))
(let* ((vs  (pio-body-vars))
       (hv  (car vs)) (uv (cadr vs)) (vv (caddr vs))
       (sv  (cadr (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN)
                                             (eq? (caddr fm) 'SET)))
                           "the exceptional set typing")))
       (ind (dk-fact! 'finite-set-induction pio-cls)))
  (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'CARD sv) 'NN)))
  (let* ((int  (dk-apply! ind sv))
         (body (dk-landed-find (lambda () (comp-me int)) (dk-head? 'FORALL))))
    (dk-apply! body hv uv vv)
    (ass)))
(qed 'nondecreasing-off-finite-set)
(topic! 'nondecreasing-off-finite-set 'analysis)
(alias! 'nondecreasing-off-finite-set
        "a function whose derivative is nonnegative off a finite set does not decrease")

;;; =====================================================================
;;; (2) THE SAME FOR A FUNCTION ON ITS INTERVAL.
;;; =====================================================================
(sp (make-wff '(FORALL a (IMPLIES (IN a RR)
     (FORALL b (IMPLIES (IN b RR)
       (IMPLIES (< a b)
         (FORALL h (IMPLIES (IN h (FUN (CCINT a b) RR))
           (IMPLIES (IS-CONTINUOUS-ON h (CCINT a b))
             (FORALL pas_ (IMPLIES (IN pas_ SET)
               (IMPLIES (IN (CARD pas_) NN)
                 (IMPLIES (FORALL pat_ (IMPLIES (IN pat_ (OOINT a b))
                            (IMPLIES (NOT (IN pat_ pas_))
                              (FORSOME pal_ (AND (HAS-DERIV-AT h pat_ pal_)
                                                 (<= 0 pal_))))))
                          (<= (h a) (h b))))))))))))))))
(dk-peel!)
(define pio-iv-diff
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the interior derivative hypothesis"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'extend-const-in-fun 'a 'b 'h)
(define pio-ext '(EXTEND-CONST h a b))
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS pio-ext 'x)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'extend-const-continuous-at 'a 'b 'h z)
      (ass))))
(dk-have! (list 'FORALL 'pat_ (list 'IMPLIES (list 'IN 'pat_ '(OOINT a b))
            (list 'IMPLIES '(NOT (IN pat_ pas_))
              (list 'FORSOME 'pal_ (list 'AND (list 'IS-DIFF-AT pio-ext 'pat_ 'pal_)
                                              '(<= 0 pal_))))))
  (lambda ()
    (let ((tv (pio-peel-point! '(OOINT a b))))
      (dk-apply! pio-iv-diff tv)
      (let ((lv (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the derivative value"))))
        (fact 'extend-const-deriv-fwd 'a 'b 'h tv lv)
        (ew lv)
        (both! (lambda () (ass)) (lambda () (ass)))))))
(dk-apply! (dk-fact! 'nondecreasing-off-finite-set 'pas_) pio-ext 'a 'b)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(fact 'extend-const-fixes 'a 'b 'a 'h)
(fact 'extend-const-fixes 'a 'b 'b 'h)
(subst (list '== (list 'h 'a) (list pio-ext 'a)))
(subst (list '== (list 'h 'b) (list pio-ext 'b)))
(ass)
(qed 'pw-nondecreasing-on-interval)
(topic! 'pw-nondecreasing-on-interval 'analysis)
(alias! 'pw-nondecreasing-on-interval
        "a function on an interval whose derivative is nonnegative off a finite set does not decrease across it")

;;; =====================================================================
;;; (3) A NONNEGATIVE INTEGRAND HAS A NONNEGATIVE PW-INTEGRAL.
;;; =====================================================================
(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL a (FORALL b
     (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
       (IMPLIES (FORALL pay_ (IMPLIES (IN pay_ (CCINT a b))
                               (<= 0 (pphi_ pay_))))
                (<= 0 (PW-INT pphi_ a b))))))))))
(dk-peel!)
(define pio-nn-ptw
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'CCINT)))
           "the pointwise nonnegativity"))
(dk-split-all! (list (dk-fact! 'pw-antiderivative-endpoints 'pwf_ 'pphi_ 'a 'b)))
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-antiderivative-continuous 'pwf_ 'pphi_ 'a 'b)
(fact 'ooint-subset-ccint 'a 'b)
(let* ((ex (dk-fact! 'pw-antiderivative-exceptional-set 'pwf_ 'pphi_ 'a 'b))
       (sv (dk-skolem! ex))
       (du (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                      (dk-contains? fm 'HAS-DERIV-AT)))
                    "the exceptional-set derivative universal")))
  (dk-have! (list 'FORALL 'pat_
              (list 'IMPLIES '(IN pat_ (OOINT a b))
                (list 'IMPLIES (list 'NOT (list 'IN 'pat_ sv))
                  (list 'FORSOME 'pal_
                    (list 'AND (list 'HAS-DERIV-AT 'pwf_ 'pat_ 'pal_)
                               '(<= 0 pal_))))))
    (lambda ()
      (let ((tv (pio-peel-point! '(OOINT a b))))
        (dk-apply! du tv)
        (fact 'subset-mem-fwd '(OOINT a b) '(CCINT a b) tv)
        (dk-apply! pio-nn-ptw tv)
        (ew (list 'pphi_ tv))
        (both! (lambda () (ass)) (lambda () (ass))))))
  (fact 'pw-nondecreasing-on-interval 'a 'b 'pwf_ sv))
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(pio-in-ccint! 'a 'a 'b (list '(IN a RR) '(<= a a) '(<= a b)))
(pio-in-ccint! 'b 'a 'b (list '(IN b RR) '(<= b b) '(<= a b)))
;; ONE citation, applied twice: a second `dk-fact!' with the same arguments
;; lands nothing and errors (the repeated-instantiation defect, batch 16-A).
(let ((vu (dk-fact! 'pw-antiderivative-value-in-rr 'pwf_ 'pphi_ 'a 'b)))
  (dk-apply! vu 'a)
  (dk-apply! vu 'b))
(dk-read-off! 'pw-int-value 'pwf_ 'pphi_ 'a 'b)
(dk-ineq! '(<= (pwf_ a) (pwf_ b)) '(IN (pwf_ a) RR) '(IN (pwf_ b) RR))
(qed 'pw-int-nonneg)
(topic! 'pw-int-nonneg 'analysis)
(alias! 'pw-int-nonneg
        "the piecewise integral of a nonnegative integrand is nonnegative")

;;; ---- the lambda kit for (4) and (5) ---------------------------------
;;; The two order laws below assemble the difference psi - phi out of the
;;; EXISTING antiderivative algebra (real-mul at -1, then sum), so the only new
;;; work is building the four functions and typing them.

(define pio-cc '(CCINT a b))
(define (pio-neg-lam f) (list 'VNB-LAMBDA 'pdt_ pio-cc (list '* -1 (list f 'pdt_))))
(define (pio-sub-lam g f)
  (list 'VNB-LAMBDA 'pdt_ pio-cc
        (list '+ (list g 'pdt_) (list '* -1 (list f 'pdt_)))))

;;; (IN LAM (FUN [a,b] RR)) by `lam-t': the pointwise leaf is closed by PTWISE!
;;; on the peeled point, the sethood leaf from (IN [a,b] SET) in the context.
(define (pio-type-lam! lam ptwise!)
  (dk-have! (list 'IN lam (list 'FUN pio-cc 'RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (pio-head (dk-goal)) 'FORALL)
             (let ((z (dk-di-var!))) (ptwise! z))
             (ass)))
       (dk-opened (lambda () (lam-t)))))))

;;; the pointwise equation a value law wants, proved by beta.
(define (pio-value-eq! lam rhs-of)
  (let ((claim (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pio-cc)
                 (list '== (list lam 'pay_) (rhs-of 'pay_))))))
    (dk-have! claim (lambda () (dk-di-var!) (dk-lam-b!) (qrfl)))
    claim))

;;; (IN (* -1 (f z)) RR) and (IN (+ (g z) (* -1 (f z))) RR).
(define (pio-neg-type! f z)
  (fact 'fun-apply-type-c f pio-cc 'RR z)
  (have! (list 'AND '(IN -1 RR) (list 'IN (list f z) 'RR)))
  (fact 'rr-mul-closed -1 (list f z))
  (ass))

;;; the negated PW-antiderivative pair, with its PW-INT equation.
(define (pio-negate! f phi)
  (let ((nf  (pio-neg-lam f))
        (nph (pio-neg-lam phi)))
    (pio-type-lam! nf  (lambda (z) (pio-neg-type! f z)))
    (pio-type-lam! nph (lambda (z) (pio-neg-type! phi z)))
    (pio-value-eq! nf  (lambda (y) (list '* -1 (list f y))))
    (pio-value-eq! nph (lambda (y) (list '* -1 (list phi y))))
    (dk-split-all!
     (list (dk-apply! (dk-fact! 'pw-antiderivative-real-mul 'a 'b f phi -1)
                      nf nph)))
    (list nf nph)))

;;; =====================================================================
;;; (4) MONOTONICITY OF THE PW-INTEGRAL.
;;; =====================================================================
(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL paw_ (FORALL ppsi_
     (FORALL a (FORALL b
       (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
       (IMPLIES (IS-PW-ANTIDERIVATIVE paw_ ppsi_ a b)
       (IMPLIES (FORALL pay_ (IMPLIES (IN pay_ (CCINT a b))
                               (<= (pphi_ pay_) (ppsi_ pay_))))
                (<= (PW-INT pphi_ a b) (PW-INT ppsi_ a b)))))))))))))
(dk-peel!)
(define pio-mn-ptw
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'CCINT)))
           "the pointwise inequality"))
(dk-split-all! (list (dk-fact! 'pw-antiderivative-endpoints 'pwf_ 'pphi_ 'a 'b)))
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-antiderivative-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-antiderivative-in-fun 'paw_ 'ppsi_ 'a 'b)
(fact 'pw-antiderivative-integrand-in-fun 'paw_ 'ppsi_ 'a 'b)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set '(CCINT a b) 'RR)
(dk-real! -1)
(let* ((neg  (pio-negate! 'pwf_ 'pphi_))
       (nf   (car neg))
       (nph  (cadr neg))
       (hh   (pio-sub-lam 'paw_ 'pwf_))
       (chi  (pio-sub-lam 'ppsi_ 'pphi_)))
  (pio-type-lam! hh
    (lambda (z)
      (pio-neg-type! 'pwf_ z)
      (fact 'fun-apply-type-c 'paw_ pio-cc 'RR z)
      (have! (list 'AND (list 'IN (list 'paw_ z) 'RR)
                   (list 'IN (list '* -1 (list 'pwf_ z)) 'RR)))
      (fact 'rr-add-closed (list 'paw_ z) (list '* -1 (list 'pwf_ z)))
      (ass)))
  (pio-type-lam! chi
    (lambda (z)
      (pio-neg-type! 'pphi_ z)
      (fact 'fun-apply-type-c 'ppsi_ pio-cc 'RR z)
      (have! (list 'AND (list 'IN (list 'ppsi_ z) 'RR)
                   (list 'IN (list '* -1 (list 'pphi_ z)) 'RR)))
      (fact 'rr-add-closed (list 'ppsi_ z) (list '* -1 (list 'pphi_ z)))
      (ass)))
  (pio-value-eq! hh  (lambda (y) (list '+ (list 'paw_ y) (list nf y))))
  (pio-value-eq! chi (lambda (y) (list '+ (list 'ppsi_ y) (list nph y))))
  (dk-split-all!
   (list (dk-apply! (dk-fact! 'pw-antiderivative-sum 'a 'b 'paw_ nf 'ppsi_ nph)
                    hh chi)))
  ;; the difference is nonnegative pointwise
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pio-cc)
              (list '<= 0 (list chi 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (dk-lam-b!)
        (fact 'fun-apply-type-c 'pphi_ pio-cc 'RR z)
        (fact 'fun-apply-type-c 'ppsi_ pio-cc 'RR z)
        (dk-apply! pio-mn-ptw z)
        (dk-ineq! (list '<= (list 'pphi_ z) (list 'ppsi_ z))
                  (list 'IN (list 'pphi_ z) 'RR)
                  (list 'IN (list 'ppsi_ z) 'RR)))))
  (fact 'pw-int-nonneg hh chi 'a 'b)
  (fact 'pw-int-in-rr 'pwf_ 'pphi_ 'a 'b)
  (fact 'pw-int-in-rr 'paw_ 'ppsi_ 'a 'b)
  (fact 'pw-int-in-rr nf nph 'a 'b)
  (fact 'pw-int-in-rr hh chi 'a 'b)
  (dk-ineq! (list '<= 0 (list 'PW-INT chi 'a 'b))
            (list '= (list 'PW-INT chi 'a 'b)
                  (list '+ (list 'PW-INT 'ppsi_ 'a 'b) (list 'PW-INT nph 'a 'b)))
            (list '= (list 'PW-INT nph 'a 'b) (list '* -1 '(PW-INT pphi_ a b)))
            (list 'IN (list 'PW-INT chi 'a 'b) 'RR)
            (list 'IN (list 'PW-INT nph 'a 'b) 'RR)
            '(IN (PW-INT pphi_ a b) RR)
            '(IN (PW-INT ppsi_ a b) RR)))
(qed 'pw-int-monotone)
(topic! 'pw-int-monotone 'analysis)
(alias! 'pw-int-monotone
        "the piecewise integral is monotone in the integrand")

;;; A goal `t <= abs(x)' for t LINEAR in x (here x itself and -1 * x), with
;;; (IN x RR) in the context.  `ineq' does not know `abs' well enough to see
;;; either bound (it declines `x <= abs(x)'), so the sign is split by
;;; `rr-leq-total' and `abs' is rewritten away in each case.
(define (pio-abs-split! x prems)
  (dk-real! 0)
  (dk-have! (list 'AND (list 'IN 0 'RR) (list 'IN x 'RR)))
  (let ((tot (dk-fact! 'rr-leq-total 0 x)))
    (dk-each-leaf! (lambda () (ai tot))
      (lambda ()
        (if (dk-ctx-form (list '<= 0 x))
            (begin (dk-read-off! 'rr-abs-of-nonneg x)
                   (apply dk-ineq! (cons (list '<= 0 x) prems)))
            (begin (dk-read-off! 'rr-abs-of-nonpos x)
                   (apply dk-ineq! (cons (list '<= x 0) prems))))))))

(define (pio-abs-ge! x) (pio-abs-split! x (list (list 'IN x 'RR))))

;;; =====================================================================
;;; (5) |PW-INT(phi)| <= PW-INT(|phi|)  --  the real half of estimate (45).
;;; =====================================================================
(sp (make-wff '(FORALL pwf_ (FORALL pphi_ (FORALL paw_ (FORALL pabs_
     (FORALL a (FORALL b
       (IMPLIES (IS-PW-ANTIDERIVATIVE pwf_ pphi_ a b)
       (IMPLIES (IS-PW-ANTIDERIVATIVE paw_ pabs_ a b)
       (IMPLIES (FORALL pay_ (IMPLIES (IN pay_ (CCINT a b))
                               (== (pabs_ pay_) (ABS (pphi_ pay_)))))
                (<= (ABS (PW-INT pphi_ a b)) (PW-INT pabs_ a b)))))))))))))
(dk-peel!)
(define pio-ab-ptw
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'ABS)))
           "the pointwise absolute-value equation"))
(dk-split-all! (list (dk-fact! 'pw-antiderivative-endpoints 'pwf_ 'pphi_ 'a 'b)))
(fact 'pw-antiderivative-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-antiderivative-integrand-in-fun 'pwf_ 'pphi_ 'a 'b)
(fact 'pw-antiderivative-in-fun 'paw_ 'pabs_ 'a 'b)
(fact 'pw-antiderivative-integrand-in-fun 'paw_ 'pabs_ 'a 'b)
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set '(CCINT a b) 'RR)
(dk-real! -1)
(let* ((neg (pio-negate! 'pwf_ 'pphi_))
       (nf  (car neg))
       (nph (cadr neg)))
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pio-cc)
              (list '<= (list 'pphi_ 'pay_) (list 'pabs_ 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'fun-apply-type-c 'pphi_ pio-cc 'RR z)
        (dk-apply! pio-ab-ptw z)
        (subst (list '== (list 'pabs_ z) (list 'ABS (list 'pphi_ z))))
        (pio-abs-ge! (list 'pphi_ z)))))
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pio-cc)
              (list '<= (list nph 'pay_) (list 'pabs_ 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (dk-lam-b!)
        (fact 'fun-apply-type-c 'pphi_ pio-cc 'RR z)
        (dk-apply! pio-ab-ptw z)
        (subst (list '== (list 'pabs_ z) (list 'ABS (list 'pphi_ z))))
        (pio-abs-ge! (list 'pphi_ z)))))
  (dk-apply! (dk-fact! 'pw-int-monotone 'pwf_ 'pphi_ 'paw_ 'pabs_) 'a 'b)
  (dk-apply! (dk-fact! 'pw-int-monotone nf nph 'paw_ 'pabs_) 'a 'b)
  (fact 'pw-int-in-rr 'pwf_ 'pphi_ 'a 'b)
  (fact 'pw-int-in-rr 'paw_ 'pabs_ 'a 'b)
  (fact 'pw-int-in-rr nf nph 'a 'b)
  (pio-abs-split! '(PW-INT pphi_ a b)
    (list (list '<= '(PW-INT pphi_ a b) '(PW-INT pabs_ a b))
          (list '<= (list 'PW-INT nph 'a 'b) '(PW-INT pabs_ a b))
          (list '= (list 'PW-INT nph 'a 'b) (list '* -1 '(PW-INT pphi_ a b)))
          (list 'IN (list 'PW-INT nph 'a 'b) 'RR)
          '(IN (PW-INT pphi_ a b) RR)
          '(IN (PW-INT pabs_ a b) RR))))
(qed 'pw-int-abs-bound)
(topic! 'pw-int-abs-bound 'analysis)
(alias! 'pw-int-abs-bound
        "the absolute value of a piecewise integral is at most the integral of the absolute value")
