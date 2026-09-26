;;; regulated-algebra.scm -- THE ALGEBRA OF REGULATED FUNCTIONS ON [a, b], THE
;;; INTEGRAND OF A ROAD IS REGULATED, AND THE INTEGRAL ALONG A ROAD EXISTS.
;;; Batch 23-A, 2026-09-23.
;;;
;;; THE SOURCE.  Dieudonne, Foundations of Modern Analysis.
;;;   VII.6  regulated functions; "the regulated functions form a closed
;;;          subspace" -- stated here in pieces, for real-valued functions ON
;;;          [a, b]: sum, difference, product, real scalar multiple, and
;;;          congruence (agreement on [a, b] with a regulated function).
;;;   (8.7.2) "any regulated mapping of I into F has a primitive in I"
;;;          (`regulated-on-has-primitive', theorem-library/regulated-has-primitive.scm).
;;;   IX.6   the integral along a road y of f continuous on its trace is the
;;;          integral over [a, b] of f(y(t)) y'(t), which EXISTS because the
;;;          integrand is regulated: a continuous function of a continuous
;;;          function is continuous, and the product of a continuous and a
;;;          regulated function is regulated.
;;;
;;; THE FILE IN ORDER.
;;;   (1) ONE-SIDED LIMITS WITHIN A SET: sum, difference, product, scalar
;;;       (right and left), from the definition.  The product estimate is
;;;       `rr-abs-prod-bound' (|uv - pq| <= e from |u| <= M, |q| <= K,
;;;       |u - p|, |v - q| <= t, (M + K) t <= e), with M = |l| + 1 bounding |f|
;;;       near the point.  The functions are GIVEN, with a POINTWISE AGREEMENT
;;;       clause for the combination (as `regulated-on-reflect' does), never a
;;;       constructed lambda in the conclusion.
;;;   (2) REGULATED FUNCTIONS ON [a, b]: regulated-on-sum / -sub / -mul /
;;;       -scalar, and regulated-on-congruence (from `regulated-on-restrict'
;;;       with [c, d] = [a, b]).  The negative is the scalar -1.
;;;   (3) continuous-on-compose-regulated: f continuous on U subset CC (as a
;;;       map on the subspace U of the normed field CC, the shape
;;;       `diff-on-implies-continuous' delivers), gamma a path with trace in
;;;       U: re(f o gamma) and im(f o gamma) are regulated on [a, b].
;;;   (4) road-integrand-regulated: the two coordinates of
;;;       t |-> f(gamma(t)) dgamma(t) are regulated on [a, b]
;;;       (re(zw) = re z re w - im z im w, `cc-re-mul' / `cc-im-mul').
;;;   (5) line-int-exists: the two IS-PRIMITIVE facts every cc-int / line-int
;;;       law takes as antecedents, in exactly their shape.
;;;
;;; Helper prefix: rga-.  Theorem binders rg..._ (no predicate body uses one).

;;; ---- file-local driver helpers ---------------------------------------

(define (rga-head g) (and (pair? g) (car g)))

;;; goal abs(y) < c: the two linear halves by `ineq' from PREMS, then the
;;; split lemma.  y and c must be typed in context.
(define (rga-abs-lt! y c prems)
  (dk-have! (list '< (list '- c) y) (lambda () (apply dk-ineq! prems)))
  (dk-have! (list '< y c) (lambda () (apply dk-ineq! prems)))
  (fact 'rr-abs-lt-of-parts y c)
  (ass))

;;; the delta clause of a limit clause CL at the positive E: skolemize, type
;;; it, return (d . its clause).
(define (rga-delta! cl e)
  (let* ((d (dk-skolem! (dk-apply! cl e)))
         (c (dk-pick (lambda (g) (and (eq? (rga-head g) 'FORALL) (dk-contains? g d)))
                     "a delta clause")))
    (fact 'rr-pos-rr-in-rr d)
    (fact 'rr-lt-of-pos-rr d)
    (cons d c)))

;;; the minimum of the deltas DS (each typed, positive, in context): returns
;;; (w . facts), FACTS the typings and order facts about w that landed.
(define (rga-min! ds)
  (let loop ((w (car ds)) (rest (cdr ds)) (facts '()))
    (if (null? rest)
        (cons w facts)
        (let* ((d (car rest))
               (w2 (dk-skolem! (dk-fact! 'rr-min-pos w d))))
          (dk-split-all!)
          (loop w2 (cdr rest)
                (append (list (list 'IN w2 'RR) (list '< 0 w2) (list '<= w2 w) (list '<= w2 d))
                        facts))))))

;;; the window facts of t for the radius R, from those for W.
(define (rga-window right? x t r)
  (if right?
      (list (list '< x t) (list '< t (list '+ x r)))
      (list (list '< (list '- x r) t) (list '< t x))))

;;; inside the eps clause of the GOAL's one-sided limit (goal on entry: the
;;; FORSOME of the delta), with the deltas DS and their clauses CLS: take w =
;;; their minimum, peel the window, land every clause at t, and run
;;; (BODY t) on the goal |h(t) - L| < eps.
(define (rga-window! right? ds cls body)
  (let* ((mw (rga-min! ds))
         (w (car mw)))
    (fact 'rr-pos-rr-of-lt w)
    (ew w)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rga-head (dk-goal)) 'POS-RR)
           (ass)
           (let* ((ls (dk-peel!))
                  (t (cadr (car (filter (lambda (g) (and (eq? (rga-head g) 'IN)
                                                         (eq? (caddr g) 'rgw_)))
                                        ls))))
                  (base (append (list '(IN rgx_ RR) (list 'IN t 'RR))
                                (map (lambda (d) (list 'IN d 'RR)) ds)
                                (cdr mw)
                                (rga-window right? 'rgx_ t w))))
             (fact 'subset-mem-fwd 'rgw_ 'RR t)
             (for-each
              (lambda (d cl)
                (for-each (lambda (g) (if (not (dk-ctx-form g))
                                          (dk-have! g (lambda () (apply dk-ineq! base)))))
                          (rga-window right? 'rgx_ t d))
                (dk-apply! cl t))
              ds cls)
             (body t)))))))

;;; open the two limit hypotheses of the lemma (pred of FA at LA, of FB at LB)
;;; and return their eps clauses.
(define (rga-open-lim! pred fa la)
  (let ((ps (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred fa 'rgw_ 'rgx_ la)))))))
    (car (filter (dk-head? 'FORALL) ps))))

;;; =====================================================================
;;; (1) ONE-SIDED LIMITS WITHIN A SET: SUM, DIFFERENCE, PRODUCT, SCALAR.
;;; =====================================================================

(define (rga-lim2-stmt right? op)
  (let ((p (if right? "is-right-limit-within" "is-left-limit-within"))
        (o (symbol->string op)))
    (string-append
     "forall([f, g, rgh_, rgw_, rgx_, rgl_, rgm_], "
     p "(f, rgw_, rgx_, rgl_) implies "
     p "(g, rgw_, rgx_, rgm_) implies rgh_ in fun(rgw_, rr) implies
      forall([rgz_ in rgw_], rgh_(rgz_) == f(rgz_) " o " g(rgz_)) implies "
     p "(rgh_, rgw_, rgx_, rgl_ " o " rgm_))")))

(define (rga-scal-stmt right?)
  (let ((p (if right? "is-right-limit-within" "is-left-limit-within")))
    (string-append
     "forall([f, rgh_, rgw_, rgx_, rgl_, rgc_ in rr], "
     p "(f, rgw_, rgx_, rgl_) implies rgh_ in fun(rgw_, rr) implies
      forall([rgz_ in rgw_], rgh_(rgz_) == rgc_ * f(rgz_)) implies "
     p "(rgh_, rgw_, rgx_, rgc_ * rgl_))")))

(define (rga-agree)
  (dk-pick (lambda (g) (and (eq? (rga-head g) 'FORALL) (dk-contains? g 'rgh_)))
           "the pointwise agreement"))

;;; the eps clause for a sum or a difference.
(define (rga-eps-add! right? op cf cg agree)
  (let* ((pe (dk-peel!))
         (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (h  (dk-halve! e))
         (dc1 (rga-delta! cf h))
         (dc2 (rga-delta! cg h)))
    (fact 'rr-pos-rr-in-rr e)
    (rga-window! right? (list (car dc1) (car dc2)) (list (cdr dc1) (cdr dc2))
     (lambda (t)
       (let* ((ft (list 'f t)) (gt (list 'g t))
              (y (list '- (list op ft gt) (list op 'rgl_ 'rgm_))))
         (fact 'fun-apply-type-c 'f 'rgw_ 'RR t)
         (fact 'fun-apply-type-c 'g 'rgw_ 'RR t)
         (fact 'rr-sub-in-rr ft 'rgl_)
         (fact 'rr-sub-in-rr gt 'rgm_)
         (dk-split-all! (list (dk-fact! 'rr-abs-lt-parts (list '- ft 'rgl_) h)))
         (dk-split-all! (list (dk-fact! 'rr-abs-lt-parts (list '- gt 'rgm_) h)))
         (fact (if (eq? op '+) 'rr-add-in-rr 'rr-sub-in-rr) ft gt)
         (fact 'rr-sub-in-rr (list op ft gt) (list op 'rgl_ 'rgm_))
         (dk-apply! agree t)
         (subst (list '= (list 'rgh_ t) (list op ft gt)))
         (rga-abs-lt! y e
           (list (list 'IN ft 'RR) (list 'IN gt 'RR) '(IN rgl_ RR) '(IN rgm_ RR)
                 (list 'IN e 'RR) (list 'IN h 'RR)
                 (list '< (list '- h) (list '- ft 'rgl_)) (list '< (list '- ft 'rgl_) h)
                 (list '< (list '- h) (list '- gt 'rgm_)) (list '< (list '- gt 'rgm_) h)
                 (list '= (list '+ h h) e))))))))

;;; the eps clause for a product u v -> p q (MUL? #t: u = f, v = g, p = l,
;;; q = m; #f: the scalar, u = c constant, v = f, p = c, q = l).  CF is the
;;; clause of f, CG that of g (unused for the scalar).
(define (rga-eps-mul! right? mul? cf cg agree)
  (let* ((pe (dk-peel!))
         (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (h  (dk-halve! e))
         (p  (if mul? 'rgl_ 'rgc_))
         (q  (if mul? 'rgm_ 'rgl_))
         (mm (if mul? '(+ (ABS rgl_) 1) '(ABS rgc_)))
         (kk (list 'ABS q))
         (cc (list '+ mm kk)))
    (fact 'rr-pos-rr-in-rr e)
    (fact 'rr-abs-closed p) (fact 'rr-abs-nonneg p)
    (fact 'rr-abs-closed q) (fact 'rr-abs-nonneg q)
    (fact 'rr-one-in)
    (fact 'rr-zero-lt-one)
    (if mul? (fact 'rr-add-in-rr (list 'ABS p) 1))
    (fact 'rr-add-in-rr mm kk)
    (dk-have! (list '<= 0 cc)
      (lambda () (dk-ineq! (list 'IN (list 'ABS p) 'RR) (list 'IN (list 'ABS q) 'RR)
                           (list '<= 0 (list 'ABS p)) (list '<= 0 (list 'ABS q)))))
    (let* ((d (dk-skolem! (dk-fact! 'rr-scale-eps cc h)))
           (sc (dk-pick (lambda (g) (and (eq? (rga-head g) 'FORALL) (dk-contains? g d)
                                         (dk-contains? g cc)))
                        "the scaling clause")))
      (fact 'rr-pos-rr-in-rr d)
      (fact 'rr-lt-of-pos-rr d)
      (if mul? (fact 'rr-pos-rr-of-lt 1))
      (let* ((dcs (if mul?
                      (list (rga-delta! cf 1) (rga-delta! cf d) (rga-delta! cg d))
                      (list (rga-delta! cf d)))))
        (rga-window! right? (map car dcs) (map cdr dcs)
         (lambda (t)
           (let* ((ft (list 'f t))
                  (u  (if mul? ft 'rgc_))
                  (v  (if mul? (list 'g t) ft))
                  (up (list '- u p)) (vq (list '- v q))
                  (a  (list 'ABS (list '- (list '* u v) (list '* p q)))))
             (fact 'fun-apply-type-c 'f 'rgw_ 'RR t)
             (if mul? (fact 'fun-apply-type-c 'g 'rgw_ 'RR t))
             (fact 'rr-sub-in-rr u p)
             (fact 'rr-sub-in-rr v q)
             (fact 'rr-abs-closed up)
             (fact 'rr-abs-closed vq)
             (fact 'rr-abs-closed u)
             ;; |u - p| <= d
             (if mul?
                 (fact 'rr-lt-implies-le (list 'ABS up) d)
                 (begin
                   (dk-have! (list '<= (list '- d) up)
                     (lambda () (dk-ineq! '(IN rgc_ RR) (list 'IN d 'RR) (list '< 0 d))))
                   (dk-have! (list '<= up d)
                     (lambda () (dk-ineq! '(IN rgc_ RR) (list 'IN d 'RR) (list '< 0 d))))
                   (fact 'rr-abs-le-of-parts up d)))
             ;; |v - q| <= d
             (fact 'rr-lt-implies-le (list 'ABS vq) d)
             ;; |u| <= M
             (if mul?
                 (begin
                   (dk-split-all! (list (dk-fact! 'rr-abs-lt-parts up 1)))
                   (fact 'rr-leq-reflexive '(ABS rgl_))
                   (dk-split-all! (list (dk-fact! 'rr-abs-le-parts 'rgl_ '(ABS rgl_))))
                   (let ((prems (list (list 'IN ft 'RR) '(IN rgl_ RR) '(IN (ABS rgl_) RR)
                                      (list '< (list '- 1) up) (list '< up 1)
                                      '(<= (- (ABS rgl_)) rgl_) '(<= rgl_ (ABS rgl_)))))
                     (dk-have! (list '<= (list '- mm) ft) (lambda () (apply dk-ineq! prems)))
                     (dk-have! (list '<= ft mm) (lambda () (apply dk-ineq! prems)))
                     (fact 'rr-abs-le-of-parts ft mm)))
                 (fact 'rr-leq-reflexive '(ABS rgc_)))
             ;; |q| <= K
             (fact 'rr-leq-reflexive kk)
             ;; (M + K) d <= h
             (dk-have! (list '<= 0 d) (lambda () (dk-ineq! (list 'IN d 'RR) (list '< 0 d))))
             (fact 'rr-leq-reflexive d)
             (dk-apply! sc d)
             ;; the product estimate, in stages (the eight-term `fact' trap)
             (let* ((r1 (dk-fact! 'rr-abs-prod-bound u v p q))
                    (r2 (inst*! r1 mm kk d h)))
               (detach-with! r2 (lambda () (dk-conj-close! (lambda () (ass))))))
             (fact 'rr-mul-in-rr u v)
             (fact 'rr-mul-in-rr p q)
             (fact 'rr-sub-in-rr (list '* u v) (list '* p q))
             (fact 'rr-abs-closed (list '- (list '* u v) (list '* p q)))
             (dk-apply! agree t)
             (subst (list '= (list 'rgh_ t) (list '* u v)))
             (dk-ineq! (list 'IN a 'RR) (list 'IN h 'RR) (list 'IN e 'RR)
                       (list '<= a h) (list '= (list '+ h h) e) (list '< 0 h)))))))))

;;; the whole lemma.  KIND is '+, '- or '* (two limits) or 'scal.
(define (rga-lim! right? kind)
  (dk-peel!)
  (let* ((pred (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN))
         (agree (rga-agree))
         (cf (rga-open-lim! pred 'f 'rgl_))
         (cg (if (eq? kind 'scal) #f (rga-open-lim! pred 'g 'rgm_))))
    (cond ((eq? kind '+) (fact 'rr-add-in-rr 'rgl_ 'rgm_))
          ((eq? kind '-) (fact 'rr-sub-in-rr 'rgl_ 'rgm_))
          ((eq? kind '*) (fact 'rr-mul-in-rr 'rgl_ 'rgm_))
          (#t (fact 'rr-mul-in-rr 'rgc_ 'rgl_)))
    (mac pred)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rga-head (dk-goal)) 'FORALL)
           (cond ((memq kind '(+ -)) (rga-eps-add! right? kind cf cg agree))
                 ((eq? kind '*) (rga-eps-mul! right? #t cf cg agree))
                 (#t (rga-eps-mul! right? #f cf cg agree)))
           (ass))))))

(sp (make-wff (rga-lim2-stmt #t '+)))
(rga-lim! #t '+)
(qed 'right-limit-within-sum)

(sp (make-wff (rga-lim2-stmt #f '+)))
(rga-lim! #f '+)
(qed 'left-limit-within-sum)

(sp (make-wff (rga-lim2-stmt #t '-)))
(rga-lim! #t '-)
(qed 'right-limit-within-sub)

(sp (make-wff (rga-lim2-stmt #f '-)))
(rga-lim! #f '-)
(qed 'left-limit-within-sub)

(sp (make-wff (rga-lim2-stmt #t '*)))
(rga-lim! #t '*)
(qed 'right-limit-within-mul)

(sp (make-wff (rga-lim2-stmt #f '*)))
(rga-lim! #f '*)
(qed 'left-limit-within-mul)

(sp (make-wff (rga-scal-stmt #t)))
(rga-lim! #t 'scal)
(qed 'right-limit-within-scalar)

(sp (make-wff (rga-scal-stmt #f)))
(rga-lim! #f 'scal)
(qed 'left-limit-within-scalar)

;;; =====================================================================
;;; (2) REGULATED FUNCTIONS ON [a, b]: SUM, DIFFERENCE, PRODUCT, SCALAR,
;;; CONGRUENCE.  The negative of f is the scalar -1 (an instance).
;;; =====================================================================

(define (rga-reg2-stmt op)
  (let ((o (symbol->string op)))
    (string-append
     "forall([f, g, rgh_, a, b], is-regulated-on(f, a, b) implies
      is-regulated-on(g, a, b) implies rgh_ in fun(ccint(a, b), rr) implies
      forall([rgz_ in ccint(a, b)], rgh_(rgz_) == f(rgz_) " o " g(rgz_)) implies
      is-regulated-on(rgh_, a, b))")))

;;; the two limit requirements of a regulated FN, unfolded (destructively).
(define (rga-open-reg! fn)
  (let ((ps (dk-split-all! (dk-landed* (lambda ()
              (mac-h 'IS-REGULATED-ON (list 'IS-REGULATED-ON fn 'a 'b)))))))
    (cons (car (filter (lambda (g) (and (eq? (rga-head g) 'FORALL)
                                        (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN)))
                       ps))
          (car (filter (lambda (g) (and (eq? (rga-head g) 'FORALL)
                                        (dk-contains? g 'IS-LEFT-LIMIT-WITHIN)))
                       ps)))))

;;; KIND: '+ '- '* (two functions f, g) or 'scal (f and the scalar rgc_).
(define (rga-reg! kind)
  (dk-peel!)
  (let* ((rf (rga-open-reg! 'f))
         (rg (if (eq? kind 'scal) #f (rga-open-reg! 'g))))
    (mac 'IS-REGULATED-ON)
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (if (eq? (rga-head gl) 'FORALL)
             (let* ((right? (dk-contains? gl 'IS-RIGHT-LIMIT-WITHIN))
                    (sel (if right? car cdr))
                    (x (dk-di-var!)))
               (dk-peel!)
               (let ((l (dk-skolem! (dk-apply! (sel rf) x))))
                 (if (eq? kind 'scal)
                     (begin
                       (ew (list '* 'rgc_ l))
                       (fact (if right? 'right-limit-within-scalar 'left-limit-within-scalar)
                             'f 'rgh_ '(CCINT a b) x l 'rgc_)
                       (ass))
                     (let ((m (dk-skolem! (dk-apply! (sel rg) x))))
                       (ew (list kind l m))
                       (fact (if right?
                                 (cond ((eq? kind '+) 'right-limit-within-sum)
                                       ((eq? kind '-) 'right-limit-within-sub)
                                       (#t 'right-limit-within-mul))
                                 (cond ((eq? kind '+) 'left-limit-within-sum)
                                       ((eq? kind '-) 'left-limit-within-sub)
                                       (#t 'left-limit-within-mul)))
                             'f 'g 'rgh_ '(CCINT a b) x l m)
                       (ass)))))
             (ass)))))))

(sp (make-wff (rga-reg2-stmt '+)))
(rga-reg! '+)
(qed 'regulated-on-sum)

(sp (make-wff (rga-reg2-stmt '-)))
(rga-reg! '-)
(qed 'regulated-on-sub)

(sp (make-wff (rga-reg2-stmt '*)))
(rga-reg! '*)
(qed 'regulated-on-mul)

(sp (make-wff "forall([f, rgh_, a, b, rgc_ in rr], is-regulated-on(f, a, b) implies
   rgh_ in fun(ccint(a, b), rr) implies
   forall([rgz_ in ccint(a, b)], rgh_(rgz_) == rgc_ * f(rgz_)) implies
   is-regulated-on(rgh_, a, b))"))
(rga-reg! 'scal)
(qed 'regulated-on-scalar)

;;; congruence: `regulated-on-restrict' with [c, d] = [a, b].
(sp (make-wff "forall([f, g, a, b], is-regulated-on(g, a, b) implies
   f in fun(ccint(a, b), rr) implies
   forall([rgz_ in ccint(a, b)], f(rgz_) == g(rgz_)) implies
   is-regulated-on(f, a, b))"))
(dk-peel!)
(dk-have! '(AND (IN a RR) (AND (IN b RR) (AND (< a b) (IN g (FUN (CCINT a b) RR)))))
  (lambda ()
    (dk-split-all! (dk-landed* (lambda ()
      (mac-h 'IS-REGULATED-ON '(IS-REGULATED-ON g a b)))))
    (dk-conj-close! (lambda () (ass)))))
(dk-split-all!)
(fact 'rr-leq-reflexive 'a)
(fact 'rr-leq-reflexive 'b)
(define rga-cg-agree
  (dk-pick (lambda (fm) (and (eq? (rga-head fm) 'FORALL) (dk-contains? fm '==)))
           "the pointwise agreement"))
(dk-have! '(FORALL rqz_ (IMPLIES (IN rqz_ (CCINT a b)) (= (f rqz_) (g rqz_))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (dk-apply! rga-cg-agree z)
      (fact 'fun-apply-type-c 'g '(CCINT a b) 'RR z)
      (fact 'fun-apply-type-c 'f '(CCINT a b) 'RR z)
      (subst (list '= (list 'f z) (list 'g z)))
      (rfl))))
(fact 'regulated-on-restrict 'g 'a 'b 'a 'b 'f)
(ass)
(qed 'regulated-on-congruence)

;;; =====================================================================
;;; (3) A CONTINUOUS FUNCTION OF A PATH: its coordinates are continuous on
;;; [a, b], hence regulated.  The mechanics are those of the continuity
;;; section of `line-int-of-derivative' (line-int-fundamental.scm), with the
;;; continuity of f on U a HYPOTHESIS in the shape `diff-on-implies-continuous'
;;; delivers.
;;; =====================================================================

(define rga-nfc '(NF-METRIC-SPACE CC-NORMED-FIELD))
(define rga-cc '(CCINT a b))
(define rga-scc (list 'SUBSPACE-MS 'RR-MS rga-cc))
(define (rga-plam body) (list 'VNB-LAMBDA 'pat_ rga-cc body))
(define rga-pfr (rga-plam '(real-part (f (pgam pat_)))))
(define rga-pfi (rga-plam '(imag-part (f (pgam pat_)))))
(define (rga-lam-b-if!) (if (dk--redex? (dk-goal)) (dk-lam-b!)))

(define (rga-cc-setup!)
  (fact 'cc-is-normed-field)
  (fact 'cc-is-metric-space)
  (fact 'nf-cc-is-metric-space)
  (fact 'nf-cc-agree-pts)
  (fact 'nf-cc-agree-dist)
  (fact 'ms-agree-pts-sym 'CC-MS rga-nfc)
  (fact 'ms-agree-dist-sym 'CC-MS rga-nfc)
  (fact 'cc-nf-carr)
  (dk-have! '(== (PTS CC-MS) CC) (lambda () (slot 'PTS) (qrfl))))

;;; the interval as a subspace of the line, and the path's read-offs.
(define (rga-path-setup!)
  (rga-cc-setup!)
  (fact 'rr-is-metric-space)
  (fact 'rr-is-set)
  (dk-have! '(== (PTS RR-MS) RR) (lambda () (slot 'PTS) (qrfl)))
  (fact 'is-path-in-fun 'pgam 'a 'b)
  (dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
  (dk-split-all!)
  (fact 'ccint-subset-rr 'a 'b)
  (fact 'subclass-of-set-is-set rga-cc 'RR)
  (dk-have! (list 'SUBSET rga-cc '(PTS RR-MS)) (lambda () (subst '(== (PTS RR-MS) RR)) (ass)))
  (fact 'subspace-is-metric-space 'RR-MS rga-cc)
  (fact 'subspace-pts 'RR-MS rga-cc)
  ;; the trace lies in u, pointwise.
  (dk-have! (list 'FORALL 'msy_ (list 'IMPLIES (list 'IN 'msy_ rga-cc) '(IN (pgam msy_) u)))
    (lambda ()
      (let ((y (dk-di-var!)))
        (fact 'trace-value-in 'pgam 'a 'b y)
        (fact 'subset-mem-fwd '(TRACE pgam a b) 'u (list 'pgam y))
        (ass)))))

(define (rga-pgu)
  (dk-pick (lambda (fm) (and (eq? (rga-head fm) 'FORALL) (dk-contains? fm 'msy_)
                             (dk-contains? fm '(pgam msy_))
                             (not (dk-contains? fm 'PTS))))
           "the trace lies in u"))

;;; a point y of [a, b]: the typings of everything evaluated there.
(define (rga-pt! y)
  (fact 'fun-apply-type-c 'pgam rga-cc 'CC y)
  (if (not (dk-ctx-form (list 'IN (list 'pgam y) 'u))) (dk-apply! (rga-pgu) y))
  (fact 'fun-apply-type-c 'f 'u 'CC (list 'pgam y))
  (fact 'real-part-in-rr (list 'f (list 'pgam y)))
  (fact 'imag-part-in-rr (list 'f (list 'pgam y))))

;;; typing of a lambda over [a, b] into RR.
(define (rga-ptype! claim point!)
  (dk-have! claim
    (lambda ()
      (for-each
       (lambda (leaf)
         (if (not (sequent-node-grounded? leaf))
             (begin
               (dk-focus! leaf)
               (if (not (eq? (rga-head (dk-goal)) 'FORALL))
                   (ass)
                   (let ((y (dk-di-var!)))
                     (point! y)
                     (rga-lam-b-if!)
                     ;; beta may leave a goal already in context, which is
                     ;; then grounded and the focus has moved on.
                     (if (not (sequent-node-grounded? leaf)) (ass)))))))
       (dk-opened (lambda () (lam-t)))))))

;;; the continuity of f o gamma at y, and the coordinate iff; returns
;;; (iff . continuity).  FCONT is f's continuity hypothesis, PCONT the path's.
(define (rga-f-cont! y fcont pcont)
  (rga-pt! y)
  (dk-have! (list 'IN y (list 'PTS rga-scc))
    (lambda () (subst (list '== (list 'PTS rga-scc) rga-cc)) (ass)))
  (dk-apply! pcont y)
  (dk-apply! fcont (list 'pgam y))
  (let* ((r (dk-fact! 'cc-compose-continuous-at rga-scc 'u 'pgam 'f y))
         (c (if (and (pair? r) (eq? (car r) 'IS-CONTINUOUS-AT))
                (list-ref r 3)
                (error "rga-f-cont!: cc-compose-continuous-at did not detach" r))))
    (dk-have! (list 'IN c (list 'FUN (list 'PTS rga-scc) 'CC))
      (lambda ()
        (fact 'ms-pts-is-set rga-scc)
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (not (eq? (rga-head (dk-goal)) 'FORALL))
               (ass)
               (let ((z (dk-di-var!)))
                 (dk-have! (list 'IN z rga-cc)
                   (lambda () (subst (list '= rga-cc (list 'PTS rga-scc))) (ass)))
                 (rga-pt! z)
                 (ass))))
         (dk-opened (lambda () (lam-t))))))
    (dk-have! (list 'IN rga-pfr (list 'FUN (list 'PTS rga-scc) 'RR))
      (lambda () (subst (list '== (list 'PTS rga-scc) rga-cc)) (ass)))
    (dk-have! (list 'IN rga-pfi (list 'FUN (list 'PTS rga-scc) 'RR))
      (lambda () (subst (list '== (list 'PTS rga-scc) rga-cc)) (ass)))
    (for-each
     (lambda (proj fl)
       (dk-have! (list 'FORALL 'u_ (list 'IMPLIES (list 'IN 'u_ (list 'PTS rga-scc))
                   (list '= (list proj (list c 'u_)) (list fl 'u_))))
         (lambda ()
           (let ((z (dk-di-var!)))
             (dk-have! (list 'IN z rga-cc)
               (lambda () (subst (list '= rga-cc (list 'PTS rga-scc))) (ass)))
             (rga-pt! z)
             (dk-lam-b!)
             (rfl)))))
     '(real-part imag-part) (list rga-pfr rga-pfi))
    (let ((iff (dk-fact! 'cc-continuous-at-iff-coords rga-scc c rga-pfr rga-pfi y)))
      (if (not (and (pair? iff) (eq? (car iff) 'IFF)))
          (error "rga-f-cont!: cc-continuous-at-iff-coords did not detach" iff))
      (cons iff r))))

(define (rga-comp-cont-on!)
  (dk-peel!)
  (let ((fcont (dk-pick (lambda (fm) (and (eq? (rga-head fm) 'FORALL)
                                          (dk-contains? fm 'IS-CONTINUOUS-AT)
                                          (dk-contains? fm 'rgy_)))
                        "the continuity of f on u")))
    (rga-path-setup!)
    (let* ((pcont (dk-fact! 'is-path-continuous 'pgam 'a 'b))
           (both (list 'FORALL 'rgp_ (list 'IMPLIES (list 'IN 'rgp_ rga-cc)
                   (list 'AND (list 'IS-CONTINUOUS-AT rga-scc 'RR-MS rga-pfr 'rgp_)
                              (list 'IS-CONTINUOUS-AT rga-scc 'RR-MS rga-pfi 'rgp_))))))
      (dk-have! (list 'FORALL 'msy_ (list 'IMPLIES (list 'IN 'msy_ (list 'PTS rga-scc))
                  '(IN (pgam msy_) u)))
        (lambda ()
          (let ((y (dk-di-var!)))
            (dk-have! (list 'IN y rga-cc)
              (lambda () (subst (list '= rga-cc (list 'PTS rga-scc))) (ass)))
            (dk-apply! (rga-pgu) y)
            (ass))))
      (dk-have! (list 'IN 'pgam (list 'FUN (list 'PTS rga-scc) 'CC))
        (lambda () (subst (list '== (list 'PTS rga-scc) rga-cc)) (ass)))
      (rga-ptype! (list 'IN rga-pfr (list 'FUN rga-cc 'RR)) rga-pt!)
      (rga-ptype! (list 'IN rga-pfi (list 'FUN rga-cc 'RR)) rga-pt!)
      (dk-have! both
        (lambda ()
          (let* ((y (dk-di-var!))
                 (ir (rga-f-cont! y fcont pcont)))
            (dk-only! (car ir) (cdr ir))
            (prop))))
      (for-each
       (lambda (fl)
         (dk-have! (list 'IS-CONTINUOUS-ON fl rga-cc)
           (lambda ()
             (mac 'IS-CONTINUOUS-ON)
             (dk-conj-close!
              (lambda ()
                (if (not (eq? (rga-head (dk-goal)) 'FORALL))
                    (ass)
                    (let ((y (dk-di-var!)))
                      (dk-split-all! (list (dk-apply! (dk-ctx-form both) y)))
                      (ass))))))))
       (list rga-pfr rga-pfi)))))

(define rga-comp-hyps
  "forall([u, f, pgam, a, b], subset(u, cc) implies f in fun(u, cc) implies
   forall([rgy_ in u], is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u),
                                        nf-metric-space(cc-normed-field), f, rgy_)) implies
   is-path(pgam, a, b) implies subset(trace(pgam, a, b), u) implies ")

(sp (make-wff (string-append rga-comp-hyps
   "is-continuous-on(vnb-lambda(pat_, ccint(a, b), real-part(f(pgam(pat_)))), ccint(a, b)) and
    is-continuous-on(vnb-lambda(pat_, ccint(a, b), imag-part(f(pgam(pat_)))), ccint(a, b)))")))
(rga-comp-cont-on!)
(dk-conj-close! (lambda () (ass)))
(qed 'continuous-on-compose-path)

(sp (make-wff (string-append rga-comp-hyps
   "is-regulated-on(vnb-lambda(pat_, ccint(a, b), real-part(f(pgam(pat_)))), a, b) and
    is-regulated-on(vnb-lambda(pat_, ccint(a, b), imag-part(f(pgam(pat_)))), a, b))")))
(dk-peel!)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(dk-split-all! (list (dk-fact! 'continuous-on-compose-path 'u 'f 'pgam 'a 'b)))
(fact 'continuous-on-implies-regulated-on rga-pfr 'a 'b)
(fact 'continuous-on-implies-regulated-on rga-pfi 'a 'b)
(dk-conj-close! (lambda () (ass)))
(qed 'continuous-on-compose-regulated)

;;; =====================================================================
;;; (4) THE INTEGRAND OF A ROAD IS REGULATED.
;;;   re(f(gamma) dgamma) = re(f o gamma) re(dgamma) - im(f o gamma) im(dgamma)
;;;   im(f(gamma) dgamma) = re(f o gamma) im(dgamma) + im(f o gamma) re(dgamma)
;;; (`cc-re-mul', `cc-im-mul'): products and a sum / difference of regulated
;;; functions, the factors from (3) and from the road (`is-road-re-regulated',
;;; `is-road-im-regulated').
;;; =====================================================================

(define rga-pdr (rga-plam '(real-part (dgam pat_))))
(define rga-pdi (rga-plam '(imag-part (dgam pat_))))
(define rga-tre (rga-plam '(real-part (* (f (pgam pat_)) (dgam pat_)))))
(define rga-tim (rga-plam '(imag-part (* (f (pgam pat_)) (dgam pat_)))))
(define (rga-vlam body) (list 'VNB-LAMBDA 'rgv_ rga-cc body))
(define (rga-fr v) (list 'real-part (list 'f (list 'pgam v))))
(define (rga-fi v) (list 'imag-part (list 'f (list 'pgam v))))
(define (rga-dr v) (list 'real-part (list 'dgam v)))
(define (rga-di v) (list 'imag-part (list 'dgam v)))
(define rga-p1 (rga-vlam (list '* (rga-fr 'rgv_) (rga-dr 'rgv_))))
(define rga-p2 (rga-vlam (list '* (rga-fi 'rgv_) (rga-di 'rgv_))))
(define rga-p3 (rga-vlam (list '* (rga-fr 'rgv_) (rga-di 'rgv_))))
(define rga-p4 (rga-vlam (list '* (rga-fi 'rgv_) (rga-dr 'rgv_))))

(define (rga-and! a b)
  (dk-have! (list 'AND a b) (lambda () (dk-conj-close! (lambda () (ass))))))

;;; a point y of [a, b], for the road: everything evaluated there typed.
(define (rga-rpt! y)
  (rga-pt! y)
  (let ((fy (list 'f (list 'pgam y))) (dy (list 'dgam y)))
    (fact 'fun-apply-type-c 'dgam rga-cc 'CC y)
    (fact 'real-part-in-rr dy)
    (fact 'imag-part-in-rr dy)
    (for-each (lambda (p q) (fact 'rr-mul-in-rr p q))
              (list (rga-fr y) (rga-fi y) (rga-fr y) (rga-fi y))
              (list (rga-dr y) (rga-di y) (rga-di y) (rga-dr y)))
    (rga-and! (list 'IN fy 'CC) (list 'IN dy 'CC))
    (fact 'cc-mul-closed fy dy)
    (fact 'real-part-in-rr (list '* fy dy))
    (fact 'imag-part-in-rr (list '* fy dy))))

;;; the agreement forall z in [a, b]. H(z) == RHS(z), by beta and CLOSE!.
(define (rga-agree! h rhs close!)
  (dk-have! (list 'FORALL 'rgz_ (list 'IMPLIES (list 'IN 'rgz_ rga-cc)
              (list '== (list h 'rgz_) (rhs 'rgz_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (rga-rpt! z)
        (dk-lam-b!)
        (close! z)))))

(define rga-road-hyps
  "forall([u, f, pgam, dgam, a, b], subset(u, cc) implies f in fun(u, cc) implies
   forall([rgy_ in u], is-continuous-at(subspace-ms(nf-metric-space(cc-normed-field), u),
                                        nf-metric-space(cc-normed-field), f, rgy_)) implies
   is-road(pgam, dgam, a, b) implies subset(trace(pgam, a, b), u) implies ")

;;; the common opening of (4) and (5): the four regulated factors, typed.
(define (rga-road-open!)
  (dk-peel!)
  (fact 'is-road-is-path 'pgam 'dgam 'a 'b)
  (fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
  (rga-path-setup!)
  (dk-split-all! (list (dk-fact! 'continuous-on-compose-regulated 'u 'f 'pgam 'a 'b)))
  (fact 'is-road-re-regulated 'pgam 'dgam 'a 'b)
  (fact 'is-road-im-regulated 'pgam 'dgam 'a 'b)
  (for-each (lambda (lam) (rga-ptype! (list 'IN lam (list 'FUN rga-cc 'RR)) rga-rpt!))
            (list rga-pfr rga-pfi rga-pdr rga-pdi rga-p1 rga-p2 rga-p3 rga-p4 rga-tre rga-tim))
  (for-each
   (lambda (p f1 g1)
     (rga-agree! p (lambda (z) (list '* (list f1 z) (list g1 z)))
                 (lambda (z) (qrfl)))
     (fact 'regulated-on-mul f1 g1 p 'a 'b))
   (list rga-p1 rga-p2 rga-p3 rga-p4)
   (list rga-pfr rga-pfi rga-pfr rga-pfi)
   (list rga-pdr rga-pdi rga-pdi rga-pdr))
  (rga-agree! rga-tre (lambda (z) (list '- (list rga-p1 z) (list rga-p2 z)))
    (lambda (z)
      (subst (dk-fact! 'cc-re-mul (list 'f (list 'pgam z)) (list 'dgam z)))
      (qrfl)))
  (fact 'regulated-on-sub rga-p1 rga-p2 rga-tre 'a 'b)
  (rga-agree! rga-tim (lambda (z) (list '+ (list rga-p3 z) (list rga-p4 z)))
    (lambda (z)
      (subst (dk-fact! 'cc-im-mul (list 'f (list 'pgam z)) (list 'dgam z)))
      (qrfl)))
  (fact 'regulated-on-sum rga-p3 rga-p4 rga-tim 'a 'b))

(sp (make-wff (string-append rga-road-hyps
   "is-regulated-on(vnb-lambda(pat_, ccint(a, b), real-part(f(pgam(pat_)) * dgam(pat_))), a, b) and
    is-regulated-on(vnb-lambda(pat_, ccint(a, b), imag-part(f(pgam(pat_)) * dgam(pat_))), a, b))")))
(rga-road-open!)
(dk-conj-close! (lambda () (ass)))
(qed 'road-integrand-regulated)

;;; =====================================================================
;;; (5) THE INTEGRAL ALONG A ROAD EXISTS: the two IS-PRIMITIVE facts that
;;; every cc-int / line-int law takes as antecedents (`cc-int-value',
;;; `line-int-opposite'), in exactly their shape -- the integrand is LINE-INT's
;;; own lambda, applied.  By `regulated-on-has-primitive' (8.7.2) twice, after
;;; `regulated-on-congruence' from the beta-reduced integrand of (4).
;;; =====================================================================

(define (rga-exists! )
  (dk-peel!)
  (dk-split-all! (list (dk-fact! 'road-integrand-regulated 'u 'f 'pgam 'dgam 'a 'b)))
  (fact 'is-road-is-path 'pgam 'dgam 'a 'b)
  (fact 'is-road-dgam-in-fun 'pgam 'dgam 'a 'b)
  (rga-path-setup!)
  (let* ((g0 (dk-goal))
         (conj (caddr (caddr g0)))
         (nre (list-ref (cadr conj) 2))
         (nim (list-ref (caddr conj) 2)))
    (for-each
     (lambda (n tt)
       (rga-ptype! (list 'IN n (list 'FUN rga-cc 'RR)) rga-rpt!)
       (rga-agree! n (lambda (z) (list tt z)) (lambda (z) (qrfl)))
       (fact 'regulated-on-congruence n tt 'a 'b))
     (list nre nim) (list rga-tre rga-tim))
    (let* ((g1 (dk-skolem! (dk-fact! 'regulated-on-has-primitive 'a 'b nre)))
           (g2 (dk-skolem! (dk-fact! 'regulated-on-has-primitive 'a 'b nim))))
      (ew g1)
      (ew g2)
      (dk-conj-close! (lambda () (ass))))))

(sp (make-wff (string-append rga-road-hyps
   "forsome([pwf_, paw_],
      is-primitive(pwf_, vnb-lambda(pat_, ccint(a, b),
        real-part((vnb-lambda(pat_, ccint(a, b), f(pgam(pat_)) * dgam(pat_)))(pat_))), a, b) and
      is-primitive(paw_, vnb-lambda(pat_, ccint(a, b),
        imag-part((vnb-lambda(pat_, ccint(a, b), f(pgam(pat_)) * dgam(pat_)))(pat_))), a, b)))")))
(rga-exists!)
(qed 'line-int-exists)

;;; the first consumer: the integral along a road of a continuous f is a
;;; complex number (`cc-int-in-cc', with the primitives of (5)).
(sp (make-wff (string-append rga-road-hyps "line-int(f, pgam, dgam, a, b) in cc)")))
(dk-peel!)
(fact 'is-road-is-path 'pgam 'dgam 'a 'b)
(dk-split! (dk-fact! 'is-path-endpoints 'pgam 'a 'b))
(dk-split-all!)
(define rga-ex (dk-fact! 'line-int-exists 'u 'f 'pgam 'dgam 'a 'b))
(define rga-w1 (dk-skolem! rga-ex))
(define rga-w2 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the second primitive")))
(dk-split-all!)
(mac 'LINE-INT)
(fact 'cc-int-in-cc 'a 'b (cadr (cadr (dk-goal))) rga-w1 rga-w2)
(ass)
(qed 'line-int-in-cc)
