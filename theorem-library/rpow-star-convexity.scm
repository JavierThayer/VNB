;;; theorem-library/rpow-star-convexity.scm -- the two REAL inequalities of the
;;; axiomatic RPOW, proved for the DEFINED power RPOW-STAR (rpow-star.scm):
;;;
;;;   bernoulli-rpow-star     0 < 1 + x, 1 <= b (b REAL)  =>  1 + b.x <= (1+x)^b
;;;   young-inequality-star   0 < a, 0 < b, 1 < p, 1 < q (REAL), 1/p + 1/q = 1
;;;                             =>  a.b <= a^p/p + b^q/q
;;;
;;; Both are the concavity of LOG.  The one analytic input is the tangent line
;;; of R-EXP at 0, proved here from the mean value theorem:
;;;
;;;   r-exp-ge-one-plus       1 + z <= exp(z)          (mvt-lower / -upper-bound)
;;;   log-le-minus-one        0 < w  =>  log w <= w - 1
;;;   log-jensen-two          0 < u, v; 0 < s, t; s + t = 1
;;;                             =>  s.log u + t.log v <= log(s.u + t.v)
;;;
;;; The weighted two-point Jensen inequality is log-le-minus-one at u/m and v/m,
;;; m = s.u + t.v, weighted by s and t and added.  Young is Jensen at
;;; u = a^p, v = b^q, s = 1/p, t = 1/q (s.log u = log a), exponentiated.
;;; Bernoulli (b > 1) is Jensen at u = (1+x)^b, v = 1, s = 1/b, t = 1 - 1/b:
;;; log(1+x) <= log(s.y + t), so 1 + x <= y/b + 1 - 1/b, times b; b = 1 is
;;; rpow-star-one.
;;;
;;; NOTHING IS ASSERTED.  All five bill `modulo 0' on the band of 2026-10-03.
;;; Every compound product that `ineq' would drop is NAMED with dk-name! first.
;;; Loads after theorem-library/rpow-star (which needs r-exp, log, recip-star,
;;; rr-order-basics) and the mvt bounds.

;;; ---- file-local helpers (prefix rsc-) ---------------------------------

(define (rsc-check name)
  (if (not (proof-done? *ps*))
      (error "rpow-star-convexity: proof did not close" name
             (expression->string (dk-goal)))))

;;; (IN t RR) by the closure laws, its atoms typed in context first
(define (rsc-type! t)
  (dk-have! (list 'IN t 'RR) (lambda () (type-term))))

(define (rsc-and . fs)
  (let build ((fs fs))
    (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (build (cdr fs))))))

;;; the conjunctive antecedent, landed whole (`fact' will not split one)
(define (rsc-need! . fs)
  (dk-have! (apply rsc-and fs) (lambda () (dk-conj-close! (lambda () (ass))))))

(define rsc-ef '(VNB-LAMBDA y_ RR (R-EXP y_)))

;;; (F t) = R-EXP(t), t typed
(define (rsc-redex! t)
  (fact 'r-exp-in-rr t)
  (dk-have! (list '= (list rsc-ef t) (list 'R-EXP t))
    (lambda () (if (not (dk-lam-b!)) (rfl)))))

;;; the mvt bound for F on [a, b], a < b in context: lower? -- derivative >= 1
;;; (0 <= the interval), else derivative <= 1 (the interval <= 0).  Returns
;;; the landed bound.
(define (rsc-mvt! lower? a b)
  (fact 'r-exp-lam-in-fun)
  (fact 'rr-one-in) (fact 'rr-zero-in)
  (fact 'r-exp-zero) (fact 'r-exp-in-rr 0)
  (rsc-need! (list 'IN rsc-ef '(FUN RR RR)) (list 'IN a 'RR) (list 'IN b 'RR)
             '(IN 1 RR) (list '< a b))
  (dk-have! (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x (list 'CCINT a b))
                                   (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS rsc-ef 'x)))
    (lambda ()
      (let ((v (dk-di-var!)))
        (fact 'ccint-elt-in-rr a b v)
        (fact 'r-exp-continuous-at v)
        (ass))))
  (dk-have! (list 'FORALL 'x
              (list 'IMPLIES (rsc-and '(IN x RR) (list '< a 'x) (list '< 'x b))
                (list 'FORSOME 'L (list 'AND (list 'IS-DIFF-AT rsc-ef 'x 'L)
                                        (if lower? '(<= 1 L) '(<= L 1))))))
    (lambda ()
      (di)
      (let* ((lnd (dk-landed-1 (lambda () (di))))
             (v   (cadr (cadr lnd))))
        (dk-split! lnd)
        (fact 'r-exp-in-rr v)
        (fact 'r-exp-deriv v)
        (if lower?
            (begin (fact 'rr-lt-implies-le 0 v)
                   (fact 'r-exp-mono 0 v))
            (begin (fact 'rr-lt-implies-le v 0)
                   (fact 'r-exp-mono v 0)))
        (ew (list 'R-EXP v))
        (dk-conj-close!
          (lambda ()
            (if (dk-head-is? (dk-goal) 'IS-DIFF-AT)
                (ass)
                (if lower?
                    (dk-ineq! (list '<= '(R-EXP 0) (list 'R-EXP v)) '(= (R-EXP 0) 1))
                    (dk-ineq! (list '<= (list 'R-EXP v) '(R-EXP 0)) '(= (R-EXP 0) 1)))))))))
  (dk-fact! (if lower? 'mvt-lower-bound 'mvt-upper-bound) rsc-ef a b 1))

;;; =====================================================================
;;; 1.  THE TANGENT LINE OF EXP AT 0:  1 + z <= exp(z).
;;; =====================================================================

(sp (make-wff '(FORALL rsz_ (IMPLIES (IN rsz_ RR) (<= (+ 1 rsz_) (R-EXP rsz_))))))
(dk-peel!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(fact 'r-exp-in-rr 'rsz_) (fact 'r-exp-in-rr 0) (fact 'r-exp-zero)
(use-cases (dk-fact! 'rr-lt-trichotomy 'rsz_ 0)
  (lambda ()                                     ; z < 0: exp' <= 1 on [z, 0]
    (let ((bd (rsc-mvt! #f 'rsz_ 0)))
      (rsc-redex! 'rsz_) (rsc-redex! 0)
      (dk-lam-b-h! bd)
      (dk-ineq! '(<= (- (R-EXP 0) (R-EXP rsz_)) (* 1 (- 0 rsz_)))
                '(= (R-EXP 0) 1))))
  (lambda ()                                     ; z = 0
    (subst '(= rsz_ 0))
    (dk-ineq! '(= (R-EXP 0) 1)))
  (lambda ()                                     ; 0 < z: exp' >= 1 on [0, z]
    (let ((bd (rsc-mvt! #t 0 'rsz_)))
      (rsc-redex! 'rsz_) (rsc-redex! 0)
      (dk-lam-b-h! bd)
      (dk-ineq! '(<= (* 1 (- rsz_ 0)) (- (R-EXP rsz_) (R-EXP 0)))
                '(= (R-EXP 0) 1)))))
(rsc-check 'r-exp-ge-one-plus)
(qed 'r-exp-ge-one-plus)
(topic! 'r-exp-ge-one-plus 'analysis)
(alias! 'r-exp-ge-one-plus "the exponential lies above its tangent at 0"
        "1 + z <= exp(z)")

;;; =====================================================================
;;; 2.  log w <= w - 1.
;;; =====================================================================

(sp (make-wff '(FORALL rsw_ (IMPLIES (IN rsw_ RR)
                 (IMPLIES (< 0 rsw_) (<= (LOG rsw_) (- rsw_ 1)))))))
(dk-peel!)
(fact 'log-in-rr 'rsw_)
(fact 'r-exp-ge-one-plus '(LOG rsw_))
(fact 'r-exp-log 'rsw_)
(fact 'r-exp-in-rr '(LOG rsw_))
(fact 'rr-one-in)
(dk-ineq! '(<= (+ 1 (LOG rsw_)) (R-EXP (LOG rsw_))) '(= (R-EXP (LOG rsw_)) rsw_))
(rsc-check 'log-le-minus-one)
(qed 'log-le-minus-one)
(topic! 'log-le-minus-one 'analysis)
(alias! 'log-le-minus-one "the logarithm lies below its tangent at 1"
        "log w <= w - 1")

;;; =====================================================================
;;; 3.  TWO-POINT JENSEN FOR LOG:  s.log u + t.log v <= log(s.u + t.v).
;;;
;;; m = s.u + t.v > 0, R = 1/m (NAMED: crs declines recip), U = u.R, V = v.R
;;; (NAMED: ineq drops a compound product).  log U <= U - 1 and
;;; log V <= V - 1; with K1 = U - 1 - log U >= 0, K2 = V - 1 - log V >= 0,
;;; 0 <= s.K1 + t.K2 = (s.U + t.V) - (s + t) - s.log U - t.log V
;;;                 = 1 - 1 - s.log u - t.log v - log R
;;; and log R = -log m.
;;; =====================================================================

(sp (make-wff
  '(FORALL rsu_ (IMPLIES (IN rsu_ RR) (FORALL rsv_ (IMPLIES (IN rsv_ RR)
    (FORALL rss_ (IMPLIES (IN rss_ RR) (FORALL rst_ (IMPLIES (IN rst_ RR)
     (IMPLIES (< 0 rsu_) (IMPLIES (< 0 rsv_) (IMPLIES (< 0 rss_) (IMPLIES (< 0 rst_)
      (IMPLIES (= (+ rss_ rst_) 1)
       (<= (+ (* rss_ (LOG rsu_)) (* rst_ (LOG rsv_)))
           (LOG (+ (* rss_ rsu_) (* rst_ rsv_)))))))))))))))))))
(dk-peel!)
(let* ((u 'rsu_) (v 'rsv_) (s 'rss_) (t 'rst_)
       (su (list '* s u)) (tv (list '* t v))
       (m  (list '+ su tv)))
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-mul-in-rr s u) (fact 'rr-mul-in-rr t v)
  (fact 'rr-mul-pos s u) (fact 'rr-mul-pos t v)
  (rsc-type! m)
  (dk-have! (list '< 0 m) (lambda () (dk-ineq! (list '< 0 su) (list '< 0 tv))))
  (fact 'rr-pos-ne-zero m)
  (rsc-need! (list 'IN m 'RR) (list 'NOT (list '= m 0)))
  (fact 'rr-recip-closed m)
  (fact 'rr-recip-inverse m)
  (fact 'rr-recip-pos m)
  (let* ((r  (dk-name! (list 'RECIP m)))
         (re (list '= r (list 'RECIP m))))
    (dk-have! (list '< 0 r) (lambda () (subst re) (ass)))
    (dk-have! (list '= (list '* m r) 1) (lambda () (subst re) (ass)))
    (fact 'rr-mul-in-rr u r) (fact 'rr-mul-in-rr v r)
    (fact 'rr-mul-pos u r) (fact 'rr-mul-pos v r)
    (let* ((uu (dk-name! (list '* u r)))
           (vv (dk-name! (list '* v r)))
           (ue (list '= uu (list '* u r)))
           (ve (list '= vv (list '* v r))))
      (dk-have! (list '< 0 uu) (lambda () (subst ue) (ass)))
      (dk-have! (list '< 0 vv) (lambda () (subst ve) (ass)))
      (for-each (lambda (x) (fact 'log-in-rr x)) (list u v r m uu vv))
      (fact 'log-le-minus-one uu)
      (fact 'log-le-minus-one vv)
      ;; log U = log u + log R, log V = log v + log R
      (fact 'log-mul u r) (fact 'log-mul v r)
      (dk-have! (list '= (list 'LOG uu) (list '+ (list 'LOG u) (list 'LOG r)))
        (lambda () (subst ue) (ass)))
      (dk-have! (list '= (list 'LOG vv) (list '+ (list 'LOG v) (list 'LOG r)))
        (lambda () (subst ve) (ass)))
      ;; log m + log R = 0
      (fact 'log-mul m r)
      (fact 'log-one)
      (dk-have! (list '= (list '+ (list 'LOG m) (list 'LOG r)) 0)
        (lambda ()
          (subst (list '= (list '+ (list 'LOG m) (list 'LOG r)) (list 'LOG (list '* m r))))
          (subst (list '= (list '* m r) 1))
          (ass)))
      ;; s.U + t.V = 1
      (dk-have! (list '= (list '+ (list '* s uu) (list '* t vv)) 1)
        (lambda ()
          (subst ue) (subst ve)
          (let ((id (list '= (list '+ (list '* s (list '* u r)) (list '* t (list '* v r)))
                             (list '* m r))))
            (dk-have! id (lambda () (crs)))
            (subst id)
            (ass))))
      ;; the two nonnegative gaps, named, and scaled
      (let ((g1 (list '- (list '- uu 1) (list 'LOG uu)))
            (g2 (list '- (list '- vv 1) (list 'LOG vv))))
        (rsc-type! g1) (rsc-type! g2)
        (let* ((k1 (dk-name! g1)) (k2 (dk-name! g2))
               (k1e (list '= k1 g1)) (k2e (list '= k2 g2)))
          (dk-have! (list '<= 0 k1)
            (lambda () (dk-ineq! k1e (list '<= (list 'LOG uu) (list '- uu 1)))))
          (dk-have! (list '<= 0 k2)
            (lambda () (dk-ineq! k2e (list '<= (list 'LOG vv) (list '- vv 1)))))
          (fact 'rr-lt-implies-le 0 s) (fact 'rr-lt-implies-le 0 t)
          (rsc-need! (list 'IN s 'RR) (list 'IN k1 'RR))
          (rsc-need! (list '<= 0 s) (list '<= 0 k1))
          (fact 'rr-leq-mul-nonneg s k1)
          (rsc-need! (list 'IN t 'RR) (list 'IN k2 'RR))
          (rsc-need! (list '<= 0 t) (list '<= 0 k2))
          (fact 'rr-leq-mul-nonneg t k2)
          ;; the products, expanded about the named atoms
          (let ((e1 (list '= (list '* s k1)
                          (list '- (list '- (list '* s uu) s)
                                (list '+ (list '* s (list 'LOG u)) (list '* s (list 'LOG r))))))
                (e2 (list '= (list '* t k2)
                          (list '- (list '- (list '* t vv) t)
                                (list '+ (list '* t (list 'LOG v)) (list '* t (list 'LOG r))))))
                (e3 (list '= (list '+ (list '* s (list 'LOG r)) (list '* t (list 'LOG r)))
                          (list 'LOG r))))
            (dk-have! e1 (lambda ()
              (subst k1e)
              (subst (list '= (list 'LOG uu) (list '+ (list 'LOG u) (list 'LOG r))))
              (crs)))
            (dk-have! e2 (lambda ()
              (subst k2e)
              (subst (list '= (list 'LOG vv) (list '+ (list 'LOG v) (list 'LOG r))))
              (crs)))
            (dk-have! e3 (lambda ()
              (let ((id (list '= (list '+ (list '* s (list 'LOG r)) (list '* t (list 'LOG r)))
                              (list '* (list '+ s t) (list 'LOG r)))))
                (dk-have! id (lambda () (crs)))
                (subst id)
                (subst (list '= (list '+ s t) 1))
                (crs))))
            (for-each (lambda (x y) (fact 'rr-mul-in-rr x y))
                      (list s s s t t t s t)
                      (list uu (list 'LOG u) (list 'LOG r) vv (list 'LOG v) (list 'LOG r) k1 k2))
            (dk-ineq! (list '<= 0 (list '* s k1)) (list '<= 0 (list '* t k2))
                      e1 e2 e3
                      (list '= (list '+ (list '* s uu) (list '* t vv)) 1)
                      (list '= (list '+ s t) 1)
                      (list '= (list '+ (list 'LOG m) (list 'LOG r)) 0))))))))
(rsc-check 'log-jensen-two)
(qed 'log-jensen-two)
(topic! 'log-jensen-two 'analysis)
(alias! 'log-jensen-two "the logarithm is concave: two-point Jensen"
        "s.log u + t.log v <= log(s.u + t.v) for s + t = 1")

;;; =====================================================================
;;; 4.  YOUNG'S INEQUALITY for RPOW-STAR, real conjugate exponents.
;;;     Jensen at u = a^p, v = b^q, s = 1/p, t = 1/q:  s.log u = log a,
;;;     so log(a.b) <= log(u/p + v/q), and exp is increasing.
;;; =====================================================================

;;; X(SY) = W for a named reciprocal SY of P with P.SY = 1 and log X = P.W0:
;;; the claim (= (* SY (LOG X)) W0) proved on a lane.
(define (rsc-cancel! sy lx pw p w0)
  (dk-have! (list '= (list '* sy lx) w0)
    (lambda ()
      (subst (list '= lx (list '* p w0)))
      (let ((id (list '= (list '* sy (list '* p w0)) (list '* (list '* p sy) w0))))
        (dk-have! id (lambda () (crs)))
        (subst id)
        (subst pw)
        (crs)))))

(sp (make-wff
  '(FORALL a (IMPLIES (AND (IN a RR) (< 0 a)) (FORALL b (IMPLIES (AND (IN b RR) (< 0 b))
     (FORALL p (IMPLIES (AND (IN p RR) (< 1 p)) (FORALL q (IMPLIES (AND (IN q RR) (< 1 q))
       (IMPLIES (= (+ (/ 1 p) (/ 1 q)) 1)
         (<= (* a b) (+ (/ (RPOW-STAR a p) p) (/ (RPOW-STAR b q) q))))))))))))))
(dk-peel!)
(dk-split-all!)
(fact 'rr-zero-in) (fact 'rr-one-in)
(mac 'binary-divide-def)
(let* ((h  '(= (+ (/ 1 p) (/ 1 q)) 1))
       (h2 (car (filter (dk-head? '=) (dk-landed (lambda () (mac-h 'binary-divide-def h))))))
       (u '(RPOW-STAR a p)) (v '(RPOW-STAR b q)))
  (dk-have! '(< 0 p) (lambda () (dk-ineq! '(< 1 p))))
  (dk-have! '(< 0 q) (lambda () (dk-ineq! '(< 1 q))))
  (for-each (lambda (x)
              (fact 'rr-pos-ne-zero x)
              (rsc-need! (list 'IN x 'RR) (list 'NOT (list '= x 0)))
              (fact 'rr-recip-closed x)
              (fact 'rr-recip-inverse x)
              (fact 'rr-recip-pos x)
              (fact 'rr-one-mul (list 'RECIP x)))
            '(p q))
  (let* ((sp_ (dk-name! '(RECIP p))) (sq_ (dk-name! '(RECIP q)))
         (spe (list '= sp_ '(RECIP p))) (sqe (list '= sq_ '(RECIP q)))
         (ppw (list '= (list '* 'p sp_) 1)) (qqw (list '= (list '* 'q sq_) 1)))
    (dk-have! (list '< 0 sp_) (lambda () (subst spe) (ass)))
    (dk-have! (list '< 0 sq_) (lambda () (subst sqe) (ass)))
    (dk-have! ppw (lambda () (subst spe) (ass)))
    (dk-have! qqw (lambda () (subst sqe) (ass)))
    (dk-have! (list '= (list '+ sp_ sq_) 1)
      (lambda ()
        (subst spe) (subst sqe)
        (subst '(= (RECIP p) (* 1 (RECIP p))))
        (subst '(= (RECIP q) (* 1 (RECIP q))))
        (ass)))
    (fact 'rpow-star-in-rr 'a 'p) (fact 'rpow-star-in-rr 'b 'q)
    (fact 'rpow-star-pos 'a 'p) (fact 'rpow-star-pos 'b 'q)
    (fact 'log-rpow-star 'a 'p) (fact 'log-rpow-star 'b 'q)
    (for-each (lambda (x) (fact 'log-in-rr x)) (list 'a 'b u v))
    (let ((jn (dk-fact! 'log-jensen-two u v sp_ sq_))
          (m  (list '+ (list '* sp_ u) (list '* sq_ v))))
      (rsc-cancel! sp_ (list 'LOG u) ppw 'p '(LOG a))
      (rsc-cancel! sq_ (list 'LOG v) qqw 'q '(LOG b))
      (fact 'rr-mul-in-rr 'a 'b)
      (fact 'rr-mul-pos 'a 'b)
      (fact 'log-mul 'a 'b)
      (fact 'log-in-rr '(* a b))
      (fact 'rr-mul-in-rr sp_ u) (fact 'rr-mul-in-rr sq_ v)
      (fact 'rr-mul-pos sp_ u) (fact 'rr-mul-pos sq_ v)
      (rsc-type! m)
      (dk-have! (list '< 0 m)
        (lambda () (dk-ineq! (list '< 0 (list '* sp_ u)) (list '< 0 (list '* sq_ v)))))
      (fact 'log-in-rr m)
      (fact 'rr-mul-in-rr sp_ (list 'LOG u)) (fact 'rr-mul-in-rr sq_ (list 'LOG v))
      (dk-have! (list '<= '(LOG (* a b)) (list 'LOG m))
        (lambda ()
          (dk-ineq! jn
                    (list '= (list '* sp_ (list 'LOG u)) '(LOG a))
                    (list '= (list '* sq_ (list 'LOG v)) '(LOG b))
                    '(= (LOG (* a b)) (+ (LOG a) (LOG b))))))
      (fact 'r-exp-mono '(LOG (* a b)) (list 'LOG m))
      (fact 'r-exp-log '(* a b))
      (fact 'r-exp-log m)
      (fact 'r-exp-in-rr '(LOG (* a b))) (fact 'r-exp-in-rr (list 'LOG m))
      (dk-have! (list '<= '(* a b) m)
        (lambda ()
          (dk-ineq! (list '<= '(R-EXP (LOG (* a b))) (list 'R-EXP (list 'LOG m)))
                    '(= (R-EXP (LOG (* a b))) (* a b))
                    (list '= (list 'R-EXP (list 'LOG m)) m))))
      (subst (list '= '(RECIP p) sp_))
      (subst (list '= '(RECIP q) sq_))
      (rsc-need! (list 'IN u 'RR) (list 'IN sp_ 'RR))
      (rsc-need! (list 'IN v 'RR) (list 'IN sq_ 'RR))
      (fact 'rr-mul-comm u sp_) (fact 'rr-mul-comm v sq_)
      (fact 'rr-mul-in-rr u sp_) (fact 'rr-mul-in-rr v sq_)
      (dk-ineq! (list '<= '(* a b) m)
                (list '= (list '* u sp_) (list '* sp_ u))
                (list '= (list '* v sq_) (list '* sq_ v))))))
(rsc-check 'young-inequality-star)
(qed 'young-inequality-star)
(topic! 'young-inequality-star 'inequalities)
(alias! 'young-inequality-star "Young's inequality for the real power"
        "a.b <= a^p/p + b^q/q for conjugate real exponents")

;;; =====================================================================
;;; 5.  BERNOULLI'S INEQUALITY for RPOW-STAR, real exponent b >= 1.
;;;     b = 1 is rpow-star-one.  b > 1: Jensen at y = (1+x)^b, 1 with the
;;;     weights S = 1/b, T = 1 - S gives log(1+x) <= log(S.y + T), so
;;;     1 + x <= S.y + T; times b, b + b.x <= y + b - 1.
;;; =====================================================================

(sp (make-wff
  '(FORALL x (IMPLIES (AND (IN x RR) (< 0 (+ 1 x)))
     (FORALL b (IMPLIES (AND (IN b RR) (<= 1 b))
       (<= (+ 1 (* b x)) (RPOW-STAR (+ 1 x) b))))))))
(dk-peel!)
(dk-split-all!)
(fact 'rr-zero-in) (fact 'rr-one-in) (fact 'rr-zero-lt-one)
(rsc-type! '(+ 1 x))
(use-cases (dk-fact! 'rr-le-cases 1 'b)
  (lambda ()                                           ; 1 < b
    (let ((y '(RPOW-STAR (+ 1 x) b)) (lx '(LOG (+ 1 x))))
      (dk-have! '(< 0 b) (lambda () (dk-ineq! '(< 1 b))))
      (fact 'rr-pos-ne-zero 'b)
      (rsc-need! '(IN b RR) '(NOT (= b 0)))
      (fact 'rr-recip-closed 'b) (fact 'rr-recip-inverse 'b) (fact 'rr-recip-pos 'b)
      (fact 'rpow-star-in-rr '(+ 1 x) 'b) (fact 'rpow-star-pos '(+ 1 x) 'b)
      (fact 'log-rpow-star '(+ 1 x) 'b)
      (fact 'log-in-rr y) (fact 'log-in-rr '(+ 1 x)) (fact 'log-in-rr 1) (fact 'log-one)
      (let* ((s_ (dk-name! '(RECIP b))) (se (list '= s_ '(RECIP b)))
             (bw (list '= (list '* 'b s_) 1)))
        (dk-have! (list '< 0 s_) (lambda () (subst se) (ass)))
        (dk-have! bw (lambda () (subst se) (ass)))
        (rsc-need! (list '< 0 s_) '(< 1 b))
        (fact 'rr-lt-scale-pos s_ 1 'b)
        (rsc-need! '(IN b RR) (list 'IN s_ 'RR))
        (fact 'rr-mul-comm 'b s_)
        (fact 'rr-mul-in-rr s_ 'b) (fact 'rr-mul-in-rr 'b s_)
        (dk-have! (list '< s_ 1)
          (lambda () (dk-ineq! (list '< (list '* s_ 1) (list '* s_ 'b)) bw
                               (list '= (list '* 'b s_) (list '* s_ 'b)))))
        (rsc-type! (list '- 1 s_))
        (let* ((t_ (dk-name! (list '- 1 s_))) (te (list '= t_ (list '- 1 s_)))
               (m (list '+ (list '* s_ y) (list '* t_ 1))))
          (dk-have! (list '< 0 t_) (lambda () (dk-ineq! te (list '< s_ 1))))
          (dk-have! (list '= (list '+ s_ t_) 1) (lambda () (subst te) (crs)))
          (let ((jn (dk-fact! 'log-jensen-two y 1 s_ t_)))
            (rsc-cancel! s_ (list 'LOG y) bw 'b lx)
            (dk-have! (list '= (list '* t_ '(LOG 1)) 0)
              (lambda () (subst '(= (LOG 1) 0)) (crs)))
            (fact 'rr-mul-in-rr s_ y) (fact 'rr-mul-pos s_ y)
            (fact 'rr-mul-in-rr s_ (list 'LOG y)) (fact 'rr-mul-in-rr t_ '(LOG 1))
            (rsc-type! m)
            (dk-have! (list '< 0 m)
              (lambda () (dk-ineq! (list '< 0 (list '* s_ y)) (list '< 0 t_))))
            (fact 'log-in-rr m)
            (dk-have! (list '<= lx (list 'LOG m))
              (lambda ()
                (dk-ineq! jn (list '= (list '* s_ (list 'LOG y)) lx)
                          (list '= (list '* t_ '(LOG 1)) 0))))
            (fact 'r-exp-mono lx (list 'LOG m))
            (fact 'r-exp-log '(+ 1 x)) (fact 'r-exp-log m)
            (fact 'r-exp-in-rr lx) (fact 'r-exp-in-rr (list 'LOG m))
            (dk-have! (list '<= '(+ 1 x) m)
              (lambda ()
                (dk-ineq! (list '<= (list 'R-EXP lx) (list 'R-EXP (list 'LOG m)))
                          (list '= (list 'R-EXP lx) '(+ 1 x))
                          (list '= (list 'R-EXP (list 'LOG m)) m))))
            (fact 'rr-lt-implies-le 0 'b)
            (rsc-need! '(<= 0 b) (list '<= '(+ 1 x) m))
            (fact 'rr-le-scale-nonneg 'b '(+ 1 x) m)
            (fact 'rr-mul-in-rr 'b 'x)
            (dk-have! (list '<= '(+ b (* b x)) (list '- (list '+ y 'b) 1))
              (lambda ()
                (let ((id1 '(= (+ b (* b x)) (* b (+ 1 x))))
                      (id2 (list '= (list '- (list '+ y 'b) 1) (list '* 'b m))))
                  (dk-have! id1 (lambda () (crs)))
                  (dk-have! id2
                    (lambda ()
                      (subst te)
                      (let ((id3 (list '= (list '* 'b (list '+ (list '* s_ y) (list '* (list '- 1 s_) 1)))
                                       (list '- (list '+ (list '* (list '* 'b s_) y) 'b)
                                             (list '* 'b s_)))))
                        (dk-have! id3 (lambda () (crs)))
                        (subst id3)
                        (subst bw)
                        (crs))))
                  (subst id1)
                  (subst id2)
                  (ass))))
            (dk-ineq! (list '<= '(+ b (* b x)) (list '- (list '+ y 'b) 1))))))))
  (lambda ()                                           ; b = 1
    (subst '(= b 1))
    (fact 'rpow-star-one '(+ 1 x))
    (subst '(= (RPOW-STAR (+ 1 x) 1) (+ 1 x)))
    (fact 'rr-mul-in-rr 1 'x)
    (dk-ineq!)))
(rsc-check 'bernoulli-rpow-star)
(qed 'bernoulli-rpow-star)
(topic! 'bernoulli-rpow-star 'inequalities)
(alias! 'bernoulli-rpow-star "Bernoulli's inequality for the real power"
        "1 + b.x <= (1 + x)^b for 1 + x > 0 and real b >= 1")

