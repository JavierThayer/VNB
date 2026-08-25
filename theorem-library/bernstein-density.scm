;;; bernstein-density.scm -- THEOREM 5.2 of docs/calculus.pdf: a continuous
;;; function on [0,1] is the uniform limit of its Bernstein polynomials.
;;;
;;;   B_n f (x)  =  sum_{l=0}^{n} f(l/n) B_{l,n}(x)                      (74)
;;;   for every eps > 0 there is an N with
;;;     |f(x) - B_n f (x)| <= eps   for all n >= N and all x in [0,1]    (91)
;;;
;;; RUNG 2 of the integration arc, completed.  Proposition 5.4 -- the partition
;;; of unity (75) and the variance bound (76) -- is bernstein-basis.scm and
;;; bernstein-moments.scm; the analytic inputs (87) and M = sup|f| are
;;; uniform-continuity-ccint.scm and ccint-abs-bounded.scm.  This file is the
;;; estimate that joins them.
;;;
;;; NOT THE NOTES' NEAR/FAR SPLIT, and that is the whole design decision.  The
;;; notes (86)-(90) break the sum at |l/n - x| <= delta and bound the two blocks
;;; separately.  SERIES-PARTIAL-SUM has no predicate decomposition -- there is
;;; no way in this tree to split a partial sum on a condition over the index --
;;; so that route is not expressible at all.  What replaces it is ONE POINTWISE
;;; BOUND, uniform in l:
;;;
;;;   |f(x) - f(l/n)| . B_{l,n}(x)  <=  (h + c (l - n x)^2) . B_{l,n}(x)
;;;
;;; with c chosen so that c (n delta)^2 = 2M.  The case analysis is still there,
;;; but it happens INSIDE the universally quantified term bound
;;; (`bernstein-term-bound'), where it is an ordinary `rr-le-total' split on
;;; |x - l/n| against delta and neither branch mentions a sum:
;;;
;;;   near, |x - l/n| <= delta : (87) gives |f(x) - f(l/n)| <= h outright, and
;;;         the quadratic term is non-negative.
;;;   far,  delta <= |x - l/n| : delta^2 <= (x - l/n)^2, so c(l - nx)^2 >= 2M
;;;         >= |f(x) - f(l/n)| by the two M-bounds.
;;;
;;; Summing then costs three citations -- (75) for the constant part, (76) for
;;; the quadratic part, and `series-partial-sum-le-termwise-ptwise' to get from
;;; the pointwise bound to the sums -- instead of a decomposition the data
;;; structure cannot express.
;;;
;;; A THIRD CASE the notes do not mention, and it is forced by the same data
;;; structure: SERIES-PARTIAL-SUM(g, succ n) is a sum over an INITIAL SEGMENT,
;;; but its linearity laws quantify `forall k in NN', so the term bound has to
;;; hold at EVERY natural l, including l > n.  There it holds because
;;; B_{l,n}(x) = 0 (`bernstein-basis-above'), which is the only place the range
;;; of the basis is used.  The split l > n / l <= n is `use-em' on (n < l) plus
;;; `nn-not-lt-le'.
;;;
;;; THE GATE, and it turned out to be cheap.  `bernstein-basis-nonneg' -- every
;;; step of the estimate needs it -- was expected to be blocked at the base of
;;; its induction, where B_{k,0}(x) is IF k = 0 THEN 1 ELSE 0 and the index k
;;; ranges over ZZ, whose order theory this tree does not have.  It is not:
;;; the base needs no ORDER on the index at all, only EXCLUDED MIDDLE on the
;;; equation k = 0, and `if-true' / `if-false' then reduce the conditional in
;;; each branch.  The successor step needs one NN case split -- `nn-zero-or-succ'
;;; on k, because the Pascal recurrence reads the basis at k-1, which is -1
;;; when k is 0 -- and there `bernstein-basis-null' supplies the value.  No ZZ
;;; betweenness, no trichotomy, no embedding of ZZ in ORD.
;;;
;;; RECIPROCALS.  `ineq' turns a product of two non-constant factors into a
;;; single opaque ATOM and does not normalise monomials, so `l * recip(n)' and
;;; `recip(n) * l' are different atoms to it and neither is a linear consequence
;;; of the other.  Every reordering here is therefore an explicit `crs' identity
;;; substituted into the goal (`bd-rw!'), and `n * recip(n) = 1' is introduced
;;; by first rewriting the goal to a form that EXPOSES that product and then
;;; substituting for it -- the idiom bernstein-moments.scm uses for (76).
;;;
;;; WHY NOT `CONVERGES-UNIFORMLY'.  That predicate (ascoli-arzela-statement.scm)
;;; requires seq in FUN(NN, FUN(PTS s, RR)) for a metric SPACE s.  The domain
;;; here is CCINT(0,1), which is not a metric space in this tree -- the missing
;;; metric SUBSPACE structure that Heine-Borel also sits behind -- so the
;;; conclusion is written out, exactly as uniform-continuity-ccint.scm writes
;;; out uniform continuity and for the same reason.
;;;
;;; THE AFFINE TRANSFER to a general [a,b] (the notes' Corollary 5.7) is NOT
;;; here; it is a separate step off `compose-continuous-at'.
;;;
;;; Loads after bernstein-moments (the basis, its recurrence, the two vanishing
;;; laws, the partition and the variance bound), series-linearity
;;; (series-partial-sum-le-termwise-ptwise and the three linearity laws),
;;; uniform-continuity-ccint and ccint-abs-bounded.

;;; ---- file-local driver (the `bd-' prefix) ----------------------------

(define (bd-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 30))
          (begin (di) (loop (+ n 1))) #t))))

(define (bd-check name)
  (if (not (proof-done? *ps*))
      (error "bernstein-density: proof did not close" name
             (expression->string (dk-goal)))))

;;; the 1-based index of an assumption, for `ineq'.  The premises are NAMED,
;;; never scanned: `ineq' refuses a call in which ANY atom of ANY named premise
;;; is uncertified in RR, and this context is full of products that are atoms.
(define (bd-at f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bd-at: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (else (loop (cdr l) (+ i 1))))))
(define (bd-ineq! . fs) (apply ineq (map bd-at fs)))

;;; a = b as a ring identity, then rewrite a to b in the goal
(define (bd-eq! a b)
  (let ((e (list '= a b)))
    (if (not (member e (dk-asms))) (have! e (lambda () (crs))))
    e))
(define (bd-rw! a b) (subst (bd-eq! a b)))

;;; split  abs(t) <= c  in the context into its two order conjuncts
(define (bd-absplit! f)
  (let* ((nw (dk-landed* (lambda () (mac-h 'rr-abs-bound f))))
         (a  (car (filter (dk-head? 'AND) nw))))
    (filter (lambda (g) (and (pair? g) (memq (car g) '(< <=))))
            (dk-landed* (lambda () (dk-split! a))))))

;;; skolemize the newest FORSOME in the context and split the AND it lands
(define (bd-obtain!)
  (let ((a (car (dk-landed* (lambda () (dk-ai-head! 'FORSOME))))))
    (dk-landed* (lambda () (dk-split! a)))))
(define (bd-find ps h) (car (filter (dk-head? h) ps)))

;;; =====================================================================
;;; 1.  THE BERNSTEIN BASIS IS NON-NEGATIVE ON [0,1].
;;;
;;;   0 <= x <= 1,  k in NN   ==>   0 <= B_{k,n}(x)
;;;
;;; Induction on n.  The BASE is where the ZZ index was expected to bite and
;;; does not: B_{k,0}(x) is IF k = 0 THEN ONE ELSE ZERO, and `use-em' on the
;;; EQUATION k = 0 -- excluded middle, no order -- lets `if-true' / `if-false'
;;; reduce the conditional in each branch to 1 resp. 0.
;;;
;;; The STEP is the Pascal recurrence: B_{k,n+1}(x) = x B_{k-1,n}(x) +
;;; (1-x) B_{k,n}(x), with both coefficients non-negative on [0,1] and both
;;; values non-negative by the induction hypothesis -- EXCEPT that the shifted
;;; index k-1 is -1 when k is 0, which is outside NN and so outside the
;;; hypothesis.  `nn-zero-or-succ' splits on that: at k = 0 the value is 0 by
;;; `bernstein-basis-null', and at k = succ q the hypothesis applies at q.
;;; =====================================================================

(quietly (lambda ()
 (sp (make-wff (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
       (forall-guarded '(x_ k_)
         (list '(IN x_ RR) '(<= 0 x_) '(<= x_ 1) '(IN k_ NN))
         '(<= 0 ((BERNSTEIN-BASIS n_ x_) k_)))))))
 (let* ((br (use-induction)) (bn (cdr (assq 'var br))) (ih (cdr (assq 'ih br))))
  (dk-focus! (cdr (assq 'base br)))
  (bd-peel!) (mac 'BERNSTEIN-BASIS) (mac 'comb-kk-zero) (lam-b)
  (let ((ifterm (caddr (dk-goal))))
    (for-each
     (lambda (cs)
       (let ((true? (member '(= k_ 0) (dk-asms-of cs))))
         (dk-focus! cs)
         (for-each
          (lambda (s)
            (dk-focus! s)
            (if (memq (car (dk-goal)) '(= NOT))
                (ass)
                (begin
                  (subst (car (filter (lambda (a)
                                        (and (pair? a) (eq? (car a) '=)
                                             (pair? (cadr a)) (eq? (car (cadr a)) 'IF)))
                                      (dk-asms))))
                  (mac (if true? 'rr-scalar-ring-one 'rr-scalar-ring-zero))
                  (arith))))
          (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))))
     (dk-opened (lambda () (use-em '(= k_ 0))))))
  (dk-focus! (cdr (assq 'step br)))
  (bd-peel!)
  (let* ((bb (list 'BERNSTEIN-BASIS bn 'x_))
         (m1 (list bb '(- k_ 1)))
         (b0 (list bb 'k_))
         (p1 (list '* 'x_ m1))
         (p2 (list '* '(- 1 x_) b0)))
    (fact 'nn-subset-zz 'k_)
    (fact 'bernstein-basis-succ bn 'x_ 'k_)
    (subst (list '= (list (list 'BERNSTEIN-BASIS (list 'succ bn) 'x_) 'k_)
                 (list '+ p1 p2)))
    (fact 'rr-one-in)
    (have! '(AND (IN 1 RR) (IN x_ RR)))
    (fact 'rr-sub-in-rr 1 'x_)
    (fact 'zz-one-in) (fact 'zz-sub-in-zz 'k_ 1)
    (fact 'bt-neg1-in-zz) (fact 'bt-neg1-neg)
    (fact 'bernstein-basis-ptwise-in-rr bn 'x_ '(- k_ 1))
    (fact 'bernstein-basis-ptwise-in-rr bn 'x_ 'k_)
    (have! '(<= 0 (- 1 x_)) (lambda () (bd-ineq! '(<= x_ 1))))
    (let ((i1 (dk-deepest (lambda () (inst+ ih 'x_)))))
      (dk-deepest (lambda () (inst+ i1 'k_)))
      (fact 'nn-zero-or-succ 'k_)
      (have! (list '<= 0 m1)
        (lambda ()
          (for-each
           (lambda (s)
             (dk-focus! s)
             (if (member '(= k_ 0) (dk-asms))
                 (begin (subst '(= k_ 0))
                        (fact 'bernstein-basis-null bn 'x_ '(- 0 1))
                        (subst (list '= (list bb '(- 0 1)) 0))
                        (arith))
                 (begin
                   (dk-ai-head! 'FORSOME) (dk-ai-head! 'AND)
                   (let* ((eqn (car (filter (lambda (a)
                                              (and (pair? a) (eq? (car a) '=)
                                                   (eq? (cadr a) 'k_)
                                                   (pair? (caddr a))
                                                   (eq? (car (caddr a)) 'succ)))
                                            (dk-asms))))
                          (q (cadr (caddr eqn))))
                     (subst eqn)
                     (fact 'nn-subset-zz q)
                     (fact 'bt-succ-minus-1 q)
                     (subst (list '= (list '- (list 'succ q) 1) q))
                     (dk-deepest (lambda () (inst+ i1 q)))
                     (ass)))))
           (dk-opened (lambda () (ai (car (filter (dk-head? 'OR) (dk-asms)))))))
          #t)))
    (have! (list 'AND '(IN x_ RR) (list 'IN m1 'RR)))
    (fact 'rr-mul-closed 'x_ m1)
    (have! (list 'AND '(<= 0 x_) (list '<= 0 m1)))
    (fact 'rr-leq-mul-nonneg 'x_ m1)
    (have! (list 'AND '(IN (- 1 x_) RR) (list 'IN b0 'RR)))
    (fact 'rr-mul-closed '(- 1 x_) b0)
    (have! (list 'AND '(<= 0 (- 1 x_)) (list '<= 0 b0)))
    (fact 'rr-leq-mul-nonneg '(- 1 x_) b0)
    (have! (list 'AND (list '<= 0 p1) (list '<= 0 p2)))
    (fact 'rr-add-nonneg p1 p2)
    (ass)))))
(bd-check 'bernstein-basis-nonneg)
(qed 'bernstein-basis-nonneg)
(topic! 'bernstein-basis-nonneg 'analysis)
(alias! 'bernstein-basis-nonneg
        "the Bernstein basis is non-negative on the unit interval")

;;; =====================================================================
;;; 2.  THE BERNSTEIN OPERATOR (Definition (74)).
;;;
;;;   B_n f (x)  =  sum_{l=0}^{n} f(l/n) B_{l,n}(x)
;;;
;;; SERIES-PARTIAL-SUM(g, k) sums g over l = 0 .. k-1, so the notes' sum to n
;;; is the partial sum at succ n -- the same convention `bernstein-partition'
;;; and `bernstein-variance-bound' are stated with.
;;; =====================================================================

(def-functoid 'BERNSTEIN-POLY '(f n x)
  (list 'SERIES-PARTIAL-SUM
        (list 'VNB-LAMBDA 'l_ 'NN
              (list '* (list 'f (list '/ 'l_ 'n))
                       (list (list 'BERNSTEIN-BASIS 'n 'x) 'l_)))
        (list 'succ 'n)))
(notation! 'BERNSTEIN-POLY 'kind 'functoid 'arity 3
  'english "the degree-$2 Bernstein polynomial of $1 at $3")

;;; =====================================================================
;;; 3.  THE POINTWISE ESTIMATE, TERM BY TERM.
;;;
;;;   B_{l,n}(x) . (f(x) - f(l/n))   is between  -B_{l,n}(x) K   and  B_{l,n}(x) K
;;;   where  K = h + c (l - n x)^2   and   c (n delta)^2 = 2M.
;;;
;;; `c' is a PARAMETER here, constrained only by that equation and by c >= 0;
;;; no reciprocal appears in the statement.  Constructing it is the last
;;; theorem's business, and confining the recip algebra to that one place is
;;; what keeps this proof readable.
;;;
;;; THREE cases, and only two of them are in the notes:
;;;   l > n     : B_{l,n}(x) = 0 (`bernstein-basis-above') and both sides vanish.
;;;               Needed because the linearity laws quantify over ALL of NN.
;;;   |x - l/n| <= delta : (87) directly, plus c (l - nx)^2 >= 0.
;;;   delta <= |x - l/n| : delta^2 <= (x - l/n)^2, and multiplying by c n^2 >= 0
;;;               turns that into 2M <= c (l - n x)^2, which the two M-bounds
;;;               on f(x) and f(l/n) then dominate.
;;;
;;; The conclusion is stated with the basis value on the LEFT of each product
;;; because that is the shape `rr-le-scale-nonneg' produces; writing it the
;;; other way round would cost a `crs' rewrite at every use.
;;; =====================================================================

(define bd-bl '((BERNSTEIN-BASIS n_ x_) l_))
(define bd-qq '(/ l_ n_))
(define bd-qr '(* l_ (recip n_)))
(define bd-sq '(* (- l_ (* n_ x_)) (- l_ (* n_ x_))))
(define bd-kk (list '+ 'hh_ (list '* 'cc_ bd-sq)))
(define (bd-diff q) (list '- '(f_ x_) (list 'f_ q)))
(define bd-dv (bd-diff bd-qr))
(define bd-z  (list '- 'x_ bd-qr))
(define bd-a  (list 'abs bd-z))
(define bd-cn '(* cc_ (* n_ n_)))
(define bd-exp '(- (* n_ x_) (* (* n_ (recip n_)) l_)))

;;; (87) at [0,1], and M = sup|f| on [0,1], as hypothesis formulas
(define bd-uc
  (list 'FORALL 'p_ (list 'IMPLIES '(IN p_ (CCINT 0 1))
    (list 'FORALL 'q_ (list 'IMPLIES '(IN q_ (CCINT 0 1))
      (list 'IMPLIES '(<= (abs (- p_ q_)) delta_)
                     '(<= (abs (- (f_ p_) (f_ q_))) hh_)))))))
(define bd-bdd
  (list 'FORALL 'z_ (list 'IMPLIES '(IN z_ (CCINT 0 1))
     '(<= (abs (f_ z_)) mm_))))

(define bd-term-stmt
  (forall-guarded '(f_ n_ x_ hh_ delta_ mm_ cc_ l_)
    (list '(IN f_ (FUN RR RR)) '(IN n_ NN) '(NOT (= n_ 0)) '(IN x_ (CCINT 0 1))
          '(IN hh_ RR) '(< 0 hh_) '(IN delta_ RR) '(< 0 delta_)
          '(IN mm_ RR) '(<= 0 mm_) '(IN cc_ RR) '(<= 0 cc_)
          (list '= '(* (* n_ n_) (* (* delta_ delta_) cc_)) '(+ mm_ mm_))
          bd-uc bd-bdd '(IN l_ NN))
    (list 'AND (list '<= (list '* bd-bl (bd-diff bd-qq)) (list '* bd-bl bd-kk))
               (list '<= (list '* bd-bl (list '* '(- 0 1) bd-kk))
                          (list '* bd-bl (bd-diff bd-qq))))))

;;; from  -K <= f(x) - f(l/n) <= K  and  0 <= B_{l,n}(x), close both conjuncts
(define (bd-close!)
  (have! (list 'AND (list '<= 0 bd-bl) (list '<= bd-dv bd-kk)))
  (fact 'rr-le-scale-nonneg bd-bl bd-dv bd-kk)
  (have! (list 'AND (list '<= 0 bd-bl) (list '<= (list '* '(- 0 1) bd-kk) bd-dv)))
  (fact 'rr-le-scale-nonneg bd-bl (list '* '(- 0 1) bd-kk) bd-dv)
  (for-each (lambda (s) (dk-focus! s) (ass)) (dk-opened (lambda () (di)))))

(quietly (lambda ()
  (sp (make-wff bd-term-stmt))
  (bd-peel!)
  ;; x lies in [0,1] as three real facts -- read off in a `have!' LANE, so the
  ;; destructive `mac-h' does not delete the CCINT membership (87) needs.
  (have! '(AND (IN x_ RR) (AND (<= 0 x_) (<= x_ 1)))
     (lambda () (mac-h 'ccint-membership '(IN x_ (CCINT 0 1))) (ass)))
  (dk-split! '(AND (IN x_ RR) (AND (<= 0 x_) (<= x_ 1))))
  (mac 'binary-divide-def)
  (fact 'nn-in-rr 'n_) (fact 'nn-in-rr 'l_) (fact 'nn-subset-zz 'l_)
  (fact 'nn-zero-le 'n_) (fact 'nn-zero-le 'l_)
  (fact 'neq-sym 'n_ 0)
  (have! '(AND (<= 0 n_) (NOT (= 0 n_))))
  (fact 'rr-le-ne-lt 0 'n_)
  (have! '(AND (IN n_ RR) (NOT (= n_ 0))))
  (fact 'rr-recip-closed 'n_)
  (fact 'rr-recip-inverse 'n_)
  (fact 'rr-recip-pos 'n_)
  (fact 'rr-lt-implies-le 0 '(recip n_))
  (fact 'rr-lt-implies-le 0 'delta_)
  (fact 'rr-mul-in-rr 'l_ '(recip n_))
  (fact 'fun-apply-type-c 'f_ 'RR 'RR 'x_)
  (fact 'fun-apply-type-c 'f_ 'RR 'RR bd-qr)
  (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'l_)
  (fact 'bernstein-basis-nonneg 'n_ 'x_ 'l_)
  (fact 'rr-sub-in-rr '(f_ x_) (list 'f_ bd-qr))
  (fact 'rr-mul-in-rr 'n_ 'x_)
  (fact 'rr-sub-in-rr 'l_ '(* n_ x_))
  (fact 'rr-mul-in-rr '(- l_ (* n_ x_)) '(- l_ (* n_ x_)))
  (fact 'rr-mul-in-rr 'cc_ bd-sq)
  (fact 'rr-add-in-rr 'hh_ (list '* 'cc_ bd-sq))
  (fact 'rr-sq-nonneg '(- l_ (* n_ x_)))
  (have! (list 'AND '(IN cc_ RR) (list 'IN bd-sq 'RR)))
  (have! (list 'AND '(<= 0 cc_) (list '<= 0 bd-sq)))
  (fact 'rr-leq-mul-nonneg 'cc_ bd-sq)
  (fact 'rr-zero-in) (fact 'rr-one-in)
  (fact 'rr-sub-in-rr 0 1)
  (fact 'rr-mul-in-rr '(- 0 1) bd-kk)

  (let ((cases (dk-opened (lambda () (use-em '(< n_ l_))))))
    ;; ---- l > n: the basis vanishes and both sides are 0 ----------------
    (dk-focus! (car (filter (lambda (s) (member '(< n_ l_) (dk-asms-of s))) cases)))
    (fact 'bernstein-basis-above 'n_ 'x_ 'l_)
    (subst (list '= bd-bl 0))
    (bd-rw! (list '* 0 bd-dv) 0)
    (bd-rw! (list '* 0 bd-kk) 0)
    (bd-rw! (list '* 0 (list '* '(- 0 1) bd-kk)) 0)
    (for-each (lambda (s) (dk-focus! s) (arith)) (dk-opened (lambda () (di))))

    ;; ---- l <= n: l/n lies in [0,1] -------------------------------------
    (dk-focus! (car (filter (lambda (s) (member '(NOT (< n_ l_)) (dk-asms-of s))) cases)))
    (fact 'nn-not-lt-le 'n_ 'l_)
    (have! '(AND (IN l_ RR) (IN (recip n_) RR)))
    (have! '(AND (<= 0 l_) (<= 0 (recip n_))))
    (fact 'rr-leq-mul-nonneg 'l_ '(recip n_))
    (have! '(AND (<= 0 (recip n_)) (<= l_ n_)))
    (fact 'rr-le-scale-nonneg '(recip n_) 'l_ 'n_)
    (fact 'rr-mul-in-rr '(recip n_) 'l_)
    (fact 'rr-mul-in-rr '(recip n_) 'n_)
    (have! '(= (* (recip n_) n_) 1)
           (lambda () (bd-rw! '(* (recip n_) n_) '(* n_ (recip n_))) (ass)))
    (have! '(<= (* (recip n_) n_) 1)
           (lambda () (subst '(= (* (recip n_) n_) 1)) (arith)))
    (have! '(AND (<= (* (recip n_) l_) (* (recip n_) n_)) (<= (* (recip n_) n_) 1)))
    (fact 'rr-le-trans '(* (recip n_) l_) '(* (recip n_) n_) 1)
    (have! (list '<= bd-qr 1)
           (lambda () (bd-rw! bd-qr '(* (recip n_) l_)) (ass)))
    (have! (list 'IN bd-qr '(CCINT 0 1))
           (lambda () (mac 'ccint-membership) (from-context!)))
    (fact 'rr-sub-in-rr 'x_ bd-qr)
    (fact 'rr-abs-closed bd-z)
    (fact 'rr-le-total bd-a 'delta_)
    (let* ((sub  (dk-opened (lambda () (ai (car (filter (lambda (a)
                    (and (pair? a) (eq? (car a) 'OR) (dk-contains? a 'abs)))
                    (dk-asms)))))))
           (near (car (filter (lambda (s) (member (list '<= bd-a 'delta_)
                                                  (dk-asms-of s))) sub)))
           (far  (car (filter (lambda (s) (member (list '<= 'delta_ bd-a)
                                                  (dk-asms-of s))) sub))))
      ;; ---- NEAR: (87) gives the bound outright -------------------------
      (dk-focus! near)
      (let ((i1 (dk-deepest (lambda () (inst+ bd-uc 'x_)))))
        (dk-deepest (lambda () (inst+ i1 bd-qr))))
      (let ((ps (bd-absplit! (list '<= (list 'abs bd-dv) 'hh_))))
        (have! (list '<= bd-dv bd-kk)
           (lambda () (apply bd-ineq! (cons (list '<= 0 (list '* 'cc_ bd-sq)) ps))))
        (have! (list '<= (list '* '(- 0 1) bd-kk) bd-dv)
           (lambda () (apply bd-ineq! (cons (list '<= 0 (list '* 'cc_ bd-sq)) ps)))))
      (bd-close!)

      ;; ---- FAR: the quadratic term alone dominates ----------------------
      (dk-focus! far)
      (dk-deepest (lambda () (inst+ bd-bdd 'x_)))
      (dk-deepest (lambda () (inst+ bd-bdd bd-qr)))
      (let ((mx (bd-absplit! '(<= (abs (f_ x_)) mm_)))
            (mq (bd-absplit! (list '<= (list 'abs (list 'f_ bd-qr)) 'mm_))))
        (fact 'rr-mul-in-rr 'delta_ 'delta_)
        (fact 'rr-mul-in-rr bd-z bd-z)
        (have! (list 'AND (list 'AND '(<= 0 delta_) (list '<= 'delta_ bd-a))
                          (list 'AND '(<= 0 delta_) (list '<= 'delta_ bd-a))))
        (fact 'rr-prod-le-prod 'delta_ bd-a 'delta_ bd-a)
        (fact 'rr-sq-nonneg bd-z)
        (fact 'rr-abs-of-nonneg-rev (list '* bd-z bd-z))
        ;; rr-abs-mult has an AND antecedent and both factors are the SAME term,
        ;; so `fact' cannot be given it (a have! of (AND P P) is an alpha
        ;; self-loop).  Applied as a MACETE to the goal it needs no antecedent.
        (have! (list '= (list 'abs (list '* bd-z bd-z)) (list '* bd-a bd-a))
               (lambda () (mac 'rr-abs-mult) (crs)))
        (have! (list '<= '(* delta_ delta_) (list '* bd-z bd-z))
          (lambda () (subst (list '= (list '* bd-z bd-z) (list 'abs (list '* bd-z bd-z))))
                     (subst (list '= (list 'abs (list '* bd-z bd-z)) (list '* bd-a bd-a)))
                     (ass)))
        (fact 'rr-sq-nonneg 'n_)
        (fact 'rr-mul-in-rr 'n_ 'n_)
        (have! '(AND (IN cc_ RR) (IN (* n_ n_) RR)))
        (have! '(AND (<= 0 cc_) (<= 0 (* n_ n_))))
        (fact 'rr-leq-mul-nonneg 'cc_ '(* n_ n_))
        (fact 'rr-mul-in-rr 'cc_ '(* n_ n_))
        (have! (list 'AND (list '<= 0 bd-cn)
                          (list '<= '(* delta_ delta_) (list '* bd-z bd-z))))
        (fact 'rr-le-scale-nonneg bd-cn '(* delta_ delta_) (list '* bd-z bd-z))
        ;; c (l - n x)^2 = (c n^2)(x - l/n)^2 -- the one use of n recip(n) = 1
        (have! (list '= (list '* 'cc_ bd-sq) (list '* bd-cn (list '* bd-z bd-z)))
          (lambda ()
            (bd-rw! (list '* bd-cn (list '* bd-z bd-z))
                    (list '* 'cc_ (list '* bd-exp bd-exp)))
            (subst '(= (* n_ (recip n_)) 1))
            (crs)))
        (fact 'eq-sym '(* (* n_ n_) (* (* delta_ delta_) cc_)) '(+ mm_ mm_))
        (have! (list '<= '(+ mm_ mm_) (list '* 'cc_ bd-sq))
          (lambda ()
            (subst '(= (+ mm_ mm_) (* (* n_ n_) (* (* delta_ delta_) cc_))))
            (bd-rw! '(* (* n_ n_) (* (* delta_ delta_) cc_))
                    (list '* bd-cn '(* delta_ delta_)))
            (subst (list '= (list '* 'cc_ bd-sq) (list '* bd-cn (list '* bd-z bd-z))))
            (ass)))
        (let ((ps (append mx mq (list (list '<= '(+ mm_ mm_) (list '* 'cc_ bd-sq))
                                      '(< 0 hh_)))))
          (have! (list '<= bd-dv bd-kk) (lambda () (apply bd-ineq! ps)))
          (have! (list '<= (list '* '(- 0 1) bd-kk) bd-dv)
                 (lambda () (apply bd-ineq! ps))))
        (bd-close!))))))
(bd-check 'bernstein-term-bound)
(qed 'bernstein-term-bound)
(topic! 'bernstein-term-bound 'analysis)
(alias! 'bernstein-term-bound
        "the pointwise Bernstein estimate, term by term")

;;; =====================================================================
;;; 4.  THE ESTIMATE.
;;;
;;;   |f(x) - B_n f (x)|  <=  h + h,   provided  c n <= h.
;;;
;;; Sum the pointwise bound of section 3.  Eight families, all literal
;;; VNB-LAMBDAs over NN so that no extra universal appears in the statement and
;;; every transfer equation is one `lam-b' plus `crs':
;;;
;;;   g  = f(l/n) B_l       the Bernstein sum itself
;;;   pp = f(x) B_l         sums to f(x), by (75) and the scalar law
;;;   dd = B_l (f(x)-f(l/n))  pp = dd + g, so dd sums to f(x) - B_n f(x)
;;;   hq = (l-nx)^2 B_l     the variance family of (76)
;;;   aa = h B_l            sums to h
;;;   bb = c hq             sums to c . sum hq
;;;   ee = B_l K = aa + bb  sums to h + c . sum hq
;;;   ne = (-1) ee          sums to -(sum ee), which is how the lower bound
;;;                         crosses the sum: monotonicity is one-sided.
;;;
;;; The variance bound (76) is  recip(n) . sum hq <= 1;  multiplied by
;;; c n >= 0 and cancelled it gives  c . sum hq <= c n <= h.  So sum ee <= h+h,
;;; and -(h+h) <= sum dd <= h+h, which `rr-abs-bound' on the goal turns into
;;; the conclusion.
;;; =====================================================================

(define (bd-lam body) (list 'VNB-LAMBDA 'l_ 'NN body))
(define bd-bll '((BERNSTEIN-BASIS n_ x_) l_))
(define bd-sql '(* (- l_ (* n_ x_)) (- l_ (* n_ x_))))
(define bd-kkl (list '+ 'hh_ (list '* 'cc_ bd-sql)))
(define bd-qlv '(/ l_ n_))
(define bd-bs  '(BERNSTEIN-BASIS n_ x_))
(define bd-g   (bd-lam (list '* (list 'f_ bd-qlv) bd-bll)))
(define bd-pp  (bd-lam (list '* '(f_ x_) bd-bll)))
(define bd-dd  (bd-lam (list '* bd-bll (list '- '(f_ x_) (list 'f_ bd-qlv)))))
(define bd-hq  (bd-lam (list '* bd-sql bd-bll)))
(define bd-ee  (bd-lam (list '* bd-bll bd-kkl)))
(define bd-ne  (bd-lam (list '* '(- 0 1) (list '* bd-bll bd-kkl))))
(define bd-aa  (bd-lam (list '* 'hh_ bd-bll)))
(define bd-bb  (bd-lam (list '* 'cc_ (list '* bd-sql bd-bll))))
(define bd-fams (list bd-g bd-pp bd-dd bd-hq bd-ee bd-ne bd-aa bd-bb))

(define (bd-app f k) (list f k))
(define (bd-at-k e) (subst-free 'l_ 'k_ e))
(define bd-sqk (bd-at-k bd-sql))
(define bd-blk (bd-at-k bd-bll))
(define bd-qk  (bd-at-k bd-qlv))
(define (bd-pw-real f)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list 'IN (bd-app f 'k_) 'RR))))
(define (bd-pw-eq f rhs)
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN) (list '= (bd-app f 'k_) rhs))))
;; beta-reduce until no lambda is left in the goal
(define (bd-lamb!)
  (let loop ((i 0))
    (if (and (< i 8) (dk-contains? (dk-goal) 'VNB-LAMBDA))
        (begin (lam-b) (loop (+ i 1))) #t)))
;; the typings every pointwise lane wants, at the bound index k_
(define (bd-types-k!)
  (fact 'nn-subset-zz 'k_) (fact 'nn-in-rr 'k_)
  (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_)
  (fact 'rr-mul-in-rr 'n_ 'x_)
  (fact 'rr-sub-in-rr 'k_ '(* n_ x_))
  (fact 'rr-mul-in-rr '(- k_ (* n_ x_)) '(- k_ (* n_ x_)))
  (fact 'rr-mul-in-rr 'cc_ bd-sqk)
  (fact 'rr-add-in-rr 'hh_ (list '* 'cc_ bd-sqk))
  (have! (list 'IN bd-qk 'RR)
         (lambda () (mac 'binary-divide-def) (fact 'rr-mul-in-rr 'k_ '(recip n_)) (ass)))
  (fact 'fun-apply-type-c 'f_ 'RR 'RR bd-qk)
  (fact 'fun-apply-type-c 'f_ 'RR 'RR 'x_)
  (fact 'rr-sub-in-rr '(f_ x_) (list 'f_ bd-qk))
  (fact 'rr-mul-in-rr bd-sqk bd-blk)
  (fact 'rr-mul-in-rr bd-blk (list '+ 'hh_ (list '* 'cc_ bd-sqk))))
(define (bd-tr! f rhs) (have! (bd-pw-eq f rhs) (lambda () (di) (bd-types-k!) (bd-lamb!) (crs))))
(define (bd-sps f) (list 'SERIES-PARTIAL-SUM f '(succ n_)))

(define bd-est-stmt
  (forall-guarded '(f_ n_ x_ hh_ delta_ mm_ cc_)
    (list '(IN f_ (FUN RR RR)) '(IN n_ NN) '(NOT (= n_ 0)) '(IN x_ (CCINT 0 1))
          '(IN hh_ RR) '(< 0 hh_) '(IN delta_ RR) '(< 0 delta_)
          '(IN mm_ RR) '(<= 0 mm_) '(IN cc_ RR) '(<= 0 cc_)
          (list '= '(* (* n_ n_) (* (* delta_ delta_) cc_)) '(+ mm_ mm_))
          '(<= (* cc_ n_) hh_)
          bd-uc bd-bdd)
    '(<= (abs (- (f_ x_) (BERNSTEIN-POLY f_ n_ x_))) (+ hh_ hh_))))

(quietly (lambda ()
  (sp (make-wff bd-est-stmt))
  (bd-peel!)
  (have! '(AND (IN x_ RR) (AND (<= 0 x_) (<= x_ 1)))
     (lambda () (mac-h 'ccint-membership '(IN x_ (CCINT 0 1))) (ass)))
  (dk-split! '(AND (IN x_ RR) (AND (<= 0 x_) (<= x_ 1))))
  (fact 'nn-in-rr 'n_) (fact 'nn-succ-closed 'n_)
  (fact 'neq-sym 'n_ 0) (fact 'nn-zero-le 'n_)
  (have! '(AND (<= 0 n_) (NOT (= 0 n_))))
  (fact 'rr-le-ne-lt 0 'n_)
  (have! '(AND (IN n_ RR) (NOT (= n_ 0))))
  (fact 'rr-recip-closed 'n_) (fact 'rr-recip-inverse 'n_)
  (fact 'fun-apply-type-c 'f_ 'RR 'RR 'x_)
  (mac 'BERNSTEIN-POLY)

  ;; every family is pointwise real
  (have! (bd-pw-real bd-bs)
    (lambda () (di) (fact 'nn-subset-zz 'k_)
               (fact 'bernstein-basis-ptwise-in-rr 'n_ 'x_ 'k_) (ass)))
  (for-each
   (lambda (f)
     (have! (bd-pw-real f)
       (lambda () (di) (bd-lamb!) (bd-types-k!)
          (fact 'rr-mul-in-rr (list 'f_ bd-qk) bd-blk)
          (fact 'rr-mul-in-rr '(f_ x_) bd-blk)
          (fact 'rr-mul-in-rr bd-blk (list '- '(f_ x_) (list 'f_ bd-qk)))
          (fact 'rr-mul-in-rr 'hh_ bd-blk)
          (fact 'rr-mul-in-rr 'cc_ (list '* bd-sqk bd-blk))
          (fact 'rr-mul-in-rr '(- 0 1)
                (list '* bd-blk (list '+ 'hh_ (list '* 'cc_ bd-sqk))))
          (ass))))
   bd-fams)

  ;; the transfer equations
  (bd-tr! bd-pp (list '* '(f_ x_) (bd-app bd-bs 'k_)))
  (bd-tr! bd-pp (list '+ (bd-app bd-dd 'k_) (bd-app bd-g 'k_)))
  (bd-tr! bd-aa (list '* 'hh_ (bd-app bd-bs 'k_)))
  (bd-tr! bd-hq (list '* bd-sqk bd-blk))
  (bd-tr! bd-bb (list '* 'cc_ (bd-app bd-hq 'k_)))
  (bd-tr! bd-ee (list '+ (bd-app bd-aa 'k_) (bd-app bd-bb 'k_)))
  (bd-tr! bd-ne (list '* '(- 0 1) (bd-app bd-ee 'k_)))

  ;; the pointwise estimate, from section 3
  (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
            (list '<= (bd-app bd-dd 'k_) (bd-app bd-ee 'k_))))
    (lambda () (di) (bd-types-k!)
       (dk-split! (dk-fact! 'bernstein-term-bound 'f_ 'n_ 'x_ 'hh_ 'delta_ 'mm_ 'cc_ 'k_))
       (bd-lamb!) (ass)))
  (have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
            (list '<= (bd-app bd-ne 'k_) (bd-app bd-dd 'k_))))
    (lambda () (di) (bd-types-k!)
       (dk-split! (dk-fact! 'bernstein-term-bound 'f_ 'n_ 'x_ 'hh_ 'delta_ 'mm_ 'cc_ 'k_))
       (bd-lamb!)
       (bd-rw! (list '* '(- 0 1) (list '* bd-blk (list '+ 'hh_ (list '* 'cc_ bd-sqk))))
               (list '* bd-blk (list '* '(- 0 1) (list '+ 'hh_ (list '* 'cc_ bd-sqk)))))
       (ass)))

  ;; sum
  (for-each (lambda (f) (fact 'series-partial-sum-in-rr-ptwise '(succ n_) f))
            (cons bd-bs bd-fams))
  (fact 'bernstein-partition 'n_ 'x_)
  (let* ((e-pp  (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) '(f_ x_) bd-bs bd-pp))
         (e-add (dk-fact! 'series-partial-sum-add-ptwise '(succ n_) bd-dd bd-g bd-pp))
         (e-aa  (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) 'hh_ bd-bs bd-aa))
         (e-bb  (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) 'cc_ bd-hq bd-bb))
         (e-ee  (dk-fact! 'series-partial-sum-add-ptwise '(succ n_) bd-aa bd-bb bd-ee))
         (e-ne  (dk-fact! 'series-partial-sum-scale-ptwise '(succ n_) '(- 0 1) bd-ee bd-ne))
         (mono1 (dk-fact! 'series-partial-sum-le-termwise-ptwise '(succ n_) bd-dd bd-ee))
         (mono2 (dk-fact! 'series-partial-sum-le-termwise-ptwise '(succ n_) bd-ne bd-dd))
         (part  (list '= (bd-sps bd-bs) 1))
         (shq   (bd-sps bd-hq))
         (dg    (list '= (list '+ (bd-sps bd-dd) (bd-sps bd-g)) '(f_ x_)))
         (aa-hh (list '= (bd-sps bd-aa) 'hh_))
         (bb-le (list '<= (bd-sps bd-bb) '(* cc_ n_))))
    (have! (list '= (bd-sps bd-pp) '(f_ x_))
      (lambda () (subst e-pp) (subst part) (crs)))
    (have! dg (lambda ()
      (subst (dk-fact! 'eq-sym (bd-sps bd-pp)
                       (list '+ (bd-sps bd-dd) (bd-sps bd-g))))
      (ass)))
    (have! aa-hh (lambda () (subst e-aa) (subst part) (crs)))
    ;; the variance bound, scaled by c n >= 0 and cancelled
    (fact 'rr-mul-in-rr 'cc_ 'n_)
    (have! '(AND (IN cc_ RR) (IN n_ RR)))
    (have! '(AND (<= 0 cc_) (<= 0 n_)))
    (fact 'rr-leq-mul-nonneg 'cc_ 'n_)
    (fact 'bernstein-variance-bound 'n_ 'x_ bd-hq)
    (mac-h 'binary-divide-def (list '<= (list '* '(/ 1 n_) shq) 1))
    (fact 'rr-mul-in-rr 1 '(recip n_))
    (fact 'rr-mul-in-rr '(* 1 (recip n_)) shq)
    (fact 'rr-mul-in-rr 'cc_ shq)
    (fact 'rr-mul-in-rr '(* cc_ n_) 1)
    (fact 'rr-mul-in-rr '(* cc_ n_) (list '* '(* 1 (recip n_)) shq))
    (have! (list 'AND '(<= 0 (* cc_ n_)) (list '<= (list '* '(* 1 (recip n_)) shq) 1)))
    (fact 'rr-le-scale-nonneg '(* cc_ n_) (list '* '(* 1 (recip n_)) shq) 1)
    (let ((lhs (list '* '(* cc_ n_) (list '* '(* 1 (recip n_)) shq))))
      (have! (list '= lhs (list '* 'cc_ shq))
        (lambda () (bd-rw! lhs (list '* '(* n_ (recip n_)) (list '* 'cc_ shq)))
                   (subst '(= (* n_ (recip n_)) 1))
                   (crs)))
      (have! (list '<= (list '* 'cc_ shq) '(* (* cc_ n_) 1))
             (lambda () (subst (dk-fact! 'eq-sym lhs (list '* 'cc_ shq))) (ass))))
    (have! '(<= (* (* cc_ n_) 1) (* cc_ n_))
           (lambda () (bd-rw! '(* (* cc_ n_) 1) '(* cc_ n_))
                      (fact 'rr-leq-reflexive '(* cc_ n_)) (ass)))
    (have! (list 'AND (list '<= (list '* 'cc_ shq) '(* (* cc_ n_) 1))
                      '(<= (* (* cc_ n_) 1) (* cc_ n_))))
    (fact 'rr-le-trans (list '* 'cc_ shq) '(* (* cc_ n_) 1) '(* cc_ n_))
    (have! bb-le (lambda () (subst e-bb) (ass)))
    ;; and the conclusion
    (fact 'rr-sub-in-rr '(f_ x_) (bd-sps bd-g))
    (fact 'rr-add-in-rr 'hh_ 'hh_)
    (mac 'rr-abs-bound)
    (let ((ps (list dg mono1 mono2 e-ee aa-hh bb-le '(<= (* cc_ n_) hh_) e-ne)))
      (for-each (lambda (s) (dk-focus! s) (apply bd-ineq! ps))
                (dk-opened (lambda () (di))))))))
(bd-check 'bernstein-approx-bound)
(qed 'bernstein-approx-bound)
(topic! 'bernstein-approx-bound 'analysis)
(alias! 'bernstein-approx-bound
        "the Bernstein approximation estimate at a fixed degree")

;;; =====================================================================
;;; 5.  THEOREM 5.2 -- uniform approximation on [0,1].
;;;
;;;   f continuous on [0,1], eps > 0
;;;     ==>  forsome N in NN. forall n >= N, forall x in [0,1].
;;;            |f(x) - B_n f (x)|  <=  eps
;;;
;;; Everything analytic is already done; this is the CHOICE of constants, and
;;; it is where the reciprocals live.
;;;
;;;   h        : eps halved, by `rr-pos-halvable' -- a WITNESS with h + h = eps,
;;;              not a quotient, so no division enters here.
;;;   delta    : the modulus of uniform continuity at h (87).
;;;   M        : the bound on |f| over [0,1].
;;;   N        : any natural above  2M recip(h) recip(delta)^2, by
;;;              `nn-unbounded-in-rr' -- the Archimedean property, and the only
;;;              asserted fact this theorem adds to the ones the estimate
;;;              already carries.
;;;   c        : 2M recip(n)^2 recip(delta)^2, for the n in hand.
;;;
;;; The two hypotheses of the estimate then read
;;;   n^2 delta^2 c = 2M      -- four cancellations of a recip against its
;;;                              argument, each introduced by rewriting the goal
;;;                              into a form that EXPOSES the product first;
;;;   c n <= h                -- the threshold, scaled from  2M recip(h)
;;;                              recip(delta)^2 <= n  by  recip(n) h >= 0.
;;;
;;; N > 0 comes free: the threshold is non-negative and N exceeds it, which is
;;; what makes n non-zero and recip(n) available at all.
;;; =====================================================================

(define bd-thm-stmt
  (forall-guarded '(f_ eps_)
    (list '(IN f_ (FUN RR RR))
          '(FORALL x (IMPLIES (IN x (CCINT 0 1)) (IS-CONTINUOUS-AT RR-MS RR-MS f_ x)))
          '(POS-RR eps_))
    (forsome-guarded 'cap_ '(IN cap_ NN)
      (forall-guarded '(n_ x_)
        (list '(IN n_ NN) '(<= cap_ n_) '(IN x_ (CCINT 0 1)))
        '(<= (abs (- (f_ x_) (BERNSTEIN-POLY f_ n_ x_))) eps_)))))

(quietly (lambda ()
  (sp (make-wff bd-thm-stmt))
  (bd-peel!)
  (fact 'rr-pos-halvable 'eps_)
  (let* ((hps (bd-obtain!))
         (hh  (cadr (bd-find hps 'POS-RR)))
         (hparts (list 'AND (list 'IN hh 'RR)
                       (list 'AND (list '<= 0 hh) (list 'NOT (list '= 0 hh))))))
    (have! hparts (lambda () (mac-h 'pos-rr (list 'POS-RR hh)) (ass)))
    (dk-split! hparts)
    (have! (list 'AND (list '<= 0 hh) (list 'NOT (list '= 0 hh))))
    (fact 'rr-le-ne-lt 0 hh)
    (fact 'neq-sym 0 hh)
    (fact 'rr-zero-in) (fact 'rr-one-in)
    (have! '(<= 0 1) (lambda () (arith)))
    (dk-fact! 'continuous-uniformly-continuous-on-ccint 'f_ 0 1 hh)
    (let* ((dps   (bd-obtain!))
           (delta (caddr (bd-find dps '<))))
      (dk-fact! 'continuous-abs-bounded-on-ccint 'f_ 0 1)
      (let* ((mps (bd-obtain!))
             (mm  (caddr (bd-find mps '<=)))
             (rh  (list 'recip hh))
             (rd  (list 'recip delta))
             (m2  (list '+ mm mm))
             (thr (list '* m2 (list '* rh (list '* rd rd)))))
        (fact 'rr-pos-ne-zero delta)
        (have! (list 'AND (list 'IN delta 'RR) (list 'NOT (list '= delta 0))))
        (have! (list 'AND (list 'IN hh 'RR) (list 'NOT (list '= hh 0))))
        (fact 'rr-recip-closed hh) (fact 'rr-recip-pos hh) (fact 'rr-recip-inverse hh)
        (fact 'rr-recip-closed delta) (fact 'rr-recip-pos delta)
        (fact 'rr-recip-inverse delta)
        (fact 'rr-lt-implies-le 0 rh)
        (fact 'rr-lt-implies-le 0 rd)
        (fact 'rr-add-in-rr mm mm)
        (have! (list 'AND (list '<= 0 mm) (list '<= 0 mm)))
        (fact 'rr-add-nonneg mm mm)
        (fact 'rr-sq-nonneg rd)
        (fact 'rr-mul-in-rr rd rd)
        (have! (list 'AND (list 'IN rh 'RR) (list 'IN (list '* rd rd) 'RR)))
        (have! (list 'AND (list '<= 0 rh) (list '<= 0 (list '* rd rd))))
        (fact 'rr-leq-mul-nonneg rh (list '* rd rd))
        (fact 'rr-mul-in-rr rh (list '* rd rd))
        (have! (list 'AND (list 'IN m2 'RR) (list 'IN (list '* rh (list '* rd rd)) 'RR)))
        (have! (list 'AND (list '<= 0 m2) (list '<= 0 (list '* rh (list '* rd rd)))))
        (fact 'rr-leq-mul-nonneg m2 (list '* rh (list '* rd rd)))
        (fact 'rr-mul-in-rr m2 (list '* rh (list '* rd rd)))
        (fact 'nn-unbounded-in-rr thr)
        (let* ((cps (bd-obtain!))
               (cap (cadr (bd-find cps 'IN))))
          (ew cap)
          (let ((ls (dk-opened (lambda () (di)))))
            (for-each (lambda (s) (dk-focus! s)
                        (if (eq? (car (dk-goal)) 'IN) (ass) #t)) ls)
            (dk-focus! (car (filter (lambda (s) (not (eq? (car (dk-goal-of s)) 'IN))) ls))))
          (bd-peel!)
          (fact 'nn-in-rr 'n_) (fact 'nn-in-rr cap)
          (have! (list 'AND (list '<= 0 thr) (list '< thr cap)))
          (fact 'rr-le-lt-trans 0 thr cap)
          (have! (list 'AND (list '< 0 cap) (list '<= cap 'n_)))
          (fact 'rr-lt-le-trans 0 cap 'n_)
          (fact 'rr-pos-ne-zero 'n_)
          (have! (list 'AND (list '< thr cap) (list '<= cap 'n_)))
          (fact 'rr-lt-le-trans thr cap 'n_)
          (fact 'rr-lt-implies-le thr 'n_)
          (have! '(AND (IN n_ RR) (NOT (= n_ 0))))
          (fact 'rr-recip-closed 'n_) (fact 'rr-recip-pos 'n_)
          (fact 'rr-recip-inverse 'n_)
          (fact 'rr-lt-implies-le 0 '(recip n_))
          (let* ((rn '(recip n_))
                 (u1 (list '* rn (list '* rd rd)))
                 (u2 (list '* rn u1))
                 (cc (list '* m2 u2))
                 (cs (list '* rn hh)))
            (have! (list 'AND (list 'IN rn 'RR) (list 'IN (list '* rd rd) 'RR)))
            (have! (list 'AND (list '<= 0 rn) (list '<= 0 (list '* rd rd))))
            (fact 'rr-leq-mul-nonneg rn (list '* rd rd))
            (fact 'rr-mul-in-rr rn (list '* rd rd))
            (have! (list 'AND (list 'IN rn 'RR) (list 'IN u1 'RR)))
            (have! (list 'AND (list '<= 0 rn) (list '<= 0 u1)))
            (fact 'rr-leq-mul-nonneg rn u1)
            (fact 'rr-mul-in-rr rn u1)
            (have! (list 'AND (list 'IN m2 'RR) (list 'IN u2 'RR)))
            (have! (list 'AND (list '<= 0 m2) (list '<= 0 u2)))
            (fact 'rr-leq-mul-nonneg m2 u2)
            (fact 'rr-mul-in-rr m2 u2)
            ;; n^2 delta^2 c = 2M
            (have! (list '= (list '* '(* n_ n_) (list '* (list '* delta delta) cc)) m2)
              (lambda ()
                (bd-rw! (list '* '(* n_ n_) (list '* (list '* delta delta) cc))
                        (list '* (list '* (list '* 'n_ rn) (list '* 'n_ rn))
                                 (list '* (list '* (list '* delta rd) (list '* delta rd)) m2)))
                (subst (list '= (list '* 'n_ rn) 1))
                (subst (list '= (list '* delta rd) 1))
                (crs)))
            ;; c n <= h
            (have! (list 'AND (list 'IN rn 'RR) (list 'IN hh 'RR)))
            (have! (list 'AND (list '<= 0 rn) (list '<= 0 hh)))
            (fact 'rr-leq-mul-nonneg rn hh)
            (fact 'rr-mul-in-rr rn hh)
            (fact 'rr-mul-in-rr cs 'n_)
            (fact 'rr-mul-in-rr cs thr)
            (fact 'rr-mul-in-rr cc 'n_)
            (have! (list 'AND (list '<= 0 cs) (list '<= thr 'n_)))
            (fact 'rr-le-scale-nonneg cs thr 'n_)
            (have! (list '= (list '* cs 'n_) hh)
              (lambda () (bd-rw! (list '* cs 'n_) (list '* (list '* 'n_ rn) hh))
                         (subst (list '= (list '* 'n_ rn) 1)) (crs)))
            (have! (list '<= (list '* cs 'n_) hh)
              (lambda () (subst (list '= (list '* cs 'n_) hh))
                         (fact 'rr-leq-reflexive hh) (ass)))
            (have! (list '= (list '* cs thr) (list '* cc 'n_))
              (lambda ()
                (bd-rw! (list '* cs thr)
                        (list '* (list '* hh rh) (list '* m2 (list '* rn (list '* rd rd)))))
                (subst (list '= (list '* hh rh) 1))
                (bd-rw! (list '* cc 'n_)
                        (list '* (list '* 'n_ rn) (list '* m2 (list '* rn (list '* rd rd)))))
                (subst (list '= (list '* 'n_ rn) 1))
                (crs)))
            (have! (list 'AND (list '<= (list '* cs thr) (list '* cs 'n_))
                              (list '<= (list '* cs 'n_) hh)))
            (fact 'rr-le-trans (list '* cs thr) (list '* cs 'n_) hh)
            (have! (list '<= (list '* cc 'n_) hh)
              (lambda () (subst (dk-fact! 'eq-sym (list '* cs thr) (list '* cc 'n_))) (ass)))
            ;; and the estimate
            (dk-fact! 'bernstein-approx-bound 'f_ 'n_ 'x_ hh delta mm cc)
            (subst (dk-fact! 'eq-sym (list '+ hh hh) 'eps_))
            (ass))))))))
(bd-check 'bernstein-uniform-approximation)
(qed 'bernstein-uniform-approximation)
(topic! 'bernstein-uniform-approximation 'analysis)
(alias! 'bernstein-uniform-approximation
        "a continuous function on [0,1] is the uniform limit of its Bernstein polynomials"
        "Theorem 5.2"
        "the Bernstein density theorem on the unit interval")
