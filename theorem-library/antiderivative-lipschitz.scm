;;; antiderivative-lipschitz.scm -- THE WITNESS ESTIMATE of docs/calculus.pdf
;;; Prop 4.16: a bound on the INTEGRAND bounds the CARATHEODORY WITNESS, at
;;; every point of the interval and by the same constant.
;;;
;;;   antiderivative-increment-bound   the MVT modulus on a SUBINTERVAL
;;;   antiderivative-lipschitz         ... with the order of the endpoints
;;;                                    unknown, hence a modulus on the right
;;;   caratheodory-witness-bound       |phi| <= M on [a,b]  =>  |psi| <= M on
;;;                                    [a,b], psi any Caratheodory witness of
;;;                                    the antiderivative at a point of [a,b]
;;;   antiderivative-pair-close        two antiderivatives AGREEING AT a whose
;;;                                    integrands are within M on [a,b] are
;;;                                    within M.(b-a) on [a,b]
;;;
;;; WHY THE THIRD ONE IS THE POINT.  Prop 4.16 makes a family of antiderivatives
;;; F_k converge by showing the WITNESSES psi_k are uniformly Cauchy, and a
;;; witness is a global object (IS-DIFF-AT's identity quantifies over all of RR)
;;; about which the data of the theorem -- a uniform bound on the derivatives
;;; ON [a,b] -- says nothing directly.  The bridge is the Mean Value Theorem,
;;; and the way it is spent is worth stating: the witness identity
;;;
;;;     h(x) - h(t) = psi(x).(x - t)
;;;
;;; turns a bound on the INCREMENT into a bound on psi the moment |x - t| can be
;;; cancelled, and `mvt-abs-bound' bounds the increment by M.(b-a) on any
;;; interval where |h'| <= M.  Applied on [t,x] -- a SUBINTERVAL of [a,b], which
;;; is where the first two theorems earn their keep -- that reads
;;; |psi(x)|.|x-t| <= M.|x-t|, and `rr-nonneg-cancel-pos' takes the factor off.
;;; The x = t case is separate and is not an estimate at all: psi(t) = phi(t) by
;;; the witness's own defining conjunct, so the bound is the hypothesis.
;;;
;;; THE SUBINTERVAL TRANSFER is the only fiddly part, and it is fiddly in
;;; exactly one way: Def 4.6's two clauses have DIFFERENT shapes and each has to
;;; be re-stated at (u,v).  The continuity clause is CCINT-guarded, so it
;;; transfers by CCINT(u,v) SUBSET CCINT(a,b) -- two `ineq' calls off
;;; `ccint-membership'.  The derivative clause carries a CONJUNCTIVE antecedent
;;; and an EXISTENTIAL consequent (mvt-abs-bound asks for "some l with
;;; IS-DIFF-AT and |l| <= M", not for the derivative by name), so it transfers by
;;; exhibiting phi(x) as the witness: the strict inequalities a <= u < x < v <= b
;;; put x in the open interval where the antiderivative differentiates, and in
;;; the closed one where the bound speaks.
;;;
;;; ORDER OF THE ENDPOINTS.  `antiderivative-increment-bound' asks u < v because
;;; the MVT does; `antiderivative-lipschitz' drops that and pays for it with
;;; `rr-lt-trichotomy' and two `rr-abs-sub-sym' rewrites.  A caller wanting the
;;; estimate at a pair of points of [a,b] -- which is every caller, the points
;;; being x and the base point t -- does not know which is larger, so the
;;; unordered form is the one that gets cited and the ordered one is scaffolding.
;;;
;;; WHAT IT COSTS.  `trust: well-known', all of it INHERITED from the MVT arc
;;; through `mvt-abs-bound': `mvt-upper-bound' bills `rr-le-scale-nonneg-right'
;;; at `well-known'.  Nothing here adds a leaf of its own, and nothing built on
;;; the Mean Value Theorem reads `modulo 0' in this tree today.
;;;
;;; ONE MECHANICAL POINT, and it cost a run.  `rr-abs-mult' and `rr-mul-closed'
;;; both carry a CONJUNCTIVE antecedent, so each wants a `have!' of the AND
;;; immediately before the `fact'.  Without it the citation lands the
;;; IMPLICATION, silently, and the `subst' that was to use the equation finds
;;; nothing to rewrite -- the failure surfaces several steps later as a `have!'
;;; whose thunk left its side goal open.
;;;
;;; THE FOURTH IS THE FORM Prop 4.16 CITES.  It is the first display of the
;;; notes' proof -- |f_k(x) - f_l(x)| - |f_k(a) - f_l(a)| <= M_{k,l}(x - a) --
;;; with the second term made ZERO by normalisation rather than carried, which
;;; is what `antiderivative-normalize.scm' arranges.  It is `antiderivative-sub'
;;; (Prop 4.8) followed by `antiderivative-lipschitz' on the difference, based
;;; at a, and then one product monotonicity to replace |x - a| by b - a.  Note
;;; that 0 <= M is NOT a hypothesis: it follows from the bound at a, the modulus
;;; being nonnegative, which is the sort of thing `ineq' will not supply for
;;; itself but closes at once when the two facts are named.
;;;
;;; Loads after antiderivative (IS-ANTIDERIVATIVE), antiderivative-transfer
;;; (antiderivative-sub), mvt-abs-bound,
;;; ccint-basics (ccint-membership), rr-abs-basics (rr-abs-of-nonneg,
;;; rr-abs-of-nonpos, rr-abs-mult, rr-abs-sub-sym, rr-abs-closed),
;;; rr-order-basics (rr-lt-trichotomy, rr-nonneg-cancel-pos),
;;; binary-minus-laws (rr-sub-in-rr), equality-basics (eq-sym),
;;; fun-apply-type-proof (fun-apply-type-c) and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `al-' prefix) --------------------

(define (al-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 20))
          (begin (di) (loop (+ n 1))) #t))))

;;; Select a hypothesis by CONTENT; a miss ERRORS.
(define (al-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "al-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

(define (al-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "al-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (al-ineq . forms) (apply ineq (map al-idx forms)))

;;; Walk an AND goal down to its leaves, running CLOSER on each.
(define (al-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (al-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (al-mem! x lo hi thunk) (have! (list 'IN x (list 'CCINT lo hi)) thunk))

;;; `rr-mul-closed' has a CONJUNCTIVE antecedent -- the AND has to be in context
;;; as ONE formula before the citation, or `fact' lands the implication.
(define (al-mul! s t)
  (have! (list 'AND (list 'IN s 'RR) (list 'IN t 'RR)))
  (fact 'rr-mul-closed s t))

;;; =====================================================================
;;; 1.  THE ORDERED INCREMENT BOUND.  Def 4.6's two clauses, re-stated on the
;;; subinterval [u,v], and `mvt-abs-bound' cited there.
;;; =====================================================================

(sp (make-wff "forall([h in fun(rr,rr), phi in fun(rr,rr), a in rr, b in rr, m_ in rr],
   is-antiderivative(h, phi, a, b) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(phi(x_)) <= m_) implies
   forall([u in rr, v in rr], u in ccint(a,b) implies v in ccint(a,b) implies
      u < v implies abs(h(v) - h(u)) <= m_ * (v - u)))"))
(quietly (lambda () (al-peel!)))
(define AL-BD (al-find 'bound (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (dk-contains? f 'abs)))))
(quietly (lambda ()
  (dk-split! (dk-landed-1 (lambda ()
     (mac-h 'IS-ANTIDERIVATIVE '(IS-ANTIDERIVATIVE h phi a b)))))
  (mac-h 'ccint-membership '(IN u (CCINT a b)))
  (dk-split! (al-find 'umem (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                                             (dk-contains? f 'u)))))
  (mac-h 'ccint-membership '(IN v (CCINT a b)))
  (dk-split! (al-find 'vmem (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                                             (dk-contains? f 'v)))))))
(define AL-CT (al-find 'cont (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                              (dk-contains? f 'IS-CONTINUOUS-AT)))))
(define AL-DF (al-find 'deriv (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (dk-contains? f 'IS-DIFF-AT)))))

;;; (i) h is continuous on the CLOSED subinterval [u,v].
(have! '(FORALL x_ (IMPLIES (IN x_ (CCINT u v))
                            (IS-CONTINUOUS-AT RR-MS RR-MS h x_)))
  (lambda ()
    (quietly (lambda ()
      (di)
      (mac-h 'ccint-membership '(IN x_ (CCINT u v)))
      (dk-split! (al-find 'xm (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                                               (dk-contains? f 'x_)))))
      (al-mem! 'x_ 'a 'b
        (lambda ()
          (mac 'ccint-membership)
          (al-and! (lambda ()
             (let ((g (dk-goal)))
               (cond ((eq? (car g) 'IN) (ass))
                     ((equal? (cadr g) 'a) (al-ineq '(<= a u) '(<= u x_)))
                     (else (al-ineq '(<= x_ v) '(<= v b)))))))))
      (inst+ AL-CT 'x_)
      (ass)))))

;;; (ii) the two-sided derivative bound on the OPEN subinterval (u,v).  The
;;; witness mvt-abs-bound asks for is phi(x) itself.
(have! '(FORALL x_ (IMPLIES (AND (IN x_ RR) (AND (< u x_) (< x_ v)))
             (FORSOME l_ (AND (IN l_ RR)
                (AND (IS-DIFF-AT h x_ l_) (<= (abs l_) m_))))))
  (lambda ()
    (quietly (lambda ()
      (di)
      (dk-split! (car (dk-landed (lambda () (di)))))
      (have! '(AND (IN x_ RR) (AND (< a x_) (< x_ b)))
        (lambda ()
          (al-and! (lambda ()
            (let ((g (dk-goal)))
              (cond ((eq? (car g) 'IN) (ass))
                    ((equal? (cadr g) 'a) (al-ineq '(<= a u) '(< u x_)))
                    (else (al-ineq '(< x_ v) '(<= v b)))))))))
      (dk-deepest (lambda () (inst+ AL-DF 'x_)))
      (al-mem! 'x_ 'a 'b
        (lambda ()
          (mac 'ccint-membership)
          (al-and! (lambda ()
             (let ((g (dk-goal)))
               (cond ((eq? (car g) 'IN) (ass))
                     ((equal? (cadr g) 'a) (al-ineq '(<= a u) '(< u x_)))
                     (else (al-ineq '(< x_ v) '(<= v b)))))))))
      (dk-deepest (lambda () (inst+ AL-BD 'x_)))
      (fact 'fun-apply-type-c 'phi 'RR 'RR 'x_)
      (ew '(phi x_))
      (al-and! (lambda () (ass)))))))

(quietly (lambda () (fact 'mvt-abs-bound 'h 'u 'v 'm_) (ass)))
(qed 'antiderivative-increment-bound)
(topic! 'antiderivative-increment-bound 'analysis)
(alias! 'antiderivative-increment-bound
        "the MVT increment bound on a subinterval"
        "a bound on the integrand bounds the increment of an antiderivative")

;;; =====================================================================
;;; 2.  THE SAME, WITH THE ENDPOINTS IN EITHER ORDER.  `rr-lt-trichotomy',
;;; and the equal case, where both sides are 0.
;;; =====================================================================

(sp (make-wff "forall([h in fun(rr,rr), phi in fun(rr,rr), a in rr, b in rr, m_ in rr],
   is-antiderivative(h, phi, a, b) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(phi(x_)) <= m_) implies
   forall([u in rr, v in rr], u in ccint(a,b) implies v in ccint(a,b) implies
      abs(h(v) - h(u)) <= m_ * abs(v - u)))"))
(quietly (lambda ()
  (al-peel!)
  (fact 'fun-apply-type-c 'h 'RR 'RR 'u)
  (fact 'fun-apply-type-c 'h 'RR 'RR 'v)
  (fact 'rr-sub-in-rr 'v 'u)
  (fact 'rr-sub-in-rr 'u 'v)
  (fact 'rr-sub-in-rr '(h v) '(h u))
  (fact 'rr-sub-in-rr '(h u) '(h v))
  (fact 'rr-zero-in)
  (fact 'rr-lt-trichotomy 'u 'v)))
(use-cases '((< u v) (= u v) (< v u))
  (lambda ()
    (quietly (lambda ()
      (fact 'antiderivative-increment-bound 'h 'phi 'a 'b 'm_ 'u 'v)
      (have! '(<= 0 (- v u)) (lambda () (al-ineq '(< u v))))
      (fact 'rr-abs-of-nonneg '(- v u))
      (subst '(= (abs (- v u)) (- v u)))
      (ass))))
  (lambda ()
    (quietly (lambda ()
      (subst '(= u v))
      (have! '(= (- (h v) (h v)) 0) (lambda () (crs)))
      (subst '(= (- (h v) (h v)) 0))
      (have! '(= (- v v) 0) (lambda () (crs)))
      (subst '(= (- v v) 0))
      (have! '(<= 0 0) (lambda () (ineq)))
      (fact 'rr-abs-of-nonneg 0)
      (subst '(= (abs 0) 0))
      (have! '(= (* m_ 0) 0) (lambda () (crs)))
      (subst '(= (* m_ 0) 0))
      (ass))))
  (lambda ()
    (quietly (lambda ()
      (fact 'antiderivative-increment-bound 'h 'phi 'a 'b 'm_ 'v 'u)
      (fact 'rr-abs-sub-sym 'v 'u)
      (subst '(= (abs (- v u)) (abs (- u v))))
      (have! '(<= 0 (- u v)) (lambda () (al-ineq '(< v u))))
      (fact 'rr-abs-of-nonneg '(- u v))
      (subst '(= (abs (- u v)) (- u v)))
      (fact 'rr-abs-sub-sym '(h v) '(h u))
      (subst '(= (abs (- (h v) (h u))) (abs (- (h u) (h v)))))
      (ass)))))
(qed 'antiderivative-lipschitz)
(topic! 'antiderivative-lipschitz 'analysis)
(alias! 'antiderivative-lipschitz
        "an antiderivative with a bounded integrand is Lipschitz on the interval")

;;; =====================================================================
;;; 3.  THE WITNESS BOUND.  Cancel |x - t| off the increment estimate; at the
;;; centre there is nothing to cancel and psi(t) = phi(t) is the answer.
;;; =====================================================================

(sp (make-wff "forall([h in fun(rr,rr), phi in fun(rr,rr), psi in fun(rr,rr),
                       a in rr, b in rr, t_ in rr, m_ in rr],
   is-antiderivative(h, phi, a, b) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(phi(x_)) <= m_) implies
   t_ in ccint(a,b) implies
   psi(t_) = phi(t_) implies
   forall([x_ in rr], h(x_) - h(t_) = psi(x_) * (x_ - t_)) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(psi(x_)) <= m_))"))
(quietly (lambda () (al-peel!)))
(define AW-ID (al-find 'ident (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (dk-contains? f 'psi)
                                               (dk-contains? f 'h)))))
(define AW-BD (al-find 'bound (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                               (dk-contains? f 'abs)))))

;;; the shared tail of the two OFF-CENTRE cases: the factor |x - t| comes off.
(define (aw-tail!)
  (fact 'antiderivative-lipschitz 'h 'phi 'a 'b 'm_ 't_ 'x_)
  (dk-deepest (lambda () (inst+ AW-ID 'x_)))
  (fact 'fun-apply-type-c 'psi 'RR 'RR 'x_)
  (fact 'rr-abs-closed '(psi x_))
  (fact 'rr-abs-closed '(- x_ t_))
  (fact 'rr-sub-in-rr 'm_ '(abs (psi x_)))
  (al-mul! '(abs (psi x_)) '(abs (- x_ t_)))
  (al-mul! 'm_ '(abs (- x_ t_)))
  (al-mul! '(abs (- x_ t_)) '(- m_ (abs (psi x_))))
  (have! '(AND (IN (psi x_) RR) (IN (- x_ t_) RR)))
  (fact 'rr-abs-mult '(psi x_) '(- x_ t_))
  (have! '(<= (* (abs (psi x_)) (abs (- x_ t_))) (* m_ (abs (- x_ t_))))
    (lambda ()
      (fact 'eq-sym '(abs (* (psi x_) (- x_ t_))) '(* (abs (psi x_)) (abs (- x_ t_))))
      (subst '(= (* (abs (psi x_)) (abs (- x_ t_))) (abs (* (psi x_) (- x_ t_)))))
      (fact 'eq-sym '(- (h x_) (h t_)) '(* (psi x_) (- x_ t_)))
      (subst '(= (* (psi x_) (- x_ t_)) (- (h x_) (h t_))))
      (ass)))
  (have! '(<= 0 (* (abs (- x_ t_)) (- m_ (abs (psi x_)))))
    (lambda ()
      (have! '(= (* (abs (- x_ t_)) (- m_ (abs (psi x_))))
                 (- (* m_ (abs (- x_ t_))) (* (abs (psi x_)) (abs (- x_ t_)))))
             (lambda () (crs)))
      (subst '(= (* (abs (- x_ t_)) (- m_ (abs (psi x_))))
                 (- (* m_ (abs (- x_ t_))) (* (abs (psi x_)) (abs (- x_ t_))))))
      (al-ineq '(<= (* (abs (psi x_)) (abs (- x_ t_))) (* m_ (abs (- x_ t_)))))))
  (fact 'rr-nonneg-cancel-pos '(abs (- x_ t_)) '(- m_ (abs (psi x_))))
  (al-ineq '(<= 0 (- m_ (abs (psi x_))))))

(quietly (lambda () (fact 'rr-zero-in) (fact 'rr-lt-trichotomy 'x_ 't_)))
(use-cases '((< x_ t_) (= x_ t_) (< t_ x_))
  (lambda ()
    (quietly (lambda ()
      (fact 'rr-sub-in-rr 'x_ 't_)
      (have! '(<= (- x_ t_) 0) (lambda () (al-ineq '(< x_ t_))))
      (fact 'rr-abs-of-nonpos '(- x_ t_))
      (have! '(= (- (- x_ t_)) (- t_ x_)) (lambda () (crs)))
      (have! '(< 0 (abs (- x_ t_)))
        (lambda () (subst '(= (abs (- x_ t_)) (- (- x_ t_))))
                   (subst '(= (- (- x_ t_)) (- t_ x_)))
                   (al-ineq '(< x_ t_))))
      (aw-tail!))))
  (lambda ()
    (quietly (lambda ()
      (subst '(= x_ t_))
      (subst '(= (psi t_) (phi t_)))
      (dk-deepest (lambda () (inst+ AW-BD 't_)))
      (ass))))
  (lambda ()
    (quietly (lambda ()
      (fact 'rr-sub-in-rr 'x_ 't_)
      (have! '(<= 0 (- x_ t_)) (lambda () (al-ineq '(< t_ x_))))
      (fact 'rr-abs-of-nonneg '(- x_ t_))
      (have! '(< 0 (abs (- x_ t_)))
        (lambda () (subst '(= (abs (- x_ t_)) (- x_ t_)))
                   (al-ineq '(< t_ x_))))
      (aw-tail!)))))
(qed 'caratheodory-witness-bound)
(topic! 'caratheodory-witness-bound 'analysis)
(alias! 'caratheodory-witness-bound
        "a bound on the integrand bounds every Caratheodory witness on the interval")

;;; =====================================================================
;;; 4.  THE PAIR ESTIMATE.  Prop 4.16's first display, with the constant of
;;; integration already normalised away.
;;; =====================================================================

;;; beta to exhaustion, guarded on PROGRESS -- never on a call count.
(define (al-beta!)
  (let loop ((n 0) (g (dk-goal)))
    (if (> n 6) #t
        (begin (lam-b)
               (let ((g2 (dk-goal)))
                 (if (equal? g g2) #t (loop (+ n 1) g2)))))))

(sp (make-wff "forall([f in fun(rr,rr), g in fun(rr,rr), phi in fun(rr,rr), psi in fun(rr,rr),
                       a in rr, b in rr, m_ in rr],
   is-antiderivative(f, phi, a, b) implies
   is-antiderivative(g, psi, a, b) implies
   f(a) = g(a) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(phi(x_) - psi(x_)) <= m_) implies
   forall([x_ in rr], x_ in ccint(a,b) implies abs(f(x_) - g(x_)) <= m_ * (b - a)))"))
(quietly (lambda () (al-peel!)))
(define AP-BD (al-find 'bd (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f 'abs)))))
(quietly (lambda ()
  (dk-split! (dk-deepest (lambda () (fact 'antiderivative-endpoints 'f 'phi 'a 'b))))
  ;; read the interval bounds off x_ WITHOUT losing the membership: `mac-h' is
  ;; destructive and antiderivative-lipschitz needs (IN x_ (CCINT a b)) itself.
  (have! '(AND (IN x_ RR) (AND (<= a x_) (<= x_ b)))
    (lambda () (mac-h 'ccint-membership '(IN x_ (CCINT a b))) (ass)))
  (dk-split! '(AND (IN x_ RR) (AND (<= a x_) (<= x_ b))))))
(define AP-SUB (dk-deepest
                 (lambda () (fact 'antiderivative-sub 'f 'g 'phi 'psi 'a 'b))))
(define AP-SUBF (cadr AP-SUB))
(define AP-SUBPHI (caddr AP-SUB))

(quietly (lambda ()
  (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
  (fact 'fun-apply-type-c 'g 'RR 'RR 'a)
  (fact 'fun-apply-type-c 'f 'RR 'RR 'x_)
  (fact 'fun-apply-type-c 'g 'RR 'RR 'x_)
  (fact 'rr-sub-in-rr '(f x_) '(g x_))
  (fact 'rr-abs-closed '(- (f x_) (g x_)))
  (fact 'rr-sub-in-rr 'x_ 'a)
  (fact 'rr-abs-closed '(- x_ a))
  (fact 'rr-sub-in-rr 'b 'a)
  (have! '(IN a (CCINT a b))
    (lambda () (mac 'ccint-membership)
               (al-and! (lambda ()
                 (let ((g (dk-goal)))
                   (cond ((eq? (car g) 'IN) (ass))
                         ((equal? (caddr g) 'a) (ineq))
                         (else (al-ineq '(< a b)))))))))
  ;; the integrand of the difference is bounded by m_ on [a,b]
  (have! (forall-guarded 'y_ '(IN y_ RR)
           (list 'IMPLIES (list 'IN 'y_ '(CCINT a b))
                 (list '<= (list 'abs (list AP-SUBPHI 'y_)) 'm_)))
    (lambda ()
      (di) (di)
      (fact 'fun-apply-type-c 'phi 'RR 'RR 'y_)
      (fact 'fun-apply-type-c 'psi 'RR 'RR 'y_)
      (al-beta!)
      (dk-deepest (lambda () (inst+ AP-BD 'y_)))
      (ass)))))

(quietly (lambda ()
  (fact 'antiderivative-map-in-fun AP-SUBF AP-SUBPHI 'a 'b)
  (fact 'antiderivative-fn-in-fun AP-SUBF AP-SUBPHI 'a 'b)
  (fact 'antiderivative-lipschitz AP-SUBF AP-SUBPHI 'a 'b 'm_ 'a 'x_)
  ;; SUBF(a) = 0 -- this is where f(a) = g(a) is spent -- and SUBF(x) = f(x)-g(x)
  (have! (list '= (list AP-SUBF 'a) 0)
    (lambda () (al-beta!) (subst '(= (f a) (g a))) (crs)))
  (have! (list '= (list AP-SUBF 'x_) '(- (f x_) (g x_)))
    (lambda () (al-beta!) (rfl)))
  (fact 'eq-sym (list AP-SUBF 'x_) '(- (f x_) (g x_)))
  (have! (list '= (list AP-SUBF 'x_)
                  (list '- (list AP-SUBF 'x_) (list AP-SUBF 'a)))
    (lambda () (subst (list '= (list AP-SUBF 'a) 0))
               (subst (list '= (list AP-SUBF 'x_) '(- (f x_) (g x_))))
               (crs)))
  (have! '(<= (abs (- (f x_) (g x_))) (* m_ (abs (- x_ a))))
    (lambda ()
      (subst (list '= '(- (f x_) (g x_)) (list AP-SUBF 'x_)))
      (subst (list '= (list AP-SUBF 'x_)
                      (list '- (list AP-SUBF 'x_) (list AP-SUBF 'a))))
      (ass)))
  ;; 0 <= m_ comes off the bound AT a; |x - a| <= b - a off the interval.
  (dk-deepest (lambda () (inst+ AP-BD 'a)))
  (fact 'fun-apply-type-c 'phi 'RR 'RR 'a)
  (fact 'fun-apply-type-c 'psi 'RR 'RR 'a)
  (fact 'rr-sub-in-rr '(phi a) '(psi a))
  (fact 'rr-abs-nonneg '(- (phi a) (psi a)))
  (have! '(<= 0 m_) (lambda () (al-ineq '(<= 0 (abs (- (phi a) (psi a))))
                                        '(<= (abs (- (phi a) (psi a))) m_))))
  (have! '(<= 0 (- x_ a)) (lambda () (al-ineq '(<= a x_))))
  (fact 'rr-abs-of-nonneg '(- x_ a))
  (have! '(<= (abs (- x_ a)) (- b a))
    (lambda () (subst '(= (abs (- x_ a)) (- x_ a))) (al-ineq '(<= x_ b))))
  (have! '(AND (<= 0 m_) (<= (abs (- x_ a)) (- b a))))
  (fact 'rr-le-scale-nonneg 'm_ '(abs (- x_ a)) '(- b a))
  (al-mul! 'm_ '(abs (- x_ a)))
  (al-mul! 'm_ '(- b a))
  (al-ineq '(<= (abs (- (f x_) (g x_))) (* m_ (abs (- x_ a))))
           '(<= (* m_ (abs (- x_ a))) (* m_ (- b a))))))
(qed 'antiderivative-pair-close)
(topic! 'antiderivative-pair-close 'analysis)
(alias! 'antiderivative-pair-close
        "Proposition 4.16 (the increment estimate)"
        "antiderivatives agreeing at a with close integrands stay close on [a,b]")
