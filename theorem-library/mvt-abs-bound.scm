;;; mvt-abs-bound.scm -- the TWO-SIDED corollary of the Mean Value Theorem:
;;;
;;;     |f'| <= M on (a,b)   =>   |f(b) - f(a)| <= M.(b - a)
;;;
;;; theorem-library/mvt-bounds-proof.scm proves the two ONE-SIDED forms
;;; (mvt-upper-bound, mvt-lower-bound).  Every estimate that actually wants a
;;; MODULUS -- a Lipschitz bound, a uniformly Cauchy family of antiderivatives,
;;; the witness estimate of calculus.pdf Prop 4.16 -- has to run both and glue
;;; them, and nothing in the tree did that.  This is the glue and nothing else:
;;; the upper form at M, the lower form at -M, and `rr-abs-bound' to read the
;;; pair as a modulus.
;;;
;;; THE HYPOTHESES ARE STATED IN Def 4.6's OWN SHAPES, deliberately.  The
;;; continuity clause is the CCINT-guarded universal
;;; `forall x in CCINT(a,b). IS-CONTINUOUS-AT(RR-MS, RR-MS, f, x)', and the
;;; derivative clause carries the CONJUNCTIVE antecedent
;;; `(AND (IN x RR) (AND (< a x) (< x b)))', both of which are what
;;; `IS-ANTIDERIVATIVE' unfolds to and what mvt-upper-bound/-lower-bound ask
;;; for.  A citation off an antiderivative is therefore a `fact' with no
;;; reshaping; stated in the curried form the surface writes more naturally,
;;; every citer would owe a four-line conversion.
;;;
;;; TWO MECHANICAL POINTS, both of which cost a run.
;;;
;;; * `inst+' does NOT detach a CONJUNCTIVE antecedent, and `ai' REPLACES the
;;;   conjunction in the context with its conjuncts.  So the hypothesis has to
;;;   be INSTANTIATED BEFORE the landed conjunction is split; done the other way
;;;   the instantiation silently lands the implication and the skolemization
;;;   below it has nothing to work on.
;;; * `rr-mul-closed' has a conjunctive antecedent too, so `M.(b-a) in RR' --
;;;   which `rr-abs-bound' needs before it will rewrite the goal at all -- wants
;;;   a `have!' of the AND first.  Without it `mac' declines, silently, and the
;;;   goal is still the modulus several steps later.
;;;
;;; WHAT IT COSTS.  `trust: well-known', and that is inherited, not incurred:
;;; `mvt-upper-bound' bills `rr-le-scale-nonneg-right' at `well-known' and the
;;; whole Rolle/MVT arc under it.  Nothing built on the MVT reads `modulo 0' in
;;; this tree today, and this file adds no leaf of its own.
;;;
;;; Loads after mvt-bounds-proof (mvt-upper-bound, mvt-lower-bound),
;;; rr-abs-basics (rr-abs-bound, rr-le-abs, rr-neg-abs-le, rr-abs-closed),
;;; binary-minus-laws (rr-sub-in-rr), fun-apply-type-proof and driver-kit.
;;; =====================================================================

;;; ---- file-local driver helpers (the `mv-' prefix) --------------------

(define (mv-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1))) #t))))

(define (mv-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (mv-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; `di' until an ASSUMPTION lands: an UNGUARDED universal with a conjunctive
;;; antecedent peels the QUANTIFIER and lands nothing, so never count `di's.
(define (mv-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "mv-di-landed!: nothing landed"))
            (else (loop (+ n 1)))))))

(define (mv-inst! fm t) (dk-deepest (lambda () (inst+ fm t))))

(define (mv-skolem! fm)
  (let* ((landed (dk-landed* (lambda () (ai fm))))
         (new (car landed)) (fvs-b (free-vars fm)))
    (list new (filter (lambda (v) (not (memq v fvs-b))) (free-vars new)))))

(define (mv-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mv-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (mv-ineq . forms) (apply ineq (map mv-idx forms)))

;;; ---- the statement ---------------------------------------------------

(sp (make-wff
 (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'm_
   (list 'IMPLIES '(IN f (FUN RR RR))
   (list 'IMPLIES '(IN a RR)
   (list 'IMPLIES '(IN b RR)
   (list 'IMPLIES '(IN m_ RR)
   (list 'IMPLIES '(< a b)
   (list 'IMPLIES '(FORALL x_ (IMPLIES (IN x_ (CCINT a b))
                                (IS-CONTINUOUS-AT RR-MS RR-MS f x_)))
   (list 'IMPLIES '(FORALL x_ (IMPLIES (AND (IN x_ RR) (AND (< a x_) (< x_ b)))
                                (FORSOME l_ (AND (IN l_ RR)
                                   (AND (IS-DIFF-AT f x_ l_) (<= (abs l_) m_))))))
     '(<= (abs (- (f b) (f a))) (* m_ (- b a))))))))))))))))
(quietly (lambda () (mv-peel!)))
(define MV-D (car (dk-asms)))          ; the two-sided derivative bound
(define MV-C (cadr (dk-asms)))         ; continuity on [a,b]

;;; The ONE-SIDED witness clause mvt-upper-bound / mvt-lower-bound ask for.
;;; SIDE selects which half of |L| <= m_ is spent.
(define (mv-side-clause bnd side)
  (list 'FORALL 'x_
     (list 'IMPLIES '(AND (IN x_ RR) (AND (< a x_) (< x_ b)))
        (list 'FORSOME 'l_ (list 'AND '(IS-DIFF-AT f x_ l_)
                                      (if (eq? side 'up) (list '<= 'l_ bnd)
                                                         (list '<= bnd 'l_)))))))

(define (mv-build-clause! bnd side)
  (have! (mv-side-clause bnd side)
    (lambda ()
      (let* ((la (car (mv-di-landed!)))     ; (AND (IN v RR) (AND (< a v) (< v b)))
             (v  (cadr (cadr la))))
        ;; INSTANTIATE BEFORE SPLITTING: `ai' replaces the conjunction with its
        ;; conjuncts, and the conjunction is what `inst+' detaches against.
        (let* ((inst (mv-inst! MV-D v))
               (sk (mv-skolem! inst))
               (lv (car (cadr sk))))
          (dk-split! (car sk))
          (fact 'rr-le-abs lv)
          (fact 'rr-neg-abs-le lv)
          (fact 'rr-abs-closed lv)
          (ew lv)
          (mv-and! (lambda ()
            (if (eq? (car (dk-goal)) 'IS-DIFF-AT) (ass)
                (mv-ineq (list '<= (list 'abs lv) 'm_)
                         (if (eq? side 'up) (list '<= lv (list 'abs lv))
                                            (list '<= (list '- (list 'abs lv)) lv)))))))))))

(quietly (lambda ()
  (fact 'rr-neg-closed 'm_)
  (fact 'rr-sub-in-rr 'b 'a)
  (fact 'fun-apply-type-c 'f 'RR 'RR 'b)
  (fact 'fun-apply-type-c 'f 'RR 'RR 'a)
  (fact 'rr-sub-in-rr '(f b) '(f a))
  ;; rr-mul-closed has a CONJUNCTIVE antecedent, which `fact' will not split
  (have! '(AND (IN m_ RR) (IN (- b a) RR)))
  (fact 'rr-mul-closed 'm_ '(- b a))
  (mv-build-clause! 'm_ 'up)
  (mv-build-clause! '(- m_) 'down)
  (have! '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN m_ RR) (< a b))))))
  (have! '(AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN b RR) (AND (IN (- m_) RR) (< a b))))))
  (fact 'mvt-upper-bound 'f 'a 'b 'm_)
  (fact 'mvt-lower-bound 'f 'a 'b '(- m_))
  (have! '(= (- (* m_ (- b a))) (* (- m_) (- b a))) (lambda () (crs)))
  (mac 'rr-abs-bound)
  (mv-and! (lambda ()
    ;; on the UPPER conjunct the subst is a no-op; on the LOWER one it turns
    ;; -(m_.(b-a)) into (-m_).(b-a), which is what mvt-lower-bound concluded.
    (vnb-guard (lambda () (subst '(= (- (* m_ (- b a))) (* (- m_) (- b a))))))
    (ass)))))
(qed 'mvt-abs-bound)
(topic! 'mvt-abs-bound 'analysis)
(alias! 'mvt-abs-bound
        "Mean Value Theorem (modulus corollary)"
        "a bound on the derivative bounds the increment")
