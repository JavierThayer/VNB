;;; bdd-metric-convergence.scm -- CONVERGENCE IS THE SAME IN d AND IN
;;; d/(1+d), proven: a sequence converges to L in BDD-METRIC(s) if and only if
;;; it converges to L in s.
;;;
;;; This is the SEQUENTIAL form of the topological equivalence that
;;; `bdd-metric-id-bicontinuous' and `bdd-metric-preserves-metric-top'
;;; (structure-library/bounded-metric.scm) assert about OPEN SETS.  The tree had
;;; no bridge from either of those to convergence -- METRIC-TOP equality is a
;;; statement about open sets, and getting a sequence out of it needs a
;;; "convergence is topological" lemma nothing has -- so the route here is the
;;; DIRECT one, through the algebra of f(t) = t/(1+t), and it adds no debt that
;;; the two asserted supports it does use do not already carry.
;;;
;;; It is the lemma the coordinate half of `product-convergence-coordinatewise'
;;; (structure-library/product-metric.scm) needs: the product metric is built on
;;; the per-factor BDD-METRIC, and the statement to be proven is about
;;; convergence in the factor (ms n) itself.
;;;
;;; WHAT HAD TO BE BUILT: `bdd-fn-reflect', the CONVERSE of `bdd-fn-mono'.  The
;;; bdd-fn-* family (structure-library/scalar-inequalities.scm) says f is
;;; nonnegative, bounded by 1, monotone, subadditive and below its argument; it
;;; does not say f REFLECTS the order, and that is exactly what the hard
;;; direction of the equivalence needs -- from rho <= f(eps) conclude d <= eps.
;;; The proof is the cross-multiplication, and it is `modulo 0': multiply
;;; a*recip(1+a) <= b*recip(1+b) by the nonnegative (1+a)(1+b), which is
;;; `rr-leq-mul-nonneg' (PRIMITIVE) on the difference, then `crs' collapses each
;;; side against (1+a)*recip(1+a) = 1 to a + a*b and b + a*b, and `ineq' reads
;;; a*b as one atom.  It belongs with the rest of the bdd-fn-* family and is
;;; here rather than there only because it needs `recip' order facts
;;; (rr-recip-pos / rr-recip-inverse / rr-le-ne-lt) that scalar-inequalities.scm
;;; loads before.
;;;
;;; TWO MECHANICS WORTH KEEPING.
;;;
;;; * `subst' rewrites LEFT to RIGHT in the GOAL, and there is no reversed form.
;;;   `bm-rev!' manufactures one: to get (= B A) from a context (= A B), cut
;;;   (= B A) and prove it by rewriting its own right-hand side with the
;;;   equation, which leaves (= B B) for `rfl'.  Three uses here, each one a
;;;   place where an equation had to be applied to a HYPOTHESIS.
;;;
;;; * The IFF is assembled by `prop' from the two implications, not by an
;;;   iff-introduction dance.  `prop' treats CONVERGES-TO(...) as an opaque
;;;   atom, which is all the assembly needs, and it discharges through the
;;;   kernel rules, so it costs no trust.
;;;
;;; Loads after theorem-library/rr-null-scale (the same neighbourhood:
;;; order-predicates, rr-recip-order, rr-order-basics, fun-apply-type-proof) and
;;; after structure-library/bounded-metric.

;;; ---- file-local driver helpers (the `bm-' prefix) --------------------

(define (bm-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (bm-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (bm-and2! a b) (have! (list 'AND a b) (lambda () (bm-and! (lambda () (ass))))))
(define (bm-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bm-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (bm-ineq . forms) (apply ineq (map bm-idx forms)))
(define (bm-eq! e) (have! e (lambda () (crs))) (subst e))
(define (bm-rev! e)   ; the reverse of a context equation, by rewriting with it
  (let ((r (list '= (caddr e) (cadr e))))
    (have! r (lambda () (subst e) (rfl)))
    r))
(define (bm-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 14) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))
(define (bm-one-plus! t)
  (let ((one+t (list '+ 1 t)))
    (bm-and2! '(IN 1 RR) (list 'IN t 'RR))
    (fact 'rr-add-closed 1 t)
    (have! (list '<= 1 one+t) (lambda () (bm-ineq (list '<= 0 t))))
    (bm-and2! '(< 0 1) (list '<= 1 one+t))
    (fact 'rr-lt-le-trans 0 1 one+t)
    (fact 'rr-pos-ne-zero one+t)
    (bm-and2! (list 'IN one+t 'RR) (list 'NOT (list '= one+t 0)))
    (fact 'rr-recip-closed one+t)
    (fact 'rr-recip-inverse one+t)
    (have! (list '<= 0 one+t) (lambda () (bm-ineq (list '<= 0 t))))))


;;; =====================================================================
;;; L1.  bdd-fn-reflect -- f(t)=t/(1+t) REFLECTS the order:  f(a) <= f(b)
;;; and a,b >= 0 give a <= b.  The converse of bdd-fn-mono, and the only new
;;; scalar fact this file needs.
;;; =====================================================================

(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
   (IMPLIES (<= 0 a) (IMPLIES (<= 0 b)
     (IMPLIES (<= (/ a (+ 1 a)) (/ b (+ 1 b))) (<= a b))))))))))
(bm-peel-to! '<=)
(mac-h 'binary-divide-def '(<= (/ a (+ 1 a)) (/ b (+ 1 b))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(bm-one-plus! 'a)
(bm-one-plus! 'b)
(define rf-ra '(recip (+ 1 a)))
(define rf-rb '(recip (+ 1 b)))
(define rf-A (list '* 'a rf-ra))
(define rf-B (list '* 'b rf-rb))
(define rf-c '(* (+ 1 a) (+ 1 b)))
(bm-and2! '(IN (+ 1 a) RR) '(IN (+ 1 b) RR))
(fact 'rr-mul-closed '(+ 1 a) '(+ 1 b))
(bm-and2! '(<= 0 (+ 1 a)) '(<= 0 (+ 1 b)))
(fact 'rr-leq-mul-nonneg '(+ 1 a) '(+ 1 b))
(bm-and2! (list 'IN 'a 'RR) (list 'IN rf-ra 'RR))
(fact 'rr-mul-closed 'a rf-ra)
(bm-and2! (list 'IN 'b 'RR) (list 'IN rf-rb 'RR))
(fact 'rr-mul-closed 'b rf-rb)
(fact 'rr-sub-in-rr rf-B rf-A)
(have! (list '<= 0 (list '- rf-B rf-A))
       (lambda () (bm-ineq (list '<= rf-A rf-B))))
(bm-and2! (list 'IN (list '- rf-B rf-A) 'RR) (list 'IN rf-c 'RR))
(bm-and2! (list '<= 0 (list '- rf-B rf-A)) (list '<= 0 rf-c))
(fact 'rr-leq-mul-nonneg (list '- rf-B rf-A) rf-c)
(bm-and2! (list 'IN rf-A 'RR) (list 'IN rf-c 'RR))
(fact 'rr-mul-closed rf-A rf-c)
(bm-and2! (list 'IN rf-B 'RR) (list 'IN rf-c 'RR))
(fact 'rr-mul-closed rf-B rf-c)
(have! (list '<= 0 (list '- (list '* rf-B rf-c) (list '* rf-A rf-c)))
  (lambda ()
    (bm-eq! (list '= (list '- (list '* rf-B rf-c) (list '* rf-A rf-c))
                     (list '* (list '- rf-B rf-A) rf-c)))
    (ass)))
(have! (list '<= (list '* rf-A rf-c) (list '* rf-B rf-c))
  (lambda () (bm-ineq (list '<= 0 (list '- (list '* rf-B rf-c) (list '* rf-A rf-c))))))
;; A*c = a + a*b  and  B*c = b + a*b
(define rf-ab '(+ a (* a b)))
(define rf-bb '(+ b (* a b)))
(have! (list '= (list '* rf-A rf-c) rf-ab)
  (lambda ()
    (bm-eq! (list '= (list '* rf-A rf-c) (list '* rf-ab (list '* '(+ 1 a) rf-ra))))
    (subst (list '= (list '* '(+ 1 a) rf-ra) 1))
    (crs)))
(have! (list '= (list '* rf-B rf-c) rf-bb)
  (lambda ()
    (bm-eq! (list '= (list '* rf-B rf-c) (list '* rf-bb (list '* '(+ 1 b) rf-rb))))
    (subst (list '= (list '* '(+ 1 b) rf-rb) 1))
    (crs)))
(define rf-e1 (bm-rev! (list '= (list '* rf-A rf-c) rf-ab)))
(define rf-e2 (bm-rev! (list '= (list '* rf-B rf-c) rf-bb)))
(have! (list '<= rf-ab rf-bb)
  (lambda () (subst rf-e1) (subst rf-e2) (ass)))
(bm-and2! '(IN a RR) '(IN b RR))
(fact 'rr-mul-closed 'a 'b)
(bm-ineq (list '<= rf-ab rf-bb))
(qed 'bdd-fn-reflect)

;;; =====================================================================
;;; L2.  bdd-metric-dist-le      rho(x,y) <= d(x,y)          [the easy way]
;;; L3.  bdd-metric-dist-reflect rho(x,y) <= e/(1+e)  =>  d(x,y) <= e
;;; the two metric-level readings of bdd-fn-le-arg and L1.
;;; =====================================================================

(define (bm-fvs forms) (apply append (map free-vars forms)))
(define (bm-skolem! ex)
  (let* ((fv0 (bm-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (bm-fvs (dk-asms)))))
      (if (null? fresh) (error "bm-skolem!: nothing appeared" ex) (car fresh)))))
(define (bm-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "bm-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define (bm-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "bm-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (bm-di-landed-1!)
  (let ((new (bm-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "bm-di-landed-1!: expected 1" (map expression->string new)))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
  (FORALL x_ (IMPLIES (IN x_ (PTS s))
    (FORALL y_ (IMPLIES (IN y_ (PTS s))
      (<= ((DIST (BDD-METRIC s)) x_ y_) ((DIST s) x_ y_))))))))))
(bm-peel-to! '<=)
(fact 'metric-dist-real 's 'x_ 'y_)
(fact 'metric-pos 's 'x_ 'y_)
(fact 'bdd-metric-distance 's 'x_ 'y_)
(subst '(= ((DIST (BDD-METRIC s)) x_ y_) (/ ((DIST s) x_ y_) (+ 1 ((DIST s) x_ y_)))))
(fact 'bdd-fn-le-arg '((DIST s) x_ y_))
(ass)
(qed 'bdd-metric-dist-le)

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
  (FORALL x_ (IMPLIES (IN x_ (PTS s))
    (FORALL y_ (IMPLIES (IN y_ (PTS s))
      (FORALL e_ (IMPLIES (IN e_ RR) (IMPLIES (<= 0 e_)
        (IMPLIES (<= ((DIST (BDD-METRIC s)) x_ y_) (/ e_ (+ 1 e_)))
                 (<= ((DIST s) x_ y_) e_)))))))))))))
(bm-peel-to! '<=)
(fact 'metric-dist-real 's 'x_ 'y_)
(fact 'metric-pos 's 'x_ 'y_)
(mac-h 'bdd-metric-distance
       '(<= ((DIST (BDD-METRIC s)) x_ y_) (/ e_ (+ 1 e_))))
(fact 'bdd-fn-reflect '((DIST s) x_ y_) 'e_)
(ass)
(qed 'bdd-metric-dist-reflect)

;;; ---------------------------------------------------------------------
(define (bm-pos-parts! x)   ; IN x RR, 0 <= x, NOT (= 0 x) from POS-RR x, kept
  (for-each
   (lambda (part)
     (have! part (lambda ()
                   (mac-h 'pos-rr (list 'POS-RR x))
                   (dk-split! (list 'AND (list 'IN x 'RR)
                                    (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
                   (ass))))
   (list (list 'IN x 'RR) (list '<= 0 x) (list 'NOT (list '= 0 x)))))

;;; =====================================================================
;;; L4.  bdd-metric-converges-fwd -- convergence in s gives convergence in
;;; BDD-METRIC s.  The SAME threshold works: rho <= d.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
  (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
    (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
      (IMPLIES (CONVERGES-TO s f lm_) (CONVERGES-TO (BDD-METRIC s) f lm_))))))))))
(bm-peel-to! 'CONVERGES-TO)
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO s f lm_)))
                           (lambda (a) (eq? (car a) 'AND))))
(define bf-tail (bm-find 'tail
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(fact 'bdd-metric-is-metric-space 's)
(fact 'bdd-metric-carrier 's)
(mac 'converges-to)
(bm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'IN) (mac 'bdd-metric-carrier) (ass))
           (else
            (let* ((eps (cadr (bm-di-landed-1!)))
                   (nex (dk-deepest (lambda () (inst+ bf-tail eps))))
                   (bigN (bm-skolem! nex))
                   (innerf (bm-find 'inner
                             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                              (let ((b (caddr a)))
                                                (and (pair? b) (eq? (car b) 'IMPLIES)
                                                     (dk-contains? (caddr b) bigN))))))))
              (bm-pos-parts! eps)
              (ew bigN)
              (bm-and!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (let ((n_ (cadr (bm-di-landed-1!))))
                       (bm-di-landed!)
                       (inst+ innerf n_)
                       (fact 'fun-apply-type-c 'f 'NN '(PTS s) n_)
                       (fact 'metric-dist-real 's (list 'f n_) 'lm_)
                       (fact 'bdd-metric-dist-le 's (list 'f n_) 'lm_)
                       (have! (list 'IN (list 'f n_) '(PTS (BDD-METRIC s)))
                              (lambda () (mac 'bdd-metric-carrier) (ass)))
                       (have! '(IN lm_ (PTS (BDD-METRIC s)))
                              (lambda () (mac 'bdd-metric-carrier) (ass)))
                       (fact 'metric-dist-real '(BDD-METRIC s) (list 'f n_) 'lm_)
                       (bm-ineq (list '<= (list '(DIST (BDD-METRIC s)) (list 'f n_) 'lm_)
                                          (list '(DIST s) (list 'f n_) 'lm_))
                                (list '<= (list '(DIST s) (list 'f n_) 'lm_) eps))))))))))))
(qed 'bdd-metric-converges-fwd)

;;; =====================================================================
;;; L5.  bdd-metric-converges-bwd -- and back.  The threshold is the one the
;;; bounded metric supplies at delta = eps/(1+eps); L3 turns it into eps.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
  (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
    (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
      (IMPLIES (CONVERGES-TO (BDD-METRIC s) f lm_) (CONVERGES-TO s f lm_))))))))))
(bm-peel-to! 'CONVERGES-TO)
(dk-split! (dk-landed-find
            (lambda () (mac-h 'converges-to '(CONVERGES-TO (BDD-METRIC s) f lm_)))
            (lambda (a) (eq? (car a) 'AND))))
(define bb-tail (bm-find 'tail
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))
(fact 'rr-zero-in)
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(mac 'converges-to)
(bm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IS-METRIC-SPACE) (ass))
           ((eq? (car g) 'IN) (ass))
           (else
            (let* ((eps (cadr (bm-di-landed-1!)))
                   (dlt (list '/ eps (list '+ 1 eps))))
              (bm-pos-parts! eps)
              (bm-one-plus! eps)
              (fact 'rr-recip-pos (list '+ 1 eps))
              (bm-and2! (list '<= 0 eps) (list 'NOT (list '= 0 eps)))
              (fact 'rr-le-ne-lt 0 eps)
              (fact 'rr-mul-pos eps (list 'recip (list '+ 1 eps)))
              (have! (list 'POS-RR dlt)
                (lambda ()
                  (mac 'binary-divide-def)
                  (dk-split! (dk-landed-find
                              (lambda () (mac-h '< (list '< 0 (list '* eps (list 'recip (list '+ 1 eps))))))
                              (lambda (a) (eq? (car a) 'AND))))
                  (bm-and2! (list 'IN eps 'RR) (list 'IN (list 'recip (list '+ 1 eps)) 'RR))
                  (fact 'rr-mul-closed eps (list 'recip (list '+ 1 eps)))
                  (mac 'pos-rr)
                  (bm-and! (lambda () (ass)))))
              ;; LUTINS instantiation (2026-09-18): the tail universal is
              ;; instantiated AT dlt = eps/(1+eps), a quotient, which owes
              ;; (= dlt dlt) unless the context types it.  The owed-leaf hook
              ;; runs `in-rr' and cannot see through `/'; `binary-divide-def'
              ;; can, and `bm-one-plus!' above already typed recip(1+eps).
              (have! (list 'IN dlt 'RR)
                (lambda ()
                  (mac 'binary-divide-def)
                  (bm-and2! (list 'IN eps 'RR)
                            (list 'IN (list 'recip (list '+ 1 eps)) 'RR))
                  (fact 'rr-mul-closed eps (list 'recip (list '+ 1 eps)))
                  (ass)))
              (let* ((nex (dk-deepest (lambda () (inst+ bb-tail dlt))))
                     (bigN (bm-skolem! nex))
                     (innerf (bm-find 'inner
                               (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                                (let ((b (caddr a)))
                                                  (and (pair? b) (eq? (car b) 'IMPLIES)
                                                       (dk-contains? (caddr b) bigN))))))))
                (ew bigN)
                (bm-and!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'IN) (ass)
                       (let ((n_ (cadr (bm-di-landed-1!))))
                         (bm-di-landed!)
                         (inst+ innerf n_)
                         (fact 'fun-apply-type-c 'f 'NN '(PTS s) n_)
                         (fact 'bdd-metric-dist-reflect 's (list 'f n_) 'lm_ eps)
                         (ass))))))))))))
(qed 'bdd-metric-converges-bwd)

;;; =====================================================================
;;; L6.  bdd-metric-converges-iff -- the two, assembled by `prop'.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
  (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
    (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
      (IFF (CONVERGES-TO (BDD-METRIC s) f lm_) (CONVERGES-TO s f lm_))))))))))
(bm-peel-to! 'IFF)
(fact 'bdd-metric-converges-fwd 's 'f 'lm_)
(fact 'bdd-metric-converges-bwd 's 'f 'lm_)
(prop)
(qed 'bdd-metric-converges-iff)

(topic! 'bdd-fn-reflect 'analysis)
(alias! 'bdd-fn-reflect "t/(1+t) reflects the order")
(topic! 'bdd-metric-dist-le 'analysis)
(alias! 'bdd-metric-dist-le "the bounded metric is below the metric")
(topic! 'bdd-metric-dist-reflect 'analysis)
(alias! 'bdd-metric-dist-reflect "a small bounded distance means a small distance")
(topic! 'bdd-metric-converges-fwd 'analysis)
(alias! 'bdd-metric-converges-fwd "convergence passes to the bounded metric")
(topic! 'bdd-metric-converges-bwd 'analysis)
(alias! 'bdd-metric-converges-bwd "convergence passes back from the bounded metric")
(topic! 'bdd-metric-converges-iff 'analysis)
(alias! 'bdd-metric-converges-iff
        "a sequence converges in the bounded metric exactly when it converges")
