;;; metric-limit-unique.scm -- A SEQUENCE IN A METRIC SPACE HAS AT MOST ONE
;;; LIMIT, proven once for an arbitrary metric space, with the RR and CC cases
;;; taken as instances.
;;;
;;;     metric-limit-unique:
;;;       CONVERGES-TO(s, f, lm1)  and  CONVERGES-TO(s, f, lm2)  =>  lm1 = lm2
;;;
;;; THE STATEMENT CARRIES NO TYPING HYPOTHESES, and that is not an economy but
;;; the reason the instances are three lines each.  CONVERGES-TO
;;; (structure-library/metric-completeness.scm) is a four-fold conjunction whose
;;; first three conjuncts are IS-METRIC-SPACE(s), IN f (FUN NN (PTS s)) and
;;; IN L (PTS s).  Everything the proof needs about s, f and the two limits is
;;; therefore already inside the hypothesis; adding `IS-METRIC-SPACE(s)' or a
;;; PTS-typing to the statement would oblige every citer to supply what it is
;;; about to hand over anyway.  In particular the RR instance below does NOT
;;; cite `rr-is-metric-space' -- which is still an asserted axiom -- so
;;; generalising this theorem costs no bill anywhere.
;;;
;;; THE ARGUMENT.  It is the textbook one, and in the abstract metric it is
;;; SHORTER than the RR-specific proof it replaces, because no absolute value
;;; ever appears:
;;;
;;;   d(lm1, lm2)  <=  d(lm1, f(n))  +  d(f(n), lm2)      metric-triangle
;;;                 =  d(f(n), lm1)  +  d(f(n), lm2)      metric-sym
;;;                 <=  e/2 + e/2  =  e                   at n = max(N1, N2)
;;;
;;; for every e > 0; then `rr-le-all-pos-nonpos' gives d(lm1,lm2) <= 0,
;;; `metric-pos' gives 0 <= d(lm1,lm2), antisymmetry makes it 0, and
;;; `metric-zero-eq' -- the identity of indiscernibles -- finishes.  The five
;;; metric laws are PROVEN by projection of the is-metric property
;;; (structure-library/metric-laws.scm), so none of them is debt.
;;;
;;; WHAT IT REPLACES.  `rr-limit-unique' was proved in
;;; theorem-library/dominated-convergence.scm (L8), sixty lines, entirely inside
;;; the reals: it unfolded (DIST RR-MS) to `abs' by `rr-ms-dist' and then spent
;;; its length on rr-abs-* bookkeeping -- rr-le-abs, rr-neg-abs-le,
;;; rr-abs-sub-sym, rr-abs-closed -- to put the two estimates in front of the
;;; oracle.  None of that is about limits.  The statement re-installed below is
;;; BYTE-IDENTICAL to the one that file installed, so every citer sees the
;;; formula it always saw; the install reports "re-installing the same
;;; statement" if the old proof is ever restored beside this one.
;;;
;;; WHAT IT BUYS.  `cc-limit-unique' -- the same three lines at CC-MS -- which
;;; is what makes a complex series limit describable by IOTA, and so is a
;;; precondition for defining the complex exponential by its power series
;;; (theorem-library/cc-series.scm is the companion brick).  The tree had limit
;;; uniqueness for RR only, which is why `iota-d' could post the uniqueness half
;;; of a real description and no complex one.
;;;
;;; Loads after metric-laws (the five laws), op-typing (metric-dist-real),
;;; rr-halving (rr-pos-halvable), rr-le-all-pos-nonpos, rr-max-basics
;;; (nn-max-closed, rr-le-max-left/right) and complex (CC-MS); must PRECEDE
;;; dominated-convergence, which cites rr-limit-unique and no longer proves it.

;;; -----------------------------------------------------------------------
;;; File-local driver helpers (prefix `mlu-'; see CLAUDE.md on where a driver
;;; helper lives).
;;; -----------------------------------------------------------------------

(define (mlu-fvs forms) (apply append (map free-vars forms)))

;;; `di' until an ASSUMPTION lands.  An UNGUARDED (FORALL x (IMPLIES ...))
;;; peels the quantifier and lands nothing, so loop on the LANDING, never on a
;;; count of `di's.
(define (mlu-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "mlu-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))

;;; Select a context formula by CONTENT, and ERROR on a miss: a focus helper
;;; that returns #f hides every later step running in the wrong branch.
(define (mlu-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "mlu-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; Skolemize a FORSOME that is ALREADY in the context.  `obtain' diffs its own
;;; lane and so cannot see one, and it swallows the error; the eigenvariable is
;;; read off here by free-variable set difference, and a miss errors.
(define (mlu-skolem! ex)
  (let* ((fv0 (mlu-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (mlu-fvs (dk-asms)))))
      (if (null? fresh)
          (error "mlu-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; `ineq' premise indices are 1-BASED, and premises are named ONE BY ONE: a
;;; single premise whose atoms cannot be certified in RR poisons the call.
(define (mlu-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "mlu-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(define (mlu-ineq . forms) (apply ineq (map mlu-idx forms)))

;;; POS-RR(x) => IN x RR, on a side lane so the POS-RR hypothesis survives.
(define (mlu-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; =======================================================================
;;; metric-limit-unique.
;;; =======================================================================

(sp (make-wff '(FORALL s (FORALL f (FORALL lm1 (FORALL lm2
   (IMPLIES (CONVERGES-TO s f lm1)
     (IMPLIES (CONVERGES-TO s f lm2) (= lm1 lm2)))))))))

;; Three `di's: the four quantifiers are UNGUARDED, so the first call peels all
;; four and lands nothing; the two antecedents come one per call after that.
(di) (di) (di)

(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO s f lm1)))
                           (dk-head? 'AND)))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to '(CONVERGES-TO s f lm2)))
                           (dk-head? 'AND)))

;;; The eps-tail of each hypothesis, discriminated by the LIMIT it mentions --
;;; never by shape: the two tails are the same shape.
(define (mlu-tail-of lm)
  (mlu-find lm (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (dk-contains? a lm) (dk-contains? a 'POS-RR)))))
(define mlu-t1 (mlu-tail-of 'lm1))
(define mlu-t2 (mlu-tail-of 'lm2))

;;; After a tail is instantiated at d and skolemized, its inner universal is the
;;; one mentioning the fresh threshold and no longer mentioning POS-RR.
(define (mlu-inner thr)
  (mlu-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a thr)
                                 (not (dk-contains? a 'POS-RR))))))

;;; d(lm1, lm2) <= eps for EVERY positive eps.  One lane; the mirror image is
;;; not needed, symmetry of the metric doing that work here.
(have! (list 'FORALL 'eps
         (list 'IMPLIES '(POS-RR eps)
               (list '<= (list (list 'DIST 's) 'lm1 'lm2) 'eps)))
  (lambda ()
    (mlu-di-landed!)
    (let* ((hex (dk-fact! 'rr-pos-halvable 'eps))
           (d   (mlu-skolem! hex))
           (e1  (dk-deepest (lambda () (inst+ mlu-t1 d))))
           (n1  (mlu-skolem! e1))
           (i1  (mlu-inner n1))
           (e2  (dk-deepest (lambda () (inst+ mlu-t2 d))))
           (n2  (mlu-skolem! e2))
           (i2  (mlu-inner n2))
           (bnd (list 'MAX n1 n2))
           (fb  (list 'f bnd)))
      (fact 'nn-max-closed n1 n2)
      (fact 'nn-in-rr n1) (fact 'nn-in-rr n2)
      (fact 'rr-le-max-left n1 n2)
      (fact 'rr-le-max-right n1 n2)
      (inst+ i1 bnd)
      (inst+ i2 bnd)
      (fact 'fun-apply-type-c 'f 'NN '(PTS s) bnd)
      (fact 'metric-sym 's 'lm1 fb)
      (fact 'metric-triangle 's 'lm1 fb 'lm2)
      ;; every atom the oracle sees needs an `IN _ RR' certificate
      (fact 'metric-dist-real 's 'lm1 'lm2)
      (fact 'metric-dist-real 's 'lm1 fb)
      (fact 'metric-dist-real 's fb 'lm1)
      (fact 'metric-dist-real 's fb 'lm2)
      (mlu-pos-in-rr! 'eps) (mlu-pos-in-rr! d)
      (mlu-ineq (list '<= (list (list 'DIST 's) 'lm1 'lm2)
                      (list '+ (list (list 'DIST 's) 'lm1 fb) (list (list 'DIST 's) fb 'lm2)))
                (list '= (list (list 'DIST 's) 'lm1 fb) (list (list 'DIST 's) fb 'lm1))
                (list '<= (list (list 'DIST 's) fb 'lm1) d)
                (list '<= (list (list 'DIST 's) fb 'lm2) d)
                (list '= (list '+ d d) 'eps)))))

;;; A nonnegative real bounded by every positive is 0, and a metric that
;;; vanishes identifies its arguments.
(define mlu-d12 '((DIST s) lm1 lm2))
(fact 'metric-dist-real 's 'lm1 'lm2)
(fact 'rr-le-all-pos-nonpos mlu-d12)
(fact 'metric-pos 's 'lm1 'lm2)
(fact 'rr-zero-in)
(have! (list 'AND (list 'IN mlu-d12 'RR) '(IN 0 RR)))
(have! (list 'AND (list '<= mlu-d12 0) (list '<= 0 mlu-d12)))
(fact 'rr-leq-antisymmetric mlu-d12 0)
(fact 'metric-zero-eq 's 'lm1 'lm2)
(ass)

(qed 'metric-limit-unique)
(topic! 'metric-limit-unique 'analysis)
(alias! 'metric-limit-unique
        "a sequence in a metric space has at most one limit")

;;; =======================================================================
;;; The two instances.  Each is the general theorem at one space: `fact' peels
;;; the four universals and detaches both convergence hypotheses from the
;;; context, so there is nothing else to do.
;;; =======================================================================

;;; RR -- statement byte-identical to the proof this file retires.
(sp (make-wff "forall([f in fun(nn,rr), lm1 in rr, lm2 in rr],
     converges-to(rr-ms, f, lm1) implies converges-to(rr-ms, f, lm2) implies
     lm1 = lm2)"))
(di) (di) (di)
(fact 'metric-limit-unique 'RR-MS 'f 'lm1 'lm2)
(ass)
(qed 'rr-limit-unique)
(topic! 'rr-limit-unique 'analysis)
(alias! 'rr-limit-unique "a real sequence has at most one limit")

;;; CC.
(sp (make-wff "forall([f in fun(nn,cc), lm1 in cc, lm2 in cc],
     converges-to(cc-ms, f, lm1) implies converges-to(cc-ms, f, lm2) implies
     lm1 = lm2)"))
(di) (di) (di)
(fact 'metric-limit-unique 'CC-MS 'f 'lm1 'lm2)
(ass)
(qed 'cc-limit-unique)
(topic! 'cc-limit-unique 'analysis)
(alias! 'cc-limit-unique "a complex sequence has at most one limit")
