;;; c-metric-summable.scm -- THE SERIES DEFINING THE CANONICAL METRIC OF A
;;; COUNTABLY-METRISED SPACE CONVERGES, proven, together with the plumbing every
;;; later argument about C-METRIC needs.
;;;
;;;     D_w(a,b) = SUM_k w(k) * min(1, d_k(a,b)),   d_k = DISTS(s)(k).
;;;
;;; The file is the mirror of theorem-library/product-summable.scm one
;;; construction over, and deliberately so: same lemma order, same helper
;;; prefix discipline, same three obstacles.  What is DIFFERENT is where the
;;; termwise bound comes from.  The product metric truncates with BDD-METRIC and
;;; spends `bdd-metric-bounded'; here the truncation is min(1,.) and the bound
;;; is `rr-min-le-left', with `rr-le-min' for the lower one -- no `recip', so
;;; `crs' can be used on the one algebraic step (see L3).
;;;
;;;   L1  c-metric-pseudometric-at    d_k is a pseudometric on PTS(s)
;;;   L2  c-metric-dist-real          d_k(u,v) in RR
;;;   L3  c-metric-term-bound         0 <= w(k)*min(1,d_k(u,v)) <= w(k)
;;;   L4  c-metric-term-seq-in-fun    the term sequence is a real sequence
;;;   L5  c-metric-summable           the series converges
;;;   L6  c-metric-carrier            PTS(C-METRIC-W(s,w)) == PTS(s)
;;;   L7  c-metric-distance           the distance FORMULA
;;;   L8  c-metric-dist-converges     the series converges TO the distance
;;;   L9  c-metric-canonical-summable the canonical instance, weights 2^-(k+1)
;;;
;;; THREE MECHANICS WORTH KEEPING.
;;;
;;; 1.  `c-metric-dist-real' IS PROVEN, where the metric-space analogue
;;;     `metric-dist-real' (structure-library/metric-space.scm) is an ASSERTED
;;;     support whose warrant reads "codomain typing of the metric op ...  kept
;;;     as a warranted PSS support rather than re-grinding the tuple typing in
;;;     every metric proof".  The grind is four citations and it is done once:
;;;     `fun-apply-type-c' twice (DISTS(s) at k, then d_k at the pair),
;;;     `pair-in-cartesian' for the pair, and `apply-tupling-2' to cross between
;;;     the curried surface form d(u,v) and the tupled d([u,v]) that
;;;     `fun-apply-type-c' delivers.  The last is used as a `subst' of the
;;;     quasi-equality, NOT as a macete: `(mac 'apply-tupling-2)' reports
;;;     "macete not applicable" -- the axiom's left side is a bare application
;;;     with a schema variable in head position.  Nothing in the tree had ever
;;;     cited apply-tupling-2 before.
;;;
;;; 2.  UNFOLD IS-C-METRIC-SPACE LAST, OR NOT AT ALL.  `mac-h' REPLACES the
;;;     hypothesis it unfolds, so a driver that opens IS-C-METRIC-SPACE(s) to
;;;     reach its conjuncts has deleted the hypothesis that every `fact' of L1,
;;;     L2 and L3 needs to detach.  L3 does not unfold it at all; L4 and L5 cite
;;;     the earlier lemmas BEFORE unfolding SUMMABLE-WEIGHT for the same reason.
;;;
;;; 3.  The weight hypothesis is a general `SUMMABLE-WEIGHT w' throughout, so
;;;     the canonical instance (L9) is one `fact' of the PROVEN
;;;     `product-metric-default-summable' (theorem-library/dyadic-weights.scm)
;;;     and no dyadic arithmetic is repeated.
;;;
;;; Loads after theorem-library/dyadic-weights (product-metric-default-summable),
;;; comparison-test-proof (comparison-test), dominated-convergence
;;; (series-limit-converges-to, SERIES-LIMIT), pseudometric-laws
;;; (pseudometric-pos), rr-min-basics (the min laws), pair-tuple-sethood
;;; (pair-in-cartesian) and structure-library/c-metric-space.

;;; ---- file-local driver helpers (the `cm-' prefix) --------------------

(define (cm-peel-to! head)
  (let lp ((n 0))
    (if (and (< n 18) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ n 1))))))

(define (cm-find pred)
  (let lp ((l (dk-asms)))
    (cond ((null? l) #f) ((pred (car l)) (car l)) (else (lp (cdr l))))))

(define (cm-need what pred)
  (or (cm-find pred) (error "cm-need: no context formula" what)))

(define (cm-split-all!)
  (let lp ()
    (let ((a (cm-find (lambda (f) (eq? (car f) 'AND)))))
      (if a (begin (ai a) (lp))))))

(define (cm-unfold-is!)
  (mac-h 'IS-C-METRIC-SPACE '(IS-C-METRIC-SPACE s))
  (cm-split-all!))

(define (cm-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (cm-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

(define (cm-and2! a b)
  (have! (list 'AND a b) (lambda () (cm-and! (lambda () (ass))))))

(define (cm-idx form)
  (let lp ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cm-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (lp (cdr l) (+ i 1))))))

(define (cm-ineq . forms) (apply ineq (map cm-idx forms)))

(define (cm-eq! e) (have! e (lambda () (crs))) (subst e))

;; the conjuncts of a context (< a b), landed without destroying it
(define (cm-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (have! part (lambda ()
                     (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                (lambda (f) (eq? (car f) 'AND))))
                     (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

(define (cm-di-landed-1!)
  (let lp ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) (car new))
            ((> n 5) (error "cm-di-landed-1!: di landed no assumption"))
            (else (lp (+ n 1)))))))

;;; the term sequence of the canonical metric, as an S-expression
(define (cm-term-lambda-w wt u v)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list wt 'k) (list 'min 1 (list (list '(DISTS s) 'k) u v)))))
(define (cm-term-lambda u v) (cm-term-lambda-w 'w u v))

;;; =====================================================================
;;; L1.  c-metric-pseudometric-at -- the k-th member of the family is a
;;; pseudometric on the carrier.  The first law of the declaration,
;;; instantiated; a theorem rather than a `have!' because L3 and every later
;;; metric-law argument wants it in one citation.
;;; =====================================================================

(sp (make-wff "forall([s], is-c-metric-space(s) implies
   forall([k_ in nn], is-pseudometric(dists(s)(k_), pts(s))))"))
(cm-peel-to! 'IS-PSEUDOMETRIC)
(cm-unfold-is!)
(inst+ (cm-need 'pseudometric-law
         (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f 'IS-PSEUDOMETRIC))))
       'k_)
(ass)
(qed 'c-metric-pseudometric-at)
(topic! 'c-metric-pseudometric-at 'constructions)
(alias! 'c-metric-pseudometric-at
        "each member of the family of a countably-metrised space is a pseudometric")

;;; =====================================================================
;;; L2.  c-metric-dist-real -- the k-th distance is real.  See mechanic 1 in
;;; the header: this is the chain `metric-dist-real' declines to run.
;;; =====================================================================

(sp (make-wff "forall([s], is-c-metric-space(s) implies
   forall([k_ in nn, u_ in pts(s), v_ in pts(s)], dists(s)(k_)(u_, v_) in rr))"))
(cm-peel-to! 'IN)
(cm-unfold-is!)
(fact 'fun-apply-type-c '(DISTS s) 'NN '(FUN (CARTESIAN (PTS s) (PTS s)) RR) 'k_)
(fact 'pair-in-cartesian '(PTS s) '(PTS s) 'u_ 'v_)
(fact 'fun-apply-type-c '((DISTS s) k_) '(CARTESIAN (PTS s) (PTS s)) 'RR '(LIST u_ v_))
(fact 'apply-tupling-2 '((DISTS s) k_) 'u_ 'v_)
(subst '(== (((DISTS s) k_) u_ v_) (((DISTS s) k_) (LIST u_ v_))))
(ass)
(qed 'c-metric-dist-real)
(topic! 'c-metric-dist-real 'constructions)
(alias! 'c-metric-dist-real
        "each pseudometric of a countably-metrised space is real-valued")

;;; =====================================================================
;;; L3.  c-metric-term-bound -- everything one term of the defining series
;;; owes: w(k)*min(1,d_k) is real, is nonnegative, and is at most w(k).
;;;
;;; The upper bound is derived from `rr-leq-mul-nonneg' (PRIMITIVE): from
;;; 0 <= 1 - min(1,d) and 0 <= w, `crs' rewrites 0 <= (1-min(1,d))*w into
;;; 0 <= w - w*min(1,d).  No multiplicative order lemma is cited, and `crs'
;;; is usable precisely because min(1,d) is an opaque atom to it and there is
;;; no `recip' anywhere in the term.
;;; =====================================================================

(define cm-d '(((DISTS s) k_) u_ v_))
(define cm-m (list 'min 1 cm-d))
(define cm-t (list '* 'wk cm-m))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
   (forall-guarded '(k_ u_ v_ wk)
                   (list '(IN k_ NN) '(IN u_ (PTS s)) '(IN v_ (PTS s)) '(IN wk RR))
     (list 'IMPLIES '(<= 0 wk)
       (conjuncts->and (list (list 'IN cm-t 'RR)
                             (list '<= 0 cm-t)
                             (list '<= cm-t 'wk)))))))))
(cm-peel-to! 'AND)
(fact 'c-metric-dist-real 's 'k_ 'u_ 'v_)
(fact 'c-metric-pseudometric-at 's 'k_)
(fact 'pseudometric-pos '((DISTS s) k_) '(PTS s) 'u_ 'v_)
(fact 'rr-one-in)
(fact 'rr-min-closed 1 cm-d)
(fact 'rr-min-le-left 1 cm-d)
(have! '(<= 0 1) (lambda () (arith)))
(fact 'rr-le-min 1 cm-d 0)
(cm-and2! '(IN wk RR) (list 'IN cm-m 'RR))
(fact 'rr-mul-closed 'wk cm-m)
(fact 'rr-sub-in-rr 1 cm-m)
(have! (list '<= 0 (list '- 1 cm-m)) (lambda () (cm-ineq (list '<= cm-m 1))))
(cm-and2! (list 'IN (list '- 1 cm-m) 'RR) '(IN wk RR))
(cm-and2! (list '<= 0 (list '- 1 cm-m)) '(<= 0 wk))
(fact 'rr-leq-mul-nonneg (list '- 1 cm-m) 'wk)
(have! (list '<= 0 (list '- 'wk cm-t))
  (lambda ()
    (cm-eq! (list '= (list '- 'wk cm-t) (list '* (list '- 1 cm-m) 'wk)))
    (ass)))
(cm-and2! '(<= 0 wk) (list '<= 0 cm-m))
(fact 'rr-leq-mul-nonneg 'wk cm-m)
(cm-and!
 (lambda ()
   (let ((g (dk-goal)))
     (cond ((eq? (car g) 'IN) (ass))
           ((equal? (cadr g) 0) (ass))
           (else (cm-ineq (list '<= 0 (list '- 'wk cm-t))))))))
(qed 'c-metric-term-bound)
(topic! 'c-metric-term-bound 'analysis)
(alias! 'c-metric-term-bound
        "a weighted truncated pseudodistance lies between 0 and its weight")

;;; =====================================================================
;;; L4 and L5.  The term sequence is a real sequence, and its series
;;; converges.  Both peel the same two hypotheses; the per-index work is the
;;; helper `cm-term!', which lands the three bounds of L3 at one index.
;;; =====================================================================

;;; the two universals the per-index helper instantiates, read off the context
;;; after SUMMABLE-WEIGHT has been opened
(define cm-wpos #f)
(define (cm-setup!)
  (dk-split! (dk-landed-find (lambda () (mac-h 'summable-weight '(SUMMABLE-WEIGHT w)))
                             (lambda (f) (eq? (car f) 'AND))))
  (set! cm-wpos (cm-need 'w-positivity
                  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a '<))))))

;;; everything the k-th term of the series needs, landed at the index k_
(define (cm-term! k_ u v)
  (fact 'fun-apply-type-c 'w 'NN 'RR k_)
  (inst+ cm-wpos k_)
  (cm-from-lt! 0 (list 'w k_))
  (fact 'c-metric-term-bound 's k_ u v (list 'w k_))
  (let ((t (list '* (list 'w k_) (list 'min 1 (list (list '(DISTS s) k_) u v)))))
    (dk-split! (list 'AND (list 'IN t 'RR)
                     (list 'AND (list '<= 0 t) (list '<= t (list 'w k_)))))
    t))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
   (list 'FORALL 'w (list 'IMPLIES '(SUMMABLE-WEIGHT w)
     (forall-guarded '(u_ v_) (list '(IN u_ (PTS s)) '(IN v_ (PTS s)))
       (list 'IN (cm-term-lambda 'u_ 'v_) '(FUN NN RR)))))))))
(cm-peel-to! 'IN)
(cm-setup!)
(dk-lam-t!)
(let ((k_ (cadr (cm-di-landed-1!))))
  (cm-term! k_ 'u_ 'v_)
  (ass))
(qed 'c-metric-term-seq-in-fun)
(topic! 'c-metric-term-seq-in-fun 'constructions)
(alias! 'c-metric-term-seq-in-fun
        "the term sequence of the canonical metric is a real sequence")

;;; ---- L5 ----

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
   (list 'FORALL 'w (list 'IMPLIES '(SUMMABLE-WEIGHT w)
     (forall-guarded '(u_ v_) (list '(IN u_ (PTS s)) '(IN v_ (PTS s)))
       (list 'SERIES-CONVERGES (cm-term-lambda 'u_ 'v_)))))))))
(cm-peel-to! 'SERIES-CONVERGES)
;; cited BEFORE cm-setup!, which `mac-h's away this theorem's own antecedent
(fact 'c-metric-term-seq-in-fun 's 'w 'u_ 'v_)
(cm-setup!)
(define cm-lam (cm-term-lambda 'u_ 'v_))
(define cm-termwise
  (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
    (list 'AND (list '<= 0 (list cm-lam 'k_))
               (list '<= (list cm-lam 'k_) (list 'w 'k_))))))
(have! cm-termwise
  (lambda ()
    (let ((k_ (cadr (cm-di-landed-1!))))
      (lam-b)
      (cm-term! k_ 'u_ 'v_)
      (cm-and! (lambda () (ass))))))
(cm-and2! cm-termwise '(SERIES-CONVERGES w))
(fact 'comparison-test cm-lam 'w)
(ass)
(qed 'c-metric-summable)
(topic! 'c-metric-summable 'analysis)
(alias! 'c-metric-summable
        "the series defining the canonical metric converges")

;;; =====================================================================
;;; L6.  c-metric-carrier -- the carrier slot, read off the functoid.
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL w (== (PTS (C-METRIC-W s w)) (PTS s))))))
(di)
(mac 'C-METRIC-W)
;; `slot' rewrites PTS to nth(1,.) at EVERY occurrence, the RIGHT-hand PTS(s)
;; included, so after the nth reduction the two sides are pts(s) and nth(1,s)
;; and `qrfl' refuses.  The second `slot' brings them to the same normal form --
;; the same double application `product-metric-distance' needs for DIST.
(slot 'PTS)
(nth-r)
(slot 'PTS)
(qrfl)
(qed 'c-metric-carrier)
(topic! 'c-metric-carrier 'constructions)
(alias! 'c-metric-carrier "the carrier of the canonical metric")

;;; =====================================================================
;;; L7.  c-metric-distance -- the DISTANCE FORMULA.  Same five moves as
;;; `product-metric-distance': turn SERIES-LIMIT back into its IOTA, unfold the
;;; functoid, project the DIST slot, reduce the nth, beta-reduce the TUPLED
;;; lambda (which the two carrier hypotheses pay for), and normalise.
;;; =====================================================================

(sp (make-wff (list 'FORALL 's (list 'FORALL 'w
   (forall-guarded '(u_ v_) (list '(IN u_ (PTS s)) '(IN v_ (PTS s)))
     (list '== (list '(DIST (C-METRIC-W s w)) 'u_ 'v_)
               (list 'SERIES-LIMIT (cm-term-lambda 'u_ 'v_))))))))
(cm-peel-to! '==)
(mac 'SERIES-LIMIT)
(mac 'C-METRIC-W)
(slot 'DIST)
(nth-r)
(lam-b)
(qrfl)
(qed 'c-metric-distance)
(topic! 'c-metric-distance 'constructions)
(alias! 'c-metric-distance
        "the canonical distance is the sum of the weighted truncated pseudodistances")

;;; =====================================================================
;;; L8.  c-metric-dist-converges -- the series converges TO the distance, which
;;; is the form every later convergence argument consumes.
;;; =====================================================================

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
   (list 'FORALL 'w (list 'IMPLIES '(SUMMABLE-WEIGHT w)
     (forall-guarded '(u_ v_) (list '(IN u_ (PTS s)) '(IN v_ (PTS s)))
       (list 'SERIES-CONVERGES-TO (cm-term-lambda 'u_ 'v_)
             (list '(DIST (C-METRIC-W s w)) 'u_ 'v_)))))))))
(cm-peel-to! 'SERIES-CONVERGES-TO)
(fact 'c-metric-term-seq-in-fun 's 'w 'u_ 'v_)
(fact 'c-metric-summable 's 'w 'u_ 'v_)
(fact 'series-limit-converges-to cm-lam)
(fact 'c-metric-distance 's 'w 'u_ 'v_)
(mac 'c-metric-distance)
(ass)
(qed 'c-metric-dist-converges)
(topic! 'c-metric-dist-converges 'analysis)
(alias! 'c-metric-dist-converges
        "the defining series converges to the canonical distance")

;;; =====================================================================
;;; L9.  The canonical instance: weights 2^-(k+1).  One citation of the PROVEN
;;; `product-metric-default-summable', which is SUMMABLE-WEIGHT of exactly the
;;; term C-METRIC names.
;;; =====================================================================

(define cm-dw '(VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1)))))

(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IS-C-METRIC-SPACE s)
   (forall-guarded '(u_ v_) (list '(IN u_ (PTS s)) '(IN v_ (PTS s)))
     (list 'SERIES-CONVERGES
       (cm-term-lambda-w cm-dw 'u_ 'v_)))))))
(cm-peel-to! 'SERIES-CONVERGES)
(fact 'product-metric-default-summable)
(fact 'c-metric-summable 's cm-dw 'u_ 'v_)
(ass)
(qed 'c-metric-canonical-summable)
(topic! 'c-metric-canonical-summable 'analysis)
(alias! 'c-metric-canonical-summable
        "the series defining the canonical dyadic metric converges")
