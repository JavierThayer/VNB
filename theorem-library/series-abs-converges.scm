;;; series-abs-converges.scm -- ABSOLUTE CONVERGENCE IMPLIES CONVERGENCE, for
;;; real series.
;;;
;;;   series-abs-converges:
;;;     g agrees pointwise with |f|,  SERIES-CONVERGES(g)  =>  SERIES-CONVERGES(f)
;;;
;;; The classical argument, and every piece of it was already in the tree except
;;; the block estimate proved two files up:
;;;
;;;   |S(f,n) - S(f,m)|  <=  S(g,n) - S(g,m)          series-abs-triangle-le
;;;                       =  (S(g,n) - S(g,N)) - (S(g,m) - S(g,N))
;;;                      <=  eps                       series-tail-small
;;;
;;; so the partial sums of f are CAUCHY, and RR is complete.  `rr-complete' and
;;; `complete-cauchy-converges' do the rest.
;;;
;;; TRANSFER FORM, as everywhere in this arc: `g' is any sequence agreeing
;;; pointwise with the absolute values, not the literal lambda.
;;;
;;; THE TWO ORIENTATIONS.  IS-CAUCHY-SEQ quantifies m and n_ independently above
;;; the threshold, while the block estimate needs to know which is the lower
;;; index.  `rr-leq-total' splits, and the two branches differ by ONE citation:
;;; `rr-abs-sub-sym' in the m <= n_ branch, where the block runs the other way
;;; round from the goal.  The estimate itself is written once, as `ac-block!'.
;;;
;;; WHAT IT COSTS: `modulo {nn-not-le-zero-pos}', inherited through
;;; `series-abs-triangle-le' -> `nn-le-gap', and that leaf is the only one.
;;;
;;; NOT THE SAME THEOREM AS `ps-absolute-implies-convergent', which is still an
;;; asserted support: that one is the POWER-SERIES specialisation, stated over
;;; PS-PARTIAL-SUM rather than SERIES-PARTIAL-SUM.  Deriving it from this needs
;;; the PS/series bridges -- `ps-partial-sum-as-series', `ps-converges-as-series'
;;; and `ps-abs-term' -- all THREE of which are themselves asserted supports in
;;; power-series.scm.  They are definitional unfoldings (both sides reduce to the
;;; same SUM-AG), so they are the same one-line species as
;;; `cc-series-partial-sum-unfold'; until they are proven, deriving the
;;; specialisation would trade one assertion for three.
;;;
;;; Loads after series-block-abs (series-abs-triangle-le), dominated-convergence
;;; (series-tail-small), rr-complete-proof (rr-complete), metric-completeness
;;; (IS-CAUCHY-SEQ, complete-cauchy-converges) and rr-abs-basics (rr-abs-sub-sym,
;;; rr-abs-nonneg).

;;; absolute convergence implies convergence, for real series.
(define (ac-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "ac-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (ac-ineq . fs) (apply ineq (map ac-idx fs)))
(define (ac-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "ac-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))
(define (ac-skolem! ex)
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (x) (if (and (pair? x) (eq? (car x) 'AND)) (dk-split! x))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "ac-skolem!: nothing fresh" ex) (car fresh)))))
(define (ac-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

(define (dk-flatten-ands ls)
  ;; `di' on a right-nested AND leaves an AND standing; split to leaves.
  (apply append
    (map (lambda (l)
           (dk-focus! l)
           (if (and (pair? (dk-goal)) (eq? (car (dk-goal)) 'AND))
               (dk-flatten-ands (dk-opened (lambda () (di))))
               (list l)))
         ls)))

;; Given lo <= hi (naturals, both at or above the tail threshold), land
;; |S(f,hi) - S(f,lo)| <= eps.
(define (ac-block! bnd tail lo hi)
  (fact 'series-abs-triangle-le hi lo 'f 'g)
  (inst+ tail hi)
  (fact 'series-partial-sum-mono lo bnd 'g)
  (fact 'series-partial-sum-in-rr hi 'f)
  (fact 'series-partial-sum-in-rr lo 'f)
  (fact 'series-partial-sum-in-rr hi 'g)
  (fact 'series-partial-sum-in-rr lo 'g)
  (fact 'series-partial-sum-in-rr bnd 'g)
  (fact 'rr-sub-in-rr (list 'SERIES-PARTIAL-SUM 'f hi) (list 'SERIES-PARTIAL-SUM 'f lo))
  (fact 'rr-abs-closed (list '- (list 'SERIES-PARTIAL-SUM 'f hi)
                                (list 'SERIES-PARTIAL-SUM 'f lo))))

(define (ac-close-cauchy! bnd tail)
  (fact 'nn-in-rr 'm) (fact 'nn-in-rr 'n_)
  (have! '(AND (IN m RR) (IN n_ RR)))
  (fact 'rr-leq-total 'm 'n_)
  (use-cases
   (list '(<= m n_) '(<= n_ m))
   (lambda ()                                   ; m <= n_ : the block runs m -> n_
     (ac-block! bnd tail 'm 'n_)
     (fact 'rr-abs-sub-sym '(SERIES-PARTIAL-SUM f m) '(SERIES-PARTIAL-SUM f n_))
     (ac-ineq (list '<= (list 'abs (list '- '(SERIES-PARTIAL-SUM f n_)
                                            '(SERIES-PARTIAL-SUM f m)))
                    (list '- '(SERIES-PARTIAL-SUM g n_) '(SERIES-PARTIAL-SUM g m)))
              (list '<= (list '- '(SERIES-PARTIAL-SUM g n_)
                                 (list 'SERIES-PARTIAL-SUM 'g bnd)) 'eps)
              (list '<= (list 'SERIES-PARTIAL-SUM 'g bnd) '(SERIES-PARTIAL-SUM g m))
              '(= (abs (- (SERIES-PARTIAL-SUM f m) (SERIES-PARTIAL-SUM f n_)))
                  (abs (- (SERIES-PARTIAL-SUM f n_) (SERIES-PARTIAL-SUM f m))))))
   (lambda ()                                   ; n_ <= m : the block runs n_ -> m
     (ac-block! bnd tail 'n_ 'm)
     (ac-ineq (list '<= (list 'abs (list '- '(SERIES-PARTIAL-SUM f m)
                                            '(SERIES-PARTIAL-SUM f n_)))
                    (list '- '(SERIES-PARTIAL-SUM g m) '(SERIES-PARTIAL-SUM g n_)))
              (list '<= (list '- '(SERIES-PARTIAL-SUM g m)
                                 (list 'SERIES-PARTIAL-SUM 'g bnd)) 'eps)
              (list '<= (list 'SERIES-PARTIAL-SUM 'g bnd) '(SERIES-PARTIAL-SUM g n_))))))

(define ac-Sf '(VNB-LAMBDA k NN (SERIES-PARTIAL-SUM f k)))

(sp (make-wff
     '(FORALL f (IMPLIES (IN f (FUN NN RR))
        (FORALL g (IMPLIES (IN g (FUN NN RR))
          (IMPLIES (FORALL j (IMPLIES (IN j NN) (= (g j) (abs (f j)))))
            (IMPLIES (SERIES-CONVERGES g) (SERIES-CONVERGES f)))))))))
(ac-peel-to! 'SERIES-CONVERGES)
(define ac-ag
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "no agreement"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL) (dk-contains? (car l) 'abs)) (car l))
          (else (loop (cdr l))))))

;;; the terms of g are nonnegative -- needed by tail-small and by monotonicity
(define ac-gnn '(FORALL i_ (IMPLIES (IN i_ NN) (<= 0 (g i_)))))
(have! ac-gnn
  (lambda ()
    (di)
    (inst+ ac-ag 'i_)
    (fact 'fun-apply-type-c 'f 'NN 'RR 'i_)
    (fact 'rr-abs-nonneg '(f i_))
    (fact 'fun-apply-type-c 'g 'NN 'RR 'i_)
    (fact 'rr-abs-closed '(f i_))
    (ac-ineq '(= (g i_) (abs (f i_))) '(<= 0 (abs (f i_))))))
;;; the partial-sum sequence of f, as a member of FUN(NN,RR)
(have! (list 'IN ac-Sf '(FUN NN RR))
  (lambda () (dk-lam-t!) (di)
             (fact 'series-partial-sum-in-rr (caddr (cadr (dk-goal))) 'f) (ass)))

;;; ... and it is CAUCHY.
(define ac-cauchy (list 'IS-CAUCHY-SEQ 'RR-MS ac-Sf))
(have! ac-cauchy
  (lambda ()
    (mac 'is-cauchy-seq)
    (slot 'PTS)
    (let ((parts (dk-opened (lambda () (di)))))
      ;; three obligations: metric space, the FUN typing, the eps clause
      (for-each
       (lambda (l)
         (dk-focus! l)
         (let ((gl (dk-goal)))
           (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
                 ((eq? (car gl) 'IN) (ass))
                 (else
                  (di) (di)                       ; forall eps, then POS-RR eps
                  (ac-pos-in-rr! 'eps)
                  ;; the absolute series' tail is small; take its threshold as N
                  (let* ((tl (dk-deepest (lambda () (fact 'series-tail-small 'g 'eps))))
                         (bnd (ac-skolem! tl))
                         (tail (let loop ((l (dk-asms)))
                                 (cond ((null? l) (error "no tail statement"))
                                       ((and (pair? (car l)) (eq? (caar l) 'FORALL)
                                             (dk-contains? (car l) bnd)
                                             (dk-contains? (car l) 'SERIES-PARTIAL-SUM)) (car l))
                                       (else (loop (cdr l)))))))
                    (ew bnd)
                    (for-each
                     (lambda (l2)
                       (dk-focus! l2)
                       (if (eq? (car (dk-goal)) 'IN)
                           (ass)
                           (begin
                             (di)                       ; the two index typings
                             (di)                       ; ... then the AND of thresholds
                             (dk-split! (list 'AND (list '<= bnd 'm) (list '<= bnd 'n_)))
                             (lam-b)                    ; one call does both applications
                             (fact 'series-partial-sum-in-rr 'm 'f)
                             (fact 'series-partial-sum-in-rr 'n_ 'f)
                             (mac 'rr-ms-dist)
                             (ac-close-cauchy! bnd tail))))
                     (dk-opened (lambda () (di)))))))))
       (dk-flatten-ands parts)))))

;;; completeness turns Cauchy into convergent, and that IS series-converges(f).
(fact 'rr-complete)
(fact 'complete-cauchy-converges 'RR-MS ac-Sf)
(mac 'series-converges)
(ass)
(qed 'series-abs-converges)

(topic! 'series-abs-converges 'analysis)
(alias! 'series-abs-converges
        "an absolutely convergent real series converges")
