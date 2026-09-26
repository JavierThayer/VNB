;;; continuous-one-sided-sign.scm -- sign preservation under continuity, from
;;; ONE side, PROVEN.  Two theorems, one driver parameterised by the side:
;;;
;;;   continuous-nonneg-left    g in FUN(RR,RR), aa < th, g continuous at th,
;;;                             0 <= g(x) on (aa, th)          =>  0 <= g(th)
;;;   continuous-nonpos-right   g in FUN(RR,RR), th < bb, g continuous at th,
;;;                             g(x) <= 0 on (th, bb)          =>  g(th) <= 0
;;;
;;; Both were `well-known' supports in theorem-library/mean-value.scm, and
;;; between them they sat in 88 bills: the interior-extremum lemma cites both,
;;; and through it Rolle, the MVT, the Taylor arc and everything downstream.
;;; The statements are reproduced VERBATIM below (`cos-statement'), copied from
;;; the retired supports, so that interior-extremum-proof.scm's `fact' citations
;;; read exactly as before.  (A first version read them off the theorem table
;;; with `lookup-theorem', which works on the band -- where the support is still
;;; installed -- and dies on a cold load, where it has been retired.)
;;;
;;; THE ARGUMENT (left side; the right is the mirror).  It is enough, by
;;; `rr-le-all-pos-nonpos', to show  -g(th) <= eps  for every eps > 0.  Fix
;;; eps.  Continuity at th gives delta > 0.  Halve the width th - aa
;;; (`rr-pos-halvable': hh > 0 with hh + hh = th - aa) and take w > 0 below
;;; both delta and hh (`rr-min-pos').  Sample at x = th - w: then
;;; aa < x < th, so 0 <= g(x) by hypothesis, and |th - x| = w <= delta, so
;;; |g(th) - g(x)| <= eps.  Hence  g(th) >= g(x) - eps >= -eps,  i.e.
;;; -g(th) <= eps.  No eps/2 split is needed: the estimate is used once.
;;; The halving is of the INTERVAL, not of eps -- w <= th - aa alone would
;;; put x at aa, and the hypothesis is open at aa.
;;;
;;; MECHANICS, all inherited from cont-agree-off-pt.scm and reused verbatim:
;;;  * `mac-h' is destructive, so POS-RR(t) is opened at its point of use
;;;    (`cos-open-pos!'): delta AFTER the eps-universal has been detached
;;;    against it, eps at the very end, after the inner universal is
;;;    instantiated.
;;;  * `rr-min-pos' and `rr-le-ne-lt' want their antecedents in context in the
;;;    right spelling; `rr-pos-halvable' wants POS-RR of the width, which is
;;;    built from `rr-lt-diff-pos' + `rr-pos-ne-zero' + `neq-sym' and one
;;;    `(mac 'pos-rr)' on the side goal.
;;;  * The inner universal is guarded on `x in PTS(RR-MS)', so the PTS form of
;;;    the sample point's typing is PUT BACK with `slot' on a side goal.
;;;  * |th - x| = w is REWRITING under `abs', invisible to `ineq': the
;;;    difference is rewritten to w by `crs', then |w| = w by
;;;    `rr-abs-of-nonneg'.  On the right side th - x = -w, so `rr-abs-sub-sym'
;;;    flips the difference first.
;;;  * Every eigenvariable (eps, delta, hh, w) is read off the LANDING by
;;;    free-variable difference (`cos-skolem!'), never guessed.
;;;
;;; LOAD WINDOW [222, 358): after theorem-library/rr-ms-dist (pos 221, the
;;; latest citation -- the others are equality-basics 153, binary-minus-laws
;;; 158, fun-apply-type-proof 159, rr-order-basics 164, rr-abs-basics 165,
;;; rr-halving 171, rr-le-all-pos 172, and the definitions in order-predicates
;;; 39 / metric-continuity 45) and before theorem-library/mean-value (pos 358),
;;; whose two supports this file retires; the earliest citer is
;;; interior-extremum-proof (359).  Cites no asserted fact: `modulo 0'.

;;; ---- file-local helpers (the `cos-' prefix) ---------------------------

(define (cos-idx form)                  ; 1-based, as `ineq' counts
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "cos-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (cos-ineq . fs) (apply ineq (map cos-idx fs)))

(define (cos-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 9) (error "cos-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(define (cos-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "cos-find: none" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ai' an existential already in context and return its eigenvariable, read
;;; off by free-variable difference.  (`obtain' cannot see an existential the
;;; context already holds -- CLAUDE.md.)
(define (cos-skolem! ex)
  (let* ((fv0 (apply append (map free-vars (dk-asms))))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (null? fresh) (error "cos-skolem!: nothing fresh" ex) (car fresh)))))

;;; POS-RR t  ->  t in RR, 0 <= t, not(0 = t), and the STRICT 0 < t that
;;; rr-min-pos wants.  DESTRUCTIVE (mac-h): call it after every detachment
;;; against POS-RR(t) has been made.
(define (cos-open-pos! t)
  (mac-h 'pos-rr (list 'POS-RR t))
  (dk-split! (list 'AND (list 'IN t 'RR)
                   (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t)))))
  (fact 'rr-zero-in)
  (have! (list 'AND (list '<= 0 t) (list 'NOT (list '= 0 t))))
  (fact 'rr-le-ne-lt 0 t))

;;; ---- the driver, parameterised by the side ----------------------------

(define (cos-statement name)
  (cond ((eq? name 'continuous-nonneg-left)
         '(FORALL g (FORALL aa (FORALL th
         (IMPLIES (IN g (FUN RR RR)) (IMPLIES (IN aa RR) (IMPLIES (IN th RR) (IMPLIES (< aa th)
         (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
         (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< aa x) (< x th))) (<= 0 (g x))))
           (<= 0 (g th))))))))))))
        ((eq? name 'continuous-nonpos-right)
         '(FORALL g (FORALL th (FORALL bb
         (IMPLIES (IN g (FUN RR RR)) (IMPLIES (IN th RR) (IMPLIES (IN bb RR) (IMPLIES (< th bb)
         (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g th)
         (IMPLIES (FORALL x (IMPLIES (AND (IN x RR) (AND (< th x) (< x bb))) (<= (g x) 0)))
           (<= (g th) 0)))))))))))
        (#t (error "cos-statement: unknown leaf" name))))

(define (cos-prove! side)
  (let* ((left? (eq? side 'left))
         (name  (if left? 'continuous-nonneg-left 'continuous-nonpos-right))
         (lo    (if left? 'aa 'th))          ; the interval is (lo, hi)
         (hi    (if left? 'th 'bb))
         (gap   (list '- hi lo))             ; its width, positive
         (tgt   (if left? '(- (g th)) '(g th))))   ; shown <= every eps
    (sp (make-wff (cos-statement name)))
    (cos-peel-to! '<=)
    (if (not (equal? (dk-goal) (if left? '(<= 0 (g th)) '(<= (g th) 0))))
        (error "cos-prove!: unexpected goal after peel" (dk-goal)))
    ;; the sign hypothesis: the ONE universal whose body's consequent is a `<='
    ;; (the eps-universal's is a FORSOME, the delta-universal's an IMPLIES).
    (let ((sign-hyp
           (cos-find 'sign-hyp
             (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                              (pair? (caddr a)) (eq? (car (caddr a)) 'IMPLIES)
                              (pair? (caddr (caddr a)))
                              (eq? (car (caddr (caddr a))) '<=))))))
      ;; unfold continuity; it is used once, so the destructive mac-h is free.
      (dk-split! (dk-landed-find
                  (lambda () (mac-h 'is-continuous-at '(IS-CONTINUOUS-AT RR-MS RR-MS g th)))
                  (dk-head? 'AND)))
      (let ((eps-univ
             (cos-find 'eps-univ
               (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (dk-contains? a 'POS-RR) (dk-contains? a 'DIST))))))
        (fact 'fun-apply-type-c 'g 'RR 'RR 'th)
        (fact 'rr-zero-in)
        (if left? (fact 'rr-neg-closed '(g th)))

        (have! (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list '<= tgt 'eps)))
          (lambda ()
            (cos-peel-to! '<=)
            (let* ((e1    (dk-deepest (lambda () (inst+ eps-univ 'eps))))
                   (delta (cos-skolem! e1)))
              ;; delta is opened only NOW: the eps-universal was detached
              ;; against POS-RR delta's sibling POS-RR eps, and mac-h replaces.
              (cos-open-pos! delta)
              ;; the width of the interval, as a POS-RR for the halving
              (fact 'rr-lt-diff-pos lo hi)          ; 0 < hi - lo
              (fact 'rr-sub-in-rr hi lo)            ; hi - lo in RR
              (fact 'rr-lt-implies-le 0 gap)
              (fact 'rr-pos-ne-zero gap)
              (fact 'neq-sym gap 0)                 ; POS-RR wants not(0 = gap)
              (have! (list 'POS-RR gap) (lambda () (mac 'pos-rr) (from-context!)))
              (let* ((hex (dk-fact! 'rr-pos-halvable gap))
                     (hh  (cos-skolem! hex)))       ; hh + hh = gap
                (cos-open-pos! hh)
                (let* ((mex (dk-fact! 'rr-min-pos delta hh))
                       (w   (cos-skolem! mex))       ; 0 < w <= delta, w <= hh
                       (x   (if left? (list '- 'th w) (list '+ 'th w)))
                       (gx  (list 'g x))
                       (dd  (list '- '(g th) gx))
                       (inner
                        (cos-find 'delta-univ
                          (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                           (dk-contains? a 'DIST) (dk-contains? a delta)
                                           (not (dk-contains? a 'POS-RR)))))))
                  ;; x in RR
                  (if left?
                      (fact 'rr-sub-in-rr 'th w)
                      (begin (have! (list 'AND '(IN th RR) (list 'IN w 'RR)))
                             (fact 'rr-add-closed 'th w)))
                  ;; dist(th, x) <= delta:  |th - x| = |w| = w <= delta.  REWRITES
                  ;; under abs, not ineq.
                  (fact 'rr-lt-implies-le 0 w)
                  (fact 'rr-abs-of-nonneg w)
                  (fact 'rr-sub-in-rr 'th x)
                  (if left?
                      (have! (list '= (list '- 'th x) w) (lambda () (crs)))
                      (begin (have! (list '= (list '- x 'th) w) (lambda () (crs)))
                             (fact 'rr-abs-sub-sym 'th x)))
                  (have! (list '<= (list '(DIST RR-MS) 'th x) delta)
                    (lambda ()
                      (mac 'rr-ms-dist)
                      (if left?
                          (subst (list '= (list '- 'th x) w))
                          (begin
                            (subst (list '= (list 'abs (list '- 'th x))
                                         (list 'abs (list '- x 'th))))
                            (subst (list '= (list '- x 'th) w))))
                      (subst (list '= (list 'abs w) w))
                      (ass)))
                  ;; the inner universal is guarded on x in PTS(RR-MS): put that
                  ;; form back rather than slot the hypothesis away.
                  (have! (list 'IN x '(PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
                  (inst+ inner x)                   ; dist(g th, g x) <= eps
                  (fact 'fun-apply-type-c 'g 'RR 'RR x)
                  (fact 'rr-sub-in-rr '(g th) gx)
                  (fact 'rr-abs-closed dd)
                  (have! (list '<= (list 'abs dd) 'eps)
                    (lambda () (mac 'rr-ms-dist-rev) (ass)))
                  (fact 'rr-le-abs dd)              ;  dd <= |dd|
                  (fact 'rr-neg-abs-le dd)          ; -|dd| <= dd
                  ;; x lies strictly inside (lo, hi): the near end by 0 < w, the
                  ;; far end by w <= hh and hh + hh = hi - lo.
                  (have! (list '< lo x)
                    (lambda ()
                      (if left?
                          (cos-ineq (list '<= w hh) (list '= (list '+ hh hh) gap) (list '< 0 hh))
                          (cos-ineq (list '< 0 w)))))
                  (have! (list '< x hi)
                    (lambda ()
                      (if left?
                          (cos-ineq (list '< 0 w))
                          (cos-ineq (list '<= w hh) (list '= (list '+ hh hh) gap) (list '< 0 hh)))))
                  (have! (list 'AND (list 'IN x 'RR) (list 'AND (list '< lo x) (list '< x hi))))
                  (inst+ sign-hyp x)                ; 0 <= g(x)  /  g(x) <= 0
                  ;; eps is opened LAST: the eps-universal above needed POS-RR eps.
                  (cos-open-pos! 'eps)
                  (if left?
                      (cos-ineq (list '<= (list '- (list 'abs dd)) dd)
                                (list '<= (list 'abs dd) 'eps)
                                (list '<= 0 gx))
                      (cos-ineq (list '<= dd (list 'abs dd))
                                (list '<= (list 'abs dd) 'eps)
                                (list '<= gx 0))))))))
        ;; a real below every positive is <= 0
        (fact 'rr-le-all-pos-nonpos tgt)
        (if left?
            (cos-ineq (list '<= tgt 0))
            (ass))
        (qed name)
        (topic! name 'analysis)))))

(cos-prove! 'left)
(alias! 'continuous-nonneg-left
        "a function continuous at th and nonnegative on a left neighbourhood is nonnegative at th")
(cos-prove! 'right)
(alias! 'continuous-nonpos-right
        "a function continuous at th and nonpositive on a right neighbourhood is nonpositive at th")
