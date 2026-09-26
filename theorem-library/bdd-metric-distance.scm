;;; bdd-metric-distance.scm -- the BDD-METRIC distance formula, proven.
;;;
;;;     forall s.  IS-METRIC-SPACE(s)  =>  forall x, y in PTS(s).
;;;         (DIST (BDD-METRIC s))(x, y)  =  d(x,y) / (1 + d(x,y)),   d = DIST(s)
;;;
;;; BDD-METRIC(s) is the def-functoid (structure-library/bounded-metric.scm:33)
;;;     (LIST (PTS s) (VNB-LAMBDA (LIST u v) (CARTESIAN (PTS s) (PTS s))
;;;                     (/ ((DIST s) u v) (+ 1 ((DIST s) u v)))))
;;; so the statement is one tupled-binder beta, exactly as product-metric-
;;; distance (theorem-library/product-summable.scm) and rr-ms-dist do it.  The
;;; support of the same name (bounded-metric.scm:45) is `well-known'.
;;;
;;; THE ONE REAL STEP.  The leaf is stated with `=', which is strict, so `rfl'
;;; on  q = q  needs q DEFINED -- a context fact (IN q RR).  With d = d(x,y):
;;;     metric-dist-real  (op-typing)          d in RR
;;;     metric-pos        (metric-laws)        0 <= d
;;;     rr-one-in, rr-add-closed               1 + d in RR
;;;     ineq                                   0 < 1 + d
;;;     rr-pos-ne-zero    (rr-order-basics)    1 + d /= 0
;;;     rr-recip-closed, rr-mul-closed         d * recip(1 + d) in RR
;;;     binary-divide-def (named-only, by name) d / (1 + d) in RR
;;; then (mac 'BDD-METRIC) (slot 'DIST) (nth-r) (lam-b), one `subst' to put the
;;; right side back into DIST form, and (rfl).  `lam-b' owes nothing extra: x
;;; and y are typed in PTS(s) above it.
;;;
;;; WINDOW.  lo is forced by metric-dist-real (theorem-library/op-typing) and
;;; metric-pos (structure-library/metric-laws), whichever loads later;
;;; rr-pos-ne-zero (theorem-library/rr-order-basics) loads before both.
;;; hi = theorem-library/bdd-metric-convergence, the earliest citer.
;;;
;;; Helper prefix: bmd-.

(define bmd-d '((DIST s) x y))
(define bmd-den (list '+ 1 bmd-d))

;; 1-based index of FORM in the focus context, for `ineq'.
(define (bmd-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "bmd-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (= ((DIST (BDD-METRIC s)) x y)
            (/ ((DIST s) x y) (+ 1 ((DIST s) x y))))))))))))
(dk-peel-to! '=)                              ; IS-METRIC-SPACE s, x, y in PTS(s)

;; d / (1 + d) in RR
(fact 'metric-dist-real 's 'x 'y)             ; (IN d RR)
(fact 'metric-pos 's 'x 'y)                   ; (<= 0 d)
(fact 'rr-one-in)
(have! (list 'AND '(IN 1 RR) (list 'IN bmd-d 'RR)))
(fact 'rr-add-closed 1 bmd-d)                 ; (IN (+ 1 d) RR)
(have! (list '< 0 bmd-den)
  (lambda () (ineq (bmd-idx (list '<= 0 bmd-d)) (bmd-idx (list 'IN bmd-d 'RR)))))
(fact 'rr-pos-ne-zero bmd-den)                ; (NOT (= (+ 1 d) 0))
(have! (list 'AND (list 'IN bmd-den 'RR) (list 'NOT (list '= bmd-den 0))))
(fact 'rr-recip-closed bmd-den)               ; (IN (recip (+ 1 d)) RR)
(have! (list 'AND (list 'IN bmd-d 'RR) (list 'IN (list 'recip bmd-den) 'RR)))
(fact 'rr-mul-closed bmd-d (list 'recip bmd-den))   ; (IN (* d (recip (+ 1 d))) RR)
(have! (list 'IN (list '/ bmd-d bmd-den) 'RR)
  (lambda () (mac 'binary-divide-def) (ass)))

;; the beta.  `slot' on the LIST literal falls back to the accessor macete,
;; which rewrites the RIGHT side's (DIST s) to nth(2, s) as well -- but NOT the
;; (DIST s) inside the lambda body (measured: after `lam-b' the goal reads
;;     d(x,y)/(1+d(x,y)) = nth(2,s)(x,y)/(1+nth(2,s)(x,y))
;; with d = DIST s).  `slot-h' cannot bring the definedness fact across
;; (`mac-h: unknown theorem/macete: dist' -- the accessor fallback exists only
;; goal-side), so the right side is brought BACK instead: the bridge
;; nth(2,s)(x,y) == d(x,y) is one `slot' + `qrfl', and `subst' takes a `=='.
;; Then both sides are the term the context types, and `rfl' closes.
(mac 'BDD-METRIC)
(slot 'DIST)
(nth-r)
(lam-b)
(have! (list '== (list '(nth 2 s) 'x 'y) bmd-d)
  (lambda () (slot 'DIST) (qrfl)))
(subst (list '== (list '(nth 2 s) 'x 'y) bmd-d))
(rfl)
(qed 'bdd-metric-distance)
(topic! 'bdd-metric-distance 'constructions)
