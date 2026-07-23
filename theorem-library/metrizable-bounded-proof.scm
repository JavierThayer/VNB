;;; metrizable-bounded-proof.scm -- T1: a topological space is metrizable iff it
;;; is metrizable by a BOUNDED metric.
;;;
;;;   metrizable-iff-bounded-metrizable :
;;;     IS-TOP-SPACE(s) => ( IS-METRIZABLE-TOP-SPACE(s) <=>
;;;                          exists md. IS-BOUNDED-METRIC-SPACE(md) and METRIC-TOP(md) == s )
;;;
;;; The engine is bounded-metric.scm.  (=>) metrizable-has-metric-top gives a metric
;;; md0 with METRIC-TOP(md0) == s; BDD-METRIC(md0) is bounded
;;; (bdd-metric-is-bounded-metric-space) and has the SAME topology
;;; (bdd-metric-preserves-metric-top), so it witnesses (b).  (<=) a bounded metric is
;;; a metric, and metric-top-is-metrizable-top-space makes s = METRIC-TOP(md)
;;; metrizable.  di on the IFF goal is iff-intro: it assumes BOTH antecedents and
;;; leaves the two consequents as goals (no extra di to assume them).

;; --- focus helper (mb- prefix); a miss ERRORS, never leaves focus put ---
(define (mb-goal-of l) (expression->string (wff-formula (sequent-node-assertion l))))
(define (mb-dump!)
  (display "\n;; FRONTIER:\n")
  (for-each (lambda (l) (display ";;   ") (display (mb-goal-of l)) (newline)) (proof-leaves)))
(define (mb-focus! str)
  (let ((hits (filter (lambda (l) (string-search-forward str (mb-goal-of l) 0)) (proof-leaves))))
    (cond ((null? hits) (mb-dump!) (error "mb-focus!: no leaf containing" str))
          ((pair? (cdr hits)) (mb-dump!) (error "mb-focus!: ambiguous" str))
          (else (dk-focus! (car hits))))))

;; Skolemize a FORSOME already in context; return the fresh eigenvariable, read off
;; by free-variable set-difference (obtain's core, for a forsome not landed by a lane).
(define (mb-skolemize! forsome)
  (let ((fv0 (sk--fvs (sk--ctx))))
    (ai forsome)
    (sk--split!)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (sk--fvs (sk--ctx)))))
      (and (pair? fresh) (car fresh)))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-TOP-SPACE s)
     (IFF (IS-METRIZABLE-TOP-SPACE s)
          (FORSOME md (AND (IS-BOUNDED-METRIC-SPACE md)
                           (== (METRIC-TOP md) s))))))))
(di)   ; forall s
(di)   ; assume is-top-space(s); goal IFF
(di)   ; iff-intro: assumes BOTH antecedents, leaves the two consequents as goals

;; ===== (=>) metrizable => bounded-metrizable : goal forsome(...), is-metrizable in ctx =====
(mb-focus! "forsome([md], is-bounded")
(fact 'metrizable-has-metric-top 's)     ; lands FORSOME md (is-metric-space md ^ metric-top md == s)
(define mb-md0 (mb-skolemize! '(FORSOME md (AND (IS-METRIC-SPACE md) (== (METRIC-TOP md) s)))))
(ew (list 'BDD-METRIC mb-md0))            ; the bounded witness d/(1+d)
(di)                                      ; split: bounded ; ==
(mb-focus! "is-bounded-metric-space")
(fact 'bdd-metric-is-bounded-metric-space mb-md0)
(ass)
(mb-focus! "metric-top")                  ; goal: metric-top(bdd-metric md0) == s
(fact 'bdd-metric-preserves-metric-top mb-md0)   ; == metric-top(bdd-metric md0) metric-top(md0)
(subst (list '== (list 'METRIC-TOP (list 'BDD-METRIC mb-md0)) (list 'METRIC-TOP mb-md0)))
(ass)                                     ; closes on metric-top(md0) == s

;; ===== (<=) bounded-metrizable => metrizable : goal is-metrizable(s), forsome in ctx =====
(mb-focus! "is-metrizable-top-space(s)")
(define mb-md1 (mb-skolemize! '(FORSOME md (AND (IS-BOUNDED-METRIC-SPACE md) (== (METRIC-TOP md) s)))))
(mac-h 'is-bounded-metric-space (list 'IS-BOUNDED-METRIC-SPACE mb-md1))   ; expose is-metric-space(md1)
(sk--split!)
(fact 'metric-top-is-metrizable-top-space mb-md1)   ; lands is-metrizable(metric-top md1)
(subst (list '== 's (list 'METRIC-TOP mb-md1)))      ; rewrite s -> metric-top(md1) in the goal
(ass)

(qed 'metrizable-iff-bounded-metrizable)
