;;; probe-mach-smoke.scm -- does mac-h crack a folded hypothesis open?
;;; The exact goal [4]: is-metric-space(t) from a folded is-continuous-at hyp.
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (asms) (map (lambda (w) (expression->string (wff-formula w)))
                    (sequent-node-assumptions (proof-state-focus *ps*))))
;; repeatedly split any top-level AND assumption into its conjuncts
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (proof-state-focus *ps*))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))

(--- "is-metric-space(t) from a folded is-continuous-at hypothesis, via mac-h")
(sp (make-wff '(IMPLIES (IS-CONTINUOUS-AT s t f a) (IS-METRIC-SPACE t))))
(di)
(==> "asms after di (folded)" (asms))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT s t f a))
(==> "asms after mac-h (unfolded in place)" (asms))
(split-ands!)
(==> "asms after split-ands!" (asms))
(ass)
(==> "is-metric-space(t) closes?" (proof-done? *ps*))

(==> "DONE-PROBE" 'ok)
