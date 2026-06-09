;;; probe-314-mach.scm -- Prop 3.14 (=>) with mac-h clearing block 1.
;;; Unfold BOTH folded hypotheses, then see what residue is left.
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (goal) (expression->string (sequent-node-assertion (proof-state-focus *ps*))))
(define (asms) (map (lambda (w) (expression->string (wff-formula w)))
                    (sequent-node-assumptions (proof-state-focus *ps*))))
(define (open-goals)
  (map (lambda (g) (expression->string (sequent-node-assertion g)))
       (proof-open-goals *ps*)))
(define (split-ands!)
  (let loop ()
    (let scan ((as (sequent-node-assumptions (proof-state-focus *ps*))))
      (cond ((null? as) 'done)
            ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND)))
             (ai (wff-formula (car as))) (loop))
            (else (scan (cdr as)))))))

(--- "3.14 (=>): load and unfold both hypotheses with mac-h")
(sp (make-wff '(IMPLIES (AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a))
                        (CONVERGES-TO t (COMPOSE f g) (f a)))))
(di)
(ai '(AND (IS-CONTINUOUS-AT s t f a) (CONVERGES-TO s g a)))
(mac-h 'IS-CONTINUOUS-AT '(IS-CONTINUOUS-AT s t f a))
(mac-h 'CONVERGES-TO     '(CONVERGES-TO s g a))
(split-ands!)
(==> "assumptions now unlocked" (asms))

(--- "unfold + beta-reduce the goal; show the clean residue")
(mac 'CONVERGES-TO)
(mac 'COMPOSE) (lam-b)
(==> "residual goal" (goal))
;; The residue is a 4-conjunct AND:
;;   is-metric-space(t)         -- now an assumption (ass)
;;   (f o g) in FUN(NN, X(t))   -- bc* compose-type from the two FUN assumptions
;;   f(a) in X(t)               -- fun-apply-type from f in FUN and a in X(s)
;;   forall eps . ...           -- the genuine eps-N analysis core, now with BOTH
;;                                 payloads (continuity-delta, convergence-N) in hand
;; Block 1 is gone; what's left is ordinary forward eps-N work, not a locked door.

(==> "DONE-PROBE" 'ok)
