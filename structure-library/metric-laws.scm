;;; metric-laws.scm -- the five metric laws, PROVEN from the definition.
;;;
;;; metric-pos / metric-self-zero / metric-zero-eq / metric-sym /
;;; metric-triangle were long ASSERTED as standalone axioms.  But symmetry --
;;; and all four siblings -- are constitutive of the definition of a metric:
;;; IS-METRIC-SPACE(s) folds in the property `is-metric(D(s),X(s))', and
;;; `is-metric' (operation-properties.scm) is an IFF whose body already states
;;; non-negativity, the two identity-of-indiscernibles halves, SYMMETRY, and
;;; the triangle inequality.  So the five axioms were redundant -- a
;;; registration oversight.  This file retires them: each is now PROVEN modulo
;;; 0 by unfolding IS-METRIC-SPACE then is-metric and projecting the conjunct.
;;;
;;; Loaded after interactive + proof-debt (needs sp/di/mac-h/qed).  See
;;; project_metric_laws_proven.

;;; --- local helpers (ml-- prefix) ---------------------------------------
(define (ml--leaves)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (ml--any p l) (let loop ((l l)) (cond ((null? l) #f) ((p (car l)) (car l)) (else (loop (cdr l))))))
(define (ml--cur) (proof-state-focus *ps*))
(define (ml--goal) (wff-formula (sequent-node-assertion (ml--cur))))
(define (ml--hyp-sub s) (let ((w (ml--any (lambda (w) (string-search-forward s (expression->string (wff-formula w)) 0)) (sequent-node-assumptions (ml--cur))))) (and w (wff-formula w))))
(define (ml--hyp-pred p) (let ((w (ml--any (lambda (w) (p (wff-formula w))) (sequent-node-assumptions (ml--cur))))) (and w (wff-formula w))))
(define (ml--split!) (let loop () (let scan ((as (sequent-node-assumptions (ml--cur)))) (cond ((null? as) 'done) ((let ((f (wff-formula (car as)))) (and (pair? f) (eq? (car f) 'AND))) (ai (wff-formula (car as))) (loop)) (else (scan (cdr as)))))))
(define (ml--fl-goal! raw) (let ((s (ml--any (lambda (s) (equal? (wff-formula (sequent-node-assertion s)) raw)) (ml--leaves)))) (and s (set-proof-state-focus! *ps* s))))
(define (ml--fl-asm! sub) (let ((s (ml--any (lambda (s) (ml--any (lambda (w) (string-search-forward sub (expression->string (wff-formula w)) 0)) (sequent-node-assumptions s))) (ml--leaves)))) (and s (set-proof-state-focus! *ps* s))))
;; forward MP on a local (IMPLIES A B) with A in ctx; leaves B in ctx.
(define (ml--detach! impl) (let ((B (caddr impl))) (cut B) (ml--fl-goal! B) (bc impl) (ass) (ml--fl-asm! (expression->string B))))
;; the un-instantiated (FORALL v (IMPLIES (IN v X) ..)) at the current nest level
(define (ml--forall-over PTS) (ml--hyp-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (let ((b (caddr f))) (and (pair? b) (eq? (car b) 'IMPLIES) (equal? (cadr b) (list 'IN (cadr f) PTS))))))))
;; di through the goal's bounded universals (and any law-internal implies),
;; then read the introduced point-eigenvars off the (IN e X) membership hyps.
;; Reading from the goal is fragile (di on a bounded forall with an atomic
;; body lands directly on the body, so (cadr (cadr goal)) can hit a literal);
;; the memberships are unambiguous.  Context is newest-first, so reverse to
;; recover quantifier (outer-first) order -- which the nest must be
;; instantiated in (u before v before w).
(define (ml--di-collect! Xse)
  (let loop () (let ((g (ml--goal)))
    (when (and (pair? g) (memq (car g) '(FORALL IMPLIES))) (di) (loop))))
  (let ((es '()))
    (for-each (lambda (w)
                (let ((f (wff-formula w)))
                  (when (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) Xse))
                    (set! es (cons (cadr f) es)))))
              (sequent-node-assumptions (ml--cur)))
    (reverse es)))                        ; -> outer-first (u before v before w)
;; close: goal is an assumption, or follows by one backchain (zero-eq's MP).
(define (ml--close!)
  (let ((g (ml--goal)))
    (cond ((ml--hyp-pred (lambda (f) (alpha-equiv? f g))) (ass))
          (else (let ((imp (ml--hyp-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES) (alpha-equiv? (caddr f) g))))))
                  (when imp (bc imp) (ass)))))))

(define (prove-metric-law! name goal-sexpr)
  (sp (make-wff goal-sexpr))
  (di) (di)                                  ; intro s; move IS-METRIC-SPACE(s) to ctx
  (mac-h 'IS-METRIC-SPACE (ml--hyp-sub "is-metric-space"))
  (ml--split!)
  (let* ((imv (ml--hyp-pred (lambda (f) (and (pair? f) (eq? (car f) 'is-metric)))))
         (Se  (cadr (cadr imv)))
         (Xse (list 'PTS Se)))
    (mac-h 'is-metric imv)
    (for-each (lambda (e)
                (inst (ml--forall-over Xse) e)
                ;; Peel the nest: detach + split a level whose consequent is a
                ;; conjunction / further quantifier.  A level with an ATOMIC
                ;; consequent (the deepest one -- e.g. triangle's bare <=) is
                ;; the goal itself; leave its (IMPLIES (IN e X) goal) in context
                ;; for ml--close! to backchain, else detach's cut collides with
                ;; the main goal.
                (let ((imp (ml--hyp-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES) (equal? (cadr f) (list 'IN e Xse)))))))
                  (when (and imp (pair? (caddr imp)) (memq (car (caddr imp)) '(AND FORALL)))
                    (ml--detach! imp) (ml--split!))))
              (ml--di-collect! Xse))
    (ml--close!))
  (if (proof-done? *ps*) (qed name)
      (error "metric-laws: failed to prove" name)))

;;; --- the five laws (same statements that were asserted) -----------------
(prove-metric-law! 'metric-pos
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (<= 0 ((DIST s) x y)))))))))
(prove-metric-law! 'metric-self-zero
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (= ((DIST s) x x) 0))))))
(prove-metric-law! 'metric-zero-eq
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (IMPLIES (= ((DIST s) x y) 0) (= x y)))))))))
(prove-metric-law! 'metric-sym
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (= ((DIST s) x y) ((DIST s) y x)))))))))
(prove-metric-law! 'metric-triangle
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL x (IMPLIES (IN x (PTS s))
       (FORALL y (IMPLIES (IN y (PTS s))
         (FORALL z (IMPLIES (IN z (PTS s))
           (<= ((DIST s) x z) (+ ((DIST s) x y) ((DIST s) y z))))))))))))
