;;; rr-lt-pos-inf.scm -- lemmas MOVED 2026-10-30 (wave-2 integration) out of theorem-library/lp-inequalities.scm
;;; into library analysis, for the library gate: cited by ch4a-coef (complex-analysis); an extended-real order fact.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   rr-lt-pos-inf

;;; ---- helper defines copied from lp-inequalities.scm ----
(define (lpi-check name)
  (if (not (proof-done? *ps*))
      (error "lp-inequalities: proof did not close" name
             (expression->string (dk-goal)))))
(define (lpi-keep-prop! . keepers)
  (let ((leaf (proof-state-focus *ps*)))
    (apply dk-only! keepers)
    (if (not (sequent-node-grounded? leaf)) (prop))))
(define (lpi-conj-close! . opt)
  (let ((closer (if (pair? opt) (car opt) from-context!)))
    (let walk ()
      (let ((g (dk-goal)))
        (if (and (pair? g) (eq? (car g) 'AND))
            (for-each (lambda (k)
                        (if (not (sequent-node-grounded? k))
                            (begin (dk-focus! k) (walk))))
                      (dk-opened (lambda () (di))))
            (closer))))))

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (< x POS-INF)))))
(dk-peel!)
(mac '<)
(lpi-conj-close!
  (lambda ()
    (if (dk-head-is? (dk-goal) '<=)
        (begin
          (dk-have! '(IN x RR-STAR)
            (lambda ()
              (let ((iff (dk-cite! 'rr-star-membership 'x)))
                (lpi-keep-prop! iff '(IN x RR)))))
          (fact 'pos-inf-upper-bound 'x) (ass))
        (begin
          (let ((eq (dk-landed (lambda () (di)))))
            (dk-have! '(IN POS-INF RR) (lambda () (subst (list '= 'POS-INF 'x)) (ass))))
          (fact 'pos-inf-not-in-rr)
          (lpi-keep-prop! '(IN POS-INF RR) '(NOT (IN POS-INF RR)))))))
(lpi-check 'rr-lt-pos-inf)
(qed 'rr-lt-pos-inf)

