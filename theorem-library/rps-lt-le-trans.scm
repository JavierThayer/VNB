;;; rps-lt-le-trans.scm -- lemmas MOVED 2026-10-30 (wave-2 integration) out of theorem-library/integral-convergence.scm
;;; into library analysis, for the library gate: cited by ch4a-coef (complex-analysis); an RR-POS-STAR order fact.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   rps-lt-le-trans

;;; ---- helper defines copied from integral-convergence.scm ----
(define (icv-keep-prop! . keepers)
  (let ((leaf (proof-state-focus *ps*)))
    (apply dk-only! keepers)
    (if (not (sequent-node-grounded? leaf)) (prop))))
(define (icv-conj-close! . opt)
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
(sp (make-wff '(FORALL x (IMPLIES (IN x RR-POS-STAR)
                 (FORALL y (IMPLIES (IN y RR-POS-STAR)
                   (FORALL z (IMPLIES (IN z RR-POS-STAR)
                     (IMPLIES (< x y) (IMPLIES (<= y z) (< x z)))))))))))
(dk-peel!)
(let ((iff (dk-cite! '< 'x 'y)))
  (dk-have! '(AND (<= x y) (NOT (= x y))) (lambda () (icv-keep-prop! iff '(< x y))))
  (dk-split! '(AND (<= x y) (NOT (= x y))))
  (dk-have! '(AND (IN x RR-POS-STAR) (AND (IN y RR-POS-STAR) (IN z RR-POS-STAR))))
  (dk-have! '(AND (<= x y) (<= y z)))
  (fact 'rr-pos-star-le-trans 'x 'y 'z)
  (mac '<)
  (icv-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (di)
            (dk-have! '(<= y x) (lambda () (subst '(= x z)) (ass)))
            (dk-have! '(AND (IN x RR-POS-STAR) (IN y RR-POS-STAR)))
            (dk-have! '(AND (<= x y) (<= y x)))
            (fact 'rr-pos-star-le-antisymm 'x 'y)
            (icv-keep-prop! '(= x y) '(NOT (= x y))))))))
(qed 'rps-lt-le-trans)
(topic! 'rps-lt-le-trans 'inequalities)

