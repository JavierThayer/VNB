;;; esup-lt-witness.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/integral-convergence.scm
;;; into library analysis, for the library gate: cited by haar-fixed-point; ESUP.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   esup-lt-witness

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
(sp (make-wff '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
                 (FORALL a (IMPLIES (IN a RR-POS-STAR)
                   (IMPLIES (< a (ESUP S)) (FORSOME y (AND (IN y S) (< a y))))))))))
(dk-peel!)
(fact 'esup-in 's)
(let ((p '(FORSOME y (AND (IN y s) (< a y))))
      (e '(ESUP s))
      (ub '(FORALL x (IMPLIES (IN x s) (<= x a)))))
  (use-em p
    (lambda () (ass))
    (lambda ()
      (dk-have! ub
        (lambda ()
          (let ((yv (dk-di-var!)))
            (fact 'subset-mem-fwd 's 'RR-POS-STAR yv)
            (use-em (list '< 'a yv)
              (lambda ()
                (dk-have! p (lambda () (ew yv) (icv-conj-close! (lambda () (ass)))))
                (icv-keep-prop! p (list 'NOT p)))
              (lambda () (fact 'rps-not-lt-le 'a yv) (ass))))))
      (dk-have! (list 'AND '(IN a RR-POS-STAR) ub))
      (fact 'esup-least 's 'a)
      (let ((iff (dk-cite! '< 'a e)))
        (dk-have! (list 'AND (list '<= 'a e) (list 'NOT (list '= 'a e)))
          (lambda () (icv-keep-prop! iff (list '< 'a e))))
        (dk-split! (list 'AND (list '<= 'a e) (list 'NOT (list '= 'a e))))
        (dk-have! (list 'AND '(IN a RR-POS-STAR) (list 'IN e 'RR-POS-STAR)))
        (dk-have! (list 'AND (list '<= 'a e) (list '<= e 'a)))
        (fact 'rr-pos-star-le-antisymm 'a e)
        (icv-keep-prop! (list '= 'a e) (list 'NOT (list '= 'a e)))))))
(qed 'esup-lt-witness)
(topic! 'esup-lt-witness 'inequalities)

