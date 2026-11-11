;;; complete-transfer.scm -- wave of 2026-11-09/10 (agent BA-ONB3), wired 2026-11-10 from scratchpad/baonb3-1109/b3-complete.scm.
;;; Library: analysis.

;;; b3-complete.scm -- COMPLETENESS PASSES BETWEEN METRIC SPACES WITH THE SAME POINTS AND THE SAME
;;; DISTANCES, and the complex numbers as a complete normed abelian group.
;;; Agent BA-ONB3, 2026-11-09.  Prefix b3c-.  Nothing asserted.
;;; DESTINATION: theorem-library/complete-transfer.scm.  Library: analysis.
;;; LOAD WINDOW [l2-families + 1, end): cc-nag-complete cites cc-nag-is-normed-ag, cc-nag-nrm,
;;; cc-nag-ag-opr (l2-families, via the view) and cc-complete, nag-metric-distance,
;;; nag-metric-carrier, nag-metric-space-is-metric-space.  complete-of-same-metric alone
;;; needs only metric-completeness and could load anywhere after it.
(define (b3c-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; b3c: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l) (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))
        (error "b3c: proof not complete" name)))
  (qed name)
  (topic! name 'analysis))
(define (b3c-open?) (not (sequent-node-grounded? (proof-state-focus *ps*))))
(define (b3c-close!) (cond ((not (b3c-open?)) #t) ((dk-asm? (dk-goal)) (ass)) ((dk-head-is? (dk-goal) '==) (qrfl)) (#t (rfl))))

;;; ===========================================================================
;;; complete-of-same-metric: t a metric space with the points of s and the distances of s;
;;; s complete => t complete.  A Cauchy sequence of t is one of s (same distances), its limit in s
;;; is a limit in t.
(sp (make-wff
  '(FORALL s (FORALL t (IMPLIES (IS-METRIC-SPACE t)
     (IMPLIES (== (PTS t) (PTS s))
       (IMPLIES (FORALL x (IMPLIES (IN x (PTS s)) (FORALL y (IMPLIES (IN y (PTS s))
                  (= ((DIST t) x y) ((DIST s) x y))))))
         (IMPLIES (IS-COMPLETE s) (IS-COMPLETE t)))))))))
(dk-peel!)
(define b3c-deq (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a '(DIST t)))) "the distances"))
(define b3c-cs (dk-project! '(FORALL f (IMPLIES (IS-CAUCHY-SEQ s f) (CONVERGES s f))) 'is-complete '(IS-COMPLETE s)))
(dk-project! '(IS-METRIC-SPACE s) 'is-complete '(IS-COMPLETE s))
(define (b3c-pts! z)            ; z in PTS t in context: z in PTS s
  (dk-have! (list 'IN z '(PTS s)) (lambda () (subst '(== (PTS s) (PTS t))) (ass))))
(define (b3c-dist! a b)         ; a, b in PTS s: (DIST t) a b = (DIST s) a b, landed
  (dk-apply! b3c-deq a b))
(mac 'is-complete)
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal)) (ass)
        (let* ((landed (dk-peel!))
               (cy (car (filter (lambda (a) (dk-head-is? a 'IS-CAUCHY-SEQ)) landed)))
               (f (caddr cy)))
          (dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'is-cauchy-seq cy)))))
          (let ((ct (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a '(DIST t)) (dk-contains? a f))) "t-Cauchy")))
            ;; f is Cauchy in s
            (dk-have! (list 'IS-CAUCHY-SEQ 's f)
              (lambda ()
                (mac 'is-cauchy-seq)
                (dk-conj-close!
                  (lambda ()
                    (cond ((dk-asm? (dk-goal)) (ass))
                          ((dk-head-is? (dk-goal) 'IN) (subst '(== (PTS s) (PTS t))) (ass))
                          (#t
                           (let* ((eps (cadr (car (dk-peel!))))
                                  (nn (dk-skolem! (dk-apply! ct eps) #t))
                                  (cb (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a nn) (dk-contains? a '(DIST t)))) "the tail")))
                             (ew nn)
                             (dk-conj-close!
                               (lambda ()
                                 (if (dk-asm? (dk-goal)) (ass)
                                     (let* ((ls (dk-peel!))
                                            (vs (map cadr (filter (lambda (a) (and (dk-head-is? a 'IN) (equal? (caddr a) 'NN))) ls)))
                                            (m (car vs)) (n (cadr vs)))
                                       (dk-split-all!)
                                       (dk-have! (list 'AND (list '<= nn m) (list '<= nn n)) (lambda () (dk-conj-close! (lambda () (ass)))))
                                       (dk-apply! cb m n)
                                       (for-each (lambda (k) (fact 'fun-apply-type-c f 'NN '(PTS t) k) (b3c-pts! (list f k))) (list m n))
                                       (let ((e (b3c-dist! (list f m) (list f n)))) (subst (list '= (caddr e) (cadr e))))
                                       (ass))))))))))))
            ;; its limit in s
            (let* ((cv (dk-apply! b3c-cs f))
                   (ex (dk-landed-1 (lambda () (mac-h 'converges cv))))
                   (lim (dk-skolem! ex))
                   (ctl (dk-pick (lambda (a) (dk-head-is? a 'CONVERGES-TO)) "the limit")))
              (dk-split-all! (list (dk-landed-1 (lambda () (mac-h 'converges-to ctl)))))
              (let ((cl (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a lim) (dk-contains? a '(DIST s)))) "s-limit")))
                (mac 'converges)
                (ew lim)
                (mac 'converges-to)
                (dk-conj-close!
                  (lambda ()
                    (cond ((dk-asm? (dk-goal)) (ass))
                          ((dk-head-is? (dk-goal) 'IN) (subst '(== (PTS t) (PTS s))) (ass))
                          (#t
                           (let* ((eps (cadr (car (dk-peel!))))
                                  (nn (dk-skolem! (dk-apply! cl eps) #t))
                                  (cb (dk-pick (lambda (a) (and (dk-head-is? a 'FORALL) (dk-contains? a nn) (dk-contains? a '(DIST s)))) "the tail")))
                             (ew nn)
                             (dk-conj-close!
                               (lambda ()
                                 (if (dk-asm? (dk-goal)) (ass)
                                     (let* ((ls (dk-peel!))
                                            (n (cadr (car (filter (lambda (a) (and (dk-head-is? a 'IN) (equal? (caddr a) 'NN))) ls)))))
                                       (dk-apply! cb n)
                                       (fact 'fun-apply-type-c f 'NN '(PTS t) n)
                                       (b3c-pts! (list f n))
                                       (subst (b3c-dist! (list f n) lim))
                                       (ass)))))))))))))))))
(b3c-done! 'complete-of-same-metric)

;;; ===========================================================================
;;; cc-nag-complete: the complex numbers are complete as a normed abelian group,
;;; IS-COMPLETE(NAG-METRIC-SPACE CC-NAG), from cc-complete through complete-of-same-metric:
;;; both spaces have the points CC, and |u + -v| = |u - v|.
(define b3c-M '(NAG-METRIC-SPACE CC-NAG))
(sp (make-wff (list 'IS-COMPLETE b3c-M)))
(fact 'cc-nag-is-normed-ag)
(fact 'nag-metric-space-is-metric-space 'CC-NAG)
(fact 'nag-metric-carrier 'CC-NAG)
(fact 'cc-nag@carr)
(fact 'cc-complete)
(fact 'cc-ms@pts)
(dk-have! (list '== (list 'PTS b3c-M) '(PTS CC-MS))
  (lambda () (subst (list '== (list 'PTS b3c-M) '(CARR CC-NAG))) (subst '(== (CARR CC-NAG) CC)) (subst '(== (PTS CC-MS) CC)) (qrfl)))
(define b3c-addl '(VNB-LAMBDA (LIST x_ y_) (CARTESIAN CC CC) (+ x_ y_)))
(define b3c-negl '(VNB-LAMBDA x_ CC (- x_)))
(define b3c-nrml '(VNB-LAMBDA x_ CC (magnitude x_)))
(define b3c-msl '(VNB-LAMBDA (LIST x y) (CARTESIAN CC CC) (magnitude (- x y))))
(fact 'cc-nag@opr)
(fact 'cc-nag@inv)
(fact 'cc-nag@nrm)
(fact 'cc-ms@dist)
(dk-have! (list 'FORALL 'b3cx_ (list 'IMPLIES '(IN b3cx_ (PTS CC-MS)) (list 'FORALL 'b3cy_ (list 'IMPLIES '(IN b3cy_ (PTS CC-MS))
             (list '= (list (list 'DIST b3c-M) 'b3cx_ 'b3cy_) '((DIST CC-MS) b3cx_ b3cy_))))))
  (lambda ()
    (let* ((xs (map cadr (dk-peel!))) (x (car xs)) (y (cadr xs)))
      (for-each (lambda (z) (dk-rewrite-h! (list 'IN z '(PTS CC-MS)) '(PTS CC-MS) 'CC)) xs)
      (for-each (lambda (z) (dk-have! (list 'IN z '(CARR CC-NAG)) (lambda () (subst '(== (CARR CC-NAG) CC)) (ass)))) xs)
      (subst (dk-cite! 'nag-metric-distance 'CC-NAG x y))
      (subst (list '== '(OPR CC-NAG) b3c-addl))
      (subst (list '== '(INV CC-NAG) b3c-negl))
      (subst (list '== '(NRM CC-NAG) b3c-nrml))
      (subst (list '== '(DIST CC-MS) b3c-msl))
      (fact 'cc-neg-closed y)
      (dk-have! (list 'AND (list 'IN x 'CC) (list 'IN (list '- y) 'CC)) (lambda () (dk-conj-close! (lambda () (ass)))))
      (fact 'cc-add-closed x (list '- y))
      (let loop ((n 0))
        (dk-saturate-slot-ops! 'CC '((+ . cc-add-closed) (- . cc-neg-closed) (magnitude . cc-magnitude-closed)))
        (if (and (< n 6) (b3c-open?) (dk-contains? (dk-goal) 'VNB-LAMBDA)) (begin (dk-lam-b!) (loop (+ n 1)))))
      (if (b3c-open?) (mac 'binary-minus-def))
      (b3c-close!))))
(fact 'complete-of-same-metric 'CC-MS b3c-M)
(b3c-close!)
(b3c-done! 'cc-nag-complete)
