;;; basw3-nag.scm -- wave of 2026-11-09/10 (agent BA-SW3), wired 2026-11-10 from scratchpad/basw3-1109/basw3-nag.scm.
;;; Library: analysis.

;;; basw3-nag.scm -- nag-complete-of-norm-cauchy: a normed abelian group in which every norm-Cauchy
;;; sequence has a norm limit has a complete metric space (the bridge BA-SW2 named, finding F5).
;;; Agent BA-SW3, wave 2026-11-09.  Destination: theorem-library/basw3-nag.scm.  Library: analysis.
;;; LOAD WINDOW: after theorem-library/rake-norm-metrics (nag-metric-space-is-metric-space,
;;; nag-metric-carrier, nag-metric-distance; load.scm:3060).  Modulo 0.  Helper prefix: bn3-.

;;; ---- nag-complete-of-norm-cauchy: a normed abelian group in which every norm-Cauchy sequence
;;; converges in norm has a complete metric space (BA-SW2 finding F5) --------------------------------
(define (bn3-ass!) (if (and (not (sequent-node-grounded? (proof-state-focus *ps*))) (dk-asm? (dk-goal))) (ass)))
(define (bn3-rhs! iff)
  (dk-have! (caddr iff) (lambda () (if (dk-only! iff (cadr iff)) (prop))))
  (dk-split-all! (list (caddr iff))))
(define (bn3-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** basw3-nag: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (if (< (string-length (expression->string a)) 300) (begin (display "      asm: ") (display (expression->string a)) (newline))))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "basw3-nag: unfinished" name))))
(define (bn3-d u v) (list '(NRM nag) (list '(OPR nag) u (list '(INV nag) v))))
(define bn3-M '(NAG-METRIC-SPACE nag))
(sp (make-wff
  (list 'FORALL 'nag (list 'IMPLIES '(IS-NORMED-AG nag)
    (list 'IMPLIES
      (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN NN (CARR nag)))
        (list 'IMPLIES
          (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list 'FORSOME 'N (list 'AND '(IN N NN)
            (list 'FORALL 'm (list 'IMPLIES '(IN m NN) (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
              (list 'IMPLIES '(AND (<= N m) (<= N n_)) (list '<= (bn3-d '(f m) '(f n_)) 'eps))))))))))
          (list 'FORSOME 'L (list 'AND '(IN L (CARR nag))
            (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list 'FORSOME 'N (list 'AND '(IN N NN)
              (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list 'IMPLIES '(<= N n_) (list '<= (bn3-d '(f n_) 'L) 'eps)))))))))))))
      (list 'IS-COMPLETE bn3-M))))))
(dk-peel!)
(define bn3-H (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (eq? (cadr h) 'f))) "the norm-Cauchy hypothesis"))
(dk-cite! 'nag-metric-space-is-metric-space 'nag)
(dk-cite! 'nag-metric-carrier 'nag)
(mac 'is-complete)
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal)) (bn3-ass!)
      (let* ((pe (dk-peel!))
             (f (caddr (car (filter (lambda (x) (dk-head-is? x 'IS-CAUCHY-SEQ)) pe))))
             (_1 (bn3-rhs! (dk-cite! 'is-cauchy-seq bn3-M f)))
             (fty (dk-rewrite-h! (list 'IN f (list 'FUN 'NN (list 'PTS bn3-M))) (list 'PTS bn3-M) '(CARR nag)))
             (cl (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x 'DIST))) "the Cauchy clause"))
             (fi! (lambda (i) (if (not (dk-asm? (list 'IN (list f i) '(CARR nag)))) (dk-cite! 'fun-apply-type-c f 'NN '(CARR nag) i))))
             (imp (inst*! bn3-H f)))
        ;; the sequence is norm-Cauchy
        (dk-have! (cadr imp)
          (lambda ()
            (let* ((eps (cadr (car (filter (lambda (x) (dk-head-is? x 'POS-RR)) (dk-peel!)))))
                   (n (dk-skolem! (dk-apply! cl eps)))
                   (c2 (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x n) (dk-contains? x 'DIST))) "the clause at N")))
              (ew n)
              (dk-conj-close!
                (lambda ()
                  (if (dk-asm? (dk-goal)) (bn3-ass!)
                    (let* ((pe2 (dk-peel!))
                           (g (dk-goal)) (B (cadr (cadr g))) (u (cadr B)) (v (cadr (caddr B)))
                           (i (cadr u)) (j (cadr v)))
                      (fi! i) (fi! j)
                      (dk-cite! 'nag-metric-distance 'nag u v)
                      (dk-apply! c2 i j)
                      (subst (list '= (bn3-d u v) (list (list 'DIST bn3-M) u v)))
                      (bn3-ass!))))))))
        (let* ((r (dk-landed-1 (lambda () (detach! imp))))
               (lv (dk-skolem! r))
               (lc (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x lv))) "the limit clause")))
          (mac 'converges)
          (ew lv)
          (mac 'converges-to)
          (dk-conj-close!
            (lambda ()
              (let ((g (dk-goal)))
                (cond ((dk-asm? g) (bn3-ass!))
                      ((and (dk-head-is? g 'IN) (dk-contains? g (list 'PTS bn3-M)))
                       (subst (list '= (list 'PTS bn3-M) '(CARR nag))) (bn3-ass!))
                      (#t
                       (let* ((eps (cadr (car (filter (lambda (x) (dk-head-is? x 'POS-RR)) (dk-peel!)))))
                              (n (dk-skolem! (dk-apply! lc eps)))
                              (c3 (dk-pick (lambda (x) (and (dk-head-is? x 'FORALL) (dk-contains? x n) (dk-contains? x 'NRM))) "the bound at N")))
                         (ew n)
                         (dk-conj-close!
                           (lambda ()
                             (if (dk-asm? (dk-goal)) (bn3-ass!)
                               (let* ((pe3 (dk-peel!))
                                      (gg (dk-goal)) (u (cadr (cadr gg))) (i (cadr u)))
                                 (fi! i)
                                 (dk-cite! 'nag-metric-distance 'nag u lv)
                                 (subst (list '= (list (list 'DIST bn3-M) u lv) (bn3-d u lv)))
                                 (dk-apply! c3 i)
                                 (bn3-ass!))))))))))))))))
(bn3-qed! 'nag-complete-of-norm-cauchy)
