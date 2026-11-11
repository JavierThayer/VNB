;;; limit-frequent.scm -- wave of 2026-11-09/10 (agent BA-2B), wired 2026-11-10 from scratchpad/ba2b-1109/limit-frequent.scm.
;;; Library: analysis.

;;; limit-frequent.scm -- a convergent sequence that takes the value c at arbitrarily large indices
;;; converges to c (BA-2 finding F1, the step "rho(y) = ||y||" of the proof of Theorem 1.23 in
;;; F. J. Thayer, "Banach Algebras and Applications": the sequence ||y^n||^(1/n) is ||y|| at
;;; every n = 2^k).  General metric spaces; the real case is s = RR-MS.
;;; Agent BA-2B, wave 2026-11-10.  Destination: theorem-library/limit-frequent.scm.
;;; Library: analysis.  All proofs modulo 0.  Helper prefix lfq-.
;;; LOAD WINDOW: after structure-library/metric-completeness (CONVERGES-TO) and the metric laws
;;; metric-pos, metric-zero-eq, metric-dist-real, and rr-le-of-le-add-all-pos, rr-limit-unique's
;;; file; it cites nothing else and can sit anywhere after those.

(define (lfq-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** limit-frequent: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "limit-frequent: unfinished" name))))
(define (lfq-cite2! . args)
  (let loop ((ch (apply dk-cite! args)))
    (if (dk-head-is? ch 'IMPLIES)
        (loop (detach-with! ch (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
        ch)))

;;; forall s, f, lm, c: f -> lm in s, and for every N there is k >= N with f(k) = c  =>  lm = c
(sp (make-wff '(FORALL s (FORALL f (FORALL lm (FORALL c (IMPLIES (CONVERGES-TO s f lm)
  (IMPLIES (FORALL lfn_ (IMPLIES (IN lfn_ NN) (FORSOME lfk_ (AND (IN lfk_ NN) (AND (<= lfn_ lfk_) (= (f lfk_) c))))))
    (= lm c)))))))))
(dk-peel!)
(let* ((cv '(CONVERGES-TO s f lm))
       (fq (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'c))) "the frequency hypothesis"))
       (ms (dk-project! '(IS-METRIC-SPACE s) 'converges-to cv))
       (ft (dk-project! '(IN f (FUN NN (PTS s))) 'converges-to cv))
       (lt (dk-project! '(IN lm (PTS s)) 'converges-to cv))
       (ev (dk-project! '(FORALL eps (IMPLIES (POS-RR eps) (FORSOME N (AND (IN N NN)
                           (FORALL n_ (IMPLIES (IN n_ NN) (IMPLIES (<= N n_) (<= ((DIST s) (f n_) lm) eps))))))))
                        'converges-to cv)))
  ;; c is a point: c = f(k0) for some k0
  (dk-have! '(IN 0 NN))
  (let* ((k0 (dk-skolem! (dk-apply! fq 0) #t)))
    (dk-cite! 'fun-apply-type-c 'f 'NN '(PTS s) k0)
    (dk-rewrite-h! (list 'IN (list 'f k0) '(PTS s)) (list 'f k0) 'c))
  (let* ((dcl '((DIST s) c lm)))
    (lfq-cite2! 'metric-dist-real 's 'c 'lm)
    (lfq-cite2! 'metric-pos 's 'c 'lm)
    ;; for every d > 0, d(c, lm) <= 0 + d
    (dk-have! (list 'FORALL 'lfd_ (list 'IMPLIES '(POS-RR lfd_) (list '<= dcl '(+ 0 lfd_))))
      (lambda ()
        (dk-peel!)
        (let* ((d (cadr (caddr (dk-goal))))
               (dd (caddr (caddr (dk-goal)))))
          (dk-cite! 'rr-pos-rr-in-rr dd)
          (let* ((nn (dk-skolem! (dk-apply! ev dd) #t))
                 (tail (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h nn) (dk-contains? h 'lm)))
                                "the tail clause"))
                 (k (dk-skolem! (dk-apply! fq nn) #t))
                 (le (dk-apply! tail k))
                 (le2 (dk-rewrite-h! le (list 'f k) 'c)))
            (dk-ineq! le2 (list 'IN dcl 'RR) (list 'IN dd 'RR))))))
    (lfq-cite2! 'rr-le-of-le-add-all-pos dcl 0)
    (dk-have! (list '= dcl 0) (lambda () (dk-ineq! (list '<= dcl 0) (list '<= 0 dcl) (list 'IN dcl 'RR))))
    (lfq-cite2! 'metric-zero-eq 's 'c 'lm)
    (subst '(= lm c))
    (rfl)))
(lfq-qed! 'limit-of-frequent-value)

;;; the real case
(sp (make-wff '(FORALL f (FORALL lm (FORALL c (IMPLIES (CONVERGES-TO RR-MS f lm)
  (IMPLIES (FORALL lfn_ (IMPLIES (IN lfn_ NN) (FORSOME lfk_ (AND (IN lfk_ NN) (AND (<= lfn_ lfk_) (= (f lfk_) c))))))
    (= lm c))))))))
(dk-peel!)
(lfq-cite2! 'limit-of-frequent-value 'RR-MS 'f 'lm 'c)
(dk-ass!)
(lfq-qed! 'rr-limit-of-frequent-value)
