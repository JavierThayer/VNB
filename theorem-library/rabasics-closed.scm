;;; rabasics-closed.scm -- calculus.pdf 3.9, complex-analysis.pdf 1.9: a set A in a metric space X
;;; is closed iff every sequence of elements of A which converges, converges to an element of A.
;;;
;;;   seq-closed-implies-closed      the CONVERSE (the half the library lacked): A subset X, every
;;;                                  limit of a sequence in A lies in A  =>  IS-CLOSED(X, A)
;;;   closed-iff-sequentially-closed the notes' "if and only if", for A subset X
;;;
;;; IS-CLOSED is its own definition (the complement in PTS is open); CLOSURE is not used.
;;; The converse is the notes' argument: if y is outside A and no ball about y lies outside A,
;;; every ball B(y, 1/(k+1)) meets A; rmm-nn-choice picks g(k) in A n B(y, 1/(k+1)); g converges
;;; to y (nn-recip-succ-small, nn-recip-succ-antitone), so y in A by hypothesis -- a contradiction.
;;;
;;; Library: analysis.  Load window: after theorem-library/riesz-markov-model (rmm-nn-choice, the
;;; latest citation) and theorem-library/metric-subspace-laws (closed-limit-in); no citer yet.
;;; Helper prefix: rbc-.

(define (rbc-find what pred)
  (let ((l (filter pred (dk-asms))))
    (if (null? l) (error "rbc-find: nothing matching" what) (car l))))

(define (rbc-rad k) (list 'recip (list '+ k 1)))

;;; ---------------------------------------------------------------------------
;;; The contradiction lane.  Context: s metric, a subset PTS(s), H, y in PTS(s), NOT(y in a),
;;; NOT G where G = forsome r. POS-RR r and BALL(s,y,r) subset COMP.  Goal: G (closed by
;;; deriving y in a).

;;; for k in NN (typed in context): land FORSOME w (AND (IN w a) (IN w BALL(s,y,1/(k+1))))
;;; -- the k-th ball meets a -- else BALL(s,y,1/(k+1)) would witness G.
(define (rbc-ball-meets! s a y comp G notG k)
  (let* ((r  (rbc-rad k))
         (bl (list 'BALL s y r))
         (gk (list 'FORSOME 'w (list 'AND (list 'IN 'w a) (list 'IN 'w bl)))))
    (dk-have! gk
      (lambda ()
        (use-em gk
          (lambda () (ass))
          (lambda ()
            (let ((notgk (list 'NOT gk)))
              (fact 'nn-recip-succ-pos k)
              (dk-have! G
                (lambda ()
                  (ew r)
                  (for-each
                   (lambda (leaf)
                     (dk-focus! leaf)
                     (if (eq? (car (dk-goal)) 'POS-RR)
                         (ass)
                         (begin
                           (mac 'subset-def)
                           (let* ((pl (dk-peel!))
                                  (x  (cadr (car (filter (lambda (f) (eq? (car f) 'IN)) pl)))))
                             (dk-project! (list 'IN x (list 'PTS s)) 'ball-membership (list 'IN x bl))
                             (mac 'complement-in-membership)
                             (for-each
                              (lambda (lf)
                                (dk-focus! lf)
                                (if (eq? (car (dk-goal)) 'IN)
                                    (ass)
                                    (begin
                                      (di)               ; assume x in a; goal FALSITY
                                      (dk-have! gk
                                        (lambda ()
                                          (ew x)
                                          (for-each (lambda (l2) (dk-focus! l2) (ass))
                                                    (dk-opened (lambda () (di))))))
                                      (dk-only! gk notgk)
                                      (prop))))
                              (dk-opened (lambda () (di))))))))
                   (dk-opened (lambda () (di))))))
              (dk-only! G notG)
              (prop))))))))

;;; the converse proper
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL a (IMPLIES (SUBSET a (PTS s))
       (IMPLIES (FORALL f (IMPLIES (IN f (FUN NN a)) (FORALL l (IMPLIES (CONVERGES-TO s f l) (IN l a)))))
         (IS-CLOSED s a))))))))
(define rbc-landed (dk-peel!))
(define rbc-s (cadr (car (filter (lambda (f) (eq? (car f) 'IS-METRIC-SPACE)) rbc-landed))))
(define rbc-a (cadr (car (filter (lambda (f) (eq? (car f) 'SUBSET)) rbc-landed))))
(define rbc-h (car (filter (lambda (f) (eq? (car f) 'FORALL)) rbc-landed)))
(define rbc-pts (list 'PTS rbc-s))
(define rbc-comp (list 'COMPLEMENT-IN rbc-pts rbc-a))

;;; y outside a, inside PTS: G holds.
(define (rbc-point! y gsub)
  (let ((notG (list 'NOT gsub)))
    (use-em gsub
      (lambda () (ass))
      (lambda ()
        ;; every ball B(y, 1/(k+1)) meets a
        (let* ((fam (list 'VNB-LAMBDA 'kq_ 'NN (list 'BALL rbc-s y (rbc-rad 'kq_))))
               (impl (dk-fact! 'rmm-nn-choice rbc-a fam)))
          (dk-have! (cadr impl)
            (lambda ()
              (let* ((pl (dk-peel!))
                     (k  (cadr (car (filter (lambda (f) (eq? (car f) 'IN)) pl)))))
                (dk-lam-b!)
                ;; the claim rbc-ball-meets! lands IS this lane's goal: dk-have! proves it in place
                (rbc-ball-meets! rbc-s rbc-a y rbc-comp gsub notG k))))
          (detach! impl)
          (let* ((ex (caddr impl))
                 (g  (dk-skolem! ex))
                 (gt (rbc-find 'g-typing (lambda (f) (equal? f (list 'IN g (list 'FUN 'NN rbc-a))))))
                 (gk (rbc-find 'g-choice (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f g))))))
            (dk-have! (list 'CONVERGES-TO rbc-s g y)
              (lambda () (rbc-converges! g y gk)))
            (inst+ rbc-h g)
            (inst+ (rbc-find 'h-at-g (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f g)
                                                      (not (eq? f gk)))))
                   y)
            (dk-only! (list 'IN y rbc-a) (list 'NOT (list 'IN y rbc-a)))
            (prop)))))))

;;; CONVERGES-TO(s, g, y) from g(k) in BALL(s, y, 1/(k+1))
(define (rbc-converges! g y gk)
  (mac 'converges-to)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
             ((and (eq? (car gl) 'IN) (equal? (cadr gl) g))
              (fact 'fun-codomain-superset g 'NN rbc-a rbc-pts) (ass))
             ((eq? (car gl) 'IN) (ass))
             (#t (rbc-eps! g y gk)))))
   (dk-opened (lambda () (rbc-split-goal!)))))

;;; split a nested AND goal into its leaves (returned)
(define (rbc-split-goal!)
  (let loop ((todo (list (proof-state-focus *ps*))) (acc '()))
    (if (null? todo)
        (reverse acc)
        (begin
          (dk-focus! (car todo))
          (if (eq? (car (dk-goal)) 'AND)
              (loop (append (dk-opened (lambda () (di))) (cdr todo)) acc)
              (loop (cdr todo) (cons (car todo) acc)))))))

(define (rbc-eps! g y gk)
  (let* ((pl   (dk-peel!))
         (eps  (cadr (car (filter (lambda (f) (eq? (car f) 'POS-RR)) pl)))))
    (dk-pos-parts! eps)
    (let* ((bigN (dk-skolem! (dk-fact! 'nn-recip-succ-small eps))))
      (ew bigN)
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (car (dk-goal)) 'IN)
             (ass)
             (let* ((pl2 (dk-peel!))
                    (n_  (cadr (car (filter (lambda (f) (eq? (car f) 'IN)) pl2))))
                    (rsml (rbc-rad n_))
                    (rbig (rbc-rad bigN)))
               (inst+ gk n_)
               (dk-lam-b-h! (rbc-find 'g-at-n (lambda (f) (and (eq? (car f) 'IN) (equal? (cadr f) (list g n_))
                                                               (pair? (caddr f)) (pair? (car (caddr f)))))))
               (fact 'fun-apply-type-c g 'NN rbc-a n_)
               (dk-project! (list 'IN (list g n_) rbc-pts) 'ball-membership
                            (list 'IN (list g n_) (list 'BALL rbc-s y rsml)))
               (dk-project! (list '<= (list (list 'DIST rbc-s) y (list g n_)) rsml) 'ball-membership
                            (list 'IN (list g n_) (list 'BALL rbc-s y rsml)))
               (fact 'metric-sym rbc-s y (list g n_))
               (fact 'metric-dist-real rbc-s y (list g n_))
               (fact 'metric-dist-real rbc-s (list g n_) y)
               (fact 'nn-recip-succ-antitone bigN n_)
               (fact 'nn-recip-succ-pos n_)
               (fact 'nn-recip-succ-pos bigN)
               (dk-pos-parts! rsml)
               (dk-pos-parts! rbig)
               (dk-ineq! (list '= (list (list 'DIST rbc-s) y (list g n_)) (list (list 'DIST rbc-s) (list g n_) y))
                         (list '<= (list (list 'DIST rbc-s) y (list g n_)) rsml)
                         (list '<= rsml rbig)
                         (list '< rbig eps)))))
       (dk-opened (lambda () (di)))))))

(mac 'is-closed)
(for-each
 (lambda (leaf)
   (dk-focus! leaf)
   (let ((gl (dk-goal)))
     (cond ((memq (car gl) '(IS-METRIC-SPACE SUBSET)) (ass))
           (#t                                       ; IS-OPEN s comp
            (mac 'is-open)
            (for-each
             (lambda (lf)
               (dk-focus! lf)
               (let ((g2 (dk-goal)))
                 (cond ((eq? (car g2) 'IS-METRIC-SPACE) (ass))
                       ((eq? (car g2) 'SUBSET) (fact 'complement-in-subset rbc-a rbc-pts) (ass))
                       (#t
                        (let* ((pl (dk-peel!))
                               (y  (cadr (car (filter (lambda (f) (eq? (car f) 'IN)) pl))))
                               (gsub (dk-goal)))
                          (dk-project! (list 'IN y rbc-pts) 'complement-in-membership (list 'IN y rbc-comp))
                          (dk-project! (list 'NOT (list 'IN y rbc-a)) 'complement-in-membership (list 'IN y rbc-comp))
                          (rbc-point! y gsub))))))
             (rbc-split-goal!))))))
 (rbc-split-goal!))
(qed 'seq-closed-implies-closed)

;;; ---------------------------------------------------------------------------
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL a (IMPLIES (SUBSET a (PTS s))
       (IFF (IS-CLOSED s a)
            (FORALL f (IMPLIES (IN f (FUN NN a)) (FORALL l (IMPLIES (CONVERGES-TO s f l) (IN l a))))))))))))
(define rbc2-landed (dk-peel!))
(define rbc2-s (cadr (car (filter (lambda (f) (eq? (car f) 'IS-METRIC-SPACE)) rbc2-landed))))
(define rbc2-a (cadr (car (filter (lambda (f) (eq? (car f) 'SUBSET)) rbc2-landed))))
(dk-iff! (lambda (g) (eq? (car g) 'FORALL))
  (lambda () (fact 'closed-limit-in rbc2-s rbc2-a) (ass))
  (lambda () (fact 'seq-closed-implies-closed rbc2-s rbc2-a) (ass)))
(qed 'closed-iff-sequentially-closed)

(display ";; RBC qed failures: ") (display *vnb-qed-failures*) (newline)
;; (probe trailer removed at integration 2026-10-27) (page-audit!)
;; (probe trailer removed at integration 2026-10-27) (report-page-audit)
