;;; rabasics-trunc.scm -- calculus.pdf 3.27: d'(x, y) = min(d(x, y), 1) is a metric, and a sequence
;;; converges for d' exactly when it converges for d.
;;;
;;; The metric is the library's TRUNC-METRIC(s) (trunc-metric-dist: DIST = min(1, d)), already proven a
;;; metric space (trunc-metric-is-metric-space).  What was missing is the convergence equivalence FOR
;;; THIS truncation (bdd-metric-converges-iff is for d/(1+d)):
;;;
;;;   trunc-metric-converges-fwd   converges-to(s, f, l)            => converges-to(trunc-metric(s), f, l)
;;;   trunc-metric-converges-bwd   converges-to(trunc-metric(s), f, l) => converges-to(s, f, l)
;;;   trunc-metric-converges-iff   the two together (the shape of bdd-metric-converges-iff)
;;;
;;; fwd: min(1, d) <= d.  bwd: given eps, take 0 < h with 2h <= min(eps, 1) (rr-min-pos, then halve);
;;; d' <= h < 1 forces min(1, d) = d, so d <= h <= eps.
;;;
;;; Library: analysis.  Load window: after theorem-library/trunc-metric-proof (trunc-metric-dist,
;;; trunc-metric-is-metric-space) and theorem-library/rr-halving / pos-rr-bridges (dk-halve!);
;;; no citer yet.  Helper prefix: rbt-.

(define (rbt-find what pred)
  (let ((l (filter pred (dk-asms))))
    (if (null? l) (error "rbt-find: nothing matching" what) (car l))))

(define (rbt-split-goal!)
  (let loop ((todo (list (proof-state-focus *ps*))) (acc '()))
    (if (null? todo)
        (reverse acc)
        (begin
          (dk-focus! (car todo))
          (if (eq? (car (dk-goal)) 'AND)
              (loop (append (dk-opened (lambda () (di))) (cdr todo)) acc)
              (loop (cdr todo) (cons (car todo) acc)))))))

;;; open the hypothesis CONVERGES-TO(m, f, l): return its tail universal
(define (rbt-open-conv! m f l)
  (mac-h 'converges-to (list 'CONVERGES-TO m f l))
  (dk-split-all!)
  (rbt-find 'tail (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'POS-RR)))))

;;; on the focus goal CONVERGES-TO(m, f, l): unfold, close the three typing conjuncts with TYPE!,
;;; and run TAIL! on the eps-N conjunct.
(define (rbt-goal-conv! type! tail!)
  (mac 'converges-to)
  (for-each (lambda (leaf)
              (dk-focus! leaf)
              (if (eq? (car (dk-goal)) 'FORALL) (tail!) (type!)))
            (rbt-split-goal!)))

(define rbt-stmt-fwd
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
       (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
         (IMPLIES (CONVERGES-TO s f lm_) (CONVERGES-TO (TRUNC-METRIC s) f lm_)))))))))
(define rbt-stmt-bwd
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
       (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
         (IMPLIES (CONVERGES-TO (TRUNC-METRIC s) f lm_) (CONVERGES-TO s f lm_)))))))))

;;; read s, f, lm off the peeled goal (CONVERGES-TO M f lm)
(define (rbt-vars)
  (let ((g (dk-goal)))
    (list (caddr g) (cadddr g))))

;;; ---------------------------------------------------------------------------
(sp (make-wff rbt-stmt-fwd))
(define rbt1-landed (dk-peel!))
(define rbt1-s (cadr (car (filter (lambda (a) (eq? (car a) 'IS-METRIC-SPACE)) rbt1-landed))))
(define rbt1-f (car (rbt-vars)))
(define rbt1-l (cadr (rbt-vars)))
(define rbt1-tail (rbt-open-conv! rbt1-s rbt1-f rbt1-l))
(fact 'trunc-metric-is-metric-space rbt1-s)
(rbt-goal-conv!
 (lambda () (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE) (ass) (begin (slot 'PTS) (ass))))
 (lambda ()
   (let* ((pl   (dk-peel!))
          (eps  (cadr (car (filter (lambda (a) (eq? (car a) 'POS-RR)) pl))))
          (parts (dk-pos-parts! eps))
          (nex  (dk-deepest (lambda () (inst+ rbt1-tail eps))))
          (bigN (dk-skolem! nex))
          (inner (rbt-find 'inner (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bigN))))))
     (ew bigN)
     (for-each
      (lambda (leaf)
        (dk-focus! leaf)
        (if (eq? (car (dk-goal)) 'IN)
            (ass)
            (let* ((pl2 (dk-peel!))
                   (n_  (cadr (car (filter (lambda (a) (eq? (car a) 'IN)) pl2))))
                   (fn  (list rbt1-f n_))
                   (dd  (list (list 'DIST rbt1-s) fn rbt1-l))
                   (dt  (list (list 'DIST (list 'TRUNC-METRIC rbt1-s)) fn rbt1-l)))
              (inst+ inner n_)
              (fact 'fun-apply-type-c rbt1-f 'NN (list 'PTS rbt1-s) n_)
              (fact 'metric-dist-real rbt1-s fn rbt1-l)
              (fact 'rr-one-in)
              (fact 'trunc-metric-dist rbt1-s fn rbt1-l)
              (subst (list '== dt (list 'min 1 dd)))
              (fact 'rr-min-le-right 1 dd)
              (fact 'rr-min-closed 1 dd)
              (dk-ineq! (list '<= (list 'min 1 dd) dd) (list '<= dd eps)))))
      (dk-opened (lambda () (di)))))))
(qed 'trunc-metric-converges-fwd)

;;; ---------------------------------------------------------------------------
(sp (make-wff rbt-stmt-bwd))
(define rbt2-landed (dk-peel!))
(define rbt2-s (cadr (car (filter (lambda (a) (eq? (car a) 'IS-METRIC-SPACE)) rbt2-landed))))
(define rbt2-f (car (rbt-vars)))
(define rbt2-l (cadr (rbt-vars)))
(define rbt2-tail (rbt-open-conv! (list 'TRUNC-METRIC rbt2-s) rbt2-f rbt2-l))
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(rbt-goal-conv!
 (lambda () (ass))
 (lambda ()
   (let* ((pl   (dk-peel!))
          (eps  (cadr (car (filter (lambda (a) (eq? (car a) 'POS-RR)) pl)))))
     (dk-pos-parts! eps)
     (let* ((w (dk-skolem! (dk-fact! 'rr-min-pos eps 1))))
       (fact 'rr-pos-rr-of-lt w)
       (let* ((h    (dk-halve! w))
              (nex  (dk-deepest (lambda () (inst+ rbt2-tail h))))
              (bigN (dk-skolem! nex))
              (inner (rbt-find 'inner (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a bigN))))))
         (ew bigN)
         (for-each
          (lambda (leaf)
            (dk-focus! leaf)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (let* ((pl2 (dk-peel!))
                       (n_  (cadr (car (filter (lambda (a) (eq? (car a) 'IN)) pl2))))
                       (fn  (list rbt2-f n_))
                       (dd  (list (list 'DIST rbt2-s) fn rbt2-l))
                       (dt  (list (list 'DIST (list 'TRUNC-METRIC rbt2-s)) fn rbt2-l))
                       (mn  (list 'min 1 dd)))
                  (inst+ inner n_)
                  (fact 'fun-apply-type-c rbt2-f 'NN (list 'PTS rbt2-s) n_)
                  (fact 'metric-dist-real rbt2-s fn rbt2-l)
                  (fact 'trunc-metric-dist rbt2-s fn rbt2-l)
                  (dk-rewrite-h! (list '<= dt h) dt mn)
                  (fact 'rr-min-closed 1 dd)
                  (fact 'rr-min-cases 1 dd)
                  (use-cases (list (list '= mn 1) (list '= mn dd))
                    (lambda ()
                      (dk-ineq! (list '= mn 1) (list '<= mn h) (list '= (list '+ h h) w)
                                (list '<= w 1) (list '< 0 h)))
                    (lambda ()
                      (dk-ineq! (list '= mn dd) (list '<= mn h) (list '= (list '+ h h) w)
                                (list '<= w eps) (list '< 0 h)))))))
          (dk-opened (lambda () (di)))))))))
(qed 'trunc-metric-converges-bwd)

;;; ---------------------------------------------------------------------------
(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
       (FORALL lm_ (IMPLIES (IN lm_ (PTS s))
         (IFF (CONVERGES-TO (TRUNC-METRIC s) f lm_) (CONVERGES-TO s f lm_))))))))))
(define rbt3-landed (dk-peel!))
(define rbt3-s (cadr (car (filter (lambda (a) (eq? (car a) 'IS-METRIC-SPACE)) rbt3-landed))))
(define rbt3-f (cadr (car (filter (lambda (a) (and (eq? (car a) 'IN) (pair? (caddr a)) (eq? (car (caddr a)) 'FUN))) rbt3-landed))))
(define rbt3-l (cadr (car (filter (lambda (a) (and (eq? (car a) 'IN) (not (equal? (cadr a) rbt3-f)))) rbt3-landed))))
(dk-iff! (lambda (g) (equal? (cadr g) rbt3-s))
  (lambda () (fact 'trunc-metric-converges-bwd rbt3-s rbt3-f rbt3-l) (ass))
  (lambda () (fact 'trunc-metric-converges-fwd rbt3-s rbt3-f rbt3-l) (ass)))
(qed 'trunc-metric-converges-iff)

(display ";; RBT qed failures: ") (display *vnb-qed-failures*) (newline)
;; (probe trailer removed at integration 2026-10-27) (page-audit!)
;; (probe trailer removed at integration 2026-10-27) (report-page-audit)
