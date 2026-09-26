;;; rake-compact-equivalences.scm -- Prop 3.12, the two remaining equivalences
;;; (batch 8, assignment 8-A; helper prefix `r9a-').
;;;
;;; Both statements are copied LITERALLY from their assertion sites,
;;; structure-library/compactness.scm:71 (compact-iff-tb-complete) and :84
;;; (compact-iff-cluster-point).  They are pure assemblies of theorems proven
;;; on 2026-09-19 (batch 7): no new mathematics, no new support.
;;;
;;;   compact-iff-cluster-point
;;;       forall s.  IS-METRIC-SPACE s  =>
;;;         ( IS-COMPACT s  <=>  forall f in FUN(NN, PTS s). forsome x. CLUSTER-POINT(s,f,x) )
;;;     (=>)  compact-seq-has-cluster                  (rake-compact-cluster)
;;;     (<=)  the hypothesis gives a cluster point for every sequence;
;;;           cluster-point-has-convergent-subseq      (rake-compact-iff-seq-compact)
;;;           turns it into a convergent subsequence, i.e. SEQ-COMPACT s, and
;;;           seq-compact-implies-compact              (rake-lebesgue-number)
;;;           closes.  The (<=) driver is the body of compact-implies-seq-compact
;;;           with the hypothesis in the place of compact-seq-has-cluster.
;;;
;;;   compact-iff-tb-complete
;;;       forall s.  IS-METRIC-SPACE s  =>
;;;         ( IS-COMPACT s  <=>  TOTALLY-BOUNDED s and IS-COMPLETE s )
;;;     (=>)  compact-implies-totally-bounded  (calculus/compact-tb-proof)
;;;           compact-implies-complete         (calculus/compact-complete-proof)
;;;     (<=)  totally-bounded-has-cauchy-subsequence (cauchy-subseq-proof) gives a
;;;           Cauchy subsequence; the second conjunct of IS-COMPLETE makes it
;;;           converge; that is SEQ-COMPACT s, and seq-compact-implies-compact
;;;           closes.  Completeness is used through the UNFOLD of IS-COMPLETE,
;;;           not through the asserted support complete-cauchy-converges
;;;           (metric-completeness.scm:78), which would put a leaf on the bill.
;;;
;;; The instantiation of the completeness law at SUBSEQ(f,phi) is preceded by
;;; the typing (IN (SUBSEQ f phi) (FUN NN (PTS s))) -- subseq-is-fun -- because
;;; a functoid application is not certified DEFINED on its own (the LUTINS rule).
;;;
;;; CITATIONS and their load.scm lines (2026-09-19):
;;;   subseq-is-fun                          theorem-library/rake-analysis2        844
;;;   compact-seq-has-cluster                theorem-library/rake-compact-cluster 1308
;;;   cluster-point-has-convergent-subseq    theorem-library/rake-compact-iff-seq-compact 1345
;;;   seq-compact-implies-compact            theorem-library/rake-lebesgue-number 1351
;;;   totally-bounded-has-cauchy-subsequence theorem-library/cauchy-subseq-proof  1378
;;;   compact-implies-complete               calculus/compact-complete-proof      1314
;;;   compact-implies-totally-bounded        calculus/compact-tb-proof            2371
;;; lo = calculus/compact-tb-proof (2371).  NOTHING cites either name (only
;;; comments do), so hi = end of load.scm: window [2371, end).

;;; ---------------------------------------------------------------------
;;; helpers (file-local, prefix r9a-)
;;; ---------------------------------------------------------------------

(define (r9a-metric-var)
  (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))

;; the eigenvariable of a landed sequence typing (IN f (FUN NN (PTS s)))
(define (r9a-seq-var landed sv)
  (cadr (or (find-first (lambda (fm)
                          (and (pair? fm) (eq? (car fm) 'IN)
                               (equal? (caddr fm) (list 'FUN 'NN (list 'PTS sv)))))
                        landed)
            (error "r9a-seq-var: no sequence typing landed"))))

;; goal (IN <pt> (PTS s)), read off a predicate hypothesis in a LANE (the
;; mac-h would otherwise consume the hypothesis the next citation needs)
(define (r9a-pt-in-pts! sv pt pred)
  (have! (list 'IN pt (list 'PTS sv))
    (lambda ()
      (dk-split-all! (dk-landed (lambda () (mac-h (car pred) pred))))
      (dk-split-all!)
      (ass))))

;; goal: the SEQ-COMPACT existential, once a cluster point / limit is in hand.
;; PHI is the subsequence index, LIM the limit point.
(define (r9a-close-seq-compact! phi lim)
  (witness! phi
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
             (ass)
             (witness! lim (lambda () (dk-conj-close! (lambda () (ass)))))))))))

;;; =====================================================================
;;; 1.  compact-iff-cluster-point   (structure-library/compactness.scm:84)
;;; =====================================================================

;; goal (SEQ-COMPACT s), from CLU = forall f in FUN(NN, PTS s). forsome x. CLUSTER-POINT
(define (r9a-seq-compact-from-cluster! sv clu)
  (mac 'SEQ-COMPACT)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE)
         (ass)
         (let* ((landed (dk-peel!))
                (fv (r9a-seq-var landed sv))
                (xv (dk-skolem! (dk-apply! clu fv))))
           (r9a-pt-in-pts! sv xv (list 'CLUSTER-POINT sv fv xv))
           (let ((phiv (dk-skolem!
                        (dk-fact! 'cluster-point-has-convergent-subseq sv fv xv))))
             (r9a-close-seq-compact! phiv xv)))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (FORALL f (IMPLIES (IN f (FUN NN (PTS s)))
            (FORSOME x (CLUSTER-POINT s f x)))))))))

(dk-peel!)
(define r9a1-sv  (r9a-metric-var))
(define r9a1-iff (dk-goal))
(define r9a1-cpt (cadr r9a1-iff))               ; (IS-COMPACT s)
(define r9a1-clu (caddr r9a1-iff))              ; the cluster-point law
(define r9a1-fwd (list 'IMPLIES r9a1-cpt r9a1-clu))
(define r9a1-bwd (list 'IMPLIES r9a1-clu r9a1-cpt))

(have! r9a1-fwd
  (lambda ()
    (let* ((landed (dk-peel!))
           (fv (r9a-seq-var landed r9a1-sv)))
      ;; compact-seq-has-cluster has a CONJUNCTIVE antecedent: have! it whole
      (have! (list 'AND r9a1-cpt
                   (list 'IN fv (list 'FUN 'NN (list 'PTS r9a1-sv)))))
      (dk-fact! 'compact-seq-has-cluster r9a1-sv fv)
      (ass))))

(have! r9a1-bwd
  (lambda ()
    (dk-peel!)
    (let ((clu (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                          (dk-contains? fm 'CLUSTER-POINT)))
                        "the cluster-point hypothesis")))
      (have! (list 'SEQ-COMPACT r9a1-sv)
        (lambda () (r9a-seq-compact-from-cluster! r9a1-sv clu)))
      (dk-fact! 'seq-compact-implies-compact r9a1-sv)
      (ass))))

(dk-only! r9a1-fwd r9a1-bwd)
(prop)

(qed 'compact-iff-cluster-point)
(topic! 'compact-iff-cluster-point 'topology)

;;; =====================================================================
;;; 2.  compact-iff-tb-complete   (structure-library/compactness.scm:71)
;;; =====================================================================

;; goal (SEQ-COMPACT s), from TOTALLY-BOUNDED s and IS-COMPLETE s in context
(define (r9a-seq-compact-from-tb! sv)
  (mac 'SEQ-COMPACT)
  (dk-conj-close!
   (lambda ()
     (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE)
         (ass)
         (let* ((landed (dk-peel!))
                (fv (r9a-seq-var landed sv))
                (phiv (dk-skolem!
                       (dk-fact! 'totally-bounded-has-cauchy-subsequence sv fv)))
                (sub (list 'SUBSEQ fv phiv)))
           ;; type the subsequence BEFORE instantiating the completeness law at it
           (have! (list 'AND (list 'IN fv (list 'FUN 'NN (list 'PTS sv)))
                        (list 'STRICTLY-MONO-NN phiv)))
           (dk-fact! 'subseq-is-fun sv fv phiv)
           ;; completeness, by the UNFOLD (not the asserted support)
           (dk-split-all!
            (dk-landed (lambda () (mac-h 'is-complete (list 'IS-COMPLETE sv)))))
           (dk-split-all!)
           (let* ((claw (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                                                   (dk-contains? fm 'IS-CAUCHY-SEQ)))
                                 "the completeness law"))
                  (conv (dk-apply! claw sub))
                  (ex   (dk-landed-find (lambda () (mac-h 'converges conv))
                                        (dk-head? 'FORSOME)))
                  (lv   (dk-skolem! ex)))
             (r9a-pt-in-pts! sv lv (list 'CONVERGES-TO sv sub lv))
             (r9a-close-seq-compact! phiv lv)))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s)
          (AND (TOTALLY-BOUNDED s) (IS-COMPLETE s)))))))

(dk-peel!)
(define r9a2-sv  (r9a-metric-var))
(define r9a2-iff (dk-goal))
(define r9a2-cpt (cadr r9a2-iff))               ; (IS-COMPACT s)
(define r9a2-tbc (caddr r9a2-iff))              ; (AND (TOTALLY-BOUNDED s) (IS-COMPLETE s))
(define r9a2-fwd (list 'IMPLIES r9a2-cpt r9a2-tbc))
(define r9a2-bwd (list 'IMPLIES r9a2-tbc r9a2-cpt))

(have! r9a2-fwd
  (lambda ()
    (dk-peel!)
    (dk-fact! 'compact-implies-totally-bounded r9a2-sv)
    (dk-fact! 'compact-implies-complete r9a2-sv)
    (dk-conj-close! (lambda () (ass)))))

(have! r9a2-bwd
  (lambda ()
    (dk-split-all! (dk-peel!))
    (have! (list 'SEQ-COMPACT r9a2-sv)
      (lambda () (r9a-seq-compact-from-tb! r9a2-sv)))
    (dk-fact! 'seq-compact-implies-compact r9a2-sv)
    (ass)))

(dk-only! r9a2-fwd r9a2-bwd)
(prop)

(qed 'compact-iff-tb-complete)
(topic! 'compact-iff-tb-complete 'topology)

;;; =====================================================================
;;; FOR THE INTEGRATOR
;;;
;;; * RETIRE the two axioms and their warrants in structure-library/
;;;   compactness.scm: compact-iff-tb-complete (:71-:82) and
;;;   compact-iff-cluster-point (:84-:95).  Both `qed's print
;;;   "re-installing the same statement".
;;; * WIRE this file after calculus/compact-tb-proof (load.scm:2371); nothing
;;;   cites either name, so any slot below that line works.
;;; =====================================================================
