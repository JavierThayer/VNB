;;; isom-uc.scm -- calculus.pdf Proposition 3.21: if X is compact, every continuous
;;; f : X --> Y is uniformly continuous.  Agent ISOM, 2026-10-26.
;;;
;;;   compact-continuous-uniformly-continuous
;;;     is-compact(s) and is-continuous(s, t, f)  ==>  is-uniformly-continuous(s, t, f)
;;;
;;; The notes prove Prop 3.22 (uniformly-continuous-off-compact) as the "slightly more
;;; general result"; 3.21 is the case K = X.  Here it is read off Cor 3.23
;;; (constant-off-compact-uniformly-continuous) at K = pts(s), where "constant off K"
;;; is vacuous: pts(s) is closed in s, so the subspace on it is compact
;;; (closed-subset-of-compact-is-compact).
;;;
;;; carrier-is-closed (beside carrier-is-open): pts(s) is closed in s.  Its complement
;;; in pts(s) is empty, so open.
;;;
;;; WINDOW.  Citations: subset-refl (subset-lemmas, 970), closed-subset-of-compact-is-compact
;;; (compact-subspace, 1483), complement-in-subset, complement-in-membership (early),
;;; constant-off-compact-uniformly-continuous (calc3-uniform, 3737).  lo = after
;;; theorem-library/calc3-uniform; hi = none.  Library: analysis.
;;;
;;; Helper prefix: iuc-.

(define (iuc-head g) (and (pair? g) (car g)))

;;; =====================================================================
;;; carrier-is-closed
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s) (IS-CLOSED s (PTS s))))))
(dk-peel!)
(define iuc-C '(COMPLEMENT-IN (PTS s) (PTS s)))
(mac 'is-closed)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ((eq? (iuc-head g) 'SUBSET) (fact 'subset-refl '(PTS s)) (ass))
      ((eq? (iuc-head g) 'IS-OPEN)
       (mac 'is-open)
       (dk-conj-close!
        (lambda ()
          (let ((g2 (dk-goal)))
            (cond
             ((eq? (iuc-head g2) 'SUBSET)
              (fact 'complement-in-subset '(PTS s) '(PTS s)) (ass))
             ((eq? (iuc-head g2) 'FORALL)
              (let* ((pl (dk-peel!))
                     (m (car (filter (lambda (h) (and (eq? (iuc-head h) 'IN)
                                                      (equal? (caddr h) iuc-C)))
                                     pl))))
                (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership m))))
                (prop)))
             (#t (ass)))))))
      (#t (ass))))))
(qed 'carrier-is-closed)
(topic! 'carrier-is-closed 'analysis)
(alias! 'carrier-is-closed "the whole space is closed in itself")

;;; =====================================================================
;;; Prop 3.21
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-COMPACT s)
       (IMPLIES (IS-CONTINUOUS s t f)
         (IS-UNIFORMLY-CONTINUOUS s t f))))))))
(dk-peel!)
(dk-project! '(IS-METRIC-SPACE s) 'is-compact '(IS-COMPACT s))
(fact 'carrier-is-closed 's)
(fact 'closed-subset-of-compact-is-compact 's '(PTS s))
(fact 'subset-refl '(PTS s))
;;; "f is constant off pts(s)" holds vacuously, with any constant.
(dk-have! '(FORSOME cv (FORALL x (IMPLIES (IN x (PTS s))
                          (IMPLIES (NOT (IN x (PTS s))) (= (f x) cv)))))
  (lambda ()
    (ew 'EMPTY-SET)
    (dk-peel!)
    (prop)))
(fact 'constant-off-compact-uniformly-continuous 's 't 'f '(PTS s))
(ass)
(qed 'compact-continuous-uniformly-continuous)
(topic! 'compact-continuous-uniformly-continuous 'analysis)
(alias! 'compact-continuous-uniformly-continuous
        "a continuous function on a compact metric space is uniformly continuous")
