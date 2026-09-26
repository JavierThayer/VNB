;;; rake-compact-complete.scm -- two of the three asserted leaves on the bill of
;;; compact-implies-complete (calculus/compact-complete-proof.scm), PROVEN.
;;;
;;;   cauchy-seq-is-fun         forall s, f. IS-CAUCHY-SEQ(s,f) => f in FUN(NN, PTS s)
;;;   cauchy-cluster-converges  forall s, f. IS-CAUCHY-SEQ(s,f) and (forsome x. CLUSTER-POINT(s,f,x))
;;;                                          => CONVERGES(s,f)
;;;
;;; Both statements are copied VERBATIM from their definition sites:
;;; structure-library/metric-completeness.scm:93 and
;;; structure-library/compactness.scm:205.  The third leaf on that bill,
;;; compact-seq-has-cluster (compactness.scm:193), is NOT here -- see the note
;;; at the end of this header.
;;;
;;; CAUCHY-SEQ-IS-FUN is the typing conjunct of the IS-CAUCHY-SEQ definition.
;;; IS-CAUCHY-SEQ is a `def-predicate', so the defining iff is a citable theorem
;;; and `mac-h' can unfold it in the hypothesis: peel, unfold, split, `ass' --
;;; subtype-laws.scm's `stl--project!' shape.
;;;
;;; CAUCHY-CLUSTER-CONVERGES is the eps/2 argument.  Skolemize the cluster
;;; point x, unfold both IS-CAUCHY-SEQ and CLUSTER-POINT in the hypotheses, and
;;; give CONVERGES the witness x.  At eps > 0, `dk-halve!' produces d with
;;; d + d = eps (and d in RR, 0 < d, POS-RR d); Cauchyness at d gives a
;;; threshold nc, and the cluster condition at (d, nc) gives an index n0 >= nc
;;; with d(f n0, x) < d.  The convergence witness is nc itself: for n_ >= nc the
;;; triangle inequality (metric-triangle, a slot law of IS-METRIC-SPACE, proven
;;; in structure-library/metric-laws.scm) plus
;;;     d(f n_, f n0) <= d,  d(f n0, x) < d,  d + d = eps
;;; is one `ineq' call.  `ineq' is a trusted oracle and adds no bill entry; its
;;; premises are named BY FORMULA (rcc-ineq) and the three distances are typed
;;; into RR beforehand with metric-dist-real, since `ineq' certifies an atom
;;; only from a STANDALONE (IN t RR).
;;;
;;; The two eps-universals that the unfolds land are told apart by the head
;;; under the POS-RR guard -- FORSOME for Cauchy (the threshold), FORALL for the
;;; cluster point (the index m) -- never by shape or by context order.
;;;
;;; The POS-RR guard is NOT a typing guard, so one `di' on
;;; (FORALL eps (IMPLIES (POS-RR eps) ...)) lands nothing; `dk-peel!' (which
;;; loops on the LANDING) is what brings the guard down.
;;;
;;; LOAD WINDOW  [286, 280)  -- EMPTY as load.scm stands; see the report.
;;;   lo = 286: the LATEST citation is metric-triangle, proven in
;;;     structure-library/metric-laws (position 285).  Then, in order:
;;;     metric-dist-real (theorem-library/op-typing, 204), rr-pos-halvable
;;;     (theorem-library/rr-halving, 182, through dk-halve!), rr-pos-rr-in-rr
;;;     and rr-lt-of-pos-rr (theorem-library/pos-rr-bridges, 175, also through
;;;     dk-halve!), fun-apply-type-c (theorem-library/fun-apply-type-proof,
;;;     160), driver-kit (138), and the definitions themselves
;;;     (structure-library/compactness 48, structure-library/metric-completeness
;;;     44).  `ineq' and the dk- kit load early and are safe.
;;;   hi = 280: the only citer of either leaf is calculus/compact-complete-proof
;;;     (position 279).  pss-topics (537) only names them in `topic!' lines.
;;;   RESOLUTION: calculus/compact-complete-proof must MOVE BELOW this file.
;;;     That is free -- nothing in the tree cites compact-implies-complete
;;;     (outside pss-topics), so the block can sit anywhere after 286.
;;;
;;; SITES TO RETIRE:
;;;   structure-library/metric-completeness.scm:93  (support + warrant! at :96)
;;;   structure-library/compactness.scm:205         (support + warrant! at :209)
;;;
;;; Helper prefix `rcc-'.  All helpers are file-local.

(define (rcc-hyp h what) (dk-pick (dk-head? h) what))
(define (rcc-find pred what) (dk-pick pred what))

;; The eps-universal a definition unfold lands: (FORALL eps (IMPLIES (POS-RR eps) <INNER ...>)).
;; INNER is FORSOME for IS-CAUCHY-SEQ (the threshold) and FORALL for CLUSTER-POINT
;; (the index) -- the one stable discriminator between the two.
(define (rcc-eps-univ inner)
  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                   (pair? (caddr a)) (eq? (car (caddr a)) 'IMPLIES)
                   (pair? (cadr (caddr a))) (eq? (car (cadr (caddr a))) 'POS-RR)
                   (pair? (caddr (caddr a))) (eq? (car (caddr (caddr a))) inner))))

;; `ineq' premises are 1-BASED context indices; name them by FORMULA instead.
(define (rcc-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rcc-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rcc-ineq . forms) (apply ineq (map rcc-idx forms)))

;;; =====================================================================
;;; cauchy-seq-is-fun -- the typing conjunct of IS-CAUCHY-SEQ.
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL f (IMPLIES (IS-CAUCHY-SEQ s f)
                                            (IN f (FUN NN (PTS s))))))))
(dk-peel!)
(mac-h 'IS-CAUCHY-SEQ (rcc-hyp 'IS-CAUCHY-SEQ "the Cauchy hypothesis"))
(dk-split-all!)
(ass)
(if (proof-done? *ps*)
    (qed 'cauchy-seq-is-fun)
    (error "rake-compact-complete: cauchy-seq-is-fun did not close"))
(topic! 'cauchy-seq-is-fun 'plumbing)

;;; =====================================================================
;;; cauchy-cluster-converges -- a Cauchy sequence with a cluster point
;;; converges (to that cluster point).
;;; =====================================================================

(sp (make-wff '(FORALL s (FORALL f
   (IMPLIES (AND (IS-CAUCHY-SEQ s f) (FORSOME x (CLUSTER-POINT s f x)))
            (CONVERGES s f))))))

;; s and f are read off the landed hypothesis, never guessed: `di' renames.
(define rcc-h (car (dk-peel!)))
(define rcc-s (cadr (cadr rcc-h)))
(define rcc-f (caddr (cadr rcc-h)))
(dk-split! rcc-h)
(define rcc-x (dk-skolem! (rcc-hyp 'FORSOME "the cluster existential")))
(mac-h 'CLUSTER-POINT (list 'CLUSTER-POINT rcc-s rcc-f rcc-x))
(mac-h 'IS-CAUCHY-SEQ (list 'IS-CAUCHY-SEQ rcc-s rcc-f))
(dk-split-all!)
(define rcc-cl-univ (rcc-find (rcc-eps-univ 'FORALL) "the cluster eps-universal"))
(define rcc-cy-univ (rcc-find (rcc-eps-univ 'FORSOME) "the Cauchy eps-universal"))

(define (rcc-dist a b) (list (list 'DIST rcc-s) a b))

;; goal: FORALL n_ in NN. nc <= n_ => d(f n_, x) <= eps
(define (rcc-tail! eps d nc n0 inner)
  (let* ((landed (dk-peel!))
         (ty (rcc-find (lambda (a) (and (pair? a) (eq? (car a) 'IN) (member a landed)))
                       "the index typing"))
         (nv (cadr ty)))
    (fact 'fun-apply-type-c rcc-f 'NN (list 'PTS rcc-s) nv)
    (fact 'fun-apply-type-c rcc-f 'NN (list 'PTS rcc-s) n0)
    ;; the Cauchy inner clause has a CONJUNCTIVE antecedent: `have!' it whole.
    (dk-have! (list 'AND (list '<= nc nv) (list '<= nc n0)))
    (dk-apply! inner nv n0)
    (let ((fnv (list rcc-f nv)) (fn0 (list rcc-f n0)))
      (fact 'metric-triangle rcc-s fnv fn0 rcc-x)
      (fact 'metric-dist-real rcc-s fnv rcc-x)
      (fact 'metric-dist-real rcc-s fnv fn0)
      (fact 'metric-dist-real rcc-s fn0 rcc-x)
      (rcc-ineq (list '<= (rcc-dist fnv rcc-x)
                      (list '+ (rcc-dist fnv fn0) (rcc-dist fn0 rcc-x)))
                (list '<= (rcc-dist fnv fn0) d)
                (list '< (rcc-dist fn0 rcc-x) d)
                (list '= (list '+ d d) eps)))))

;; goal: FORALL eps. POS-RR(eps) => FORSOME N in NN. FORALL n_ in NN. N <= n_ => ...
(define (rcc-eps-branch!)
  (let* ((landed (dk-peel!))          ; POS-RR is not a typing guard: one `di' lands nothing
         (pos (rcc-find (lambda (a) (and (pair? a) (eq? (car a) 'POS-RR) (member a landed)))
                        "the POS-RR guard"))
         (eps (cadr pos)))
    (fact 'rr-pos-rr-in-rr eps)       ; dk-halve! types the HALF, not eps
    (let* ((d   (dk-halve! eps))
           (cex (dk-deepest (lambda () (inst+ rcc-cy-univ d))))
           (nc  (dk-skolem! cex)))
      (dk-split-all!)
      (let* ((inner (rcc-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a nc)))
                              "the Cauchy inner clause"))
             (cld   (dk-deepest (lambda () (inst+ rcc-cl-univ d))))
             (clat  (dk-apply! cld nc))
             (n0    (dk-skolem! clat)))
        (dk-split-all!)
        (ew nc)
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'IN)
               (ass)
               (rcc-tail! eps d nc n0 inner))))))))

(mac 'CONVERGES)
(ew rcc-x)
(mac 'CONVERGES-TO)
(dk-conj-close!
 (lambda ()
   (if (memq (car (dk-goal)) '(IS-METRIC-SPACE IN))
       (ass)
       (rcc-eps-branch!))))

(if (proof-done? *ps*)
    (qed 'cauchy-cluster-converges)
    (error "rake-compact-complete: cauchy-cluster-converges did not close"))
(topic! 'cauchy-cluster-converges 'analysis)

;;; =====================================================================
;;; NOT PROVEN HERE: compact-seq-has-cluster (structure-library/compactness.scm:193)
;;;
;;;   forall s, f.  IS-COMPACT(s) and f in FUN(NN, PTS s)
;;;                 =>  forsome x. CLUSTER-POINT(s, f, x)
;;;
;;; This is calculus.pdf Prop 3.12 (1)=>(3) -- open-cover compactness implies
;;; sequential compactness -- and it is a real theorem, not a projection.  The
;;; statement is SOUND (no untyped index, no unguarded strict `=', and the
;;; empty metric space is not a counterexample: PTS(s) = {} makes
;;; f in FUN(NN, PTS s) unsatisfiable, so the implication is vacuous).
;;; Nothing in the tree proves a cluster point from compactness: the only
;;; existing route is the ASSERTED axiom compact-iff-cluster-point
;;; (compactness.scm:85), and deriving from it would only relabel the debt.
;;; The cleanest honest route and the bricks it needs are in the report.
