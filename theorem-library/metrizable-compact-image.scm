;;; metrizable-compact-image.scm -- THE CONTINUOUS IMAGE OF A COMPACT SPACE IS
;;; COMPACT, IN THE CATEGORY OF METRIZABLE TOPOLOGICAL SPACES, PROVED THROUGH
;;; SEQUENCES (the user's request, 2026-10-01: "in that category ... it can be
;;; done using sequences.  I like using sequences to prove things whenever
;;; possible").
;;;
;;; The metric-space version by open
;;; covers (`compact-image', compact-image.scm) is a different proof of a
;;; different statement and is not used here.
;;;
;;; Continuity of a map between topological spaces is TOP-SPACE's generated
;;; morphism predicate IS-HOM-TOP-SPACE (top-space.scm), unfolded through its
;;; defining theorem `is-hom-top-space-def' (mac / mac-h by that name), as
;;; hom-kinds.scm does for the other generated homs.  Compactness of a
;;; topological space is IS-COMPACT-T, and the subspace topology SUBSPACE-TOP,
;;; both in structure-library/top-continuity.scm.
;;;
;;; WHAT IS PROVEN (all modulo 0):
;;;
;;;   metric-top-opens-iff   IS-METRIC-SPACE(md) =>
;;;                            (u in OPENS(METRIC-TOP md) iff IS-OPEN(md, u))
;;;   (T1) metric-top-compact
;;;                          IS-METRIC-SPACE(md) =>
;;;                            (IS-COMPACT-T(METRIC-TOP md) iff IS-COMPACT(md))
;;;   (T2) metric-top-hom    IS-METRIC-SPACE(s), IS-METRIC-SPACE(t) =>
;;;                            (IS-HOM-TOP-SPACE(METRIC-TOP s, METRIC-TOP t, f)
;;;                               iff IS-CONTINUOUS(s, t, f))
;;;   seq-compact-image      THE SEQUENCE ARGUMENT, on metrics:
;;;                          IS-CONTINUOUS(md, mt, f), SEQ-COMPACT(md) =>
;;;                            SEQ-COMPACT(SUBSPACE-MS(mt, IMAGE(f, PTS md)))
;;;   (T3a) metrizable-compact-t-iff-seq-compact
;;;                          METRIC-TOP(md) == s => (IS-COMPACT-T(s) iff SEQ-COMPACT(md))
;;;   (T3b) metrizable-hom-iff-sequential
;;;                          METRIC-TOP(md) == s, METRIC-TOP(mt) == t =>
;;;                            (IS-HOM-TOP-SPACE(s, t, f) iff f maps PTS(md) into
;;;                             PTS(mt) and sends every sequence converging to a
;;;                             to one converging to f(a))
;;;   metrizable-compact-image-ms   (the metric form of the theorem)
;;;                          s, t metrizable, IS-HOM-TOP-SPACE(s, t, f),
;;;                          IS-COMPACT-T(s), mt any metric with METRIC-TOP(mt) == t
;;;                            => IS-COMPACT(SUBSPACE-MS(mt, IMAGE(f, PTS s)))
;;;   subspace-top-pts, subspace-top-opens   the read-offs of SUBSPACE-TOP
;;;   (S1) subspace-top-is-top-space
;;;                          IS-TOP-SPACE(t), A subset PTS(t) =>
;;;                            IS-TOP-SPACE(SUBSPACE-TOP(t, A))
;;;   (S2) subspace-top-of-metric-top
;;;                          IS-METRIC-SPACE(mt), A subset PTS(mt) =>
;;;                            SUBSPACE-TOP(METRIC-TOP mt, A) == METRIC-TOP(SUBSPACE-MS(mt, A))
;;;   (T4) metrizable-compact-image   THE THEOREM, stated topologically:
;;;                          s, t metrizable, IS-HOM-TOP-SPACE(s, t, f), IS-COMPACT-T(s)
;;;                            => IS-COMPACT-T(SUBSPACE-TOP(t, IMAGE(f, PTS s)))
;;;
;;; THE PROOF OF THE METRIC FORM.  A metric md realising s is read off
;;; metrizability (`metrizable-has-metric-top').  Compactness and continuity
;;; cross s == METRIC-TOP(md), t == METRIC-TOP(mt) by `subst', then T1 and T2
;;; bring them down to md and mt, and `compact-iff-seq-compact' makes md
;;; SEQUENTIALLY compact.  Then `seq-compact-image' is the sequence proof:
;;;   * a sequence g in the image IMAGE(f, PTS md);
;;;   * preimages h(k) chosen by a CHOICE FUNCTION OVER THE FIBRES,
;;;       h = k |-> CHOICE{ x in PTS(md) : f(x) = g(k) },
;;;     packaged by `dk-abstract!' as a function symbol with its value equation
;;;     (no recursion is needed: each choice is independent of the others, so
;;;     DC-ITER is not the device here); each fibre is inhabited because g(k)
;;;     lies in the image (`image-membership-iff'), so `choice-axiom' applies;
;;;   * a subsequence h o phi converging to a point L of md (SEQ-COMPACT md);
;;;   * f o (h o phi) converges to f(L) (`continuous-at-implies-sequential');
;;;   * f o (h o phi) = g o phi, by function extensionality, pointwise from
;;;     f(h(k)) = g(k);
;;;   * f(L) lies in the image, so the convergence moves into the subspace
;;;     (`subspace-converges-to').
;;; Finally `compact-iff-seq-compact' on the subspace turns SEQ-COMPACT back into
;;; IS-COMPACT.  No open cover is touched by the sequence proof; open covers
;;; enter only through the definition of IS-COMPACT-T, in the transfer T1.
;;;
;;; THE TOPOLOGICAL FORM (T4) is the metric form plus two transfers: a metric mt
;;; realising t, T1 on the metric subspace SUBSPACE-MS(mt, IMAGE), and the
;;; bridge S2, which says the subspace topology of t = METRIC-TOP(mt) on the
;;; image is the topology of the subspace metric.  S2 is proved by
;;; extensionality on the two separations: a trace u ^ A of a metric open u is
;;; open in the subspace metric (`subspace-open-trace'), and every open of the
;;; subspace metric is such a trace (`subspace-open-is-trace').  S1 (the
;;; subspace topology is a topology) is not needed by T4 and is proved for
;;; itself: the four laws for traces, the union law through the family
;;; { u in OPENS(t) : u ^ A in fam }, whose union cut down to A is the union of
;;; fam -- no choice of a u per member is needed.
;;;
;;; LOAD WINDOW.  lo is forced by `metrizable-has-metric-top'
;;; (theorem-library/rake-bdd-metric, load.scm line ~3294), the latest of the
;;; citations; the others are earlier: metric-top-is-top-space
;;; (metric-top-proof), metric-top@preimage (functor-invariance),
;;; open-preimage-implies-continuous / continuous-implies-open-preimage
;;; (rake-open-sets), continuous-at-implies-sequential /
;;; sequential-implies-continuous-at (sequential-continuity),
;;; continuous-is-continuous-at (rake-norm-metrics), compact-iff-seq-compact
;;; (rake-lebesgue-number), subspace-* (metric-subspace-laws), compose-apply
;;; (compose-apply-proof), subseq-is-fun / subseq-apply, ms-pts-is-set.  It also
;;; needs structure-library/top-continuity before it.  hi = none: nothing cites
;;; it yet.  The slot is right after "theorem-library/rake-bdd-metric".
;;;
;;; Helper prefix: mci-.

;;; ---- file-local helpers (prefix mci-) ----------------------------------

;;; From the IFF in context and one side of it in context, land the other side.
;;; Done on a lane, the context cut down to the two formulas, by `prop'.
(define (mci-iff-move! iff from to)
  (if (eq? #t (dk-have! to (lambda () (dk-only! iff from) (prop))))
      #t                                  ; it was the focus goal, and is closed
      (or (dk-ctx-form to) (error "mci-iff-move!: did not land" (expression->string to)))))

;;; Run the branching THUNK and VISIT each leaf it opened that is still open
;;; (a leaf hash-consing grounded is skipped).  Never the global leaf list:
;;; that holds the siblings' leaves too.
(define (mci-each! thunk visit)
  (for-each (lambda (n) (if (not (sequent-node-grounded? n)) (visit n)))
            (dk-opened thunk)))

;;; Close the focus leaf with `ass' unless R says a helper already closed it.
(define (mci-ass-unless! r) (if (not (eq? r #t)) (ass)))

;;; The instance of metric-top-opens-iff at the metric space M and the set W.
(define (mci-opens-iff! m w)
  (let ((f (dk-cite! 'metric-top-opens-iff m w)))
    (if (not (dk-head-is? f 'IFF))
        (error "mci-opens-iff!: the citation landed" (expression->string f)))
    f))

;;; W is open in M  ==>  W in OPENS(METRIC-TOP M), and back.
(define (mci-to-opens! m w)
  (let ((iff (mci-opens-iff! m w)))
    (mci-iff-move! iff (list 'IS-OPEN m w) (list 'IN w (list 'OPENS (list 'METRIC-TOP m))))))
(define (mci-from-opens! m w)
  (let ((iff (mci-opens-iff! m w)))
    (mci-iff-move! iff (list 'IN w (list 'OPENS (list 'METRIC-TOP m))) (list 'IS-OPEN m w))))

;;; PTS(METRIC-TOP M) == PTS(M), landed (the functor carries the points across).
(define (mci-pts-eq! m)
  (let ((e (list '== (list 'PTS (list 'METRIC-TOP m)) (list 'PTS m))))
    (dk-have! e (lambda () (slot 'pts) (qrfl)))
    e))

;;; =====================================================================
;;; (0) THE OPENS OF THE METRIC TOPOLOGY ARE THE METRIC OPENS.
;;; =====================================================================
(sp (make-wff '(FORALL md (IMPLIES (IS-METRIC-SPACE md)
     (FORALL ou_ (IFF (IN ou_ (OPENS (METRIC-TOP md))) (IS-OPEN md ou_)))))))
(dk-peel!)
(fact 'ms-pts-is-set 'md)
(slot 'opens)
(dk-iff! (lambda (g) (dk-head-is? g 'IS-OPEN))
  (lambda ()
    (sep-me (dk-pick (lambda (h) (and (dk-head-is? h 'IN) (dk-contains? h 'SEP))) "the SEP membership"))
    (dk-split-all!)
    (ass))
  (lambda ()
    (dk-project! '(SUBSET ou_ (PTS md)) 'is-open '(IS-OPEN md ou_))
    (fact 'subclass-of-set-is-set 'ou_ '(PTS md))
    (mci-each! (lambda () (sep-mi)) (lambda (k)
                (dk-focus! k)
                (if (dk-head-is? (dk-goal) 'IS-OPEN)
                    (ass)
                    (begin
                      (mac 'power-set-membership)
                      (dk-conj-close!
                       (lambda ()
                         (if (dk-head-is? (dk-goal) 'FORALL)
                             (let ((z (dk-di-var!)))
                               (fact 'subset-mem-fwd 'ou_ '(PTS md) z)
                               (ass))
                             (ass)))))))
              )))
(qed 'metric-top-opens-iff)

;;; =====================================================================
;;; (T1) METRIC-TOP(md) IS COMPACT AS A TOPOLOGICAL SPACE IFF md IS COMPACT.
;;; =====================================================================
(sp (make-wff '(FORALL md (IMPLIES (IS-METRIC-SPACE md)
     (IFF (IS-COMPACT-T (METRIC-TOP md)) (IS-COMPACT md))))))
(dk-peel!)
(fact 'metric-top-is-top-space 'md)
(mci-pts-eq! 'md)
(dk-iff! (lambda (g) (dk-head-is? g 'IS-COMPACT))
  ;; ==> : compact-t(METRIC-TOP md) gives compact(md)
  (lambda ()
    (mac-h 'is-compact-t '(IS-COMPACT-T (METRIC-TOP md)))
    (dk-split-all!)
    (let ((cl (dk-pick (dk-head? 'FORALL) "the compactness clause")))
      (mac 'is-compact)
      (dk-conj-close!
       (lambda ()
         (if (dk-head-is? (dk-goal) 'IS-METRIC-SPACE)
             (ass)
             (let* ((cov (car (dk-peel!)))            ; IS-OPEN-COVER(md, C)
                    (c   (caddr cov))
                    (mem (dk-project! `(FORALL U (IMPLIES (IN U ,c) (IS-OPEN md U)))
                                      'is-open-cover cov))
                    (un  (dk-project! `(== (BIG-UNION U ,c U) (PTS md)) 'is-open-cover cov)))
               (dk-have! `(FORALL U (IMPLIES (IN U ,c) (IN U (OPENS (METRIC-TOP md)))))
                 (lambda ()
                   (let ((u (dk-di-var!)))
                     (dk-apply! mem u)
                     (mci-ass-unless! (mci-to-opens! 'md u)))))
               (dk-have! `(== (BIG-UNION U ,c U) (PTS (METRIC-TOP md)))
                 (lambda () (subst (list '= '(PTS (METRIC-TOP md)) '(PTS md))) (ass)))
               (let* ((ex (dk-apply! cl c))
                      (fv (dk-skolem! ex)))
                 (ew fv)
                 (dk-conj-close!
                  (lambda ()
                    (if (dk-head-is? (dk-goal) 'IS-OPEN-COVER)
                        (begin
                          (mac 'is-open-cover)
                          (dk-conj-close!
                           (lambda ()
                             (cond ((dk-head-is? (dk-goal) 'FORALL)
                                    (let ((u (dk-di-var!)))
                                      (fact 'subset-mem-fwd fv c u)
                                      (dk-apply! mem u)
                                      (ass)))
                                   ((dk-head-is? (dk-goal) '==)
                                    (subst (list '= '(PTS md) '(PTS (METRIC-TOP md))))
                                    (ass))
                                   (#t (ass))))))
                        (ass)))))))))))
  ;; <== : compact(md) gives compact-t(METRIC-TOP md)
  (lambda ()
    (mac 'is-compact-t)
    (dk-conj-close!
     (lambda ()
       (if (dk-head-is? (dk-goal) 'IS-TOP-SPACE)
           (ass)
           (let* ((landed (dk-peel!))
                  (un  (find-first (dk-head? '==) landed))
                  (mem (find-first (dk-head? 'FORALL) landed))
                  (c   (caddr (cadr un))))
             (dk-have! `(IS-OPEN-COVER md ,c)
               (lambda ()
                 (mac 'is-open-cover)
                 (dk-conj-close!
                  (lambda ()
                    (cond ((dk-head-is? (dk-goal) 'FORALL)
                           (let ((u (dk-di-var!)))
                             (dk-apply! mem u)
                             (mci-ass-unless! (mci-from-opens! 'md u))))
                          ((dk-head-is? (dk-goal) '==)
                           (subst (list '= '(PTS md) '(PTS (METRIC-TOP md))))
                           (ass))
                          (#t (ass)))))))
             (mac-h 'is-compact '(IS-COMPACT md))
             (dk-split-all!)
             (let* ((cl (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL)
                                                  (dk-contains? h 'IS-OPEN-COVER)))
                                 "the compactness clause"))
                    (ex (dk-apply! cl c))
                    (fv (dk-skolem! ex)))
               (dk-project! `(== (BIG-UNION U ,fv U) (PTS md)) 'is-open-cover
                            `(IS-OPEN-COVER md ,fv))
               (ew fv)
               (dk-conj-close!
                (lambda ()
                  (if (dk-head-is? (dk-goal) '==)
                      (begin (subst (list '= '(PTS (METRIC-TOP md)) '(PTS md))) (ass))
                      (ass)))))))))))
(qed 'metric-top-compact)

;;; =====================================================================
;;; (T2) f IS CONTINUOUS BETWEEN THE METRIC TOPOLOGIES IFF IT IS CONTINUOUS.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f (IMPLIES (IS-METRIC-SPACE s) (IMPLIES (IS-METRIC-SPACE t)
     (IFF (IS-HOM-TOP-SPACE (METRIC-TOP s) (METRIC-TOP t) f) (IS-CONTINUOUS s t f)))))))))
(dk-peel!)
(fact 'metric-top-is-top-space 's)
(fact 'metric-top-is-top-space 't)
(mci-pts-eq! 's)
(mci-pts-eq! 't)
(dk-iff! (lambda (g) (dk-head-is? g 'IS-CONTINUOUS))
  ;; ==>
  (lambda ()
    (mac-h 'is-hom-top-space-def '(IS-HOM-TOP-SPACE (METRIC-TOP s) (METRIC-TOP t) f))
    (dk-split-all!)
    (let ((pre (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'PREIMAGE)))
                        "the preimage clause")))
      (dk-have! '(AND (IS-METRIC-SPACE s) (AND (IS-METRIC-SPACE t) (IN f (FUN (PTS s) (PTS t)))))
        (lambda ()
          (dk-conj-close!
           (lambda ()
             (if (dk-head-is? (dk-goal) 'IN)
                 (begin (subst '(= (PTS s) (PTS (METRIC-TOP s))))
                        (subst '(= (PTS t) (PTS (METRIC-TOP t))))
                        (ass))
                 (ass))))))
      (let ((ch (dk-fact! 'open-preimage-implies-continuous 's 't 'f)))
        (if (dk-head-is? ch 'IMPLIES)
            (detach-with! ch
              (lambda ()
                (let* ((op (car (dk-peel!)))           ; IS-OPEN(t, v)
                       (v  (caddr op)))
                  (mci-to-opens! 't v)
                  (dk-apply! pre v)
                  (mac-h 'metric-top@preimage
                         (list 'IN (list 'PREIMAGE '(METRIC-TOP s) 'f v) '(OPENS (METRIC-TOP s))))
                  (mci-ass-unless! (mci-from-opens! 's (list 'PREIMAGE 's 'f v)))))))
        (ass))))
  ;; <==
  (lambda ()
    (mac 'is-hom-top-space-def)
    (dk-conj-close!
     (lambda ()
       (cond ((dk-head-is? (dk-goal) 'IS-TOP-SPACE) (ass))
             ((dk-head-is? (dk-goal) 'IN)
              (dk-project! '(IN f (FUN (PTS s) (PTS t))) 'is-continuous '(IS-CONTINUOUS s t f))
              (subst '(= (PTS (METRIC-TOP s)) (PTS s)))
              (subst '(= (PTS (METRIC-TOP t)) (PTS t)))
              (ass))
             (#t
              (let* ((mem (car (dk-peel!)))            ; u in OPENS(METRIC-TOP t)
                     (u   (cadr mem)))
                (mci-from-opens! 't u)
                (fact 'continuous-implies-open-preimage 's 't 'f u)
                (mac 'metric-top@preimage)
                (mci-ass-unless! (mci-to-opens! 's (list 'PREIMAGE 's 'f u))))))))))
(qed 'metric-top-hom)
;;; =====================================================================
;;; (L1) THE SEQUENCE PROOF.  A continuous image of a sequentially compact
;;; metric space is sequentially compact (as a subspace of the target).
;;; =====================================================================
(define mci-img '(IMAGE cmf_ (PTS md)))
(define mci-sub (list 'SUBSPACE-MS 'mt mci-img))

;;; The fibre of cmf_ over g(k), as a SEP over PTS(md).  The binder `chq_' is
;;; used by no predicate body and by nothing the kernel mints.
(define (mci-fibre g k) (list 'SEP 'chq_ '(PTS md) (list '= '(cmf_ chq_) (list g k))))

;;; With (IN k NN) and (IN g (FUN NN IMG)) in context: land
;;;   (IN (CHOICE fibre) (PTS md))  and  (= (cmf_ (CHOICE fibre)) (g k)).
;;; The fibre is inhabited because g(k) lies in the image.
(define (mci-choice-parts! g k)
  (let ((gk (list g k)))
    (fact 'fun-apply-type-c g 'NN mci-img k)
    (let* ((ex (dk-image-hyp! (list 'IN gk mci-img)))
           (x0 (dk-skolem! ex)))
      (choose! (mci-fibre g k) x0
        (lambda ()
          (mci-each! (lambda () (sep-mi)) (lambda (n) (dk-focus! n) (ass))
                    ))))))

(sp (make-wff '(FORALL md (FORALL mt (FORALL cmf_
     (IMPLIES (IS-METRIC-SPACE md) (IMPLIES (IS-METRIC-SPACE mt)
     (IMPLIES (IS-CONTINUOUS md mt cmf_) (IMPLIES (SEQ-COMPACT md)
       (SEQ-COMPACT (SUBSPACE-MS mt (IMAGE cmf_ (PTS md)))))))))))))
(dk-peel!)
(dk-project! '(IN cmf_ (FUN (PTS md) (PTS mt))) 'is-continuous '(IS-CONTINUOUS md mt cmf_))
(fact 'ms-pts-is-set 'md)
(fact 'ms-pts-is-set 'mt)
(fact 'nn-is-set)
(dk-have! (list 'SUBSET mci-img '(PTS mt))
  (lambda ()
    (mac 'subset-def)
    (let ((w (dk-di-var!)))
      (fact 'image-subset-codomain '(PTS md) '(PTS mt) 'cmf_ w)
      (ass))))
(fact 'subspace-is-metric-space 'mt mci-img)
(mac 'seq-compact)
(mac 'subspace-pts)
(dk-conj-close!
 (lambda ()
   (if (dk-head-is? (dk-goal) 'IS-METRIC-SPACE)
       (ass)
       (let* ((gty (car (dk-peel!)))                  ; g in FUN(NN, IMG)
              (g   (cadr gty)))
         ;; --- the preimages, one per index, by a choice function over the fibres
         (let* ((hv (dk-abstract! 'NN '(PTS md)
                                  (lambda (k) (list 'CHOICE (mci-fibre g k)))
                                  (lambda (k) (mci-choice-parts! g k) (ass))))
                (h  (car hv))
                (ve (cdr hv))
                (ptw `(FORALL kq_ (IMPLIES (IN kq_ NN) (= (cmf_ (,h kq_)) (,g kq_))))))
           (dk-have! ptw
             (lambda ()
               (let ((k (dk-di-var!)))
                 (subst (dk-apply! ve k))
                 (mci-choice-parts! g k)
                 (ass))))
           ;; --- a convergent subsequence of the preimages
           (mac-h 'seq-compact '(SEQ-COMPACT md))
           (dk-split-all!)
           (let* ((cl  (dk-pick (lambda (f) (and (dk-head-is? f 'FORALL)
                                                 (dk-contains? f 'STRICTLY-MONO-NN)))
                                "the sequential compactness clause"))
                  (ex1 (dk-apply! cl h))
                  (phi (dk-skolem! ex1))
                  (ex2 (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME)
                                                 (dk-contains? f 'CONVERGES-TO)))
                                "the limit existential"))
                  (lim (dk-skolem! ex2))
                  (sq  (list 'SUBSEQ h phi))
                  (gsq (list 'SUBSEQ g phi))
                  (flim (list 'cmf_ lim)))
             (dk-have! (list 'AND (list 'IN h '(FUN NN (PTS md))) (list 'STRICTLY-MONO-NN phi)))
             (fact 'subseq-is-fun 'md h phi)
             (dk-have! (list 'IN sq '(SQN (PTS md)))
               (lambda () (mac 'sqn-membership) (ass)))
             ;; --- its image converges, by sequential continuity at the limit
             (fact 'continuous-is-continuous-at 'md 'mt 'cmf_ lim)
             (let* ((seqc (dk-fact! 'continuous-at-implies-sequential 'md 'mt 'cmf_ lim))
                    (cnv  (dk-apply! seqc sq)))
               ;; --- g's subsequence, as a sequence in the image and in PTS(mt)
               (dk-have! (list 'AND (list 'IN g (list 'FUN 'NN (list 'PTS mci-sub)))
                               (list 'STRICTLY-MONO-NN phi))
                 (lambda () (mac 'subspace-pts) (dk-conj-close! (lambda () (ass)))))
               (fact 'subseq-is-fun mci-sub g phi)
               (mac-h 'subspace-pts (list 'IN gsq (list 'FUN 'NN (list 'PTS mci-sub))))
               (fact 'fun-codomain-superset gsq 'NN mci-img '(PTS mt))
               (dk-project! (list 'IN phi '(FUN NN NN)) 'strictly-mono-nn (list 'STRICTLY-MONO-NN phi))
               (dk-have! (list 'AND (list 'IN sq '(FUN NN (PTS md))) '(IN cmf_ (FUN (PTS md) (PTS mt)))))
               (fact 'compose-type 'NN '(PTS md) '(PTS mt) 'cmf_ sq)
               ;; --- COMPOSE(f, h o phi) = g o phi, pointwise
               (dk-fun-ext! (list 'COMPOSE 'cmf_ sq) gsq 'NN '(PTS mt) #f #f
                 (lambda (v)
                   (subst (dk-fact! 'compose-apply 'NN '(PTS md) '(PTS mt) 'cmf_ sq v))
                   (subst (dk-fact! 'subseq-apply h phi v))
                   (subst (dk-fact! 'subseq-apply g phi v))
                   (fact 'fun-apply-type-c phi 'NN 'NN v)
                   (dk-apply! (dk-ctx-form ptw) (list phi v))
                   (ass)))
               (dk-have! (list 'CONVERGES-TO 'mt gsq flim)
                 (lambda () (subst (list '= gsq (list 'COMPOSE 'cmf_ sq))) (ass)))
               ;; --- the limit lies in the image
               (fact 'fun-apply-type-c 'cmf_ '(PTS md) '(PTS mt) lim)
               (dk-have! (list 'IN flim mci-img)
                 (lambda ()
                   (dk-image-goal!)
                   (ew lim)
                   (dk-conj-close! (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (ass))))))
               (let ((sciff (dk-cite! 'subspace-converges-to 'mt mci-img gsq flim)))
               (ew phi)
               (dk-conj-close!
                (lambda ()
                  (if (dk-head-is? (dk-goal) 'FORSOME)
                      (begin (ew flim)
                             (dk-conj-close!
                              (lambda ()
                                (if (dk-head-is? (dk-goal) 'CONVERGES-TO)
                                    (mci-ass-unless!
                                     (mci-iff-move! sciff (list 'CONVERGES-TO 'mt gsq flim)
                                                    (list 'CONVERGES-TO mci-sub gsq flim)))
                                    (ass)))))
                      (ass))))))))))))
(qed 'seq-compact-image)
;;; =====================================================================
;;; (T3a) A METRIZABLE SPACE IS COMPACT IFF A METRIC REALISING IT IS
;;; SEQUENTIALLY COMPACT.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL md (IMPLIES (IS-METRIC-SPACE md) (IMPLIES (== (METRIC-TOP md) s)
     (IFF (IS-COMPACT-T s) (SEQ-COMPACT md))))))))
(dk-peel!)
(subst '(= s (METRIC-TOP md)))
(let ((i1 (dk-cite! 'metric-top-compact 'md))
      (i2 (dk-cite! 'compact-iff-seq-compact 'md)))
  (dk-only! i1 i2)
  (prop))
(qed 'metrizable-compact-t-iff-seq-compact)

;;; =====================================================================
;;; (T3b) A MAP BETWEEN METRIZABLE SPACES IS CONTINUOUS IFF IT IS
;;; SEQUENTIALLY CONTINUOUS FOR METRICS REALISING THEM.
;;; =====================================================================
(define mci-seqc
  '(FORALL a (IMPLIES (IN a (PTS md))
     (FORALL sq (IMPLIES (IN sq (SQN (PTS md)))
       (IMPLIES (CONVERGES-TO md sq a)
                (CONVERGES-TO mt (COMPOSE f sq) (f a))))))))
(sp (make-wff '(FORALL s (FORALL t (FORALL md (FORALL mt (FORALL f
     (IMPLIES (IS-METRIC-SPACE md) (IMPLIES (IS-METRIC-SPACE mt)
     (IMPLIES (== (METRIC-TOP md) s) (IMPLIES (== (METRIC-TOP mt) t)
       (IFF (IS-HOM-TOP-SPACE s t f)
            (AND (IN f (FUN (PTS md) (PTS mt)))
                 (FORALL a (IMPLIES (IN a (PTS md))
                   (FORALL sq (IMPLIES (IN sq (SQN (PTS md)))
                     (IMPLIES (CONVERGES-TO md sq a)
                              (CONVERGES-TO mt (COMPOSE f sq) (f a))))))))))))))))))))
(dk-peel!)
(subst '(= s (METRIC-TOP md)))
(subst '(= t (METRIC-TOP mt)))
(define mci-rhs (list 'AND '(IN f (FUN (PTS md) (PTS mt))) mci-seqc))
(dk-have! (list 'IFF '(IS-CONTINUOUS md mt f) mci-rhs)
  (lambda ()
    (dk-iff! (lambda (g) (dk-head-is? g 'AND))
      ;; ==> : continuity gives the sequential criterion at every point
      (lambda ()
        (dk-project! '(IN f (FUN (PTS md) (PTS mt))) 'is-continuous '(IS-CONTINUOUS md mt f))
        (dk-conj-close!
         (lambda ()
           (if (dk-head-is? (dk-goal) 'IN)
               (ass)
               (let* ((landed (dk-peel!))
                      (a  (cadr (find-first (lambda (h) (and (dk-head-is? h 'IN)
                                                             (equal? (caddr h) '(PTS md))))
                                            landed)))
                      (sq (cadr (find-first (lambda (h) (and (dk-head-is? h 'IN)
                                                             (dk-contains? h 'SQN)))
                                            landed))))
                 (fact 'continuous-is-continuous-at 'md 'mt 'f a)
                 (dk-apply! (dk-fact! 'continuous-at-implies-sequential 'md 'mt 'f a) sq)
                 (ass))))))
      ;; <== : the sequential criterion at every point gives continuity
      (lambda ()
        (dk-split! (dk-pick (dk-head? 'AND) "the sequential criterion"))
        (mac 'is-continuous)
        (dk-conj-close!
         (lambda ()
           (if (dk-head-is? (dk-goal) 'FORALL)
               (let* ((a (dk-di-var!))
                      (cl (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL)
                                                    (dk-contains? h 'COMPOSE)))
                                   "the sequential clause")))
                 (dk-apply! cl a)
                 (fact 'sequential-implies-continuous-at 'md 'mt 'f a)
                 (ass))
               (ass)))))))
  )
(let ((i1 (dk-cite! 'metric-top-hom 'md 'mt 'f))
      (i2 (dk-ctx-form (list 'IFF '(IS-CONTINUOUS md mt f) mci-rhs))))
  (dk-only! i1 i2)
  (prop))
(qed 'metrizable-hom-iff-sequential)

;;; =====================================================================
;;; (T4) THE CONTINUOUS IMAGE OF A COMPACT METRIZABLE SPACE IS COMPACT.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-METRIZABLE-TOP-SPACE s) (IMPLIES (IS-METRIZABLE-TOP-SPACE t)
     (IMPLIES (IS-HOM-TOP-SPACE s t f) (IMPLIES (IS-COMPACT-T s)
       (FORALL mt (IMPLIES (IS-METRIC-SPACE mt) (IMPLIES (== (METRIC-TOP mt) t)
         (IS-COMPACT (SUBSPACE-MS mt (IMAGE f (PTS s))))))))))))))))
(dk-peel!)
;; a metric realising s
(define mci-md (dk-skolem! (dk-fact! 'metrizable-has-metric-top 's)))
(define mci-mtd (list 'METRIC-TOP mci-md))
(define mci-img4 (list 'IMAGE 'f (list 'PTS mci-md)))
(define mci-sub4 (list 'SUBSPACE-MS 'mt mci-img4))
;; carry compactness and continuity across s == METRIC-TOP(md), t == METRIC-TOP(mt)
(dk-have! (list 'IS-COMPACT-T mci-mtd)
  (lambda () (subst (list '= mci-mtd 's)) (ass)))
(dk-have! (list 'IS-HOM-TOP-SPACE mci-mtd '(METRIC-TOP mt) 'f)
  (lambda () (subst (list '= mci-mtd 's)) (subst '(= (METRIC-TOP mt) t)) (ass)))
;; ... down to the metric: compact, hence SEQUENTIALLY compact; continuous
(mci-iff-move! (dk-cite! 'metric-top-compact mci-md)
               (list 'IS-COMPACT-T mci-mtd) (list 'IS-COMPACT mci-md))
(mci-iff-move! (dk-cite! 'compact-iff-seq-compact mci-md)
               (list 'IS-COMPACT mci-md) (list 'SEQ-COMPACT mci-md))
(mci-iff-move! (dk-cite! 'metric-top-hom mci-md 'mt 'f)
               (list 'IS-HOM-TOP-SPACE mci-mtd '(METRIC-TOP mt) 'f)
               (list 'IS-CONTINUOUS mci-md 'mt 'f))
;; THE SEQUENCE ARGUMENT: the image is sequentially compact
(fact 'seq-compact-image mci-md 'mt 'f)
;; ... and a sequentially compact metric space is compact
(dk-project! (list 'IN 'f (list 'FUN (list 'PTS mci-md) '(PTS mt)))
             'is-continuous (list 'IS-CONTINUOUS mci-md 'mt 'f))
(dk-have! (list 'SUBSET mci-img4 '(PTS mt))
  (lambda ()
    (mac 'subset-def)
    (let ((w (dk-di-var!)))
      (fact 'image-subset-codomain (list 'PTS mci-md) '(PTS mt) 'f w)
      (ass))))
(fact 'subspace-is-metric-space 'mt mci-img4)
(mci-pts-eq! mci-md)
(subst (list '= 's mci-mtd))
(subst (list '= (list 'PTS mci-mtd) (list 'PTS mci-md)))
(mci-ass-unless!
 (mci-iff-move! (dk-cite! 'compact-iff-seq-compact mci-sub4)
                (list 'SEQ-COMPACT mci-sub4) (list 'IS-COMPACT mci-sub4)))
(qed 'metrizable-compact-image-ms)
;;; =====================================================================
;;; THE SUBSPACE TOPOLOGY: read-offs, the topology laws, and the bridge to
;;; the subspace metric.
;;; =====================================================================
(define mci-stopens
  '(SEP stw_ (POWER A) (FORSOME stu_ (AND (IN stu_ (OPENS t)) (= stw_ (INTERSECTION stu_ A))))))

;;; (IN (INTERSECTION a b) SET), from (IN b SET) in context.
(define (mci-inter-set! a b)
  (let ((want (list 'IN (list 'INTERSECTION a b) 'SET)))
    (if (not (dk-asm? want))
        (dk-have! want
          (lambda ()
            (dk-have! (list 'OR (list 'IN a 'SET) (list 'IN b 'SET)) (lambda () (oi-r) (ass)))
            (fact 'intersection-set-closure a b)
            (ass))))))

;;; Unfold every membership in an INTERSECTION in the goal.
(define (mci-inter-mem? e)
  (and (pair? e)
       (or (and (eq? (car e) 'IN) (= (length e) 3) (dk-head-is? (caddr e) 'INTERSECTION))
           (any-pred mci-inter-mem? e))))
(define (mci-unfold-inter!)
  (let loop ((n 0))
    (if (and (< n 6) (mci-inter-mem? (dk-goal)))
        (let ((g0 (dk-goal)))
          (mac 'intersection-membership)
          (if (not (equal? (dk-goal) g0)) (loop (+ n 1)))))))

;;; (= X Y) for two sets whose memberships are PROPOSITIONALLY equivalent once
;;; intersections are unfolded.  EXTRA is a procedure of the point z run before
;;; `prop'; it returns the context formulas `prop' needs besides the IFF goal.
;;; The sethood of X and Y must be in context (the LUTINS rule, for
;;; class-extensionality's instance).
(define (mci-ext! x y extra)
  (dk-have! (list 'FORALL 'zqz_ (list 'IFF (list 'IN 'zqz_ x) (list 'IN 'zqz_ y)))
    (lambda ()
      (let* ((z (dk-di-var! (lambda (g) (cadr (cadr g)))))
             (keepers (extra z)))
        (mci-unfold-inter!)
        (apply dk-only! keepers)
        (prop))))
  (fact 'class-extensionality x y)
  (ass))

;;; With (IS-OPEN m u) in context: (IN u (POWER (PTS m))).  Needs (IN (PTS m) SET).
(define (mci-power-of-open! m u)
  (let ((want (list 'IN u (list 'POWER (list 'PTS m)))))
    (dk-have! want
      (lambda ()
        (dk-project! (list 'SUBSET u (list 'PTS m)) 'is-open (list 'IS-OPEN m u))
        (fact 'subclass-of-set-is-set u (list 'PTS m))
        (mac 'power-set-membership)
        (dk-conj-close!
         (lambda ()
           (if (dk-head-is? (dk-goal) 'FORALL)
               (let ((z (dk-di-var!)))
                 (fact 'subset-mem-fwd u (list 'PTS m) z)
                 (ass))
               (ass))))))
    want))

;;; --- the read-offs ---------------------------------------------------
(sp (make-wff '(FORALL t (FORALL A (== (PTS (SUBSPACE-TOP t A)) A)))))
(di)
(mac 'SUBSPACE-TOP)
(slot 'PTS)
(nth-r)
(qrfl)
(qed 'subspace-top-pts)

(sp (make-wff (list 'FORALL 't (list 'FORALL 'A (list '== '(OPENS (SUBSPACE-TOP t A)) mci-stopens)))))
(di)
(mac 'SUBSPACE-TOP)
(slot 'OPENS)                 ; also turns the OPENS(t) inside the SEP into NTH(2, t) ...
(nth-r)
(slot 'OPENS)                 ; ... so the right-hand side's OPENS(t) is read the same way
(qrfl)
(qed 'subspace-top-opens)

;;; --- (S1) the subspace topology is a topology ------------------------
(sp (make-wff '(FORALL t (FORALL A (IMPLIES (IS-TOP-SPACE t) (IMPLIES (SUBSET A (PTS t))
     (IS-TOP-SPACE (SUBSPACE-TOP t A))))))))
(dk-peel!)
(mac-h 'is-top-space '(IS-TOP-SPACE t))
(dk-split-all!)
(fact 'subclass-of-set-is-set 'A '(PTS t))
(fact 'power-set 'A)
(dk-have! (list 'SUBSET mci-stopens '(POWER A))
  (lambda ()
    (mac 'subset-def)
    (let ((w (dk-di-var!)))
      (sep-me (list 'IN w mci-stopens))
      (dk-split-all!)
      (ass))))
(define mci-s1-inter (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'INTERSECTION)))
                              "the intersection law"))
(define mci-s1-union (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'BIG-UNION)))
                              "the union law"))
;; a member of the subspace opens: skolemise its trace.  Returns (u1 . (= w (INTERSECTION u1 A))).
(define (mci-trace! w)
  (sep-me (list 'IN w mci-stopens))
  (dk-split-all!)
  (let* ((ex (dk-pick (lambda (h) (and (dk-head-is? h 'FORSOME) (dk-contains? h w)
                                       (dk-contains? h 'INTERSECTION)))
                      "the trace existential"))
         (u1 (dk-skolem! ex)))
    (fact 'membership-implies-sethood u1 '(OPENS t))
    u1))
(mac 'is-top-space)
(mac 'subspace-top-pts)
(mac 'subspace-top-opens)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
      ;; length
      ((dk-head-is? g '=)
       (mac 'SUBSPACE-TOP) (len-r) (rfl))
      ;; A in SET
      ((equal? g '(IN A SET)) (ass))
      ;; the opens lie in POWER(POWER A)
      ((and (dk-head-is? g 'IN) (equal? (caddr g) '(POWER (POWER A))))
       (mac 'power-set-membership)
       (dk-conj-close!
        (lambda ()
          (if (dk-head-is? (dk-goal) 'FORALL)
              (let ((w (dk-di-var!)))
                (fact 'subset-mem-fwd mci-stopens '(POWER A) w)
                (ass))
              (begin (sep-set) (ass))))))
      ;; EMPTY-SET is open
      ((equal? g (list 'IN 'EMPTY-SET mci-stopens))
       (fact 'empty-set-is-set)
       (mci-each! (lambda () (sep-mi))
        (lambda (k)
          (dk-focus! k)
          (if (dk-head-is? (dk-goal) 'IN)
              (begin (fact 'power-empty-in 'A) (ass))
              (begin
                (ew 'EMPTY-SET)
                (dk-conj-close!
                 (lambda ()
                   (if (dk-head-is? (dk-goal) 'IN)
                       (ass)
                       (begin
                         (mci-inter-set! 'EMPTY-SET 'A)
                         (mci-ext! 'EMPTY-SET '(INTERSECTION EMPTY-SET A)
                                   (lambda (z)
                                     (list (dk-fact! 'empty-set-has-no-members z)))))))))))
        ))
      ;; A is open
      ((equal? g (list 'IN 'A mci-stopens))
       (mci-each! (lambda () (sep-mi))
        (lambda (k)
          (dk-focus! k)
          (if (dk-head-is? (dk-goal) 'IN)
              (begin (fact 'power-whole-in 'A) (ass))
              (begin
                (ew '(PTS t))
                (dk-conj-close!
                 (lambda ()
                   (if (dk-head-is? (dk-goal) 'IN)
                       (ass)
                       (begin
                         (mci-inter-set! '(PTS t) 'A)
                         (mci-ext! 'A '(INTERSECTION (PTS t) A)
                                   (lambda (z)
                                     (list (dk-fact! 'subset-mem-fwd 'A '(PTS t) z)))))))))))
        ))
      ;; binary intersections
      ((and (dk-head-is? g 'FORALL) (not (dk-contains? g 'BIG-UNION)))
       (let* ((landed (dk-peel!))
              (ws (map cadr (filter (lambda (h) (and (dk-head-is? h 'IN)
                                                     (equal? (caddr h) mci-stopens)))
                                    landed)))
              (w1 (car ws)) (w2 (cadr ws))
              (u1 (mci-trace! w1))
              (u2 (mci-trace! w2)))
         (fact 'subset-mem-fwd mci-stopens '(POWER A) w1)
         (fact 'subset-mem-fwd mci-stopens '(POWER A) w2)
         (fact 'power-inter-closed 'A w1 w2)
         (fact 'power-mem-sethood 'A w1)
         (fact 'power-mem-sethood 'A w2)
         (dk-apply! mci-s1-inter u1 u2)
         (fact 'membership-implies-sethood (list 'INTERSECTION u1 u2) '(OPENS t))
         (mci-each! (lambda () (sep-mi))
          (lambda (k)
            (dk-focus! k)
            (if (dk-head-is? (dk-goal) 'IN)
                (ass)
                (begin
                  (ew (list 'INTERSECTION u1 u2))
                  (dk-conj-close!
                   (lambda ()
                     (if (dk-head-is? (dk-goal) 'IN)
                         (ass)
                         (begin
                           (subst (list '= w1 (list 'INTERSECTION u1 'A)))
                           (subst (list '= w2 (list 'INTERSECTION u2 'A)))
                           (mci-inter-set! u1 'A)
                           (mci-inter-set! u2 'A)
                           (mci-inter-set! (list 'INTERSECTION u1 'A) (list 'INTERSECTION u2 'A))
                           (mci-inter-set! (list 'INTERSECTION u1 u2) 'A)
                           (mci-ext! (list 'INTERSECTION (list 'INTERSECTION u1 'A)
                                           (list 'INTERSECTION u2 'A))
                                     (list 'INTERSECTION (list 'INTERSECTION u1 u2) 'A)
                                     (lambda (z) '())))))))))
          )))
      ;; arbitrary unions
      (#t
       (let* ((landed (dk-peel!))
              (sub  (find-first (dk-head? 'SUBSET) landed))
              (fam  (cadr sub))
              (bu   (list 'BIG-UNION 'u fam 'u))
              (up   (list 'SEP 'stv_ '(OPENS t) (list 'IN (list 'INTERSECTION 'stv_ 'A) fam)))
              (bup  (list 'BIG-UNION 'u up 'u)))
         (dk-have! (list 'SUBSET fam '(POWER A))
           (lambda ()
             (mac 'subset-def)
             (let ((w (dk-di-var!)))
               (fact 'subset-mem-fwd fam mci-stopens w)
               (fact 'subset-mem-fwd mci-stopens '(POWER A) w)
               (ass))))
         (fact 'power-big-union-closed 'A fam)
         (fact 'power-mem-sethood 'A bu)
         (dk-have! (list 'SUBSET up '(OPENS t))
           (lambda ()
             (mac 'subset-def)
             (let ((w (dk-di-var!)))
               (sep-me (list 'IN w up))
               (dk-split-all!)
               (ass))))
         (dk-apply! mci-s1-union up)
         (fact 'membership-implies-sethood bup '(OPENS t))
         (mci-inter-set! bup 'A)
         (mci-each! (lambda () (sep-mi))
          (lambda (k)
            (dk-focus! k)
            (if (dk-head-is? (dk-goal) 'IN)
                (ass)
                (begin
                  (ew bup)
                  (dk-conj-close!
                   (lambda ()
                     (if (dk-head-is? (dk-goal) 'IN)
                         (ass)
                         (begin
                           (dk-have! (list 'FORALL 'zqz_ (list 'IFF (list 'IN 'zqz_ bu)
                                                               (list 'IN 'zqz_ (list 'INTERSECTION bup 'A))))
                             (lambda ()
                               (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
                                 (dk-iff! (lambda (g) (dk-contains? g 'INTERSECTION))
                                   ;; z in the union of fam  ==>  z in (union of up) ^ A
                                   (lambda ()
                                     (let* ((w  (cadr (dk-landed-find
                                                       (lambda () (bu-me (list 'IN z bu)))
                                                       (lambda (f) (and (dk-head-is? f 'IN)
                                                                        (equal? (caddr f) fam))))))
                                            (_  (fact 'subset-mem-fwd fam mci-stopens w))
                                            (u1 (mci-trace! w))
                                            (zi (list 'IN z (list 'INTERSECTION u1 'A))))
                                       (dk-have! zi (lambda () (subst (list '= (list 'INTERSECTION u1 'A) w)) (ass)))
                                       (mac-h 'intersection-membership zi)
                                       (dk-split-all!)
                                       (dk-have! (list 'IN u1 up)
                                         (lambda ()
                                           (mci-each! (lambda () (sep-mi))
                                            (lambda (n)
                                              (dk-focus! n)
                                              (if (equal? (dk-goal) (list 'IN u1 '(OPENS t)))
                                                  (ass)
                                                  (begin (subst (list '= (list 'INTERSECTION u1 'A) w)) (ass))))
                                            )))
                                       (mac 'intersection-membership)
                                       (dk-conj-close!
                                        (lambda ()
                                          (if (dk-contains? (dk-goal) 'BIG-UNION)
                                              (for-each (lambda (n) (dk-focus! n) (ass))
                                                        (dk-opened (lambda () (bu-mi u1))))
                                              (ass))))))
                                   ;; z in (union of up) ^ A  ==>  z in the union of fam
                                   (lambda ()
                                     (mac-h 'intersection-membership
                                            (list 'IN z (list 'INTERSECTION bup 'A)))
                                     (dk-split-all!)
                                     (let ((u1 (cadr (dk-landed-find
                                                      (lambda () (bu-me (list 'IN z bup)))
                                                      (lambda (f) (and (dk-head-is? f 'IN)
                                                                       (equal? (caddr f) up)))))))
                                       (sep-me (list 'IN u1 up))
                                       (dk-split-all!)
                                       (for-each
                                        (lambda (n)
                                          (dk-focus! n)
                                          (if (mci-inter-mem? (dk-goal))
                                              (begin (mac 'intersection-membership)
                                                     (dk-conj-close! (lambda () (ass))))
                                              (ass)))
                                        (dk-opened (lambda () (bu-mi (list 'INTERSECTION u1 'A)))))))))))
                           (fact 'class-extensionality bu (list 'INTERSECTION bup 'A))
                           (ass))))))))
          )))))))
(qed 'subspace-top-is-top-space)

;;; --- (S2) the subspace topology of a metric topology is the topology of
;;; the subspace metric --------------------------------------------------
(define mci-s2-sub '(SUBSPACE-MS mt A))
(sp (make-wff '(FORALL mt (FORALL A (IMPLIES (IS-METRIC-SPACE mt) (IMPLIES (SUBSET A (PTS mt))
     (== (SUBSPACE-TOP (METRIC-TOP mt) A) (METRIC-TOP (SUBSPACE-MS mt A)))))))))
(dk-peel!)
(fact 'ms-pts-is-set 'mt)
(fact 'subclass-of-set-is-set 'A '(PTS mt))
(fact 'subspace-is-metric-space 'mt 'A)
(mac 'SUBSPACE-TOP)
(slot 'OPENS)
(mac 'METRIC-TOP)
(mac 'subspace-pts)
(define mci-s2-g (dk-goal))
(define mci-s2-l (caddr (cadr mci-s2-g)))     ; the SEP of traces
(define mci-s2-r (caddr (caddr mci-s2-g)))    ; the SEP of subspace-metric opens
(define mci-s2-mtsep '(SEP u (POWER (PTS mt)) (IS-OPEN mt u)))
(dk-have! (list 'FORALL 'zqz_ (list 'IFF (list 'IN 'zqz_ mci-s2-l) (list 'IN 'zqz_ mci-s2-r)))
  (lambda ()
    (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (dk-iff! (lambda (g) (dk-contains? (caddr g) 'SUBSPACE-MS))
        ;; a trace of a metric open is open in the subspace metric
        (lambda ()
          (sep-me (list 'IN z mci-s2-l))
          (dk-split-all!)
          (let* ((ex (dk-pick (dk-head? 'FORSOME) "the trace existential"))
                 (u1 (dk-skolem! ex)))
            (sep-me (list 'IN u1 mci-s2-mtsep))
            (dk-split-all!)
            (fact 'subspace-open-trace 'mt 'A u1)
            (mci-each! (lambda () (sep-mi))
             (lambda (n)
               (dk-focus! n)
               (if (dk-head-is? (dk-goal) 'IS-OPEN)
                   (begin (subst (list '= z (list 'INTERSECTION u1 'A))) (ass))
                   (ass)))
             )))
        ;; an open of the subspace metric is a trace of a metric open
        (lambda ()
          (sep-me (list 'IN z mci-s2-r))
          (dk-split-all!)
          (let* ((ex (dk-fact! 'subspace-open-is-trace 'mt 'A z))
                 (u1 (dk-skolem! ex)))
            (mci-power-of-open! 'mt u1)
            (mci-each! (lambda () (sep-mi))
             (lambda (n)
               (dk-focus! n)
               (if (dk-head-is? (dk-goal) 'FORSOME)
                   (begin
                     (ew u1)
                     (dk-conj-close!
                      (lambda ()
                        (if (dk-head-is? (dk-goal) '=)
                            (ass)
                            (begin (mci-each! (lambda () (sep-mi)) (lambda (m) (dk-focus! m) (ass))
                                             ))))))
                   (ass)))
             )))))))
(fact 'class-extensionality mci-s2-l mci-s2-r)
(subst (list '= mci-s2-l mci-s2-r))
(qrfl)
(qed 'subspace-top-of-metric-top)

;;; =====================================================================
;;; (T4') THE THEOREM, STATED TOPOLOGICALLY.  The continuous image of a compact
;;; metrizable space is compact in the subspace topology.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-METRIZABLE-TOP-SPACE s) (IMPLIES (IS-METRIZABLE-TOP-SPACE t)
     (IMPLIES (IS-HOM-TOP-SPACE s t f) (IMPLIES (IS-COMPACT-T s)
       (IS-COMPACT-T (SUBSPACE-TOP t (IMAGE f (PTS s)))))))))))))
(dk-peel!)
(define mci-mt (dk-skolem! (dk-fact! 'metrizable-has-metric-top 't)))
(define mci-img5 '(IMAGE f (PTS s)))
(define mci-sub5 (list 'SUBSPACE-MS mci-mt mci-img5))
(fact 'metrizable-compact-image-ms 's 't 'f mci-mt)
(fact 'ms-pts-is-set mci-mt)
(dk-project! '(IN f (FUN (PTS s) (PTS t))) 'is-hom-top-space-def '(IS-HOM-TOP-SPACE s t f))
(mci-pts-eq! mci-mt)
(dk-have! (list 'SUBSET mci-img5 (list 'PTS mci-mt))
  (lambda ()
    (mac 'subset-def)
    (let ((w (dk-di-var!)))
      (fact 'image-subset-codomain '(PTS s) '(PTS t) 'f w)
      (subst (list '= (list 'PTS mci-mt) (list 'PTS (list 'METRIC-TOP mci-mt))))
      (subst (list '= (list 'METRIC-TOP mci-mt) 't))
      (ass))))
(fact 'subspace-is-metric-space mci-mt mci-img5)
(mci-iff-move! (dk-cite! 'metric-top-compact mci-sub5)
               (list 'IS-COMPACT mci-sub5) (list 'IS-COMPACT-T (list 'METRIC-TOP mci-sub5)))
(fact 'subspace-top-of-metric-top mci-mt mci-img5)
(subst (list '= 't (list 'METRIC-TOP mci-mt)))
(subst (list '= (list 'SUBSPACE-TOP (list 'METRIC-TOP mci-mt) mci-img5) (list 'METRIC-TOP mci-sub5)))
(ass)
(qed 'metrizable-compact-image)
