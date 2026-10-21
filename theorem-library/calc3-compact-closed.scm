;;; calc3-compact-closed.scm -- calculus.pdf Cor 3.20: A CONTINUOUS BIJECTION FROM A
;;; COMPACT METRIC SPACE IS A HOMEOMORPHISM, and the brick it was missing, A COMPACT
;;; SUBSET OF A METRIC SPACE IS CLOSED.  Agent CALC-3, 2026-10-19.
;;;
;;;   compact-subspace-is-closed
;;;     forall s. is-metric-space(s) => forall A. A subset pts(s) =>
;;;       is-compact(subspace-ms(s, A)) => is-closed(s, A)
;;;
;;;   compact-continuous-bijection-is-homeomorphism            (Cor 3.20)
;;;     forall s, t, f. is-compact(s) => is-continuous(s, t, f) =>
;;;       f in bijection(pts(s), pts(t)) => is-homeomorphism(s, t, f)
;;;
;;; "A subset A is compact" is IS-COMPACT(SUBSPACE-MS(s, A)), as in Prop 3.19
;;; (compact-image.scm).  IS-HOMEOMORPHISM is structure-library/calc3-vocab.scm.
;;;
;;; COMPACT => CLOSED.  The notes use it without proof.  Here: a point z of the
;;; closure of A is the limit of a sequence g of points of A with g(k) in the ball
;;; B(z, 1/(k+1)) -- chosen by countable choice (rmm-nn-choice, the device of
;;; ca5-function-spaces.scm), each ball meeting A because it is an open set
;;; containing z (closure-membership).  The subspace is sequentially compact
;;; (compact-implies-seq-compact), so a subsequence of g converges IN THE SUBSPACE to
;;; some l in A; it converges in s to l as well (subspace-converges-to) and, being a
;;; subsequence of g, to z (subseq-of-convergent); limits are unique, so z = l is in
;;; A.  Hence closure(A) subset A and A is closed (closure-subset-closed).
;;;
;;; COR 3.20, as the compact-image.scm header planned it.  Let g be the inverse
;;; bijection.  For A closed in s: A is compact (closed-subset-of-compact-is-compact),
;;; f(A) is compact (3.19, continuous-image-of-compact), hence closed in t (the brick);
;;; and the g-preimage of A IS f(A) (inverse-bij-left / -right).  So g pulls closed
;;; sets back to closed sets and is continuous (closed-preimage-implies-continuous).
;;;
;;; WINDOW.  The latest citations: continuous-image-of-compact
;;; (theorem-library/compact-image, the lo), rmm-nn-choice (theorem-library/
;;; riesz-markov-model), compact-implies-seq-compact, closed-subset-of-compact-is-compact,
;;; subspace-converges-to / subspace-pts (theorem-library/metric-subspace-laws),
;;; closure-* (theorem-library/metric-closure-laws), nn-recip-succ-*, metric-limit-unique,
;;; subseq-of-convergent, subseq-is-fun, inverse-bij-*, image-membership-iff,
;;; preimage-membership, closed-preimage-implies-continuous.  lo = compact-image;
;;; hi = none.  Library: analysis.
;;;
;;; Helper prefix: c3k-.

(define (c3k-head g) (and (pair? g) (car g)))

;;; Countable choice through rmm-nn-choice, the driver of ca5-function-spaces.scm
;;; (ca5-choose-seq! / ca5-seq-at!), copied: L = k |-> {w in A : P(k, w)}.
(define c3k-seq-family '())
(define (c3k-choose-seq! A Pf witness-of)
  (let* ((L   (list 'VNB-LAMBDA 'c3kk_ 'NN (list 'SEP 'c3kw_ A (Pf 'c3kk_ 'c3kw_))))
         (inh (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
                (list 'FORSOME 'w (list 'AND (list 'IN 'w A) (list 'IN 'w (list L 'k))))))))
    (dk-have! inh
      (lambda ()
        (let* ((k (dk-di-var!)))
          (dk-lam-b!)
          (let ((w (witness-of k)))
            (ew w)
            (dk-conj-close!
              (lambda ()
                (if (dk-head-is? (caddr (dk-goal)) 'SEP)
                    (dk-close-all! (lambda () (sep-mi)))
                    (ass))))))))
    (let ((g (dk-skolem! (dk-cite! 'rmm-nn-choice A L))))
      (set! c3k-seq-family (cons (cons g L) c3k-seq-family))
      g)))
(define (c3k-seq-at! g k)
  (let* ((L  (cdr (assq g c3k-seq-family)))
         (cl (dk-ctx-form (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list 'IN (list g 'k) (list L 'k))))))
         (h  (dk-apply! (or cl (error "c3k-seq-at!: the choice clause is not in context" g)) k)))
    (dk-lam-b-h! h)
    (let ((m (dk-pick (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) (list g k))
                                       (dk-head-is? (caddr f) 'SEP)))
                      "the chosen membership")))
      (dk-split-all! (dk-landed (lambda () (sep-me m)))))))

;;; The right-hand side of a cited IFF, proved from its left (in context) and split.
(define (c3k-iff-rhs! iff)
  (let ((rhs (caddr iff)))
    (dk-have! rhs (lambda () (prop)))
    (if (eq? (c3k-head rhs) 'AND) (dk-split-all! (list rhs)))
    rhs))

;;; =====================================================================
;;; (1) A COMPACT SUBSET OF A METRIC SPACE IS CLOSED.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (FORALL A (IMPLIES (SUBSET A (PTS s))
       (IMPLIES (IS-COMPACT (SUBSPACE-MS s A))
         (IS-CLOSED s A))))))))
(dk-peel!)
(dk-have! '(IN A SET) (lambda () (dk-sethood! 'A)))
(dk-have! '(SUBSET (CLOSURE s A) A)
  (lambda ()
    (mac 'subset-def)
    (let ((z (dk-di-var!)))                              ; z in CLOSURE(s, A)
      (c3k-iff-rhs! (dk-cite! 'closure-membership 's 'A z))   ; z in PTS(s), the open-set universal
      (let* ((uc (dk-pick (lambda (h) (and (eq? (c3k-head h) 'FORALL) (dk-contains? h 'IS-OPEN) (dk-contains? h 'FORSOME)))
                          "the closure universal"))
             (g (c3k-choose-seq! 'A
                  (lambda (k w) (list 'IN w (list 'BALL 's z (list 'RECIP (list '+ k 1)))))
                  (lambda (k)
                    (let* ((r  (list 'RECIP (list '+ k 1)))
                           (bl (list 'BALL 's z r)))
                      (fact 'nn-recip-succ-pos k)
                      (dk-pos-parts! r)
                      (fact 'ball-is-open 's z r)
                      (fact 'ball-center-in 's z r)
                      (dk-have! (list 'AND (list 'IS-OPEN 's bl) (list 'IN z bl))
                        (lambda () (dk-conj-close! (lambda () (ass)))))
                      (dk-skolem! (dk-apply! uc bl)))))))
        ;; g converges to z in s
        (dk-have! (list 'CONVERGES-TO 's g z)
          (lambda ()
            (mac 'CONVERGES-TO)
            (dk-conj-close!
             (lambda ()
               (cond
                ((eq? (c3k-head (dk-goal)) 'FORALL)
                 (let* ((pe (dk-peel!))
                        (eps (cadr (car pe)))
                        (n (dk-skolem! (dk-cite! 'nn-recip-succ-small eps))))
                   (ew n)
                   (dk-conj-close!
                    (lambda ()
                      (if (eq? (c3k-head (dk-goal)) 'FORALL)
                          (let* ((pn (dk-peel!))
                                 (m (cadr (car (filter (lambda (f) (and (eq? (c3k-head f) 'IN)
                                                                        (eq? (caddr f) 'NN)))
                                                       pn))))
                                 (gm (list g m))
                                 (rm (list 'RECIP (list '+ m 1)))
                                 (rn (list 'RECIP (list '+ n 1))))
                            (c3k-seq-at! g m)
                            (mac-h 'ball-membership (list 'IN gm (list 'BALL 's z rm)))
                            (dk-split-all!)
                            (fact 'metric-sym 's z gm)
                            (fact 'metric-dist-real 's z gm)
                            (fact 'metric-dist-real 's gm z)
                            (fact 'nn-recip-succ-antitone n m)
                            (fact 'nn-recip-succ-pos m)
                            (fact 'nn-recip-succ-pos n)
                            (fact 'rr-pos-rr-in-rr rm)
                            (fact 'rr-pos-rr-in-rr rn)
                            (fact 'rr-pos-rr-in-rr eps)
                            (dk-ineq! (list '= (list '(DIST s) z gm) (list '(DIST s) gm z))
                                      (list '<= (list '(DIST s) z gm) rm)
                                      (list '<= rm rn)
                                      (list '< rn eps)
                                      (list 'IN (list '(DIST s) z gm) 'RR)
                                      (list 'IN (list '(DIST s) gm z) 'RR)
                                      (list 'IN rm 'RR) (list 'IN rn 'RR) (list 'IN eps 'RR)))
                          (ass))))))
                ((eq? (c3k-head (dk-goal)) 'IN)
                 (if (dk-contains? (dk-goal) 'FUN)
                     (fact 'fun-codomain-superset g 'NN 'A '(PTS s)))
                 (ass))
                (#t (ass)))))))
        ;; a subsequence converges in the subspace
        (let ((sub '(SUBSPACE-MS s A)))
          (fact 'subspace-pts 's 'A)
          (fact 'subspace-is-metric-space 's 'A)
          (fact 'compact-implies-seq-compact sub)
          (c3k-iff-rhs! (dk-cite! 'seq-compact sub))
          (dk-have! (list 'IN g (list 'FUN 'NN (list 'PTS sub)))
            (lambda () (subst (list '== (list 'PTS sub) 'A)) (ass)))
          (let* ((us (dk-pick (lambda (h) (and (eq? (c3k-head h) 'FORALL) (dk-contains? h 'SUBSEQ)))
                              "the sequential compactness universal"))
                 (phi (dk-skolem! (dk-apply! us g)))
                 (lex (dk-pick (lambda (h) (and (eq? (c3k-head h) 'FORSOME) (dk-contains? h 'SUBSEQ)))
                               "the limit existential"))
                 (l (dk-skolem! lex))
                 (sq (list 'SUBSEQ g phi)))
            (dk-have! (list 'IN l 'A) (lambda () (subst (list '== 'A (list 'PTS sub))) (ass)))
            (dk-have! (list 'AND (list 'IN g (list 'FUN 'NN (list 'PTS sub))) (list 'STRICTLY-MONO-NN phi))
              (lambda () (dk-conj-close! (lambda () (ass)))))
            (fact 'subseq-is-fun sub g phi)
            (dk-have! (list 'IN sq (list 'FUN 'NN 'A))
              (lambda () (subst (list '== 'A (list 'PTS sub))) (ass)))
            (c3k-iff-rhs! (dk-cite! 'subspace-converges-to 's 'A sq l))
            (fact 'subseq-of-convergent 's g phi z)
            (fact 'metric-limit-unique 's sq l z)
            (subst (list '= z l))
            (ass)))))))
(fact 'closure-subset-closed 's 'A)
(ass)
(qed 'compact-subspace-is-closed)
(topic! 'compact-subspace-is-closed 'analysis)
(alias! 'compact-subspace-is-closed "a compact subset of a metric space is closed")

;;; =====================================================================
;;; (2) COR 3.20.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL f
     (IMPLIES (IS-COMPACT s)
       (IMPLIES (IS-CONTINUOUS s t f)
         (IMPLIES (IN f (BIJECTION (PTS s) (PTS t)))
           (IS-HOMEOMORPHISM s t f)))))))))
(dk-peel!)
(c3k-iff-rhs! (dk-cite! 'is-compact 's))
(c3k-iff-rhs! (dk-cite! 'is-continuous 's 't 'f))
(define c3k-g '(INVERSE-BIJ f (PTS s) (PTS t)))
(fact 'inverse-bij-in-fun '(PTS s) '(PTS t) 'f)
(dk-have! (list 'FORALL 'A (list 'IMPLIES '(IS-CLOSED s A) (list 'IS-CLOSED 't (list 'PREIMAGE 't c3k-g 'A))))
  (lambda ()
    (let* ((pa (dk-peel!))
           (A (caddr (car pa)))
           (im (list 'IMAGE 'f A))
           (pre (list 'PREIMAGE 't c3k-g A)))
      (c3k-iff-rhs! (dk-cite! 'is-closed 's A))
      (fact 'closed-subset-of-compact-is-compact 's A)
      (fact 'continuous-image-of-compact 's 't 'f A)
      (dk-have! (list 'SUBSET im '(PTS t))
        (lambda ()
          (mac 'subset-def)
          (let* ((w (dk-di-var!))
                 (x (begin (c3k-iff-rhs! (dk-cite! 'image-membership-iff 'f A w))
                           (dk-skolem! (dk-pick (lambda (h) (and (eq? (c3k-head h) 'FORSOME)
                                                                 (dk-contains? h 'f)))
                                                "the image witness")))))
            (fact 'subset-mem-fwd A '(PTS s) x)
            (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) x)
            (subst (list '= w (list 'f x)))
            (ass))))
      (fact 'compact-subspace-is-closed 't im)
      (dk-have! (list 'FORALL 'c3kz_ (list 'IFF (list 'IN 'c3kz_ pre) (list 'IN 'c3kz_ im)))
        (lambda ()
          (let ((y (dk-di-var! (lambda (g) (cadr (cadr g))))))
            (dk-iff!
             (lambda (g) (dk-contains? g 'IMAGE))
             (lambda ()                                     ; y in the preimage
               (mac-h 'preimage-membership (list 'IN y pre))
               (dk-split-all!)
               (mac 'image-membership-iff)
               (dk-conj-close!
                (lambda ()
                  (cond
                   ((eq? (c3k-head (dk-goal)) 'FORSOME)
                    (let ((gy (list c3k-g y)))
                      (ew gy)
                      (dk-conj-close!
                       (lambda ()
                         (if (eq? (c3k-head (dk-goal)) '=)
                             (fact 'inverse-bij-right '(PTS s) '(PTS t) 'f y))
                         (ass)))))
                   (#t (fact 'membership-implies-sethood y '(PTS t)) (ass))))))
             (lambda ()                                     ; y in the image
               (c3k-iff-rhs! (dk-cite! 'image-membership-iff 'f A y))
               (let ((x (dk-skolem! (dk-pick (lambda (h) (and (eq? (c3k-head h) 'FORSOME)
                                                              (dk-contains? h 'f)))
                                             "the image witness"))))
                 (fact 'subset-mem-fwd A '(PTS s) x)
                 (fact 'fun-apply-type-c 'f '(PTS s) '(PTS t) x)
                 (fact 'inverse-bij-left '(PTS s) '(PTS t) 'f x)
                 (subst (list '= y (list 'f x)))
                 (mac 'preimage-membership)
                 (dk-conj-close!
                  (lambda ()
                    (if (dk-contains? (dk-goal) 'INVERSE-BIJ)
                        (subst (list '= (list c3k-g (list 'f x)) x)))
                    (ass)))))))))
      (fact 'class-extensionality pre im)
      (subst (list '= pre im))
      (ass))))
(dk-have! (list 'AND '(IS-METRIC-SPACE t) (list 'AND '(IS-METRIC-SPACE s) (list 'IN c3k-g '(FUN (PTS t) (PTS s)))))
  (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'closed-preimage-implies-continuous 't 's c3k-g)
(mac 'IS-HOMEOMORPHISM)
(dk-conj-close! (lambda () (ass)))
(qed 'compact-continuous-bijection-is-homeomorphism)
(topic! 'compact-continuous-bijection-is-homeomorphism 'analysis)
(alias! 'compact-continuous-bijection-is-homeomorphism
        "a continuous bijection from a compact metric space is a homeomorphism")
