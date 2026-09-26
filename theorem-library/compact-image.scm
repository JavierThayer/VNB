;;; compact-image.scm -- THE CONTINUOUS IMAGE OF A COMPACT SPACE IS COMPACT
;;; (calculus.pdf, Proposition 3.19), and the COMPACTNESS OF THE TRACE of a
;;; path, which follows from it (complex-analysis.pdf 3.1.1: "gamma_* is
;;; sometimes called the trace of gamma.  It is always a compact set").
;;;
;;; NOT HERE: that the trace is BOUNDED (forsome M. every point of the trace has
;;; magnitude at most M).  It follows from compactness through
;;; `compact-implies-totally-bounded' at radius 1 plus a MAXIMUM over the finite
;;; 1-net, and the library has no theorem that a FINITE SET OF REALS HAS AN UPPER
;;; BOUND -- the brick that step wants, one `finite-set-induction' with the
;;; witness max(M, x) at the step.  Reported, not attempted.
;;;
;;; THE NOTES' STATEMENT.  Prop 3.19 reads
;;;
;;;     Suppose F : X --> Y is continuous and A subset X is compact.
;;;     Then f(A) is compact.
;;;
;;; The library's IS-COMPACT is a predicate of a metric SPACE, not of a subset,
;;; so "A subset X is compact" is IS-COMPACT(SUBSPACE-MS(s, A)) and "f(A) is
;;; compact" is IS-COMPACT(SUBSPACE-MS(t, IMAGE(f, A))) -- the image carries the
;;; metric of the target space, cut down to it (structure-library/
;;; metric-subspace.scm).  `continuous-image-of-compact' below is exactly that
;;; sentence.  Nothing is assumed about A but SUBSET A (PTS s), which the notes'
;;; "A subset X" says; the empty A is allowed and comes out right (the empty
;;; subspace is a metric space and is compact).
;;;
;;; THE WHOLE-SPACE FORM IS THE WORKHORSE.  `compact-image' is the case
;;; A = PTS(s); the notes' form is derived from it by restricting f to A
;;; (`restrict-continuous-at', `restrict-in-fun', and `image-restrict' below).
;;; The trace of a path is the whole-space form at s = SUBSPACE-MS(RR-MS,
;;; CCINT(a,b)) and f = gamma, so IS-PATH's own continuity conjunct is what it
;;; wants and no restriction is needed.
;;;
;;; THE COVER ARGUMENT, AND WHY NO CHOICE FUNCTION IS NEEDED.  The notes pull an
;;; open cover {U_i} of f(A) back along f.  Mechanically the pull-back needs,
;;; for each W in the cover, an open V of s with V = f^-1(W) -- and then the
;;; finite subcover of s has to be pushed FORWARD again to a finite subfamily of
;;; the given cover.  Both directions are canonical here, so nothing is chosen:
;;;
;;;     D = { V in POWER(PTS s) : IS-OPEN(s, V) and
;;;                               forsome W. (W in C and V = PREIMAGE(s, f, W)) }
;;;
;;; is an open cover of s (the SEP over POWER(PTS s) makes it a SET, which is
;;; what the CARD bricks need -- the device of `compact-subspace.scm'), and from
;;; a finite F subset D the finite subfamily of C is the forward image
;;;
;;;     G = { W in IMAGE(V |-> IMAGE(f, V), F) : W in C }.
;;;
;;; G is finite (`card-image-finite' then `card-subset-nn'), and it is a
;;; subfamily of C because IMAGE(f, PREIMAGE(s, f, W)) = W whenever W is
;;; contained in the image of f -- `image-of-preimage-onto' below, the one step
;;; that uses surjectivity onto the image.  A member W of the cover IS so
;;; contained: it is open in the subspace, hence a subset of its points, which
;;; are the image.
;;;
;;; The openness of PREIMAGE(s, f, W) for W open in the SUBSPACE is
;;; `preimage-subspace-open': W is a trace U ^ B (`subspace-open-is-trace'), and
;;; PREIMAGE(s, f, U ^ B) = PREIMAGE(s, f, U) because f lands in B, so
;;; `continuous-implies-open-preimage' applies to U.  This is why the file does
;;; not need f corestricted to a map into the subspace (which would want a
;;; codomain-shrinking rule for FUN that the tree does not have).
;;;
;;; NOT PROVEN HERE: Corollary 3.20 (a continuous bijection from a compact space
;;; is a homeomorphism).  INVERSE-BIJ exists, so no notion has to be invented and
;;; the statement is "IS-CONTINUOUS(t, s, INVERSE-BIJ(f, PTS s, PTS t))"; the
;;; missing brick is "a compact -- or merely complete -- SUBSPACE of a metric
;;; space is CLOSED", the converse of `subspace-complete', which the library does
;;; not have.  With it, 3.20 is: a closed A is compact as a subspace
;;; (`closed-subset-of-compact-is-compact'), its image is compact
;;; (3.19), hence closed, and `closed-preimage-implies-continuous' finishes,
;;; since the g-preimage of A is IMAGE(f, A) for g the inverse bijection.
;;;
;;; WINDOW (scratchpad/window.py).  Everything cited is old except
;;; `subspace-open-is-trace' / `subspace-is-metric-space' / `restrict-*'
;;; (theorem-library/metric-subspace-laws), `heine-borel-ccint'
;;; (theorem-library/heine-borel-interval) and the IS-PATH read-offs
;;; (theorem-library/road-laws).  The slot is therefore after road-laws.
;;;
;;; Helper prefix: cim-.

;;; ---- file-local driver helpers (the three copied from compact-subspace.scm;
;;; ---- each is owed to driver-kit.scm, see the report) -----------------

(define (cim-head g) (and (pair? g) (car g)))
(define (cim-concl g) (if (eq? (cim-head g) 'IMPLIES) (caddr g) g))

;;; Split an AND goal to its atoms and run CLOSER on each.
(define (cim-and! closer)
  (if (eq? (cim-head (dk-goal)) 'AND)
      (for-each (lambda (k) (dk-focus! k) (cim-and! closer))
                (dk-opened (lambda () (di))))
      (closer)))

;;; `bu-me' the membership MEM and return the index eigenvariable, taken from
;;; the landing that is a membership in FAM -- never by shape.
(define (cim-bu-skolem! mem fam)
  (let* ((new (dk-landed (lambda () (bu-me mem))))
         (fm  (or (find-first (lambda (h) (and (pair? h) (eq? (car h) 'IN)
                                               (equal? (caddr h) fam)))
                              new)
                  (error "cim-bu-skolem!: no landed membership in" fam))))
    (cadr fm)))

;;; From (IN e SEP) take the condition apart and close the goal from the context.
(define (cim-sep-close! e sp)
  (sep-me (list 'IN e sp))
  (dk-split-all!)
  (ass))

;;; `(== (BIG-UNION b FAM b) RHS)' by class extensionality.  BODY is run on the
;;; peeled point with the two arguments (z, the big union as the GOAL spells it).
(define (cim-extensional! rhs body)
  (let ((bu (cadr (dk-goal))))
    (have! (list 'FORALL 'zqz_ (list 'IFF (list 'IN 'zqz_ bu) (list 'IN 'zqz_ rhs)))
      (lambda ()
        (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
          (body z bu))))
    (fact 'class-extensionality bu rhs)
    (subst (list '= bu rhs))
    (qrfl)))

;;; =====================================================================
;;; (1) A PREIMAGE IS A MEMBER OF THE POWER SET OF THE POINTS.
;;; The packaging the cover family needs: PREIMAGE(s,f,V) is a SEP over PTS(s),
;;; so it is a set and all its members are points.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IN (PTS s) SET)
     (FORALL fqf_ (FORALL vqu_
       (IN (PREIMAGE s fqf_ vqu_) (POWER (PTS s)))))))))
(dk-peel!)
(have! '(IN (PREIMAGE s fqf_ vqu_) SET)
  (lambda () (mac 'PREIMAGE) (sep-set) (ass)))
(have! '(FORALL z_ (IMPLIES (IN z_ (PREIMAGE s fqf_ vqu_)) (IN z_ (PTS s))))
  (lambda ()
    (let ((e (dk-di-var!)))
      (mac-h 'preimage-membership (list 'IN e '(PREIMAGE s fqf_ vqu_)))
      (dk-split-all!)
      (ass))))
(fact 'power-mem-intro '(PTS s) '(PREIMAGE s fqf_ vqu_))
(ass)
(qed 'preimage-in-power)
(topic! 'preimage-in-power 'topology)

;;; =====================================================================
;;; (2) THE IMAGE OF A PREIMAGE, FOR A SET INSIDE THE IMAGE.
;;;     W subset IMAGE(f, PTS s)  =>  IMAGE(f, PREIMAGE(s, f, W)) = W.
;;; The one place surjectivity onto the image is used.
;;; =====================================================================
;;; The sethood hypothesis is what CERTIFIES the two sides as DEFINED for
;;; `class-extensionality' (the LUTINS rule): a SEP over a certified domain is
;;; certified, an IMAGE is not, so the image has to be TYPED before the
;;; universal is instantiated at it.
(sp (make-wff '(FORALL s (IMPLIES (IN (PTS s) SET)
     (FORALL fqf_ (FORALL wqu_
       (IMPLIES (SUBSET wqu_ (IMAGE fqf_ (PTS s)))
         (= (IMAGE fqf_ (PREIMAGE s fqf_ wqu_)) wqu_))))))))
(dk-peel!)
(have! '(IN (PREIMAGE s fqf_ wqu_) SET)
  (lambda () (mac 'PREIMAGE) (sep-set) (ass)))
(fact 'image-set 'fqf_ '(PREIMAGE s fqf_ wqu_))
(have! '(FORALL zqz_ (IFF (IN zqz_ (IMAGE fqf_ (PREIMAGE s fqf_ wqu_)))
                          (IN zqz_ wqu_)))
  (lambda ()
    (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (dk-iff!
       (lambda (g) (dk-contains? (cim-concl g) 'IMAGE))
       ;; <== : z in W  ==>  z in IMAGE(f, PREIMAGE(s,f,W))
       (lambda ()
         (dk-peel!)
         ;; NOT `subset-mem-fwd' here: instantiating a universal AT the term
         ;; IMAGE(f, PTS s) owes the definedness sequent `t = t' (the LUTINS
         ;; rule), and nothing in this statement types that image.  Unfolding
         ;; the SUBSET hypothesis instead instantiates only at the point z.
         (mac-h 'subset-def '(SUBSET wqu_ (IMAGE fqf_ (PTS s))))
         (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                              (dk-contains? h 'IMAGE)))
                             "the pointwise subset hypothesis")
                    z)
         (mac-h 'image-membership-iff (list 'IN z '(IMAGE fqf_ (PTS s))))
         (let ((x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
           (have! (list 'IN x '(PREIMAGE s fqf_ wqu_))
             (lambda ()
               (mac 'preimage-membership)
               (dk-conj-close!
                (lambda ()
                  (if (equal? (cadr (dk-goal)) x)
                      (ass)
                      (begin (subst (list '= (list 'fqf_ x) z)) (ass)))))))
           (mac 'image-membership-iff)
           (ew x)
           (both! (lambda () (ass)) (lambda () (ass)))))
       ;; ==> : z in IMAGE(f, PREIMAGE(s,f,W))  ==>  z in W
       (lambda ()
         (dk-peel!)
         (mac-h 'image-membership-iff
                (list 'IN z '(IMAGE fqf_ (PREIMAGE s fqf_ wqu_))))
         (let ((x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
           (mac-h 'preimage-membership (list 'IN x '(PREIMAGE s fqf_ wqu_)))
           (dk-split-all!)
           (subst (list '= z (list 'fqf_ x)))
           (ass)))))))
(fact 'class-extensionality '(IMAGE fqf_ (PREIMAGE s fqf_ wqu_)) 'wqu_)
(ass)
(qed 'image-of-preimage-onto)
(topic! 'image-of-preimage-onto 'constructions)

;;; =====================================================================
;;; (3) THE PREIMAGE OF A SUBSPACE-OPEN SET IS OPEN.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL fqf_
     (IMPLIES (IS-CONTINUOUS s t fqf_)
       (FORALL bqb_ (IMPLIES (SUBSET bqb_ (PTS t))
         (IMPLIES (FORALL zqp_ (IMPLIES (IN zqp_ (PTS s))
                                        (IN (fqf_ zqp_) bqb_)))
           (FORALL wqu_ (IMPLIES (IS-OPEN (SUBSPACE-MS t bqb_) wqu_)
             (IS-OPEN s (PREIMAGE s fqf_ wqu_)))))))))))))
(dk-peel!)
(let ((op (dk-fact! 'continuous-implies-open-preimage 's 't 'fqf_))
      (pt (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                    (dk-contains? h 'bqb_)))
                   "the pointwise landing hypothesis")))
  (mac-h 'IS-CONTINUOUS '(IS-CONTINUOUS s t fqf_))
  (dk-split-all!)
  (let* ((ex (dk-fact! 'subspace-open-is-trace 't 'bqb_ 'wqu_))
         (u  (dk-skolem! ex)))
    (have! (list '= '(PREIMAGE s fqf_ wqu_) (list 'PREIMAGE 's 'fqf_ u))
      (lambda ()
        (have! (list 'FORALL 'zqz_
                 (list 'IFF '(IN zqz_ (PREIMAGE s fqf_ wqu_))
                            (list 'IN 'zqz_ (list 'PREIMAGE 's 'fqf_ u))))
          (lambda ()
            (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
              (dk-iff!
               (lambda (g) (dk-contains? (cim-concl g) 'wqu_))
               ;; z in PREIMAGE(s,f,U)  ==>  z in PREIMAGE(s,f,W)
               (lambda ()
                 (dk-peel!)
                 (mac-h 'preimage-membership (list 'IN z (list 'PREIMAGE 's 'fqf_ u)))
                 (dk-split-all!)
                 (dk-apply! pt z)
                 (mac 'preimage-membership)
                 (dk-conj-close!
                  (lambda ()
                    (if (equal? (caddr (dk-goal)) '(PTS s))
                        (ass)
                        (begin
                          (subst (list '= 'wqu_ (list 'INTERSECTION u 'bqb_)))
                          (mac 'intersection-membership)
                          (dk-conj-close! (lambda () (ass))))))))
               ;; z in PREIMAGE(s,f,W)  ==>  z in PREIMAGE(s,f,U)
               (lambda ()
                 (dk-peel!)
                 (mac-h 'preimage-membership (list 'IN z '(PREIMAGE s fqf_ wqu_)))
                 (dk-split-all!)
                 (have! (list 'IN (list 'fqf_ z) (list 'INTERSECTION u 'bqb_))
                   (lambda ()
                     (subst (list '= (list 'INTERSECTION u 'bqb_) 'wqu_))
                     (ass)))
                 (mac-h 'intersection-membership
                        (list 'IN (list 'fqf_ z) (list 'INTERSECTION u 'bqb_)))
                 (dk-split-all!)
                 (mac 'preimage-membership)
                 (dk-conj-close! (lambda () (ass))))))))
        (fact 'class-extensionality '(PREIMAGE s fqf_ wqu_)
                                    (list 'PREIMAGE 's 'fqf_ u))
        (ass)))
    (subst (list '= '(PREIMAGE s fqf_ wqu_) (list 'PREIMAGE 's 'fqf_ u)))
    (dk-apply! op u)
    (ass)))
(qed 'preimage-subspace-open)
(topic! 'preimage-subspace-open 'topology)

;;; =====================================================================
;;; (4) THE WHOLE-SPACE FORM: the continuous image of a compact space is
;;;     compact, as a subspace of the target.
;;; =====================================================================

(define (cim-dd cv)
  (list 'SEP 'dqu_ '(POWER (PTS s))
        (list 'AND '(IS-OPEN s dqu_)
              (list 'FORSOME 'dqw_
                    (list 'AND (list 'IN 'dqw_ cv)
                          (list '= 'dqu_ '(PREIMAGE s fqf_ dqw_)))))))

(sp (make-wff '(FORALL s (FORALL t (FORALL fqf_
     (IMPLIES (IS-CONTINUOUS s t fqf_)
       (IMPLIES (IS-COMPACT s)
         (IS-COMPACT (SUBSPACE-MS t (IMAGE fqf_ (PTS s)))))))))))
(dk-peel!)
(define cim-bb '(IMAGE fqf_ (PTS s)))
(define cim-sub (list 'SUBSPACE-MS 't cim-bb))
(define cim-ptw
  (list 'FORALL 'zqp_ (list 'IMPLIES '(IN zqp_ (PTS s))
                            (list 'IN '(fqf_ zqp_) cim-bb))))
;; IS-CONTINUOUS is NOT unfolded on the main branch: `preimage-subspace-open'
;; wants it whole.  Its three typing conjuncts come out on have! LANES.
(mac-h 'IS-COMPACT '(IS-COMPACT s))
(dk-split-all!)
(dk-have! '(IS-METRIC-SPACE t)
  (lambda () (mac-h 'IS-CONTINUOUS '(IS-CONTINUOUS s t fqf_)) (dk-split-all!) (ass)))
(dk-have! '(IN fqf_ (FUN (PTS s) (PTS t)))
  (lambda () (mac-h 'IS-CONTINUOUS '(IS-CONTINUOUS s t fqf_)) (dk-split-all!) (ass)))
;; the three standing facts about the image
(have! '(IN (PTS s) SET)
  (lambda () (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s)) (dk-split-all!) (ass)))
(have! cim-ptw
  (lambda ()
    (let ((e (dk-di-var!)))
      (mac 'image-membership-iff)
      (ew e)
      (both! (lambda () (ass)) (lambda () (rfl))))))
;; NOT `image-subset-codomain' (an ASSERTED leaf with no warrant, structure-
;; library/injection.scm): the same step is one `fun-apply-type-c' on the
;; witness of the image membership.
(have! (list 'SUBSET cim-bb '(PTS t))
  (lambda ()
    (mac 'subset-def)
    (let ((e (dk-di-var!)))
      (mac-h 'image-membership-iff (list 'IN e cim-bb))
      (let ((x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
        (fact 'fun-apply-type-c 'fqf_ '(PTS s) '(PTS t) x)
        (subst (list '= e (list 'fqf_ x)))
        (ass)))))
(fact 'subspace-is-metric-space 't cim-bb)
(fact 'image-set 'fqf_ '(PTS s))
(mac 'IS-COMPACT)
(cim-and!
 (lambda ()
   (if (eq? (cim-head (dk-goal)) 'IS-METRIC-SPACE)
       (ass)
       (begin
         (di)                                  ; peel the cover variable
         (let ((cv (caddr (cadr (dk-goal)))))
           (di)                                ; land IS-OPEN-COVER(sub, cv)
           (mac-h 'IS-OPEN-COVER (list 'IS-OPEN-COVER cim-sub cv))
           (dk-split-all!)
           (let* ((dd    (cim-dd cv))
                  (copen (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                   (dk-contains? h cv)
                                                   (dk-contains? h 'IS-OPEN)))
                                  "the openness universal of the cover"))
                  (cbu   (cadr (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '==)
                                                         (dk-contains? h cv)))
                                        "the cover's big union")))
                  ;; W open in the subspace  =>  W subset B
                  (wsub! (lambda (w)
                           (have! (list 'SUBSET w cim-bb)
                             (lambda ()
                               (mac-h 'IS-OPEN (list 'IS-OPEN cim-sub w))
                               (dk-split-all!)
                               (mac-h 'subspace-pts
                                      (list 'SUBSET w (list 'PTS cim-sub)))
                               (ass)))))
                  ;; W open in the subspace  =>  PREIMAGE(s,f,W) open in s
                  (wopen! (lambda (w)
                            (dk-apply! copen w)
                            (fact 'preimage-subspace-open 's 't 'fqf_ cim-bb w))))
             ;; ---------- D is a set, and an open cover of s ----------
             (have! (list 'IN dd 'SET)
               (lambda () (sep-set) (fact 'power-set '(PTS s)) (ass)))
             (have! (list 'IS-OPEN-COVER 's dd)
               (lambda ()
                 (mac 'IS-OPEN-COVER)
                 (cim-and!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond
                       ((eq? (cim-head g) 'IS-METRIC-SPACE) (ass))
                       ((eq? (cim-head g) 'FORALL)
                        (cim-sep-close! (dk-di-var!) dd))
                       (#t
                        (cim-extensional!
                         '(PTS s)
                         (lambda (z bu)
                           (dk-iff!
                            (lambda (g2) (dk-contains? (cim-concl g2) 'BIG-UNION))
                            ;; z in PTS s  ==>  z in BIG-UNION(D)
                            (lambda ()
                              (dk-peel!)
                              (dk-apply! cim-ptw z)
                              (have! (list 'IN (list 'fqf_ z) cbu)
                                (lambda ()
                                  (subst (list '== cbu (list 'PTS cim-sub)))
                                  (mac 'subspace-pts)
                                  (ass)))
                              (let ((w (cim-bu-skolem! (list 'IN (list 'fqf_ z) cbu) cv)))
                                (wopen! w)
                                (for-each
                                 (lambda (k)
                                   (dk-focus! k)
                                   (let ((g3 (dk-goal)))
                                     (if (equal? (caddr g3) dd)
                                         (in-sep!
                                          (lambda () (fact 'preimage-in-power 's 'fqf_ w) (ass))
                                          (lambda ()
                                            (both! (lambda () (ass))
                                                   (lambda ()
                                                     (ew w)
                                                     (both! (lambda () (ass))
                                                            (lambda () (rfl)))))))
                                         (begin
                                           (mac 'preimage-membership)
                                           (dk-conj-close! (lambda () (ass)))))))
                                 (dk-opened
                                  (lambda () (bu-mi (list 'PREIMAGE 's 'fqf_ w)))))))
                            ;; z in BIG-UNION(D)  ==>  z in PTS s
                            (lambda ()
                              (dk-peel!)
                              (let ((e (cim-bu-skolem! (list 'IN z bu) dd)))
                                (sep-me (list 'IN e dd))
                                (dk-split-all!)
                                (fact 'power-mem-in '(PTS s) e z)
                                (ass)))))))))))))
             ;; ---------- the finite subcover of s, and the family G ----------
             (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                  (dk-contains? h 'IS-OPEN-COVER)
                                                  (dk-contains? h 'FORSOME)))
                                 "the compactness universal of s")
                        dd)
             (let* ((fv  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the finite subcover")))
                    (lam (list 'VNB-LAMBDA 'dqv_ fv (list 'IMAGE 'fqf_ 'dqv_)))
                    (img (list 'IMAGE lam fv))
                    (gg  (list 'SEP 'gqw_ img (list 'IN 'gqw_ cv))))
               (fact 'subclass-of-set-is-set fv dd)
               (mac-h 'IS-OPEN-COVER (list 'IS-OPEN-COVER 's fv))
               (dk-split-all!)
               (let ((fbu (cadr (dk-pick (lambda (h) (and (pair? h) (eq? (car h) '==)
                                                          (dk-contains? h fv)))
                                         "the subcover's big union"))))
                 (fact 'image-set lam fv)
                 (fact 'card-image-finite lam fv)
                 (have! (list 'IN gg 'SET) (lambda () (sep-set) (ass)))
                 (have! (list 'AND (list 'IN img 'SET) (list 'IN (list 'CARD img) 'NN)))
                 (let* ((uni  (dk-fact! 'card-subset-nn img))
                        (inst (inst*! uni gg)))
                   (have! (cadr inst)
                     (lambda ()
                       (both! (lambda () (ass))
                              (lambda () (cim-sep-close! (dk-di-var!) gg)))))
                   (detach! inst))
                 (ew gg)
                 (cim-and!
                  (lambda ()
                    (let ((g (dk-goal)))
                      (cond
                       ;; G subset C
                       ((eq? (cim-head g) 'SUBSET)
                        (mac 'subset-def)
                        (cim-sep-close! (dk-di-var!) gg))
                       ;; CARD(G) in NN
                       ((eq? (cim-head g) 'IN) (ass))
                       ;; G is an open cover of the subspace
                       (#t
                        (mac 'IS-OPEN-COVER)
                        (mac 'subspace-pts)
                        (cim-and!
                         (lambda ()
                           (let ((g2 (dk-goal)))
                             (cond
                              ((eq? (cim-head g2) 'IS-METRIC-SPACE) (ass))
                              ((eq? (cim-head g2) 'FORALL)
                               (let ((w (dk-di-var!)))
                                 (sep-me (list 'IN w gg))
                                 (dk-split-all!)
                                 (dk-apply! copen w)
                                 (ass)))
                              (#t
                               (cim-extensional!
                                cim-bb
                                (lambda (z bu)
                                  (dk-iff!
                                   (lambda (g3) (dk-contains? (cim-concl g3) 'BIG-UNION))
                                   ;; z in B  ==>  z in BIG-UNION(G)
                                   (lambda ()
                                     (dk-peel!)
                                     (mac-h 'image-membership-iff (list 'IN z cim-bb))
                                     (let ((p (dk-skolem!
                                               (dk-pick (dk-head? 'FORSOME)
                                                        "the image witness"))))
                                       (have! (list 'IN p fbu)
                                         (lambda () (subst (list '== fbu '(PTS s))) (ass)))
                                       (let ((v0 (cim-bu-skolem! (list 'IN p fbu) fv)))
                                         (fact 'subset-mem-fwd fv dd v0)
                                         (sep-me (list 'IN v0 dd))
                                         (dk-split-all!)
                                         (let ((w0 (dk-skolem!
                                                    (dk-pick (dk-head? 'FORSOME)
                                                             "the cover member of v0"))))
                                           (dk-apply! copen w0)
                                           (wsub! w0)
                                           (fact 'image-of-preimage-onto 's 'fqf_ w0)
                                           ;; IMAGE(f, v0) = w0, and it is in C
                                           (have! (list '= (list 'IMAGE 'fqf_ v0) w0)
                                             (lambda ()
                                               (subst (list '= v0 (list 'PREIMAGE 's 'fqf_ w0)))
                                               (ass)))
                                           (for-each
                                            (lambda (k)
                                              (dk-focus! k)
                                              (let ((g4 (dk-goal)))
                                                (if (equal? (caddr g4) gg)
                                                    (in-sep!
                                                     (lambda ()
                                                       (mac 'image-membership-iff)
                                                       (ew v0)
                                                       (both! (lambda () (ass))
                                                              (lambda () (lam-b) (rfl))))
                                                     (lambda ()
                                                       (subst (list '= (list 'IMAGE 'fqf_ v0) w0))
                                                       (ass)))
                                                    (begin
                                                      (mac 'image-membership-iff)
                                                      (ew p)
                                                      (both! (lambda () (ass))
                                                             (lambda () (ass)))))))
                                            (dk-opened
                                             (lambda () (bu-mi (list 'IMAGE 'fqf_ v0)))))))))
                                   ;; z in BIG-UNION(G)  ==>  z in B
                                   (lambda ()
                                     (dk-peel!)
                                     (let ((e (cim-bu-skolem! (list 'IN z bu) gg)))
                                       (sep-me (list 'IN e gg))
                                       (dk-split-all!)
                                       (dk-apply! copen e)
                                       (wsub! e)
                                       (fact 'subset-mem-fwd e cim-bb z)
                                       (ass))))))))))))))))))))))))
(qed 'compact-image)
(topic! 'compact-image 'topology)
(alias! 'compact-image
        "the continuous image of a compact space is compact")

;;; =====================================================================
;;; (5) THE IMAGE OF A RESTRICTION.
;;; =====================================================================
(sp (make-wff '(FORALL aqa_ (IMPLIES (IN aqa_ SET)
     (FORALL fqf_
       (= (IMAGE (RESTRICT fqf_ aqa_) aqa_) (IMAGE fqf_ aqa_)))))))
(dk-peel!)
(fact 'image-set 'fqf_ 'aqa_)
(fact 'image-set '(RESTRICT fqf_ aqa_) 'aqa_)
(have! '(FORALL zqz_ (IFF (IN zqz_ (IMAGE (RESTRICT fqf_ aqa_) aqa_))
                          (IN zqz_ (IMAGE fqf_ aqa_))))
  (lambda ()
    (let ((z (dk-di-var! (lambda (g) (cadr (cadr g))))))
      (dk-iff!
       (lambda (g) (dk-contains? (cim-concl g) 'RESTRICT))
       ;; z in IMAGE(f, A)  ==>  z in IMAGE(RESTRICT(f,A), A)
       (lambda ()
         (dk-peel!)
         (mac-h 'image-membership-iff (list 'IN z '(IMAGE fqf_ aqa_)))
         (let ((x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
           (fact 'restrict-apply 'fqf_ 'aqa_ x)
           (mac 'image-membership-iff)
           (ew x)
           (both! (lambda () (ass))
                  (lambda ()
                    (subst (list '== (list (list 'RESTRICT 'fqf_ 'aqa_) x)
                                      (list 'fqf_ x)))
                    (ass)))))
       ;; z in IMAGE(RESTRICT(f,A), A)  ==>  z in IMAGE(f, A)
       (lambda ()
         (dk-peel!)
         (mac-h 'image-membership-iff (list 'IN z '(IMAGE (RESTRICT fqf_ aqa_) aqa_)))
         (let ((x (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the image witness"))))
           (fact 'restrict-apply 'fqf_ 'aqa_ x)
           (mac 'image-membership-iff)
           (ew x)
           (both! (lambda () (ass))
                  (lambda ()
                    (subst (list '== (list 'fqf_ x)
                                      (list (list 'RESTRICT 'fqf_ 'aqa_) x)))
                    (ass)))))))))
(fact 'class-extensionality '(IMAGE (RESTRICT fqf_ aqa_) aqa_) '(IMAGE fqf_ aqa_))
(ass)
(qed 'image-restrict)
(topic! 'image-restrict 'constructions)

;;; =====================================================================
;;; (6) THE NOTES' PROPOSITION 3.19.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL t (FORALL fqf_
     (IMPLIES (IS-CONTINUOUS s t fqf_)
       (FORALL aqa_ (IMPLIES (SUBSET aqa_ (PTS s))
         (IMPLIES (IS-COMPACT (SUBSPACE-MS s aqa_))
           (IS-COMPACT (SUBSPACE-MS t (IMAGE fqf_ aqa_))))))))))))
(dk-peel!)
(define cim-ssub '(SUBSPACE-MS s aqa_))
(define cim-rst '(RESTRICT fqf_ aqa_))
(begin
  (have! '(IN (PTS s) SET)
    (lambda ()
      (mac-h 'IS-CONTINUOUS '(IS-CONTINUOUS s t fqf_))
      (dk-split-all!)
      (mac-h 'IS-METRIC-SPACE '(IS-METRIC-SPACE s))
      (dk-split-all!)
      (ass)))
  (fact 'subclass-of-set-is-set 'aqa_ '(PTS s))
  (have! (list 'IS-CONTINUOUS cim-ssub 't cim-rst)
    (lambda ()
      (mac 'IS-CONTINUOUS)
      (mac 'subspace-pts)
      (cim-and!
       (lambda ()
         (let ((g (dk-goal)))
           (cond
            ((eq? (cim-head g) 'IS-METRIC-SPACE)
             (if (equal? (cadr g) cim-ssub)
                 (begin
                   (mac-h 'IS-COMPACT (list 'IS-COMPACT cim-ssub))
                   (dk-split-all!)
                   (ass))
                 (begin
                   (mac-h 'IS-CONTINUOUS (list 'IS-CONTINUOUS 's 't 'fqf_))
                   (dk-split-all!)
                   (ass))))
            ((eq? (cim-head g) 'IN)
             (mac-h 'IS-CONTINUOUS (list 'IS-CONTINUOUS 's 't 'fqf_))
             (dk-split-all!)
             (fact 'restrict-in-fun 'fqf_ '(PTS s) '(PTS t) 'aqa_)
             (ass))
            (#t
             (let ((e (dk-di-var!)))
               (mac-h 'IS-CONTINUOUS (list 'IS-CONTINUOUS 's 't 'fqf_))
               (dk-split-all!)
               (fact 'subset-mem-fwd 'aqa_ '(PTS s) e)
               (dk-apply! (dk-pick (lambda (h) (and (pair? h) (eq? (car h) 'FORALL)
                                                    (dk-contains? h 'IS-CONTINUOUS-AT)))
                                   "the pointwise continuity universal")
                          e)
               (fact 'restrict-continuous-at 's 'aqa_ 't 'fqf_ e)
               (ass)))))))))
  ;; the citation names PTS(SUBSPACE-MS(s,A)); rewrite it to A IN THE LANDING,
  ;; not in the goal (a goal-side `subst' of A would reach A inside the
  ;; subspace term itself).
  (let ((cc (dk-fact! 'compact-image cim-ssub 't cim-rst)))
    (mac-h 'subspace-pts cc)
    (fact 'image-restrict 'aqa_ 'fqf_)
    (subst (list '= '(IMAGE fqf_ aqa_) (list 'IMAGE cim-rst 'aqa_)))
    (ass)))
(qed 'continuous-image-of-compact)
(topic! 'continuous-image-of-compact 'topology)
(alias! 'continuous-image-of-compact
        "Proposition 3.19"
        "the continuous image of a compact subset is compact")

;;; =====================================================================
;;; (7) THE TRACE OF A PATH IS COMPACT.
;;;     complex-analysis.pdf 3.1.1: "gamma_* is sometimes called the TRACE of
;;;     gamma.  It is always a compact set."
;;;
;;; TRACE(gamma, a, b) is IMAGE(gamma, CCINT(a, b)), and IS-PATH's continuity
;;; conjunct is continuity AT each point of the closed interval AS A SUBSPACE of
;;; RR-MS -- exactly the hypothesis `compact-image' wants at
;;; s = SUBSPACE-MS(RR-MS, CCINT(a,b)), whose compactness is `heine-borel-ccint'.
;;; =====================================================================
(define cim-icc '(CCINT av_ bv_))
(define cim-isub (list 'SUBSPACE-MS 'RR-MS cim-icc))

(sp (make-wff '(FORALL pgam (FORALL av_ (FORALL bv_
     (IMPLIES (IS-PATH pgam av_ bv_)
       (IS-COMPACT (SUBSPACE-MS CC-MS (TRACE pgam av_ bv_))))))))) 
(dk-peel!)
(dk-split-all! (list (dk-fact! 'is-path-endpoints 'pgam 'av_ 'bv_)))
(fact 'is-path-in-fun 'pgam 'av_ 'bv_)
(define cim-pcont (dk-fact! 'is-path-continuous 'pgam 'av_ 'bv_))
(fact 'rr-is-metric-space)
(fact 'cc-is-metric-space)
(dk-have! (list 'SUBSET cim-icc '(PTS RR-MS))
  (lambda () (slot 'PTS) (fact 'ccint-subset-rr 'av_ 'bv_) (ass)))
(fact 'subspace-is-metric-space 'RR-MS cim-icc)
(fact 'heine-borel-ccint 'av_ 'bv_)
(have! (list 'IS-CONTINUOUS cim-isub 'CC-MS 'pgam)
  (lambda ()
    (mac 'IS-CONTINUOUS)
    (mac 'subspace-pts)
    (cim-and!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
          ((eq? (cim-head g) 'IS-METRIC-SPACE) (ass))
          ((eq? (cim-head g) 'IN) (slot 'PTS) (ass))
          (#t
           (let ((e (dk-di-var!)))
             (dk-apply! cim-pcont e)
             (ass)))))))))
(let ((cc (dk-fact! 'compact-image cim-isub 'CC-MS 'pgam)))
  (mac-h 'subspace-pts cc)
  (mac 'TRACE)
  (ass))
(qed 'path-trace-compact)
(topic! 'path-trace-compact 'topology)
(alias! 'path-trace-compact
        "the trace of a path is a compact set")
