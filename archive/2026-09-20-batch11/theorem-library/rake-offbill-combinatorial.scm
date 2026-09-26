;;; theorem-library/rake-offbill-combinatorial.scm
;;; ====================================================================
;;; Batch 8-D: the off-bill `combinatorial' PSS entries that batch 6/7 made
;;; cheap.  Three theorems, in dependency order:
;;;
;;;   tb-block-step             theorem-library/cauchy-subsequence.scm:208
;;;   tb-has-eps-cauchy-subseq  theorem-library/cauchy-subsequence.scm:173
;;;   block-family              theorem-library/cauchy-subsequence.scm:278
;;;
;;; Each statement is copied LITERALLY from its support site.
;;;
;;; WHY THEY ARE NOW SHORT.  Every one of the three was asserted as "the
;;; pigeonhole construction", and the pigeonhole is no longer theirs: it is
;;; `cover-block-step' (proven, theorem-library/rake-tb-leaves.scm) and
;;; `block-family-combinatorial' (proven, theorem-library/block-family-
;;; combinatorial-proof.scm), both stated with the metric abstracted away as
;;; a FINITE COVER.  The bridge from total boundedness to those covers is
;;; `tb-rad-ball-cover' (proven, theorem-library/rake-tb-leaves-2.scm).  So
;;; all three reduce to: manufacture the cover, cite the combinatorial
;;; theorem, read the cover member back as a ball.
;;;
;;; THE ONE DEVICE WORTH NAMING.  tb-rad-ball-cover is stated for a SEQUENCE
;;; of radii; tb-block-step wants ONE radius.  Rather than rebuild the
;;; net-to-cover construction at a single radius (that is ~150 lines in
;;; rake-tb-leaves-2.scm), the sequence is taken CONSTANT:
;;;
;;;     rad := (VNB-LAMBDA kv_ NN r)
;;;
;;; and the level-0 cover is used.  Its positivity hypothesis is one `di' +
;;; `lam-b' + `ass'; the ball equation the cover clause returns carries the
;;; unreduced redex `((VNB-LAMBDA kv_ NN r) 0)', which `lam-b-h' collapses to
;;; `r' -- the argument 0 is typed by `nn-zero-in' BEFORE the reduction.
;;; The lambda's binder is `kv_', a name no predicate body in the citations
;;; binds (CLAUDE.md: a driver-built lambda whose binder collides is renamed
;;; by subst-free and every later `equal?' lookup silently misses).
;;;
;;; LOAD WINDOW.  lo = the slot right after theorem-library/subsequence-principle
;;; (load.scm line 1532), which proves `fun-codomain-subset' -- the LATEST of the
;;; citations.  The others, in descending order of load.scm line:
;;; block-family-combinatorial-proof 1381, rake-tb-leaves-2 1364
;;; (tb-rad-ball-cover), rake-tb-leaves 1361 (cover-block-step), rake-nn-enum
;;; 1358 (nn-enum-spec), rake-balls 1324 (ball-2r-triangle), nn-infinite 1223
;;; (nn-in-inf-subsets), rake-analysis2 848 (subseq-is-fun), rr-halving 786
;;; (rr-pos-halvable, through dk-halve!), fun-apply-type-proof 646
;;; (fun-apply-type-c), cauchy-subsequence 357 (the definitions SUBSEQ /
;;; STRICTLY-MONO-NN / IS-EPS-CAUCHY-SEQ / NULL-RR-SEQ), block-family-
;;; combinatorial (IS-FINITE-COVER), metric-topology (TOTALLY-BOUNDED, BALL),
;;; number-systems (nn-zero-in).
;;; hi = end: NO proof in the tree cites any of the three (window.py reports
;;; theorem-library/cauchy-subsequence as a citer, but that is the support
;;; DECLARATION, which the integrator retires).  The free slot immediately
;;; after "theorem-library/subsequence-principle" is what this file wants.
;;; No late tactic: `subst', `mac', `lam-b(-h)' and the dk- kit only -- no
;;; contra / prep / ineq-supply.
;;;
;;; DO NOT COMPILE THIS FILE: it uses the top-level macro `bc*' (CLAUDE.md,
;;; "COMPILE THE TREE FIRST").
;;;
;;; Helper prefix: r9d-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r9d-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-offbill-combinatorial: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (wff-formula (sequent-node-assertion l))))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (sequent-node-assumptions l)))
                  (proof-open-goals *ps*))
        (error "rake-offbill-combinatorial: unfinished proof" name))))

;;; FORM is what `dk-fact!' returned.  If `fact' could not detach an
;;; antecedent it hands back the IMPLIES; prove the antecedent with THUNK (or
;;; skip the `have!' when it is already in context -- CLAUDE.md: a `have!' of
;;; a formula already in context is a silent self-loop) and detach.
(define (r9d-detach! form thunk)
  (if (and (pair? form) (eq? (car form) 'IMPLIES))
      (begin
        (if (not (member (cadr form) (dk-asms)))
            (have! (cadr form) thunk))
        (r9d-detach! (dk-landed-1 (lambda () (detach! form))) thunk))
      form))

(define (r9d-typed? cls)
  (lambda (fm) (and (pair? fm) (eq? (car fm) 'IN) (equal? (caddr fm) cls))))

;;; the context assumption that CONTAINS the symbol SYM (used only to tell the
;;; two universals tb-rad-ball-cover lands apart -- one mentions
;;; IS-FINITE-COVER, the other BALL)
(define (r9d-mentions? sym)
  (lambda (fm) (dk-contains? fm sym)))

;;; close every open leaf whose goal is already in its own context (`lam-b'
;;; posts the argument typing as a leaf even when the typing is in context)
(define (r9d-sweep!)
  (let loop ()
    (let ((hit #f))
      (for-each
       (lambda (nd)
         (if (and (not hit) (member (dk-goal-of nd) (dk-asms-of nd)))
             (begin (set! hit #t) (dk-focus! nd) (ass))))
       (proof-leaves))
      (if hit (loop)))))

;;; =====================================================================
;;; 1.  tb-block-step -- THE SUPPORT, stated literally
;;;     (theorem-library/cauchy-subsequence.scm:208).
;;;
;;;   TOTALLY-BOUNDED s, f : NN -> PTS(s), r > 0, J an infinite block
;;;     ==> an infinite J_ subset J and a centre c in PTS(s) with
;;;         f(i) in BALL(s, c, r) for every i in J_.
;;;
;;; = cover-block-step at the level-0 cover of the CONSTANT radius sequence.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (PTS s)))
           (FORALL r
             (IMPLIES (POS-RR r)
               (FORALL J
                 (IMPLIES (IN J (INF-SUBSETS NN))
                   (FORSOME J_
                     (AND (IN J_ (INF-SUBSETS NN))
                     (AND (SUBSET J_ J)
                          (FORSOME c
                            (AND (IN c (PTS s))
                                 (FORALL i
                                   (IMPLIES (IN i J_)
                                     (IN (f i) (BALL s c r)))))))))))))))))))

(dk-peel!)

(define r9d-1-s (cadr (dk-pick (dk-head? 'TOTALLY-BOUNDED) "the totally bounded space")))
(define r9d-1-J (cadr (dk-pick (r9d-typed? '(INF-SUBSETS NN)) "the index block J")))
(define r9d-1-f (cadr (dk-pick (r9d-typed? (list 'FUN 'NN (list 'PTS r9d-1-s))) "the sequence f")))
(define r9d-1-r (cadr (dk-pick (dk-head? 'POS-RR) "the radius r")))
(define r9d-1-PTS (list 'PTS r9d-1-s))

;; 0 in NN -- the level at which the constant cover is read, and the LUTINS
;; certificate for every instantiation at it.
(fact 'nn-zero-in)

;; the constant radius sequence
(define r9d-1-rad (list 'VNB-LAMBDA 'kv_ 'NN r9d-1-r))

(define r9d-1-cover
  (r9d-detach! (dk-fact! 'tb-rad-ball-cover r9d-1-s r9d-1-rad)
               (lambda ()                       ; forall k in NN.  rad(k) > 0
                 (dk-di-var!)
                 (lam-b)                         ; (POS-RR r), plus the owed (IN k NN)
                 (r9d-sweep!))))

(dk-split! r9d-1-cover)                          ; (IN (PTS s) SET) + the existential
(define r9d-1-cov (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the cover existential")))

(define r9d-1-Ucov (dk-pick (r9d-mentions? 'IS-FINITE-COVER) "the finite-cover clause"))
(define r9d-1-Uball (dk-pick (r9d-mentions? 'BALL) "the ball-membership clause"))

(define r9d-1-C (list r9d-1-cov 0))
(dk-apply! r9d-1-Ucov 0)                         ; IS-FINITE-COVER (cov 0) (PTS s)

;; (cov 0) is an APPLICATION of an untyped variable, so it is not certified
;; DEFINED; the sethood conjunct of IS-FINITE-COVER supplies the typing, in a
;; `have!' lane because `mac-h' REPLACES what it unfolds.
(have! (list 'IN r9d-1-C 'SET)
       (lambda ()
         (dk-split-all!
          (dk-landed (lambda ()
                       (mac-h 'IS-FINITE-COVER
                              (list 'IS-FINITE-COVER r9d-1-C r9d-1-PTS)))))
         (ass)))

(define r9d-1-Jx
  (dk-skolem! (dk-fact! 'cover-block-step r9d-1-PTS r9d-1-f r9d-1-C r9d-1-J)))
(define r9d-1-U (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the cover member")))
(define r9d-1-capture
  (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm r9d-1-U)))
           "the capture universal"))

(define r9d-1-c
  (dk-skolem! (dk-apply! (dk-apply! r9d-1-Uball 0) r9d-1-U)))
(define r9d-1-eq
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) '=) (equal? (cadr fm) r9d-1-U)))
           "the ball equation for U"))
(lam-b-h r9d-1-eq)                               ; U = BALL(s, c, r)
(define r9d-1-ball (list 'BALL r9d-1-s r9d-1-c r9d-1-r))

(ew r9d-1-Jx)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (memq (car g) '(IN SUBSET))
         (ass)
         (begin                                  ; FORSOME c. c in PTS(s) and ...
           (ew r9d-1-c)
           (dk-conj-close!
            (lambda ()
              (if (eq? (car (dk-goal)) 'IN)
                  (ass)
                  (let ((iv (dk-di-var!)))
                    (subst (list '= r9d-1-ball r9d-1-U))
                    (dk-apply! r9d-1-capture iv)
                    (ass))))))))))

(r9d-qed! 'tb-block-step)
(topic! 'tb-block-step 'combinatorial)

;;; =====================================================================
;;; 2.  tb-has-eps-cauchy-subseq -- THE SUPPORT, stated literally
;;;     (theorem-library/cauchy-subsequence.scm:173).
;;;
;;;   TOTALLY-BOUNDED s, f : NN -> PTS(s), eps > 0
;;;     ==> a strictly monotone phi with SUBSEQ(f, phi) eps-Cauchy.
;;;
;;; tb-block-step at radius eps/2 and block NN, then NN-ENUM of the block
;;; (nn-enum-spec) as the reindexing, then ball-2r-triangle: two terms of one
;;; (eps/2)-ball are within eps/2 + eps/2 = eps.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (PTS s)))
           (FORALL eps
             (IMPLIES (POS-RR eps)
               (FORSOME phi
                 (AND (STRICTLY-MONO-NN phi)
                      (IS-EPS-CAUCHY-SEQ s eps (SUBSEQ f phi))))))))))))

(dk-peel!)

(define r9d-2-s (cadr (dk-pick (dk-head? 'TOTALLY-BOUNDED) "the totally bounded space")))
(define r9d-2-f (cadr (dk-pick (r9d-typed? (list 'FUN 'NN (list 'PTS r9d-2-s))) "the sequence f")))
(define r9d-2-eps (cadr (dk-pick (dk-head? 'POS-RR) "the radius eps")))

(have! (list 'IS-METRIC-SPACE r9d-2-s)
       (lambda ()
         (dk-split-all!
          (dk-landed (lambda () (mac-h 'TOTALLY-BOUNDED (list 'TOTALLY-BOUNDED r9d-2-s)))))
         (ass)))

;; d = eps/2:  (POS-RR d) (= (+ d d) eps) (IN d RR) (< 0 d)
(define r9d-2-d (dk-halve! r9d-2-eps))

;; the block: all of NN, refined once at radius d
(fact 'nn-in-inf-subsets)
(define r9d-2-Jx
  (dk-skolem! (dk-fact! 'tb-block-step r9d-2-s r9d-2-f r9d-2-d 'NN)))
(define r9d-2-c
  (dk-skolem! (dk-pick (lambda (fm) (and ((dk-head? 'FORSOME) fm) (dk-contains? fm 'BALL)))
                       "the centre existential")))
(define r9d-2-ball (list 'BALL r9d-2-s r9d-2-c r9d-2-d))
(define r9d-2-capture
  (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm r9d-2-ball)))
           "the capture universal"))

;; phi = NN-ENUM(J_).  nn-enum-spec FIRST: it is the typing that certifies the
;; CHOICE term for every later instantiation (CLAUDE.md, the LUTINS rule).
(define r9d-2-phi (list 'NN-ENUM r9d-2-Jx))
(dk-split-all! (dk-landed (lambda () (fact 'nn-enum-spec r9d-2-Jx))))
(fact 'fun-codomain-subset r9d-2-phi 'NN r9d-2-Jx 'NN)
(have! (list 'STRICTLY-MONO-NN r9d-2-phi)
       (lambda () (mac 'STRICTLY-MONO-NN) (from-context!)))

;; the verbose positivity spelling ball-2r-triangle is guarded on
(define r9d-2-dpos
  (list 'AND (list 'IN r9d-2-d 'RR)
        (list 'AND (list '<= 0 r9d-2-d) (list 'NOT (list '= 0 r9d-2-d)))))
(have! r9d-2-dpos
       (lambda () (mac-h 'POS-RR (list 'POS-RR r9d-2-d)) (ass)))

(ew r9d-2-phi)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
       (ass)
       (begin
         (mac 'IS-EPS-CAUCHY-SEQ)
         (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond
                ((eq? (car g) 'IS-METRIC-SPACE) (ass))
                ((eq? (car g) 'IN) (bc* 'subseq-is-fun) (di) (ass-all))
                (#t
                 ;; `di' peels the two index binders in one or two steps
                 ;; depending on the guard shape: read m and n_ off the GOAL,
                 ;; never off a landing count.
                 (dk-peel!)
                 (let* ((gdist (cadr (dk-goal)))     ; ((DIST s) SUBSEQ(m), SUBSEQ(n_))
                        (mv (cadr (cadr gdist)))
                        (nv (cadr (caddr gdist)))
                        (ym (list r9d-2-f (list r9d-2-phi mv)))
                        (yn (list r9d-2-f (list r9d-2-phi nv))))
                   ;; the two indices land in J_, hence the two terms in the ball
                   (fact 'fun-apply-type-c r9d-2-phi 'NN r9d-2-Jx mv)
                   (fact 'fun-apply-type-c r9d-2-phi 'NN r9d-2-Jx nv)
                   (dk-apply! r9d-2-capture (list r9d-2-phi mv))
                   (dk-apply! r9d-2-capture (list r9d-2-phi nv))
                   (dk-split! (dk-fact! 'ball-2r-triangle
                                        r9d-2-s r9d-2-c r9d-2-d ym yn))
                   ;; SUBSEQ(f,phi)(m) = f(phi m), at indices already typed
                   (mac 'SUBSEQ)
                   (lam-b)
                   (r9d-sweep!)
                   (dk-focus! (or (any-pred (lambda (nd) (eq? (car (dk-goal-of nd)) '<=))
                                            (proof-leaves))
                                  (error "tb-has-eps-cauchy-subseq: no estimate leaf")))
                   (subst (list '= r9d-2-eps (list '+ r9d-2-d r9d-2-d)))
                   (ass)))))))))))

(r9d-qed! 'tb-has-eps-cauchy-subseq)
(topic! 'tb-has-eps-cauchy-subseq 'combinatorial)

;;; =====================================================================
;;; 3.  block-family -- THE SUPPORT, stated literally
;;;     (theorem-library/cauchy-subsequence.scm:278).
;;;
;;;   TOTALLY-BOUNDED s, f : NN -> PTS(s), rad a positive null sequence
;;;     ==> a nested family blk of infinite blocks, blk(k) pinning f into a
;;;         single rad(k)-ball.
;;;
;;; = block-family-combinatorial at the ball covers tb-rad-ball-cover builds.
;;; The metric re-enters only in the last three lines, where the captured
;;; cover MEMBER is rewritten into the ball it equals.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (IMPLIES (TOTALLY-BOUNDED s)
       (FORALL f
         (IMPLIES (IN f (FUN NN (PTS s)))
           (FORALL rad
             (IMPLIES (NULL-RR-SEQ rad)
               (FORSOME blk
                 (AND (IN blk (FUN NN (INF-SUBSETS NN)))
                 (AND (FORALL k
                        (IMPLIES (IN k NN) (SUBSET (blk (succ k)) (blk k))))
                      (FORALL k
                        (IMPLIES (IN k NN)
                          (FORSOME c
                            (AND (IN c (PTS s))
                                 (FORALL i
                                   (IMPLIES (IN i (blk k))
                                     (IN (f i) (BALL s c (rad k))))))))))))))))))))

(dk-peel!)

(define r9d-3-s (cadr (dk-pick (dk-head? 'TOTALLY-BOUNDED) "the totally bounded space")))
(define r9d-3-f (cadr (dk-pick (r9d-typed? (list 'FUN 'NN (list 'PTS r9d-3-s))) "the sequence f")))
(define r9d-3-rad (cadr (dk-pick (dk-head? 'NULL-RR-SEQ) "the radius sequence")))
(define r9d-3-PTS (list 'PTS r9d-3-s))

;; the pointwise positivity of rad is a conjunct of NULL-RR-SEQ, and is what
;; tb-rad-ball-cover is guarded on
(dk-split-all!
 (dk-landed (lambda () (mac-h 'NULL-RR-SEQ (list 'NULL-RR-SEQ r9d-3-rad)))))

(define r9d-3-cover
  (r9d-detach! (dk-fact! 'tb-rad-ball-cover r9d-3-s r9d-3-rad)
               (lambda () (ass))))
(dk-split! r9d-3-cover)
(define r9d-3-cov (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the cover existential")))
(define r9d-3-Uball (dk-pick (r9d-mentions? 'BALL) "the ball-membership clause"))

(define r9d-3-blk
  (dk-skolem! (dk-fact! 'block-family-combinatorial r9d-3-PTS r9d-3-f r9d-3-cov)))
(define r9d-3-capture
  (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm r9d-3-cov)
                             (dk-contains? fm r9d-3-blk)))
           "the capture universal"))

(ew r9d-3-blk)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'IN) (ass))
       ((dk-contains? g 'SUBSET) (ass))
       (#t
        (let* ((kv   (dk-di-var!))
               (uv   (dk-skolem! (dk-apply! r9d-3-capture kv)))
               (icap (dk-pick (lambda (fm) (and ((dk-head? 'FORALL) fm) (dk-contains? fm uv)))
                              "the block capture at this level"))
               (cv   (dk-skolem! (dk-apply! (dk-apply! r9d-3-Uball kv) uv)))
               (ball (list 'BALL r9d-3-s cv (list r9d-3-rad kv))))
          (ew cv)
          (dk-conj-close!
           (lambda ()
             (if (eq? (car (dk-goal)) 'IN)
                 (ass)
                 (let ((iv (dk-di-var!)))
                   (subst (list '= ball uv))
                   (dk-apply! icap iv)
                   (ass)))))))))))

(r9d-qed! 'block-family)
(topic! 'block-family 'combinatorial)
