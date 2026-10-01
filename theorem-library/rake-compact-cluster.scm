;;; rake-compact-cluster.scm -- a compact metric space is sequentially compact.
;;;
;;;     compact-seq-has-cluster:
;;;       forall s, f.  IS-COMPACT s and f in FUN(NN, PTS s)  =>
;;;                     forsome x. CLUSTER-POINT(s, f, x)
;;;
;;; Statement UNCHANGED from the support it retires
;;; (structure-library/compactness.scm:193, warranted `reference' --
;;; calculus.pdf Prop 3.12 (1)=>(3)).  It is the SINGLE remaining leaf on the
;;; bill of compact-implies-complete (calculus/compact-complete-proof.scm).
;;;
;;; THE ROUTE (the choice-free open-cover argument; see the closing block for
;;; why the shorter-looking routes are circular).  Suppose no point is a
;;; cluster point.  The cover is the SET
;;;
;;;     COV = { u in POWER(PTS s) | IS-OPEN s u  and
;;;             forsome m in NN. forall n in NN. m <= n => f(n) not in u }
;;;
;;; -- the open sets the sequence ABANDONS, each carrying its own abandonment
;;; index.  Nothing has to be recovered from a member later: the index is read
;;; off the member's own defining property, so no centre and no radius is
;;; stored and NO CHOICE of a pair is needed to build the cover.  (This is the
;;; ptwise-cauchy-unif.scm pattern, whose driver this one follows step for
;;; step; batch 6 had estimated 400 lines for a pair-valued-choice version.)
;;;
;;;   COV IS AN OPEN COVER.  Members are open by construction and lie in
;;;   POWER(PTS s), so the union is inside PTS s.  Conversely let v in PTS s.
;;;   v is not a cluster point, so v ESCAPES:
;;;       eps > 0,  m in NN,  forall n in NN. not (m <= n and d(f n, v) < eps).
;;;   That is r8g-escape!, and it is the one place the driver had to do a
;;;   negation by hand: `push-not-h' REFUSES the CLUSTER-POINT tail, whose
;;;   FORALL eps hides a second universal (see r8g-esc-inner's comment).
;;;   Then BALL(s, v, eps) is in COV: open (ball-is-open), a subset of PTS s,
;;;   and abandoned from m on -- for n >= m a point f(n) of the ball would give
;;;   d(v, f n) < eps, hence d(f n, v) < eps by metric-sym, contradicting the
;;;   line above.  And v is in that ball (metric-self-zero).
;;;
;;;   THE FINITE SUBCOVER.  IS-COMPACT at COV gives SUB subset COV with
;;;   CARD SUB in NN and IS-OPEN-COVER s SUB; SUB is a set
;;;   (subclass-of-set-is-set, COV being a SEP over the set POWER(PTS s)).
;;;
;;;   THE MAX.  For u in SUB the abandonment indices are
;;;   CAPS(u) = { m in NN | forall n in NN. m <= n => f(n) not in u };
;;;   CHOICE picks one and the choice is sound because u in COV exhibits a
;;;   member (choose!, driver-kit).  THR = IMAGE(u |-> CHOICE(CAPS u), SUB) is
;;;   finite (card-image-finite) and a subset of NN, so nn-finite-subset-bounded
;;;   gives N in NN with N <= y => y not in THR, and every chosen index w
;;;   satisfies w <= N (rr-leq-total, the other branch refuted by `prop').
;;;
;;;   THE CONTRADICTION.  f(N) lies in PTS s, hence in some u in SUB
;;;   (open-cover-covers-point); u's chosen index w satisfies w <= N, so u is
;;;   abandoned at N -- f(N) not in u.  That is the contradiction, and `prop'
;;;   closes the (unchanged) existential goal.
;;;
;;; CITATIONS and load positions (0-based over prover-load, 2026-09-19):
;;;   class-extensionality, choice-axiom, subset-def, power-set,
;;;   power-set-membership, rr-leq-total  -- library.scm / number-systems
;;;   (primitive); image-membership-iff (structure-library/injection, 98);
;;;   cluster-point, is-compact, is-open-cover (structure-library/compactness,
;;;   62); is-metric-space, is-open, pos-rr, `<' (early); fun-apply-type-c
;;;   (163); nn-in-rr (nn-order-basics, 188); subclass-of-set-is-set,
;;;   subset-mem-fwd (subset-lemmas, 215); card-image-finite (287);
;;;   nn-finite-subset-bounded (302); ball-sep-unfold, open-cover-covers-point
;;;   (ball-cover-lemmas, 317); metric-sym, metric-self-zero
;;;   (structure-library/metric-laws, 326); ball-is-open
;;;   (theorem-library/ball-is-open, TODAY AT 351 -- see the window below).
;;;
;;; LOAD WINDOW.  hi = 328, calculus/compact-complete-proof.scm, the only citer
;;; of compact-seq-has-cluster in the tree.  lo = 326 (metric-laws) for
;;; everything EXCEPT ball-is-open, which sits at 351 although its own latest
;;; citation is metric-triangle (326).  So the integrator must first MOVE
;;; theorem-library/ball-is-open.scm up to just after structure-library/
;;; metric-laws (its window is [327, 353), its only citer being
;;; ptwise-cauchy-unif at 353), and then load THIS file after it.  The
;;; resulting order is
;;;     326 structure-library/metric-laws
;;;         theorem-library/ball-is-open          (moved up from 351)
;;;         theorem-library/rake-compact-complete (was 327)
;;;         theorem-library/rake-compact-cluster  (this file)
;;;         calculus/compact-complete-proof       (was 328)
;;; The alternative -- moving calculus/compact-complete-proof.scm DOWN past
;;; ball-is-open -- also works: nothing in the tree cites the theorem it
;;; installs, compact-implies-complete, except pss-topics far below.
;;;
;;; Helper prefix: r8g-.

;;; --- statement (copied from the support's definition site) ----------------

(define r8g-stmt
  '(FORALL s (FORALL f
     (IMPLIES (AND (IS-COMPACT s) (IN f (FUN NN (PTS s))))
              (FORSOME x (CLUSTER-POINT s f x))))))

;;; --- file-local helpers ---------------------------------------------------

(define (r8g-head? fm h) (and (pair? fm) (eq? (car fm) h)))

(define (r8g-mentions? fm sym)
  (let loop ((e fm))
    (cond ((eq? e sym) #t)
          ((pair? e) (or (loop (car e)) (loop (cdr e))))
          (#t #f))))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (r8g-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit))
            (dk-opened thunk)))

;; P(u, m): the sequence SQ is out of u from index m on.
(define (r8g-P sq u m)
  (list 'FORALL 'n_
        (list 'IMPLIES (list 'AND (list 'IN 'n_ 'NN) (list '<= m 'n_))
              (list 'NOT (list 'IN (list sq 'n_) u)))))

;; "u is abandoned by SQ"
(define (r8g-missed sq u)
  (list 'FORSOME 'm_ (list 'AND (list 'IN 'm_ 'NN) (r8g-P sq u 'm_))))

;; the cover: the open subsets of PTS s that SQ abandons
(define (r8g-cover sv sq)
  (list 'SEP 'u_ (list 'POWER (list 'PTS sv))
        (list 'AND (list 'IS-OPEN sv 'u_) (r8g-missed sq 'u_))))

;; the abandonment indices of u
(define (r8g-caps sq u) (list 'SEP 'm_ 'NN (r8g-P sq u 'm_)))

;;; The ESCAPE existential of a point v that is NOT a cluster point:
;;;   forsome eps > 0. forsome m in NN. forall n in NN. not (m <= n and
;;;                                                         d(f n, v) < eps).
;;; `push-not-h' will NOT produce it: the CLUSTER-POINT tail is
;;; `forall eps (implies (pos-rr eps) (forall m ...))' and the tactic refuses a
;;; FORALL whose body hides a second universal ("`di' would peel past it"), so
;;; the three alternations are done by hand below (r8g-escape!).
(define (r8g-esc-inner sv sq v ev mv)
  (list 'FORALL 'n_
        (list 'IMPLIES (list 'IN 'n_ 'NN)
              (list 'NOT (list 'AND (list '<= mv 'n_)
                               (list '< (list (list 'DIST sv) (list sq 'n_) v) ev))))))

(define (r8g-esc2 sv sq v ev)
  (list 'FORSOME 'mq_
        (list 'AND (list 'IN 'mq_ 'NN) (r8g-esc-inner sv sq v ev 'mq_))))

(define (r8g-esc sv sq v)
  (list 'FORSOME 'ep_
        (list 'AND (list 'POS-RR 'ep_) (r8g-esc2 sv sq v 'ep_))))

;; (IN d RR), (<= 0 d), (NOT (= 0 d)) and their conjunction, off (POS-RR d),
;; which stays in context (mac-h in a lane -- it REPLACES otherwise).
(define (r8g-pos-atoms! d)
  (let ((conj (list 'AND (list 'IN d 'RR)
                    (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))))
    (dk-have! conj (lambda () (mac-h 'pos-rr (list 'POS-RR d)) (ass)))
    (dk-split-all! (list conj))            ; `ai' REMOVES the conjunction ...
    (have! conj)))                         ; ... and ball-is-open wants it whole

;; (IN z (BALL s c r)) in context: open it to its SEP atoms through the PROVEN
;; unfold equation ball-sep-unfold, not through the support ball-membership.
(define (r8g-open-ball-h! mem)
  (let ((sm (dk-landed-1 (lambda () (mac-h 'ball-sep-unfold mem)))))
    (dk-split-all! (dk-landed (lambda () (sep-me sm))))))

;;; --- the cover is an open cover -------------------------------------------

;; goal (IN v (PTS s)), context (IN v BU): v is in some member, a subset of PTS s.
(define (r8g-bu-in-pts! sv v bu cov)
  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN v bu)))))
         (memC (dk-pick (lambda (fm) (and (r8g-head? fm 'IN) (equal? (caddr fm) cov)
                                          (member fm landed)))
                        "the landed member-of-cover"))
         (e (cadr memC)))
    (dk-split-all! (dk-landed (lambda () (sep-me memC))))
    (let ((pw (dk-pick (lambda (fm) (and (r8g-head? fm 'IN) (eq? (cadr fm) e)
                                         (r8g-head? (caddr fm) 'POWER)))
                       "the member in POWER(PTS s)")))
      (dk-split-all! (dk-landed (lambda () (mac-h 'power-set-membership pw))))
      (let ((incl (dk-pick (lambda (fm) (and (r8g-head? fm 'FORALL)
                                             (r8g-mentions? fm e)
                                             (r8g-mentions? fm 'PTS)))
                           "the inclusion universal")))
        (dk-apply! incl v)
        (ass)))))

;; goal (IN v (BALL s v eps)) -- the centre is in its own ball.
(define (r8g-centre-in-ball! sv v)
  (dk-fact! 'metric-self-zero sv v)
  (mac 'ball-sep-unfold)
  (r8g-each-leaf!
   (lambda () (sep-mi))
   (lambda ()
     (if (r8g-head? (dk-goal) 'AND)
         (begin (subst (list '= (list (list 'DIST sv) v v) 0)) (dk-conj-close!))
         (ass)))))

;; goal P(ball, mv): the ball about v is abandoned from mv on.
(define (r8g-tail-misses! sv sq v epsv ball mv ntail)
  (let ((landed (dk-peel!)))
    (dk-split-all! landed)
    (let* ((g   (dk-goal))                      ; (NOT (IN (sq n) ball))
           (mem (cadr g))
           (nv  (cadr (cadr mem))))
      (di)                                      ; assume mem; goal FALSITY
      (r8g-open-ball-h! mem)
      (let* ((fn  (list sq nv))
             (dvn (list (list 'DIST sv) v fn))
             (dnv (list (list 'DIST sv) fn v)))
        (dk-fact! 'metric-sym sv fn v)          ; (= dnv dvn)
        (have! (list '< dnv epsv)
          (lambda () (subst (list '= dnv dvn)) (mac '<) (dk-conj-close!)))
        (let ((inst (dk-apply! ntail nv)))      ; (NOT (AND (<= mv nv) (< dnv epsv)))
          (dk-only! inst (list '<= mv nv) (list '< dnv epsv))
          (prop))))))

;; goal (IN ball COV): sep-mi, then the three obligations.
(define (r8g-ball-in-cover! sv sq v epsv ball cov mv ntail)
  (r8g-each-leaf!
   (lambda () (sep-mi))
   (lambda ()
     (let ((g (dk-goal)))
       (if (r8g-head? (caddr g) 'POWER)             ; (IN ball (POWER (PTS s)))
           (begin
             (mac 'power-set-membership)
             (dk-conj-close!
              (lambda ()
                (if (r8g-head? (dk-goal) 'FORALL)
                    (let ((mem (car (dk-peel!))))
                      (r8g-open-ball-h! mem)
                      (ass))
                    (begin (mac 'ball-sep-unfold) (sep-set) (ass))))))
           ;; (AND (IS-OPEN s ball) (FORSOME m_ ...))
           (r8g-each-leaf!
            (lambda () (di))
            (lambda ()
              (let ((g2 (dk-goal)))
                (cond ((r8g-head? g2 'IS-OPEN)
                       (fact 'ball-is-open sv v epsv) (ass))
                      ((r8g-head? g2 'FORSOME)
                       (ew mv)
                       (r8g-each-leaf!
                        (lambda () (di))
                        (lambda ()
                          (if (r8g-head? (dk-goal) 'IN)
                              (ass)
                              (r8g-tail-misses! sv sq v epsv ball mv ntail)))))
                      (#t (error "r8g-ball-in-cover!: unexpected goal"
                                 (expression->string g2))))))))))))

;; goal FALSITY, with (NOT ee) and the two eigenvariables of the peeled
;; CLUSTER-POINT tail in context: rebuild the escape existential at them.
(define (r8g-cluster-tail! sv sq v ee notee)
  (let* ((landed (dk-peel!))
         (posf (dk-pick (lambda (fm) (and (r8g-head? fm 'POS-RR) (member fm landed)))
                        "the eps guard"))
         (ev   (cadr posf))
         (mf   (dk-pick (lambda (fm) (and (r8g-head? fm 'IN) (eq? (caddr fm) 'NN)
                                          (member fm landed)))
                        "the index guard"))
         (mvv  (cadr mf))
         (notg (dk-landed-1 (lambda () (pbc)))))     ; goal FALSITY
    (have! ee
      (lambda ()
        (ew ev)
        (r8g-each-leaf!
         (lambda () (di))
         (lambda ()
           (if (r8g-head? (dk-goal) 'POS-RR)
               (ass)
               (begin
                 (ew mvv)
                 (r8g-each-leaf!
                  (lambda () (di))
                  (lambda ()
                    (if (r8g-head? (dk-goal) 'IN)
                        (ass)
                        (let* ((ld (dk-peel!))
                               (nv (cadr (car ld))))
                          (di)                       ; assume the AND; goal FALSITY
                          (have! (cadr notg) (lambda () (ew nv) (prop)))
                          (ai notg)))))))))))
    (ai notee)))

;; (NOT (CLUSTER-POINT s sq v)) in context, with the three typing conjuncts:
;; land and return the escape existential.
(define (r8g-escape! sv sq v notcl)
  (let ((ee (r8g-esc sv sq v)))
    (have! ee
      (lambda ()
        (let ((notee (dk-landed-1 (lambda () (pbc)))))   ; goal FALSITY
          (have! (list 'CLUSTER-POINT sv sq v)
            (lambda ()
              (mac 'cluster-point)
              (dk-conj-close!
               (lambda ()
                 (if (r8g-head? (dk-goal) 'FORALL)
                     (r8g-cluster-tail! sv sq v ee notee)
                     (ass))))))
          (ai notcl))))
    ee))

;; goal (IN v BU), context (IN v (PTS s)): v is not a cluster point, so the
;; ball it abandons is a member of the cover containing v.
(define (r8g-pts-in-bu! sv sq v bu cov ncl)
  (let* ((notcl (dk-apply! ncl v))                ; (NOT (CLUSTER-POINT s sq v))
         (ee    (r8g-escape! sv sq v notcl))
         (epsv  (dk-skolem! ee))
         (ex2   (dk-pick (lambda (fm) (equal? fm (r8g-esc2 sv sq v epsv)))
                         "the index existential"))
         (mv    (dk-skolem! ex2))
         (ntail (dk-pick (lambda (fm) (equal? fm (r8g-esc-inner sv sq v epsv mv)))
                         "the abandonment universal"))
         (ball  (list 'BALL sv v epsv)))
    (begin
      (r8g-pos-atoms! epsv)
      (r8g-each-leaf!
       (lambda () (bu-mi ball))
       (lambda ()
         (if (equal? (caddr (dk-goal)) ball)
             (r8g-centre-in-ball! sv v)
             (r8g-ball-in-cover! sv sq v epsv ball cov mv ntail)))))))

;; goal (IS-OPEN-COVER s COV)
(define (r8g-cover-is-open-cover! sv sq cov ncl)
  (mac 'is-open-cover)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
         ((r8g-head? g 'IS-METRIC-SPACE) (ass))
         ((r8g-head? g 'FORALL)                       ; members are open
          (let ((mem (car (dk-peel!))))
            (dk-split-all! (dk-landed (lambda () (sep-me mem))))
            (ass)))
         ((r8g-head? g '==)                           ; BIG-UNION == PTS s
          (let ((bu (cadr g)))
            (have! (list '= bu (list 'PTS sv))
              (lambda ()
                (bc* 'class-extensionality)
                (di)
                (let ((v (cadr (cadr (dk-goal)))))    ; (IFF (IN v BU) (IN v (PTS s)))
                  (r8g-each-leaf!
                   (lambda () (di))
                   (lambda ()
                     (if (r8g-head? (caddr (dk-goal)) 'PTS)
                         (r8g-bu-in-pts! sv v bu cov)
                         (r8g-pts-in-bu! sv sq v bu cov ncl)))))))
            (subst (list '= bu (list 'PTS sv)))
            (qrfl)))
         (#t (error "r8g-cover-is-open-cover!: unexpected conjunct"
                    (expression->string g))))))))

;;; --- the chosen abandonment index -----------------------------------------

;; u in SUB (subset COV): land (IN (CHOICE CAPS(u)) NN) and P(u, CHOICE CAPS(u)).
;; Returns CAPS(u).
(define (r8g-choose-cap! sq u sub cov)
  (let ((memC (dk-fact! 'subset-mem-fwd sub cov u)))
    (dk-split-all! (dk-landed (lambda () (sep-me memC))))
    (let* ((ex   (dk-pick (lambda (fm) (equal? fm (r8g-missed sq u)))
                          "the abandonment existential"))
           (cap  (dk-skolem! ex))
           (caps (r8g-caps sq u)))
      (choose! caps cap
               (lambda () (r8g-each-leaf! (lambda () (sep-mi)) (lambda () (ass)))))
      caps)))

;; goal (SUBSET (IMAGE phi SUB) NN)
(define (r8g-image-in-nn! sq phi sub thr cov)
  (let* ((w  (subset-by-element!))
         (ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff (list 'IN w thr)))))
         (x  (dk-skolem! ex))
         (eq (dk-pick (lambda (fm) (and (r8g-head? fm '=) (pair? (cadr fm))
                                        (equal? (car (cadr fm)) phi)))
                      "the applied-lambda equation")))
    (lam-b-h eq)                                   ; (= (CHOICE caps) w)
    (let ((caps (r8g-choose-cap! sq x sub cov)))
      (subst (list '= w (list 'CHOICE caps)))
      (ass))))

;;; --- the contradiction ----------------------------------------------------

(define (r8g-finish! sv sq sub cov thr phi bnd bigN)
  (let* ((fn (list sq bigN)))
    (dk-fact! 'fun-apply-type-c sq 'NN (list 'PTS sv) bigN)
    (let* ((u    (dk-skolem! (dk-fact! 'open-cover-covers-point sv sub fn)))
           (caps (r8g-choose-cap! sq u sub cov))
           (w    (list 'CHOICE caps))
           (memu (list 'IN fn u)))
      (have! (list 'IN w thr) (lambda () (r8g-in-image! phi sub u w)))
      (let ((imp (inst*! bnd w)))                  ; (IMPLIES (<= N w) (NOT (IN w thr)))
        (dk-fact! 'nn-in-rr bigN)
        (dk-fact! 'nn-in-rr w)
        (have! (list 'AND (list 'IN bigN 'RR) (list 'IN w 'RR)))
        (let ((tot (dk-fact! 'rr-leq-total bigN w)))
          (have! (list '<= w bigN)
            (lambda () (dk-only! tot imp (list 'IN w thr)) (prop))))
        (have! (list 'AND (list 'IN bigN 'NN) (list '<= w bigN)))
        (let* ((pw  (dk-pick (lambda (fm) (equal? fm (r8g-P sq u w)))
                             "the abandonment property of the chosen index"))
               (res (inst*! pw bigN)))             ; (NOT (IN (sq N) u))
          (dk-only! res memu)
          (prop))))))

;; goal (IN w (IMAGE phi SUB)) with w = CHOICE(CAPS u), u in SUB
(define (r8g-in-image! phi sub u w)
  (dk-image-goal!)
  (ew u)
  (r8g-each-leaf!
   (lambda () (di))
   (lambda ()
     (if (r8g-head? (dk-goal) 'IN)
         (ass)
         (begin (lam-b) (rfl))))))

;;; --- main -----------------------------------------------------------------

(define (r8g-main! sv sq ncl cpt)
  (let ((cov (r8g-cover sv sq)))
    (have! (list 'IS-OPEN-COVER sv cov)
      (lambda () (r8g-cover-is-open-cover! sv sq cov ncl)))
    (let ((sub (dk-skolem! (dk-apply! cpt cov))))
      (have! (list 'IN cov 'SET)
        (lambda () (sep-set) (fact 'power-set (list 'PTS sv)) (ass)))
      (dk-fact! 'subclass-of-set-is-set sub cov)
      (let* ((phi (list 'VNB-LAMBDA 'u_ sub (list 'CHOICE (r8g-caps sq 'u_))))
             (thr (list 'IMAGE phi sub)))
        (dk-fact! 'card-image-finite phi sub)
        (have! (list 'SUBSET thr 'NN)
          (lambda () (r8g-image-in-nn! sq phi sub thr cov)))
        (let* ((bigN (dk-skolem! (dk-fact! 'nn-finite-subset-bounded thr)))
               (bnd  (dk-pick (lambda (fm) (and (r8g-head? fm 'FORALL)
                                                (r8g-mentions? fm bigN)))
                              "the bound universal")))
          (r8g-finish! sv sq sub cov thr phi bnd bigN))))))

(sp (make-wff r8g-stmt))
(define r8g-top (dk-peel!))
(define r8g-conj (car r8g-top))
(define r8g-sv (cadr (cadr r8g-conj)))            ; s, off (IS-COMPACT s)
(define r8g-sq (cadr (caddr r8g-conj)))           ; f, off (IN f (FUN NN (PTS s)))
(define r8g-amsp (list 'IS-METRIC-SPACE r8g-sv))
(dk-split-all! r8g-top)
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-compact (list 'IS-COMPACT r8g-sv)))))
(define r8g-CPT
  (dk-pick (lambda (fm) (and (r8g-head? fm 'FORALL) (r8g-mentions? fm 'IS-OPEN-COVER)))
           "the finite-subcover law"))
(have! (list 'IN (list 'PTS r8g-sv) 'SET)
  (lambda ()
    (dk-split-all! (dk-landed (lambda () (mac-h 'is-metric-space r8g-amsp))))
    (ass)))
(define r8g-goal (dk-goal))
(use-em r8g-goal
        (lambda () (ass))
        (lambda ()
          (let ((ncl (dk-landed-find (lambda () (push-not-h (list 'NOT r8g-goal)))
                                     (dk-head? 'FORALL))))
            (r8g-main! r8g-sv r8g-sq ncl r8g-CPT))))

(qed 'compact-seq-has-cluster)
(topic! 'compact-seq-has-cluster 'topology)

;;; ===========================================================================
;;; WHY THE SHORTER-LOOKING ROUTES ARE NOT AVAILABLE (checked before writing).
;;;
;;;   * compact-iff-cluster-point and compact-iff-tb-complete
;;;     (structure-library/compactness.scm) are ASSERTED axioms, so citing
;;;     either replaces one billed leaf with another.
;;;   * compact-implies-totally-bounded (calculus/compact-tb-proof.scm) is
;;;     PROVEN, and totally-bounded-has-cauchy-subsequence is PROVEN, so a
;;;     compact space's sequences have Cauchy subsequences -- but a Cauchy
;;;     subsequence has a LIMIT only in a complete space, and completeness is
;;;     exactly what compact-implies-complete derives FROM this theorem.  That
;;;     route is circular.
;;;   * the nested-tails route (the closures of the tails have the finite
;;;     intersection property) needs a CLOSURE functoid, which the tree does
;;;     not have, and compact-iff-fip is likewise an asserted axiom.
;;;
;;; So compactness must be used through its own definition, and the only
;;; question is how much choice the open cover costs.  The answer here is
;;; none: a cover member is not required to be a ball, so the abandonment
;;; index can be part of the DEFINING CONDITION of the cover rather than a
;;; function of the member chosen in advance.  Only the finite subcover's
;;; indices are chosen, one CHOICE over a provably inhabited SEP, exactly as
;;; in ptwise-cauchy-unif.scm.
;;; ===========================================================================
