;;; rake-baire-2.scm -- the BAIRE CATEGORY theorem (batch 13-C, 2026-09-20).
;;;
;;; Continues theorem-library/rake-baire.scm (batch 12-F), which left the step
;;; (`nowhere-dense-closed-ball', metric-closure-laws.scm), the nesting transitivity
;;; (`nested-family-monotone') and `closed-set-limit-in' in place and stopped before
;;; the recursion.  This file supplies the missing bricks and then the support
;;; `baire-category' itself (structure-library/baire-category.scm:73).
;;;
;;; THE STATEMENT, checked BEFORE proving.  It is
;;;
;;;   forall s. IS-COMPLETE(s) => (forsome x. x in PTS(s)) => IS-NONMEAGER(s, PTS(s))
;;;
;;; The inhabitedness guard was added 2026-09-20 and is needed (the file records the
;;; counterexample).  The other species: IS-MEAGER indexes its family by a FUNCTION
;;; ee in FUN(NN, POWER(PTS s)), so the family is a set and the union is a genuine
;;; countable union -- nothing is left underdetermined there; IS-COMPLETE carries
;;; IS-METRIC-SPACE(s), so `s' is typed; there is no strict `=' on an untyped term,
;;; no CHOICE of a possibly empty class, no finiteness claim.  The statement is
;;; proved here unchanged.
;;;
;;; THE ROUTE.  Three layers, each a theorem of its own.
;;;
;;;   (A) closed-ball plumbing:
;;;         closed-ball-in-carrier   CLOSED-BALL(s,c,r) subset PTS(s)
;;;         closed-ball-center-in    0 <= r  =>  c in CLOSED-BALL(s,c,r)
;;;         closed-ball-in-power     CLOSED-BALL(s,c,r) in POWER(PTS s)
;;;         closed-set-limit-in-tail closed-set-limit-in with the membership
;;;                                  required only on a TAIL of the sequence.
;;;                                  This is the one `closed-set-limit-in' cannot
;;;                                  do: the centres of a nested family lie in the
;;;                                  n-th ball only from index n on.
;;;   (B) nested-closed-balls-point  -- the mathematical heart, stated for an
;;;         arbitrary nested family of closed balls with rad(succ n) <= 1/(n+1):
;;;         in a COMPLETE space they have a common point.  Cauchy centres,
;;;         completeness, then (A) on every ball.  The decay is stated on the
;;;         SUCCESSOR radius because that is what the construction produces
;;;         (the step at stage k bounds the radius it CHOOSES, not the one it
;;;         starts from); the whole-sequence form rad(n) <= 1/(n+1) would put
;;;         an extra n = 0 case on every caller.
;;;   (C) baire-category -- the recursion.  The state space is
;;;         XS = { p in CARTESIAN(PTS s, RR) : POS-RR(NTH 2 p) }: a pair
;;;         (centre, radius) whose radius is POSITIVE BY MEMBERSHIP, so the
;;;         totality hypothesis of `dc-on-nn-pred' holds on the WHOLE state space
;;;         and no invariant has to be carried along the recursion.  (RR-POS-STAR
;;;         will not do: it is [0,+inf] -- it contains 0 and POS-INF, at neither of
;;;         which the step `nowhere-dense-closed-ball' applies.)  The step at stage
;;;         k picks, inside BALL(s, centre(u), radius(u)), a closed ball of radius
;;;         at most 1/(k+1) missing CLOSURE(s, ee(k)); `dc-on-nn-pred'
;;;         (theorem-library/rake-dc-on-nn.scm) turns that into a sequence, (B)
;;;         gives the common point, and the point is in no ee(k).
;;;
;;; Helper prefix: rb2-.
;;;
;;; LOAD WINDOW [371, end).  lo = 371 is forced by `cartesian-nth'
;;; (theorem-library/finsum-fiber, 370); the next latest are `nested-family-monotone'
;;; (rake-baire, 363) and the metric-closure-laws block (362).  Nothing in the tree
;;; cites `baire-category' in a proof, so hi is the end of the list; the natural slot
;;; is immediately after theorem-library/finsum-fiber.
;;;
;;; `scratchpad/window.py' reports `lo = 1630 hi = 1569 EMPTY WINDOW'.  That is an
;;; artifact: the only `hi' it finds for `baire-category' is
;;; structure-library/baire-category.scm (load.scm:1569), which is the support's own
;;; INSTALL site, not a citer -- and that is exactly what the integrator retires.  The
;;; one other occurrence of the name in the tree is
;;; `(rests-on 'open-mapping-theorem '(baire-category))'
;;; (structure-library/frechet-open-mapping.scm:279, load position 364), and `rests-on'
;;; only registers an edge: its typo guard `rests-on-unknown-deps' runs at the END of
;;; the load, by which time this file has installed the name.  So the window is
;;; genuinely [371, end).

;;; =====================================================================
;;; FILE-LOCAL DRIVER HELPERS
;;; =====================================================================

(define (rb2-head? f h) (and (pair? f) (eq? (car f) h)))

;;; `qed' with a loud failure: print every open leaf with its context before
;;; erroring, rather than letting the qed failure be the only trace.
(define (rb2-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-baire-2: ") (display name)
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
        (error "rake-baire-2: unfinished" name))))

;;; (POS-RR e) in context -> its three atoms and their conjunction, which is what
;;; ball-is-open / ball-center-in are guarded on.  Copied from mcl-pos-parts!
;;; (metric-closure-laws.scm); the kit's dk-pos-parts! is newer than the band this
;;; file is probed against, so the copy stays until integration.
(define (rb2-pos-parts! e)
  (fact 'rr-pos-rr-in-rr e)
  (let ((lt (dk-fact! 'rr-lt-of-pos-rr e)))
    (dk-split! (dk-landed-1 (lambda () (mac-h '< lt)))))
  (fact 'rr-lt-of-pos-rr e)
  (have-f! `(AND (IN ,e RR) (AND (<= 0 ,e) (NOT (= 0 ,e))))))

;;; The interior universal of an unfolded IS-OPEN, picked by the SET its guard
;;; ranges over (mcl-interior-univ).
(define (rb2-interior-univ set)
  (dk-pick (lambda (f)
             (and (rb2-head? f 'FORALL) (rb2-head? (caddr f) 'IMPLIES)
                  (let ((ante (cadr (caddr f))))
                    (and (rb2-head? ante 'IN) (equal? (caddr ante) set)))))
           "the interior universal"))

;;; DESTRUCTIVE in (IS-OPEN s u): split it, instantiate its interior universal at
;;; Y, skolemize; return the radius (mcl-radius!).
(define (rb2-radius! op y)
  (dk-split-all! (dk-landed (lambda () (mac-h 'is-open op))))
  (dk-skolem! (dk-apply! (rb2-interior-univ (caddr op)) y)))

;;; (IN (PTS m) SET) out of IS-METRIC-SPACE(m), in a `have!' LANE -- `mac-h'
;;; REPLACES what it unfolds and the predicate is wanted again afterwards.
(define (rb2-pts-in-set! m)
  (have! (list 'IN (list 'PTS m) 'SET)
         (lambda ()
           (dk-split-all!
            (dk-landed (lambda () (mac-h 'IS-METRIC-SPACE (list 'IS-METRIC-SPACE m)))))
           (ass))))

;;; =====================================================================
;;; (A1) closed-ball-in-carrier -- a closed ball lies in the space.
;;; =====================================================================
;;; CLOSED-BALL is a separation over PTS(s), so this is the membership read-off
;;; and nothing else.  Unguarded: at a negative radius the ball is empty.

(sp (make-wff '(FORALL s (FORALL cv_ (FORALL qv_
   (SUBSET (CLOSED-BALL s cv_ qv_) (PTS s)))))))
(dk-peel!)
(let ((zv (subset-by-element!)))
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'closed-ball-membership
                                (list 'IN zv (list 'CLOSED-BALL 's 'cv_ 'qv_))))))
  (ass))
(rb2-qed! 'closed-ball-in-carrier)
(gloss! 'closed-ball-in-carrier
  "A closed ball is a subset of the space: CLOSED-BALL(s,c,r) is a separation
   over PTS(s).  True at every radius, negative ones included (the ball is then
   empty).")
(topic! 'closed-ball-in-carrier 'topology)

;;; =====================================================================
;;; (A2) closed-ball-center-in -- the centre is in its own closed ball.
;;; =====================================================================
;;; The open-ball twin `ball-center-in' needs a STRICTLY positive radius; the
;;; closed ball only needs a NONNEGATIVE one, which is why this is stated on
;;; (<= 0 r) and not on POS-RR r.

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
   (FORALL cv_ (IMPLIES (IN cv_ (PTS s))
     (FORALL qv_ (IMPLIES (IN qv_ RR)
       (IMPLIES (<= 0 qv_)
         (IN cv_ (CLOSED-BALL s cv_ qv_)))))))))))
(dk-peel!)
(mac 'closed-ball-membership)
(dk-conj-close!
 (lambda ()
   (if (rb2-head? (dk-goal) 'IN)
       (ass)
       (begin (subst (dk-fact! 'metric-self-zero 's 'cv_)) (ass)))))
(rb2-qed! 'closed-ball-center-in)
(gloss! 'closed-ball-center-in
  "The centre of a closed ball of NONNEGATIVE radius belongs to it, since
   d(c,c) = 0 <= r.  The open-ball form needs r > 0.")
(topic! 'closed-ball-center-in 'topology)

;;; =====================================================================
;;; (A3) closed-ball-in-power -- a closed ball is a member of POWER(PTS s).
;;; =====================================================================
;;; What `nested-family-monotone' wants: a family of closed balls typed as a
;;; member of FUN(NN, POWER(PTS s)).

(sp (make-wff '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
   (FORALL cv_ (FORALL qv_
     (IN (CLOSED-BALL s cv_ qv_) (POWER (PTS s)))))))))
(dk-peel!)
(fact 'closed-ball-is-set 's 'cv_ 'qv_)
(fact 'closed-ball-in-carrier 's 'cv_ 'qv_)
(have! '(FORALL zv_ (IMPLIES (IN zv_ (CLOSED-BALL s cv_ qv_)) (IN zv_ (PTS s))))
       (lambda ()
         (let ((zw (dk-di-var!)))
           (fact 'subset-mem-fwd '(CLOSED-BALL s cv_ qv_) '(PTS s) zw)
           (ass))))
(fact 'power-mem-intro '(PTS s) '(CLOSED-BALL s cv_ qv_))
(ass)
(rb2-qed! 'closed-ball-in-power)
(gloss! 'closed-ball-in-power
  "A closed ball is a SET contained in PTS(s), hence a member of POWER(PTS s):
   the typing a family of closed balls needs to be a member of
   FUN(NN, POWER(PTS s)).")
(topic! 'closed-ball-in-power 'topology)

;;; =====================================================================
;;; (A4) closed-set-limit-in-tail -- a limit of a sequence EVENTUALLY inside a
;;;      closed set is in it.
;;; =====================================================================
;;; `closed-set-limit-in' (metric-closure-laws.scm) demands (f n) in A for EVERY
;;; n.  The centres of a nested family of balls lie in the n-th ball only from
;;; index n on, so the whole-sequence form cannot be used and a shift lemma
;;; (which the tree does not have) would be the only alternative.  The proof is
;;; the same as closed-set-limit-in's, with the single index nv replaced by
;;; MAX(nv, nb_): the convergence threshold and the tail threshold are both met
;;; there.

(define (rb2-univ-with pred what)            ; a FORALL/IMPLIES whose ANTECEDENT fits
  (dk-pick (lambda (f)
             (and (rb2-head? f 'FORALL) (rb2-head? (caddr f) 'IMPLIES)
                  (pred (cadr (caddr f)) (caddr (caddr f)))))
           what))

;;; The two NN-guarded universals in play have the SAME outer shape -- the
;;; convergence tail and the hypothesis' tail -- so they are told apart by the
;;; head of the INNERMOST consequent: `<=' for the convergence bound, `IN' for
;;; the membership.
(define (rb2-nn-univ inner-head what)
  (rb2-univ-with (lambda (ante conseq)
                   (and (rb2-head? ante 'IN) (equal? (caddr ante) 'NN)
                        (rb2-head? conseq 'IMPLIES)
                        (rb2-head? (caddr conseq) inner-head)))
                 what))

(sp (make-wff '(FORALL s (FORALL av_ (FORALL fv_ (FORALL lv_ (FORALL nb_
   (IMPLIES (IS-CLOSED s av_)
     (IMPLIES (CONVERGES-TO s fv_ lv_)
       (IMPLIES (IN nb_ NN)
         (IMPLIES (FORALL n (IMPLIES (IN n NN)
                              (IMPLIES (<= nb_ n) (IN (fv_ n) av_))))
           (IN lv_ av_))))))))))))
(dk-peel!)
(dk-split-all! (dk-landed (lambda () (mac-h 'converges-to '(CONVERGES-TO s fv_ lv_)))))
(let ((cvu (rb2-univ-with (lambda (a c) (rb2-head? a 'POS-RR)) "the convergence universal"))
      (ptw (rb2-nn-univ 'IN "the tail membership hypothesis")))
  (pbc)                                      ; assume (NOT (IN lv_ av_)); goal FALSITY
  (have! '(IN lv_ (COMPLEMENT-IN (PTS s) av_))
         (lambda () (mac 'complement-in-membership) (dk-conj-close! (lambda () (ass)))))
  (dk-split-all! (dk-landed (lambda () (mac-h 'is-closed '(IS-CLOSED s av_)))))
  (let* ((comp '(COMPLEMENT-IN (PTS s) av_))
         (r0   (rb2-radius! (list 'IS-OPEN 's comp) 'lv_)))
    (rb2-pos-parts! r0)
    (fact 'ball-is-set 's 'lv_ r0)
    (let* ((hlf (dk-halve! r0))
           (nv  (dk-skolem! (dk-apply! cvu hlf)))
           (tail (rb2-nn-univ '<= "the convergence tail"))
           (mv  (list 'MAX nv 'nb_)))
      (fact 'nn-max-closed nv 'nb_)
      (fact 'nn-in-rr nv)
      (fact 'nn-in-rr 'nb_)
      (fact 'rr-le-max-left nv 'nb_)
      (fact 'rr-le-max-right nv 'nb_)
      (dk-apply! tail mv)                    ; (<= ((DIST s) (fv_ mv) lv_) hlf)
      (dk-apply! ptw mv)                     ; (IN (fv_ mv) av_)
      (let* ((fn  (list 'fv_ mv))
             (dfl (list (list 'DIST 's) fn 'lv_))
             (dlf (list (list 'DIST 's) 'lv_ fn)))
        (fact 'subset-mem-fwd 'av_ '(PTS s) fn)
        (fact 'metric-dist-real 's fn 'lv_)
        (fact 'metric-dist-real 's 'lv_ fn)
        (fact 'metric-sym 's fn 'lv_)
        (have! (list '<= dlf hlf)
               (lambda () (dk-ineq! (list '= dfl dlf) (list '<= dfl hlf))))
        (have! (list '< hlf r0)
               (lambda () (dk-ineq! (list '= (list '+ hlf hlf) r0) (list '< 0 hlf))))
        (have! (list 'AND (list 'IN fn '(PTS s))
                     (list 'AND (list 'IN hlf 'RR)
                           (list 'AND (list 'IN r0 'RR)
                                 (list 'AND (list '<= dlf hlf) (list '< hlf r0))))))
        (dk-fact! 'ball-mem-from-le 's 'lv_ fn hlf r0)
        (fact 'subset-mem-fwd (list 'BALL 's 'lv_ r0) comp fn)
        (dk-split-all! (dk-landed (lambda () (mac-h 'complement-in-membership
                                                    (list 'IN fn comp)))))
        (ai (list 'NOT (list 'IN fn 'av_)))))))
(rb2-qed! 'closed-set-limit-in-tail)
(gloss! 'closed-set-limit-in-tail
  "A convergent sequence whose terms lie in a CLOSED set from some index on has
   its limit there.  The tail form of closed-set-limit-in; what a nested family
   of closed balls needs, since the centres enter the n-th ball only at index n.")
(topic! 'closed-set-limit-in-tail 'topology)

;;; =====================================================================
;;; (B) nested-closed-balls-point -- nested closed balls with radii -> 0 in a
;;;     COMPLETE space have a common point.
;;; =====================================================================
;;; The mathematical heart of Baire, stated for an arbitrary pair of sequences
;;; (centres, radii) rather than for the ones the recursion builds, so that the
;;; construction and the analysis are separate theorems.
;;;
;;; The decay hypothesis is rad(n) <= 1/(n+1), which is all the Cauchy estimate
;;; needs (nn-recip-succ-small).  A geometric 2^-n bound would be a second
;;; development for nothing.
;;;
;;; Why the radii are only required NONNEGATIVE: the centre lies in its own
;;; CLOSED ball already at radius 0 (closed-ball-center-in), and the argument
;;; never opens a ball.

(define (rb2-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA)) #t)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((rb2-redex? (car l)) #t)
                    (#t (loop (cdr l))))))))

;;; beta-reduce every redex of the HYPOTHESIS F, to a fixpoint; return the
;;; reduced formula as the context holds it.  `lam-b' reaches only the goal.
(define (rb2-beta-h! f0)
  (let loop ((f f0) (k 0))
    (cond ((not (rb2-redex? f)) f)
          ((> k 4) (error "rb2-beta-h!: beta did not finish on"
                          (expression->string f)))
          (#t (let ((landed (dk-landed (lambda () (lam-b-h f)))))
                (if (null? landed)
                    (error "rb2-beta-h!: lam-b-h landed nothing for"
                           (expression->string f)))
                (loop (car landed) (+ k 1)))))))

;;; CH is an instantiation chain stopped at an IMPLIES; prove its antecedent --
;;; READ OFF CH, never rebuilt -- with BODY, and detach.
(define (rb2-detach-with! ch body)
  (if (not (rb2-head? ch 'IMPLIES))
      (error "rb2-detach-with!: not an implication" (expression->string ch)))
  (let ((ante (cadr ch)))
    ;; `have!' of a formula the context already holds (up to alpha) is a silent
    ;; self-loop, so the lane is skipped when the antecedent is already there.
    (if (not (any-pred (lambda (f) (alpha-equiv? f ante)) (dk-asms)))
        (have! ante body))
    (dk-apply! ch)))

(sp (make-wff
  '(FORALL s
    (IMPLIES (IS-COMPLETE s)
     (FORALL ctr_
      (IMPLIES (IN ctr_ (FUN NN (PTS s)))
       (FORALL rds_
        (IMPLIES (IN rds_ (FUN NN RR))
         (IMPLIES (FORALL n (IMPLIES (IN n NN) (<= 0 (rds_ n))))
          (IMPLIES (FORALL n (IMPLIES (IN n NN)
                     (SUBSET (CLOSED-BALL s (ctr_ (succ n)) (rds_ (succ n)))
                             (CLOSED-BALL s (ctr_ n) (rds_ n)))))
           (IMPLIES (FORALL n (IMPLIES (IN n NN) (<= (rds_ (succ n)) (recip (+ n 1)))))
            (FORSOME lv_
             (AND (IN lv_ (PTS s))
                  (FORALL n (IMPLIES (IN n NN)
                              (IN lv_ (CLOSED-BALL s (ctr_ n) (rds_ n))))))))))))))))))

(define rb2-b-landed (dk-peel!))
(define rb2-b-nonneg
  (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                            (rb2-head? (caddr f) 'IMPLIES)
                            (rb2-head? (caddr (caddr f)) '<=)
                            (equal? (cadr (caddr (caddr f))) 0)))
           "the nonnegativity hypothesis"))
(define rb2-b-nest
  (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                            (rb2-head? (caddr f) 'IMPLIES)
                            (rb2-head? (caddr (caddr f)) 'SUBSET)))
           "the nesting hypothesis"))
(define rb2-b-decay
  (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                            (rb2-head? (caddr f) 'IMPLIES)
                            (rb2-head? (caddr (caddr f)) '<=)
                            (not (equal? (cadr (caddr (caddr f))) 0))))
           "the decay hypothesis"))

(have! '(IS-METRIC-SPACE s)
       (lambda ()
         (dk-split-all! (dk-landed (lambda () (mac-h 'is-complete '(IS-COMPLETE s)))))
         (ass)))
(rb2-pts-in-set! 's)

;;; the family of closed balls, as a member of FUN(NN, POWER(PTS s))
(define rb2-b-gg
  '(VNB-LAMBDA nv_ NN (CLOSED-BALL s (ctr_ nv_) (rds_ nv_))))
(define rb2-b-pw '(POWER (PTS s)))

(have! (list 'IN rb2-b-gg (list 'FUN 'NN rb2-b-pw))
       (lambda ()
         (dk-lam-t!)
         (let ((kv (dk-di-var!)))
           (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) kv)
           (fact 'fun-apply-type-c 'rds_ 'NN 'RR kv)
           (fact 'closed-ball-in-power 's (list 'ctr_ kv) (list 'rds_ kv))
           (ass))))

;;; the nesting hypothesis, transported to the lambda family
(have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
              (list 'SUBSET (list rb2-b-gg '(succ n)) (list rb2-b-gg 'n))))
       (lambda ()
         (let ((kv (dk-di-var!)))
           (fact 'nn-succ-closed kv)
           (dk-lam-b!)
           (dk-apply! rb2-b-nest kv)
           (ass))))

;;; a <= b  =>  the b-th centre lies in the a-th closed ball
(define rb2-b-inball
  (list 'FORALL 'av_ (list 'IMPLIES '(IN av_ NN)
    (list 'FORALL 'bv_ (list 'IMPLIES '(IN bv_ NN)
      (list 'IMPLIES '(<= av_ bv_)
        '(IN (ctr_ bv_) (CLOSED-BALL s (ctr_ av_) (rds_ av_)))))))))

(have! rb2-b-inball
  (lambda ()
    (dk-peel!)
    (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) 'av_)
    (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) 'bv_)
    (fact 'fun-apply-type-c 'rds_ 'NN 'RR 'av_)
    (fact 'fun-apply-type-c 'rds_ 'NN 'RR 'bv_)
    (dk-apply! rb2-b-nonneg 'bv_)
    (fact 'closed-ball-center-in 's '(ctr_ bv_) '(rds_ bv_))
    (let* ((ch (dk-fact! 'nested-family-monotone 'bv_ rb2-b-pw rb2-b-gg))
           (uu (if (rb2-head? ch 'IMPLIES)
                   (rb2-detach-with! ch (lambda () (ass)))
                   ch))
           (sub (rb2-beta-h! (dk-apply! uu 'av_))))
      (fact 'subset-mem-fwd (cadr sub) (caddr sub) '(ctr_ bv_))
      (ass))))


;;; the centres are a Cauchy sequence.  Given eps, halve it, take the stage nw
;;; at which 1/(nw+1) is already below the half (nn-recip-succ-small), and run
;;; both indices through the nw-th centre: each is within rds_(nw) <= 1/(nw+1)
;;; of it.
(have! '(IS-CAUCHY-SEQ s ctr_)
  (lambda ()
    (mac 'is-cauchy-seq)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (cond
           ((rb2-head? g 'IS-METRIC-SPACE) (ass))
           ((rb2-head? g 'IN) (ass))
           (#t
            (dk-peel!)                                   ; eps and (POS-RR eps)
            (let* ((ev  (cadr (dk-pick (dk-head? 'POS-RR) "the epsilon")))
                   (hlf (dk-halve! ev))
                   (nw  (dk-skolem! (dk-fact! 'nn-recip-succ-small hlf)))
                   (rcp (list 'recip (list '+ nw 1)))
                   (sw  (list 'succ nw))
                   (rdw (list 'rds_ sw))
                   (cw  (list 'ctr_ sw)))
              (fact 'rr-pos-rr-in-rr ev)
              (fact 'nn-recip-succ-pos nw)
              (fact 'rr-pos-rr-in-rr rcp)
              (fact 'nn-succ-closed nw)
              (fact 'fun-apply-type-c 'rds_ 'NN 'RR sw)
              (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) sw)
              (dk-apply! rb2-b-decay nw)                 ; (<= (rds_ (succ nw)) rcp)
              (ew sw)
              (dk-conj-close!
               (lambda ()
                 (if (rb2-head? (dk-goal) 'IN)
                     (ass)
                     (begin
                       (dk-split-all! (dk-peel!))
                       (let* ((dd  (cadr (dk-goal)))
                              (mv  (cadr (cadr dd)))
                              (nv2 (cadr (caddr dd)))
                              (cm  (list 'ctr_ mv))
                              (cn  (list 'ctr_ nv2))
                              (dmn (list '(DIST s) cm cn))
                              (dmw (list '(DIST s) cm cw))
                              (dwm (list '(DIST s) cw cm))
                              (dwn (list '(DIST s) cw cn)))
                         (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) mv)
                         (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) nv2)
                         (let ((atw (dk-apply! rb2-b-inball sw)))
                           (dk-split-all!
                            (dk-landed
                             (lambda () (mac-h 'closed-ball-membership
                                               (dk-apply! atw mv)))))
                           (dk-split-all!
                            (dk-landed
                             (lambda () (mac-h 'closed-ball-membership
                                               (dk-apply! atw nv2))))))
                         (fact 'metric-triangle 's cm cw cn)
                         (fact 'metric-sym 's cw cm)
                         (fact 'metric-dist-real 's cm cn)
                         (fact 'metric-dist-real 's cm cw)
                         (fact 'metric-dist-real 's cw cm)
                         (fact 'metric-dist-real 's cw cn)
                         (dk-ineq! (list '<= dmn (list '+ dmw dwn))
                                   (list '= dwm dmw)
                                   (list '<= dwm rdw)
                                   (list '<= dwn rdw)
                                   (list '<= rdw rcp)
                                   (list '< rcp hlf)
                                   (list '= (list '+ hlf hlf) ev)))))))))))))))

;;; completeness gives the limit, and every closed ball of the family, being
;;; closed and holding the centres from its own index on, holds it too.
(define rb2-b-conv
  (dk-fact! 'complete-cauchy-converges 's 'ctr_))
(define rb2-b-lim
  (dk-skolem! (car (dk-landed (lambda () (mac-h 'converges rb2-b-conv))))))

(have! (list 'IN rb2-b-lim '(PTS s))
  (lambda ()
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'converges-to (list 'CONVERGES-TO 's 'ctr_ rb2-b-lim)))))
    (ass)))

(ew rb2-b-lim)
(dk-conj-close!
 (lambda ()
   (if (rb2-head? (dk-goal) 'IN)
       (ass)
       (let* ((kv (dk-di-var!))
              (cb (list 'CLOSED-BALL 's (list 'ctr_ kv) (list 'rds_ kv))))
         (fact 'fun-apply-type-c 'ctr_ 'NN '(PTS s) kv)
         (fact 'fun-apply-type-c 'rds_ 'NN 'RR kv)
         (fact 'closed-ball-is-set 's (list 'ctr_ kv) (list 'rds_ kv))
         (fact 'closed-ball-is-closed 's (list 'ctr_ kv) (list 'rds_ kv))
         (let ((ch (dk-fact! 'closed-set-limit-in-tail 's cb 'ctr_ rb2-b-lim kv)))
           (if (rb2-head? ch 'IMPLIES)
               (rb2-detach-with! ch
                 (lambda ()
                   (let ((jv (dk-di-var!)))
                     (di)
                     (dk-apply! rb2-b-inball kv jv)
                     (ass))))
               ch))
         (ass)))))
(rb2-qed! 'nested-closed-balls-point)
(gloss! 'nested-closed-balls-point
  "Cantor's nested-ball principle: in a COMPLETE metric space a decreasing
   sequence of closed balls whose radii are nonnegative and bounded by 1/(n+1)
   has a point in common.  The centres are Cauchy because the m-th centre lies
   in the n-th ball whenever n <= m; the limit lies in every ball because each
   is closed and holds the centres from its own index on.")
(topic! 'nested-closed-balls-point 'topology)

;;; =====================================================================
;;; (C) baire-category -- the support, stated literally
;;;     (structure-library/baire-category.scm:73).
;;; =====================================================================
;;; Suppose PTS(s) were covered by the countable family ee of nowhere-dense
;;; sets.  Build, by dependent choice over the state space
;;;
;;;     XS = { p in CARTESIAN(PTS s, RR) : POS-RR(NTH 2 p) },
;;;
;;; a sequence of states u(0) = [x0, 1], u(succ k) chosen inside
;;; BALL(s, NTH 1 (u k), NTH 2 (u k)) by `nowhere-dense-closed-ball' at
;;; A := ee(k) and bound 1/(k+1), so that CLOSED-BALL(s, NTH 1 (u (succ k)),
;;; NTH 2 (u (succ k))) misses CLOSURE(s, ee(k)) entirely.  The radius is
;;; positive BY MEMBERSHIP IN XS, which is what makes the totality hypothesis
;;; of `dc-on-nn-pred' hold at EVERY state and removes the need for an
;;; invariant along the recursion.  `nested-closed-balls-point' then produces a
;;; point in every closed ball, hence in no ee(k) -- contradicting the cover.

(define rb2-c-cart '(CARTESIAN (PTS s) RR))
(define rb2-c-xs '(SEP pv_ (CARTESIAN (PTS s) RR) (POS-RR (NTH 2 pv_))))

;;; the set-valued step, at the family EE
(define (rb2-c-nxt ee)
  (list 'VNB-LAMBDA '(LIST kv_ uv_) (list 'CARTESIAN 'NN rb2-c-xs)
    (list 'SEP 'yv_ rb2-c-xs
      (list 'AND
        '(SUBSET (CLOSED-BALL s (NTH 1 yv_) (NTH 2 yv_))
                 (BALL s (NTH 1 uv_) (NTH 2 uv_)))
        (list 'AND
          '(<= (NTH 2 yv_) (recip (+ kv_ 1)))
          (list 'FORALL 'zv_
            (list 'IMPLIES '(IN zv_ (CLOSED-BALL s (NTH 1 yv_) (NTH 2 yv_)))
              (list 'NOT (list 'IN 'zv_ (list 'CLOSURE 's (list ee 'kv_)))))))))))

;;; (IN T XS) in context -> the two projections typed and the radius positive.
(define (rb2-c-parts! t)
  (have! (list 'IN t rb2-c-cart)
         (lambda () (sep-me (list 'IN t rb2-c-xs)) (ass)))
  (have! (list 'POS-RR (list 'NTH 2 t))
         (lambda () (sep-me (list 'IN t rb2-c-xs)) (ass)))
  (dk-split! (dk-fact! 'cartesian-nth t '(PTS s) 'RR)))

(sp (make-wff '(FORALL s (IMPLIES (IS-COMPLETE s)
     (IMPLIES (FORSOME x (IN x (PTS s)))
       (IS-NONMEAGER s (PTS s)))))))
(dk-peel!)
(have! '(IS-METRIC-SPACE s)
       (lambda ()
         (dk-split-all! (dk-landed (lambda () (mac-h 'is-complete '(IS-COMPLETE s)))))
         (ass)))
(rb2-pts-in-set! 's)
(define rb2-c-x0 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the inhabitedness witness")))
(define rb2-c-a0 (list 'LIST rb2-c-x0 1))

(mac 'is-nonmeager)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((rb2-head? g 'IS-METRIC-SPACE) (ass))
       ((rb2-head? g 'SUBSET) (subset-by-element!) (ass))
       (#t
        ;; assume PTS(s) IS meager and derive FALSITY
        (dk-split-all!
         (dk-landed (lambda () (mac-h 'is-meager (car (dk-landed (lambda () (di))))))))
        (let* ((eex (dk-pick (dk-head? 'FORSOME) "the meager family"))
               (ee  (dk-skolem! eex))
               (nwd (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                                              (rb2-head? (caddr f) 'IMPLIES)
                                              (rb2-head? (caddr (caddr f)) 'IS-NOWHERE-DENSE)))
                             "the nowhere-dense universal"))
               (cov (dk-pick (lambda (f) (and (rb2-head? f 'SUBSET)
                                              (rb2-head? (caddr f) 'BIG-UNION)))
                             "the cover"))
               (nxt (rb2-c-nxt ee)))
          ;; ---- the state space is a SET, and holds the base point ----
          (have! (list 'IN rb2-c-cart 'SET)
                 (lambda () (fact 'rr-is-set)
                            (mac 'cartesian-set-iff)
                            (dk-conj-close! (lambda () (ass)))))
          (have! (list 'SUBSET rb2-c-xs rb2-c-cart)
                 (lambda () (mac 'subset-def)
                            (let ((m (dk-landed-1 (lambda () (di)))))
                              (sep-me m) (ass))))
          (fact 'subclass-of-set-is-set rb2-c-xs rb2-c-cart)
          (fact 'rr-one-in)
          (fact 'rr-zero-lt-one)
          (fact 'rr-pos-rr-of-lt 1)
          (fact 'pair-in-cartesian '(PTS s) 'RR rb2-c-x0 1)
          (have! (list 'IN rb2-c-a0 rb2-c-xs)
                 (lambda () (in-sep! (lambda () (ass)) (lambda () (nth-r) (ass)))))
          ;; ---- totality of the step over the WHOLE state space ----
          (have! (list 'FORALL 'k
                   (list 'IMPLIES '(IN k NN)
                     (list 'FORALL 'u
                       (list 'IMPLIES (list 'IN 'u rb2-c-xs)
                         (list 'FORSOME 'y
                           (list 'AND (list 'IN 'y rb2-c-xs)
                                 (list 'IN 'y (list nxt 'k 'u))))))))
            (lambda ()
              (dk-peel!)
              (rb2-c-parts! 'u)
              (fact 'nn-recip-succ-pos 'k)
              (dk-apply! nwd 'k)
              (let* ((exx (dk-fact! 'nowhere-dense-closed-ball 's (list ee 'k)
                                    '(NTH 1 u) '(NTH 2 u) '(recip (+ k 1))))
                     (xw  (dk-skolem! exx))
                     (qw  (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the radius"))))
                (fact 'rr-pos-rr-in-rr qw)
                (fact 'pair-in-cartesian '(PTS s) 'RR xw qw)
                (let ((yy (list 'LIST xw qw)))
                  (have! (list 'IN yy rb2-c-xs)
                         (lambda () (in-sep! (lambda () (ass)) (lambda () (nth-r) (ass)))))
                  (ew yy)
                  (dk-conj-close!
                   (lambda ()
                     (if (equal? (dk-goal) (list 'IN yy rb2-c-xs))
                         (ass)
                         (begin
                           (dk-lam-b!)
                           (in-sep! (lambda () (ass))
                                    (lambda () (nth-r)
                                               (dk-conj-close! (lambda () (ass)))))))))))))
          ;; ---- the recursion ----
          (let* ((exf (dk-fact! 'dc-on-nn-pred rb2-c-xs rb2-c-a0 nxt))
                 (fw  (dk-skolem! exf))
                 (stp (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                                                (rb2-head? (caddr f) 'IMPLIES)
                                                (rb2-head? (caddr (caddr f)) 'IN)))
                               "the per-stage step"))
                 (cen (list 'VNB-LAMBDA 'nv_ 'NN (list 'NTH 1 (list fw 'nv_))))
                 (rds (list 'VNB-LAMBDA 'nv_ 'NN (list 'NTH 2 (list fw 'nv_)))))
            ;; open the step at stage KV: land the three conditions on the
            ;; successor state.  DESTRUCTIVE in the instance it opens.
            (define (rb2-c-step! kv)
              (let* ((inst (dk-apply! stp kv))
                     (red  (car (dk-landed (lambda () (lam-b-h inst))))))
                (dk-split-all! (dk-landed (lambda () (sep-me red))))))
            (have! (list 'IN cen (list 'FUN 'NN '(PTS s)))
              (lambda ()
                (dk-lam-t!)
                (let ((kv (dk-di-var!)))
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs kv)
                  (rb2-c-parts! (list fw kv))
                  (ass))))
            (have! (list 'IN rds (list 'FUN 'NN 'RR))
              (lambda ()
                (dk-lam-t!)
                (let ((kv (dk-di-var!)))
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs kv)
                  (rb2-c-parts! (list fw kv))
                  (ass))))
            (have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list '<= 0 (list rds 'n))))
              (lambda ()
                (let ((kv (dk-di-var!)))
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs kv)
                  (rb2-c-parts! (list fw kv))
                  (rb2-pos-parts! (list 'NTH 2 (list fw kv)))
                  (dk-lam-b!)
                  (ass))))
            (have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
                     (list 'SUBSET
                       (list 'CLOSED-BALL 's (list cen '(succ n)) (list rds '(succ n)))
                       (list 'CLOSED-BALL 's (list cen 'n) (list rds 'n)))))
              (lambda ()
                (let* ((kv (dk-di-var!))
                       (skv (list 'succ kv)))
                  (fact 'nn-succ-closed kv)
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs kv)
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs skv)
                  (rb2-c-parts! (list fw kv))
                  (rb2-c-step! kv)
                  (dk-lam-b!)
                  (fact 'ball-in-closed-ball 's (list 'NTH 1 (list fw kv))
                                                (list 'NTH 2 (list fw kv)))
                  (fact 'subset-trans
                        (list 'CLOSED-BALL 's (list 'NTH 1 (list fw skv))
                                              (list 'NTH 2 (list fw skv)))
                        (list 'BALL 's (list 'NTH 1 (list fw kv))
                                       (list 'NTH 2 (list fw kv)))
                        (list 'CLOSED-BALL 's (list 'NTH 1 (list fw kv))
                                              (list 'NTH 2 (list fw kv))))
                  (ass))))
            (have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
                     (list '<= (list rds '(succ n)) '(recip (+ n 1)))))
              (lambda ()
                (let ((kv (dk-di-var!)))
                  (fact 'nn-succ-closed kv)
                  (fact 'fun-apply-type-c fw 'NN rb2-c-xs kv)
                  (rb2-c-step! kv)
                  (dk-lam-b!)
                  (ass))))
            (let* ((ch0 (dk-fact! 'nested-closed-balls-point 's cen rds))
                   (exl (let loop ((ch ch0))
                          (if (rb2-head? ch 'IMPLIES)
                              (loop (rb2-detach-with! ch (lambda () (ass))))
                              ch)))
                   (ll  (dk-skolem! exl))
                   (blu (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                                                  (rb2-head? (caddr f) 'IMPLIES)
                                                  (rb2-head? (caddr (caddr f)) 'IN)
                                                  (equal? (cadr (caddr (caddr f))) ll)))
                                 "the common-point universal")))
              (fact 'subset-mem-fwd '(PTS s) (caddr cov) ll)
              (let* ((landed (dk-landed (lambda () (bu-me (list 'IN ll (caddr cov))))))
                     (n0 (cadr (or (find-first (lambda (h)
                                                 (and (rb2-head? h 'IN)
                                                      (eq? (caddr h) 'NN)
                                                      (member h landed)))
                                               landed)
                                   (error "baire-category: no index landed by bu-me")))))
                (dk-apply! nwd n0)
                (have! (list 'SUBSET (list ee n0) '(PTS s))
                       (lambda ()
                         (dk-split-all!
                          (dk-landed (lambda () (mac-h 'is-nowhere-dense
                                                       (list 'IS-NOWHERE-DENSE 's (list ee n0))))))
                         (ass)))
                (fact 'closure-contains 's (list ee n0))
                (fact 'subset-mem-fwd (list ee n0) (list 'CLOSURE 's (list ee n0)) ll)
                (fact 'nn-succ-closed n0)
                (fact 'fun-apply-type-c fw 'NN rb2-c-xs n0)
                (rb2-c-parts! (list fw n0))
                (rb2-c-step! n0)
                (let* ((zcl (dk-pick (lambda (f) (and (rb2-head? f 'FORALL)
                                                      (rb2-head? (caddr f) 'IMPLIES)
                                                      (rb2-head? (caddr (caddr f)) 'NOT)))
                                     "the missing-closure clause"))
                       (inb (dk-apply! blu (list 'succ n0))))
                  (car (dk-landed (lambda () (lam-b-h inb))))
                  (dk-apply! zcl ll)
                  (ai (list 'NOT (list 'IN ll (list 'CLOSURE 's (list ee n0)))))))))))))))
(rb2-qed! 'baire-category)

;;; `baire-category' keeps its `gloss!' and `topic!' at the definition site
;;; (structure-library/baire-category.scm:78-86), which is why neither is repeated
;;; here: only the `support' (:73) and the `warrant!' (:77) are retired.
