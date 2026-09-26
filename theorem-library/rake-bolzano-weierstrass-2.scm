;;; NOTE 2026-09-20 (batch 12-B).  Where this file says the tree has no metric SUBSPACE
;;; structure, that is history: SUBSPACE-MS(s, A) and RESTRICT(f, A) are defined in
;;; structure-library/metric-subspace.scm, their laws are in
;;; theorem-library/metric-subspace-laws.scm and compact-subspace.scm, and
;;; `heine-borel-ccint' (theorem-library/heine-borel-interval.scm) states that
;;; SUBSPACE-MS(RR-MS, CCINT(a, b)) is compact.

;;; theorem-library/rake-bolzano-weierstrass-2.scm
;;; ====================================================================
;;; BOLZANO-WEIERSTRASS -- batch 8-E, items (A) and (B) of the footer of
;;; theorem-library/rake-bolzano-weierstrass.scm, which must load first.
;;;
;;;   rr-interval-seq-has-convergent-subseq
;;;       lo, hi in RR, h in FUN(NN, CCINT(lo,hi))
;;;         =>  forsome phi. STRICTLY-MONO-NN(phi) and forsome p in RR.
;;;             CONVERGES-TO(RR-MS, SUBSEQ(h,phi), p)
;;;   rr-bolzano-weierstrass
;;;       the same with the ABS hypothesis -- h in FUN(NN,RR), bd in RR,
;;;       abs(h i) <= bd for every i -- which is the form consumers cite
;;;   bounded-block-converges
;;;       the same ALONG AN INFINITE BLOCK: 8-B's statement (the analytic
;;;       brick the Ascoli route asked for)
;;;
;;; THE ROUTE, and what each step is.  The library already had every piece of
;;; the COMBINATORIAL half of Bolzano-Weierstrass and none of the analytic
;;; half, because the analytic half is "the interval is totally bounded" and
;;; the tree cannot say that (no metric SUBSPACE structure).  The first file
;;; replaces it by a statement about SETS -- a finite cover of small mesh --
;;; and from there the classical proof runs verbatim:
;;;
;;;   rad  <- null-rr-seq-exists                (a positive null radius seq)
;;;   cov  <- ccint-grid-cover-seq (lo, hi, rad)          [the first file]
;;;   blk  <- block-family-combinatorial (CCINT(lo,hi), h, cov)
;;;   phi  <- diagonalization (blk)             (strictly mono, tail in blk k)
;;;   the Cauchy estimate: past the threshold N0 where rad(k) <= eps, the
;;;         diagonal puts phi(m) and phi(p) in blk(N0), the capture clause puts
;;;         h(phi m) and h(phi p) in ONE member U of cov(N0), and the mesh of
;;;         cov(N0) bounds their distance by rad(N0) <= eps.
;;;   then rr-cauchy-converges, which takes the ABS form of Cauchy directly, so
;;;         no metric vocabulary enters the estimate at all.
;;;
;;; NO HALVING.  The metric route (cauchy-subseq-proof.scm) halves eps because
;;; two points of one r-BALL are 2r apart.  Two points of one CELL are eps
;;; apart, so the estimate is one citation shorter than its metric twin.
;;;
;;; WHERE THE LIMIT'S TYPE COMES FROM.  rr-cauchy-converges concludes
;;; CONVERGES(RR-MS, -), whose witness is typed (IN p (PTS RR-MS)); the
;;; statement wants (IN p RR).  That step is `slot-h PTS' inside a `have!'
;;; lane (cauchy-criterion-right.scm:283 is the precedent): firing the
;;; rr-ms@pts accessor macete by name is what accessor-callsite-audit forbids.
;;; Going the other way -- proving a goal (IN t (PTS RR-MS)) -- is `slot PTS'.
;;;
;;; THE ABS COROLLARY, and the one trick in it.  Typing h into the SEP'd
;;; codomain CCINT(-bd, bd) is NOT fun-codomain-subset/-superset (they widen a
;;; codomain, and this narrows one): the door is `fun-codomain-iff', which
;;; splits (IN h (FUN A B)) into the partial-function typing (IN h (FUN A)) and
;;; the pointwise membership, and reassembles it at the new codomain.  The
;;; lower endpoint is NOT spelled `(- 0 bd)' or `(- bd)': the term is READ OFF
;;; an instance of rr-abs-bound (whose right-hand side is exactly
;;; `-bd <= x and x <= bd'), so the driver never guesses how the printer
;;; spells unary minus and no `crs' call is needed to reconcile two spellings.
;;;
;;; THE ADDED GUARD, and why.  8-B's statement of bounded-block-converges
;;; leaves `bd' UNTYPED: `abs(h i) <= bd' certifies bd DEFINED but not real
;;; (the LUTINS rule), and no lemma of the shape "x <= y and x in RR implies
;;; y in RR" exists -- every order axiom in number-systems.scm is guarded the
;;; other way.  Both statements here therefore carry `(IN bd RR)', curried,
;;; ahead of the bound.  That is the species "an index bound left UNTYPED";
;;; the guard costs a consumer one citation and is free wherever bd came from
;;; a POINTWISE-BOUNDED clause, which types it.
;;;
;;; LOAD WINDOW [2931, end).  window.py: `lo = 2930   hi = none   ok'.  lo is
;;; theorem-library/rake-bolzano-weierstrass itself (load.scm:2930), for
;;; ccint-grid-cover-seq; every other citation is far below -- ccint-subset-rr
;;; (monotone-inverse, 2029), ccint-membership (ccint-basics, 2011), CCINT
;;; (extreme-value, 2005), fun-codomain-subset (subsequence-principle, 1535),
;;; rr-cauchy-converges (seq-limit-core, 1453), rr-is-metric-space
;;; (rr-metric-space-proof, 1410), block-family-combinatorial (1384),
;;; diagonalization (1378), rake-nn-enum (1361), nn-infinite (1223),
;;; subseq-apply (591).  hi: nothing cites the three yet.  So the slot is
;;; IMMEDIATELY AFTER the first file.  No late tactic is used (no contra, prep
;;; or ineq-supply; `prop', `slot', `slot-h' and the dk- kit load early).
;;;
;;; WHERE THIS GOES NEXT.  `bounded-block-converges' is the totality of the
;;; dependent choice in item (C) of the first file's footer -- the RR copy of
;;; rake-block-tower.scm part B -- which produces the pointwise diagonal that
;;; `ascoli-sequential-from-diagonal' (rake-ascoli.scm) takes as its one
;;; remaining antecedent.  (C) is NOT in this file; the user schedules it.
;;;
;;; Helper prefix: r9f-  (the first file's helpers are r9e-; this file
;;; redefines none of them, so the two can be concatenated in a probe).
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r9f-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-bw-2: ") (display name)
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
        (error "rake-bw-2: unfinished" name))))

(define (r9f-need pred what lst)
  (or (any-pred pred lst)
      (error "rake-bw-2: missing" what (map expression->string lst))))

;;; `lam-b' to a fixpoint: a fixed-count call leaves an inert step.
(define (r9f-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA)) #t)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((r9f-redex? (car l)) #t)
                    (#t (loop (cdr l))))))))

(define (r9f-beta!)
  (let loop ((i 0))
    (if (and (< i 6) (r9f-redex? (dk-goal)))
        (begin (lam-b) (loop (+ i 1))))))

;;; (IN (CCINT lo hi) SET) -- a subclass of the set RR.
(define (r9f-ccint-set! lo hi)
  (let ((tm (list 'CCINT lo hi)))
    (have! (list 'IN tm 'SET)
      (lambda ()
        (fact 'rr-is-set)
        (fact 'ccint-subset-rr lo hi)
        (fact 'subclass-of-set-is-set tm 'RR)
        (ass)))))

;;; The FUN NN NN typing carried by STRICTLY-MONO-NN, landed WITHOUT consuming
;;; the predicate (`mac-h' replaces what it unfolds, and every later citation
;;; wants the predicate).
(define (r9f-fun-typing! ps)
  (have! (list 'IN ps '(FUN NN NN))
    (lambda ()
      (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN ps))
      (dk-split-all!)
      (ass))))

;;; The conjunct list of a def-predicate hypothesis, unfolded destructively.
(define (r9f-unfold! name form)
  (dk-landed (lambda () (mac-h name form)))
  (dk-split-all!))

;;; =====================================================================
;;; L1.  rr-interval-seq-has-convergent-subseq
;;;
;;;   lo, hi in RR,  h in FUN(NN, CCINT(lo,hi))
;;;     =>  forsome phi. STRICTLY-MONO-NN(phi)
;;;           and forsome p in RR. CONVERGES-TO(RR-MS, SUBSEQ(h,phi), p)
;;;
;;; No inhabitedness guard: if CCINT(lo,hi) is empty (hi < lo) then
;;; FUN(NN, CCINT(lo,hi)) is empty and the hypothesis is unsatisfiable, so the
;;; statement is vacuously true and the driver never needs a point.
;;; =====================================================================

(sp (make-wff
  '(FORALL lov_
     (IMPLIES (IN lov_ RR)
       (FORALL hiv_
         (IMPLIES (IN hiv_ RR)
           (FORALL hqv_
             (IMPLIES (IN hqv_ (FUN NN (CCINT lov_ hiv_)))
               (FORSOME phv_
                 (AND (STRICTLY-MONO-NN phv_)
                      (FORSOME ptv_
                        (AND (IN ptv_ RR)
                             (CONVERGES-TO RR-MS (SUBSEQ hqv_ phv_) ptv_)))))))))))))

(define r9f-a-landed (dk-peel!))

(define r9f-a-Hfun
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
           "the typing of the sequence"))
(define r9f-a-h  (cadr r9f-a-Hfun))
(define r9f-a-V  (caddr (caddr r9f-a-Hfun)))       ; (CCINT lo hi)
(define r9f-a-lo (cadr r9f-a-V))
(define r9f-a-hi (caddr r9f-a-V))

;;; ---- the ambient set, and h as a real sequence -------------------------
(r9f-ccint-set! r9f-a-lo r9f-a-hi)
(fact 'ccint-subset-rr r9f-a-lo r9f-a-hi)                  ; V subset RR
(fact 'fun-codomain-superset r9f-a-h 'NN r9f-a-V 'RR)        ; h : NN -> RR

;;; ---- the radius sequence ----------------------------------------------
(define r9f-a-rad (dk-skolem! (dk-fact! 'null-rr-seq-exists)))
(r9f-unfold! 'NULL-RR-SEQ (list 'NULL-RR-SEQ r9f-a-rad))

(define r9f-a-HPOS
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'POS-RR)
                            (not (dk-contains? f 'FORSOME))))
           "the positivity of the radii"))
(define r9f-a-HNULL
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'FORSOME)))
           "the null-threshold clause"))

;;; ---- the sequence of grid covers ---------------------------------------
(define r9f-a-cov
  (dk-skolem! (dk-fact! 'ccint-grid-cover-seq r9f-a-lo r9f-a-hi r9f-a-rad)))
(define r9f-a-HCOV
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r9f-a-cov)))
           "the cover clause"))

;; block-family-combinatorial wants the IS-FINITE-COVER conjunct alone
(define r9f-a-HFC
  (list 'FORALL 'kq_
    (list 'IMPLIES '(IN kq_ NN)
          (list 'IS-FINITE-COVER (list r9f-a-cov 'kq_) r9f-a-V))))
(have! r9f-a-HFC
  (lambda ()
    (let ((kv (dk-di-var!)))
      (dk-split! (dk-apply! r9f-a-HCOV kv))
      (ass))))

;;; ---- the nested block family and the diagonal --------------------------
(define r9f-a-blk
  (dk-skolem! (dk-fact! 'block-family-combinatorial r9f-a-V r9f-a-h r9f-a-cov)))
(dk-split-all!)

(define r9f-a-HCAP
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r9f-a-blk)
                            (dk-contains? f 'FORSOME)))
           "the capture clause"))

(define r9f-a-phi (dk-skolem! (dk-fact! 'diagonalization r9f-a-blk)))
(dk-split-all!)

(define r9f-a-HTAIL
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r9f-a-phi)
                            (dk-contains? f r9f-a-blk)))
           "the diagonal tail clause"))

(r9f-fun-typing! r9f-a-phi)

(define r9f-a-sub (list 'SUBSEQ r9f-a-h r9f-a-phi))

(have! (list 'IN r9f-a-sub '(FUN NN RR))
  (lambda ()
    (mac 'SUBSEQ)
    (dk-lam-t!)
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r9f-a-phi 'NN 'NN kv)
      (fact 'fun-apply-type-c r9f-a-h 'NN 'RR (list r9f-a-phi kv))
      (ass))))

;;; ---- the Cauchy estimate ------------------------------------------------
;;; The claim is READ OFF the rr-cauchy-converges instance, never rebuilt: its
;;; binders are the theorem's own and a reconstruction would match nothing.

(define r9f-a-CIMP (dk-fact! 'rr-cauchy-converges r9f-a-sub))

(if (not (and (pair? r9f-a-CIMP) (eq? (car r9f-a-CIMP) 'IMPLIES)))
    (error "rake-bw-2: rr-cauchy-converges did not land as an implication"
           (expression->string r9f-a-CIMP)))

(define r9f-a-CAUCHY (cadr r9f-a-CIMP))

;; two indices past the threshold: their values sit in one cell of cov(N0)
(define (r9f-a-est! ev nz uv hin diam)
  (dk-peel!)
  (let* ((g    (dk-goal))                         ; (<= (ABS (- (sub m) (sub p))) eps)
         (diff (cadr (cadr g)))
         (mv   (cadr (cadr diff)))
         (pv   (cadr (caddr diff)))
         (hm   (list r9f-a-h (list r9f-a-phi mv)))
         (hp   (list r9f-a-h (list r9f-a-phi pv))))
    (fact 'fun-apply-type-c r9f-a-phi 'NN 'NN mv)
    (fact 'fun-apply-type-c r9f-a-phi 'NN 'NN pv)
    ;; ONE instantiation at the level, then one per index: a second
    ;; `(dk-apply! HTAIL nz _)' would re-derive the level's own formula, land
    ;; nothing new, and die as a silent no-op.
    (let ((tailn (dk-apply! r9f-a-HTAIL nz)))
      (dk-apply! tailn mv)                        ; phi(m) in blk(N0)
      (dk-apply! tailn pv))
    (dk-apply! hin (list r9f-a-phi mv))           ; h(phi m) in U
    (dk-apply! hin (list r9f-a-phi pv))
    (dk-apply! diam uv hm hp)                     ; the mesh bound, with typings
    (dk-split-all!)
    (fact 'rr-sub-in-rr hm hp)
    (fact 'rr-abs-closed (list '- hm hp))
    (fact 'fun-apply-type-c r9f-a-rad 'NN 'RR nz)
    (fact 'rr-le-trans-c (list 'ABS (list '- hm hp)) (list r9f-a-rad nz) ev)
    (subst (dk-fact! 'subseq-apply r9f-a-h r9f-a-phi mv))
    (subst (dk-fact! 'subseq-apply r9f-a-h r9f-a-phi pv))
    (ass)))

(have! r9f-a-CAUCHY
  (lambda ()
    (let* ((ls  (dk-peel!))
           (ev  (cadr (r9f-need (dk-head? 'POS-RR) "eps" ls)))
           (tyv (dk-fact! 'rr-pos-rr-in-rr ev))     ; (IN eps RR), for the chain
           (nz  (dk-skolem! (dk-apply! r9f-a-HNULL ev)))
           (hthr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                           (dk-contains? f nz)
                                           (dk-contains? f r9f-a-rad)))
                          "the threshold clause")))
      (fact 'nn-le-refl nz)
      (have! (list 'AND (list 'IN nz 'NN) (list '<= nz nz)))
      (dk-apply! hthr nz)                          ; rad(N0) <= eps
      (let* ((uv  (dk-skolem! (dk-apply! r9f-a-HCAP nz)))
             (hin (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f uv)))
                           "the capture at the threshold level"))
             (two (dk-split! (dk-apply! r9f-a-HCOV nz)))
             (diam (r9f-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                              (dk-contains? f 'ABS)))
                             "the mesh clause at the threshold level" two)))
        (witness! nz
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (if (eq? (car (dk-goal)) 'IN)
                   (ass)
                   (r9f-a-est! ev nz uv hin diam))))))))))

(define r9f-a-CONV (dk-landed-1 (lambda () (detach! r9f-a-CIMP))))

;;; ---- the limit, and its type -------------------------------------------
(r9f-unfold! 'CONVERGES r9f-a-CONV)
(define r9f-a-L (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the limit")))

(have! (list 'IN r9f-a-L 'RR)
  (lambda ()
    (mac-h 'CONVERGES-TO (list 'CONVERGES-TO 'RR-MS r9f-a-sub r9f-a-L))
    (dk-split-all!)
    (slot-h 'PTS (list 'IN r9f-a-L '(PTS RR-MS)))
    (ass)))

(witness! r9f-a-phi
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
           (ass)
           (witness! r9f-a-L (lambda () (dk-conj-close! (lambda () (ass))))))))))

(r9f-qed! 'rr-interval-seq-has-convergent-subseq)
(topic! 'rr-interval-seq-has-convergent-subseq 'analysis)
(gloss! 'rr-interval-seq-has-convergent-subseq
  "Bolzano-Weierstrass for a sequence confined to a closed interval: it has a
   convergent subsequence.  Proven from the eps-grid finite cover of the
   interval (rake-bolzano-weierstrass.scm) through the library's own
   combinatorial machinery -- infinite pigeonhole down a tower of nested index
   blocks, then diagonalization -- and rr-cauchy-converges.  No metric
   subspace structure is used or needed.")

;;; =====================================================================
;;; L2.  rr-bolzano-weierstrass -- the form consumers cite.
;;;
;;;   h in FUN(NN,RR),  bd in RR,  abs(h i) <= bd for every i in NN
;;;     =>  forsome phi. STRICTLY-MONO-NN(phi) and forsome p in RR.
;;;         CONVERGES-TO(RR-MS, SUBSEQ(h,phi), p)
;;;
;;; L1 at the interval [-bd, bd].  The whole work is typing h into that
;;; interval: `fun-codomain-iff' both ways (it is the only door that NARROWS a
;;; codomain), and the lower endpoint read off rr-abs-bound's own right-hand
;;; side rather than spelled.
;;; =====================================================================

(sp (make-wff
  '(FORALL hqv_
     (IMPLIES (IN hqv_ (FUN NN RR))
       (FORALL bdv_
         (IMPLIES (IN bdv_ RR)
           (IMPLIES (FORALL iqv_ (IMPLIES (IN iqv_ NN) (<= (ABS (hqv_ iqv_)) bdv_)))
             (FORSOME phv_
               (AND (STRICTLY-MONO-NN phv_)
                    (FORSOME ptv_
                      (AND (IN ptv_ RR)
                           (CONVERGES-TO RR-MS (SUBSEQ hqv_ phv_) ptv_))))))))))))

(define r9f-b-landed (dk-peel!))

(define r9f-b-h  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (equal? (caddr f) '(FUN NN RR))))
                                "the sequence")))
(define r9f-b-bd (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (eq? (caddr f) 'RR)))
                                "the bound")))
(define r9f-b-HB
  (r9f-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'ABS)))
            "the pointwise bound" r9f-b-landed))

;; The spelling of -bd is READ OFF rr-abs-bound at (bd, bd): its right-hand
;; side is `-bd <= bd and bd <= bd', so the first conjunct's left term IS the
;; negation, however the reader spells it.  No `crs', no guess.
(define r9f-b-PROBE (dk-fact! 'rr-abs-bound r9f-b-bd r9f-b-bd))
(define r9f-b-neg (cadr (cadr (caddr r9f-b-PROBE))))
(define r9f-b-V (list 'CCINT r9f-b-neg r9f-b-bd))

;; the partial-function half of the typing, in a lane (mac-h REPLACES it)
(have! (list 'IN r9f-b-h '(FUN NN))
  (lambda ()
    (mac-h 'fun-codomain-iff (list 'IN r9f-b-h '(FUN NN RR)))
    (dk-split-all!)
    (ass)))

(have! (list 'IN r9f-b-h (list 'FUN 'NN r9f-b-V))
  (lambda ()
    (mac 'fun-codomain-iff)
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN)
           (ass)
           (let* ((iv  (dk-di-var!))
                  (hi_ (list r9f-b-h iv)))
             (fact 'fun-apply-type-c r9f-b-h 'NN 'RR iv)
             (dk-apply! r9f-b-HB iv)                     ; abs(h i) <= bd
             (let* ((iff (dk-fact! 'rr-abs-bound hi_ r9f-b-bd))
                    (rhs (caddr iff)))
               (have! rhs
                 (lambda ()
                   (dk-only! iff (list '<= (list 'ABS hi_) r9f-b-bd))
                   (prop)))
               (dk-split-all!)
               (let* ((mem  (dk-fact! 'ccint-membership r9f-b-neg r9f-b-bd hi_))
                      (conj (caddr mem)))
                 (have! conj (lambda () (dk-conj-close! (lambda () (ass)))))
                 (dk-only! mem conj)
                 (prop)))))))))

;; (IN -bd RR).  If the term rr-abs-bound handed back and the one rr-neg-closed
;; produces were spelled differently, this `ass' would fail loudly -- which is
;; the point of landing it here rather than assuming the spelling.
(have! (list 'IN r9f-b-neg 'RR)
  (lambda ()
    (fact 'rr-neg-closed r9f-b-bd)
    (ass)))

(define r9f-b-EX
  (dk-fact! 'rr-interval-seq-has-convergent-subseq r9f-b-neg r9f-b-bd r9f-b-h))
(define r9f-b-phi (dk-skolem! r9f-b-EX))
(define r9f-b-L (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the limit")))

(witness! r9f-b-phi
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
           (ass)
           (witness! r9f-b-L (lambda () (dk-conj-close! (lambda () (ass))))))))))

(r9f-qed! 'rr-bolzano-weierstrass)
(topic! 'rr-bolzano-weierstrass 'analysis)
(gloss! 'rr-bolzano-weierstrass
  "Bolzano-Weierstrass: a bounded real sequence has a convergent subsequence.
   The bound is stated with abs and the bound itself is typed (abs(h i) <= bd
   certifies bd defined, not real).")

;;; =====================================================================
;;; L3.  bounded-block-converges -- 8-B's statement.
;;;
;;;   h in FUN(NN,RR),  bd in RR,  abs(h i) <= bd,  J in INF-SUBSETS(NN)
;;;     =>  forsome b. b in INF-SUBSETS(NN), SUBSET(b, J), and forsome p in RR.
;;;         CONVERGES-ALONG(RR-MS, h, b, p)
;;;
;;; The TRANSPORT of L2 along a block, which is part A of
;;; theorem-library/rake-block-tower.scm (block-step-converges) with "bounded
;;; real sequence" in place of "sequence in a SEQ-COMPACT space": enumerate J
;;; by e := NN-ENUM(J), apply L2 to g := i |-> h(e i), put psi := v |-> e(phi v)
;;; -- strictly monotone with all its values in J -- and take b to be the set
;;; of values of psi inside J.  b is infinite by strictly-mono-image-infinite;
;;; an index of b past psi(N) is psi(k) for a k past N
;;; (strictly-mono-le-reflect), where h(i) = SUBSEQ(g,phi)(k) is already within
;;; eps of the limit.  Not one line of the estimate mentions DIST: the value
;;; equation is carried as a quasi-equation and `subst' does the rest.
;;; =====================================================================

(sp (make-wff
  '(FORALL hqv_
     (IMPLIES (IN hqv_ (FUN NN RR))
       (FORALL bdv_
         (IMPLIES (IN bdv_ RR)
           (IMPLIES (FORALL iqv_ (IMPLIES (IN iqv_ NN) (<= (ABS (hqv_ iqv_)) bdv_)))
             (FORALL jqv_
               (IMPLIES (IN jqv_ (INF-SUBSETS NN))
                 (FORSOME bqv_
                   (AND (IN bqv_ (INF-SUBSETS NN))
                   (AND (SUBSET bqv_ jqv_)
                        (FORSOME ptv_
                          (AND (IN ptv_ RR)
                               (CONVERGES-ALONG RR-MS hqv_ bqv_ ptv_)))))))))))))))

(define r9f-c-landed (dk-peel!))

(define r9f-c-h (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                (equal? (caddr f) '(FUN NN RR))))
                               "the sequence")))
(define r9f-c-bd (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                 (eq? (caddr f) 'RR)))
                                "the bound")))
(define r9f-c-J (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                (equal? (caddr f) '(INF-SUBSETS NN))))
                               "the index block")))
(define r9f-c-HB
  (r9f-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'ABS)))
            "the pointwise bound" r9f-c-landed))

;;; ---- the enumeration of J ----------------------------------------------
(define r9f-c-e (list 'NN-ENUM r9f-c-J))

(define r9f-c-e-atoms
  (dk-split-all! (dk-landed (lambda () (fact 'nn-enum-spec r9f-c-J)))))
(define r9f-c-emono
  (r9f-need (dk-head? 'FORALL) "the monotonicity of the enumeration"
            r9f-c-e-atoms))

(have! (list 'SUBSET r9f-c-J 'NN)
  (lambda ()
    (mac-h 'inf-subsets-membership (list 'IN r9f-c-J '(INF-SUBSETS NN)))
    (dk-split-all!)
    (ass)))

(fact 'fun-codomain-superset r9f-c-e 'NN r9f-c-J 'NN)        ; e : NN -> NN
(have! (list 'STRICTLY-MONO-NN r9f-c-e)
  (lambda () (mac 'STRICTLY-MONO-NN) (from-context!)))

;;; ---- the composite sequence g = i |-> h(e i) ---------------------------
(define r9f-c-g (list 'VNB-LAMBDA 'vq_ 'NN (list r9f-c-h (list r9f-c-e 'vq_))))

(have! (list 'IN r9f-c-g '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((iv (dk-di-var!)))
      (fact 'fun-apply-type-c r9f-c-e 'NN 'NN iv)
      (fact 'fun-apply-type-c r9f-c-h 'NN 'RR (list r9f-c-e iv))
      (ass))))

(have! (list 'FORALL 'iqv_
        (list 'IMPLIES '(IN iqv_ NN)
              (list '<= (list 'ABS (list r9f-c-g 'iqv_)) r9f-c-bd)))
  (lambda ()
    (let ((iv (dk-di-var!)))
      (fact 'fun-apply-type-c r9f-c-e 'NN 'NN iv)
      (r9f-beta!)
      (dk-apply! r9f-c-HB (list r9f-c-e iv))
      (ass))))

;;; ---- Bolzano-Weierstrass at g ------------------------------------------
(define r9f-c-phi
  (dk-skolem! (dk-fact! 'rr-bolzano-weierstrass r9f-c-g r9f-c-bd)))
(define r9f-c-L (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the limit")))

(define r9f-c-phi-atoms
  (r9f-unfold! 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN r9f-c-phi)))
(define r9f-c-phimono
  (r9f-need (dk-head? 'FORALL) "the monotonicity of phi" r9f-c-phi-atoms))

;;; ---- psi = v |-> e(phi v) ----------------------------------------------
(define r9f-c-psi (list 'VNB-LAMBDA 'vq_ 'NN (list r9f-c-e (list r9f-c-phi 'vq_))))

(have! (list 'STRICTLY-MONO-NN r9f-c-psi)
  (lambda ()
    (mac 'STRICTLY-MONO-NN)
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN)
           (begin
             (dk-lam-t!)
             (let ((iv (dk-di-var!)))
               (fact 'fun-apply-type-c r9f-c-phi 'NN 'NN iv)
               (fact 'fun-apply-type-c r9f-c-e 'NN 'NN (list r9f-c-phi iv))
               (ass)))
           (let* ((ls (dk-peel!))
                  (gl (dk-goal))
                  (mv (cadr (cadr gl)))
                  (nv (cadr (caddr gl))))
             (r9f-beta!)
             (dk-apply! r9f-c-phimono mv nv)
             (fact 'fun-apply-type-c r9f-c-phi 'NN 'NN mv)
             (fact 'fun-apply-type-c r9f-c-phi 'NN 'NN nv)
             (dk-apply! r9f-c-emono (list r9f-c-phi mv) (list r9f-c-phi nv))
             (ass)))))))

(r9f-fun-typing! r9f-c-psi)

(have! (list 'FORALL 'kq_ (list 'IMPLIES '(IN kq_ NN)
               (list 'IN (list r9f-c-psi 'kq_) r9f-c-J)))
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r9f-c-phi 'NN 'NN kv)
      (r9f-beta!)
      (fact 'fun-apply-type-c r9f-c-e 'NN r9f-c-J (list r9f-c-phi kv))
      (ass))))

;;; ---- the refined block --------------------------------------------------
(define r9f-c-bmem
  (dk-fact! 'strictly-mono-image-infinite r9f-c-psi r9f-c-J))
(define r9f-c-b (cadr r9f-c-bmem))          ; the SEP, READ OFF the instance

;;; ---- the convergence hypothesis, unfolded -------------------------------
(define r9f-c-conv-atoms
  (r9f-unfold! 'CONVERGES-TO
               (list 'CONVERGES-TO 'RR-MS (list 'SUBSEQ r9f-c-g r9f-c-phi) r9f-c-L)))
(define r9f-c-epsu
  (r9f-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'POS-RR)))
            "the eps clause of the limit" r9f-c-conv-atoms))

;;; ---- the eps lane --------------------------------------------------------
(define (r9f-c-eps!)
  (dk-peel!)
  (let* ((ev   (cadr (dk-pick (dk-head? 'POS-RR) "eps")))
         (bigN (dk-skolem! (dk-apply! r9f-c-epsu ev)))
         (tail (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                         (dk-contains? f bigN)))
                        "the past-the-threshold estimate")))
    (fact 'fun-apply-type-c r9f-c-psi 'NN 'NN bigN)
    (witness! (list r9f-c-psi bigN)
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (if (eq? (car (dk-goal)) 'IN)
               (ass)
               (begin
                 (dk-peel!)
                 (let* ((hmem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                        (equal? (caddr f) r9f-c-b)))
                                       "the block membership of the index"))
                        (iv (cadr hmem))
                        (fs (dk-landed (lambda () (sep-me (list 'IN iv r9f-c-b)))))
                        (kv (dk-skolem! (r9f-need (dk-head? 'FORSOME)
                                                  "the index's psi-witness" fs))))
                   (have! (list '<= (list r9f-c-psi bigN) (list r9f-c-psi kv))
                     (lambda () (subst (list '= (list r9f-c-psi kv) iv)) (ass)))
                   (fact 'strictly-mono-le-reflect r9f-c-psi bigN kv)
                   (dk-apply! tail kv)
                   (fact 'fun-apply-type-c r9f-c-phi 'NN 'NN kv)
                   (have! (list '== (list r9f-c-h iv)
                                    (list (list 'SUBSEQ r9f-c-g r9f-c-phi) kv))
                     (lambda ()
                       (subst (list '= iv (list r9f-c-psi kv)))
                       (subst (dk-fact! 'subseq-apply r9f-c-g r9f-c-phi kv))
                       (r9f-beta!)
                       (qrfl)))
                   (subst (list '= (list r9f-c-h iv)
                                   (list (list 'SUBSEQ r9f-c-g r9f-c-phi) kv)))
                   (ass))))))))))

(witness! r9f-c-b
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((gl (dk-goal)))
         (cond
           ((eq? (car gl) 'SUBSET)
            (mac 'subset-def)
            (let ((xv (dk-di-var!)))
              (sep-me (list 'IN xv r9f-c-b))
              (ass)))
           ((eq? (car gl) 'FORSOME)
            (witness! r9f-c-L
              (lambda ()
                (dk-conj-close!
                 (lambda ()
                   (if (eq? (car (dk-goal)) 'IN)
                       (ass)
                       (begin
                         (mac 'CONVERGES-ALONG)
                         (dk-conj-close!
                          (lambda ()
                            (let ((g2 (dk-goal)))
                              (cond
                                ((eq? (car g2) 'IS-METRIC-SPACE)
                                 (fact 'rr-is-metric-space) (ass))
                                ;; (IN h (FUN NN (PTS RR-MS))) and
                                ;; (IN p (PTS RR-MS)): rewrite the accessor in
                                ;; the GOAL -- `slot', never the rr-ms@pts
                                ;; macete by name.  The rewritten sequent can
                                ;; hash-cons onto a node already grounded, in
                                ;; which case focus has moved on and a bare
                                ;; `ass' would fire on the eps clause and warn.
                                ((eq? (car g2) 'IN)
                                 (slot 'PTS)
                                 (if (eq? (car (dk-goal)) 'IN) (ass)))
                                (#t (r9f-c-eps!)))))))))))))
           (#t (ass))))))))

(r9f-qed! 'bounded-block-converges)
(topic! 'bounded-block-converges 'analysis)
(gloss! 'bounded-block-converges
  "A bounded real sequence converges along an infinite sub-block of any
   infinite index block.  The analytic brick the Ascoli route asks for: it is
   block-step-converges with `bounded real sequence' in place of `sequence in
   a sequentially compact space', and it is what the missing metric SUBSPACE
   structure would otherwise have been wanted for.")
