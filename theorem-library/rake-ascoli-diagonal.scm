;;; theorem-library/rake-ascoli-diagonal.scm
;;; ====================================================================
;;; ASCOLI-ARZELA, the last stretch -- batch 11-F.  Two theorems:
;;;
;;;   ascoli-pointwise-diagonal   the one remaining antecedent of
;;;                               `ascoli-sequential-from-diagonal'
;;;                               (theorem-library/rake-ascoli.scm), copied
;;;                               from that statement's sixth antecedent
;;;   ascoli-arzela-sequential    THE SUPPORT, stated literally
;;;                               (theorem-library/ascoli-arzela-statement.scm:120),
;;;                               in one `fact' from the two
;;;
;;; THE ROUTE (the footer of theorem-library/rake-bolzano-weierstrass-2.scm,
;;; item (C); RAKE-BATCH8-REPORTS.md entries 8-B and 8-E).  It is the RR copy of
;;; theorem-library/rake-block-tower.scm part B, with `bounded-block-converges'
;;; (PROVEN, rake-bolzano-weierstrass-2) as the totality of the dependent choice
;;; in place of SEQ-COMPACT, and then rake-diagonal-subseq.scm's L1 assembly:
;;;
;;;   coord(n) := i |-> fam(i)(dseq(n))              the n-th coordinate sequence
;;;   nxt(k,u) := { b in INF-SUBSETS(NN) : b subset u and coord(k) converges
;;;                 along b to some real }
;;;   totality of nxt  =  bounded-block-converges at coord(k), the bound the
;;;                 POINTWISE-BOUNDED hypothesis gives at the point dseq(k),
;;;                 and the block u
;;;   f   <- dc-on-nn-pred (X := INF-SUBSETS(NN), base NN, step nxt)
;;;   S   := n |-> f(succ n)                         the INDEX SHIFT
;;;   delta <- diagonalization (S)                   tail past k inside S(k)
;;;   per point dseq(m): coord-block-estimate + converges-to-transfer
;;;
;;; NO METRIC SUBSPACE anywhere: the closed bounded interval never appears as a
;;; space, only as the bound of a real sequence, which is what
;;; bounded-block-converges consumes.
;;;
;;; NO SECOND CHOICE FOR THE LIMIT.  rake-block-tower needs a product POINT, so
;;; its limit is a VNB-LAMBDA with a CHOICE body.  CONVERGES-ON asks only that
;;; each real sequence k |-> fam(k)(dseq(m)) CONVERGE -- an existential per m --
;;; so the rung's own existential is skolemized inside the m-lane and no CHOICE,
;;; and no lambda, is built for the limit at all.
;;;
;;; THE ANTECEDENTS OF ascoli-pointwise-diagonal ARE ONLY POINTWISE-BOUNDED AND
;;; IS-DENSE-SEQ: compactness, continuity and equicontinuity play no part in the
;;; diagonal extraction.  POINTWISE-BOUNDED already carries IS-METRIC-SPACE(s)
;;; and the typing of fam, and it types its bound `(IN bd RR)', which is exactly
;;; what bounded-block-converges needs (that statement's added guard, 8-E).
;;;
;;; THE INDEX SHIFT AND THE ONE REWRITE IT COSTS.  `diagonalization' is cited at
;;; the VNB-LAMBDA S, so its conclusion speaks of the REDEX (S m) while the
;;; tower's rung speaks of f(succ m).  The value equation
;;;
;;;     r11f-HSVAL:  forall n in NN.  (S n) == f(succ n)
;;;
;;; is proved once, by `lam-b' + `qrfl', and the tail clause is transported by a
;;; single `subst'.  Everything cited afterwards names f(succ m), which the
;;; context TYPES -- an applied VNB-LAMBDA is not certified defined (the LUTINS
;;; rule), and instantiating at (S m) would owe `(S m) = (S m)'.
;;;
;;; DEFINEDNESS.  Nothing is instantiated before it is typed: (dseq m) and
;;; (dseq k) by fun-apply-type-c off the IS-DENSE-SEQ typing, f(succ m) by
;;; fun-apply-type-c off the dependent choice, each coordinate value by two
;;; fun-apply-type-c steps, and the limit pv by the rung's own `(IN pv RR)'.
;;;
;;; PTS(RR-MS) vs RR.  coord-block-estimate, subseq-is-fun and
;;; converges-to-transfer are stated in a general metric space, so their typings
;;; read `(IN t (PTS RR-MS))'.  A goal of that shape is `slot PTS'; reading one
;;; off a hypothesis is `slot-h PTS' or, here, the CONVERGES-ALONG unfold in a
;;; `have!' lane.  Firing the rr-ms@pts accessor macete by name is what
;;; accessor-callsite-audit forbids.
;;;
;;; LOAD WINDOW [2936, end).  window.py prints `lo = 2935  hi = 1475  EMPTY
;;; WINDOW', and the hi is an ARTEFACT: 1475 is where the SUPPORT
;;; `ascoli-arzela-sequential' is installed (ascoli-arzela-statement.scm), not a
;;; citer.  Once that support is retired the window is [2936, end): no proof in
;;; the tree cites either theorem, and the name appears elsewhere only in
;;; comments and in generated reference pages.
;;;   lo = 2935, theorem-library/rake-bolzano-weierstrass-2, for
;;;   `bounded-block-converges'.  The other late citations: converges-to-transfer
;;;   (product-convergence, 2451), ascoli-sequential-from-diagonal (rake-ascoli,
;;;   2391), coord-block-estimate (coord-block-estimate-proof, 1604), the
;;;   definitions IS-DENSE-SEQ / CONVERGES-ON (ascoli-analytic-cores, 1481),
;;;   POINTWISE-BOUNDED (ascoli-arzela-statement, 1475), rr-is-metric-space
;;;   (rr-metric-space-proof, 1431); everything else (diagonalization,
;;;   dc-on-nn-pred, subseq-apply, subseq-is-fun, fun-apply-type-c,
;;;   nn-in-inf-subsets, inf-subsets-is-set) is far below.
;;;   So the slot is IMMEDIATELY AFTER theorem-library/rake-bolzano-weierstrass-2.
;;; No late tactic is used (no contra, prep or ineq-supply).
;;;
;;; THE RETIREMENT, for the integrator: the `support' + `warrant!' +
;;; `rests-on' of `ascoli-arzela-sequential',
;;; theorem-library/ascoli-arzela-statement.scm:120, :134 and :175.  The three
;;; `def-predicate's, the `notation!'s, the `gloss!' and the `topic!' in that
;;; file STAY (the vocabulary is what this proof uses).  The statement below is
;;; the support's own, character for character: the probe answered
;;; `install-theorem!: ascoli-arzela-sequential is already installed;
;;; re-installing the SAME STATEMENT', which is the check that it is.  Retiring
;;; it drops one entry from the PSS (reference/PSS.md) and the `reference' tier
;;; warrant with it; load.scm:2390's comment ("stays asserted until that
;;; antecedent is proven") is now stale.
;;;
;;; Helper prefix: r11f-.  CASE FOLD: this file does NOT define `r11f-S' -- it
;;; would rebind `r11f-s', the compact space, and the failure is a typing goal
;;; about PTS of a VNB-LAMBDA 250 lines later.  The shift is `r11f-shft'.
;;;
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r11f-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-ascoli-diagonal: ") (display name)
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
        (error "rake-ascoli-diagonal: unfinished" name))))

(define (r11f-need pred what lst)
  (or (any-pred pred lst)
      (error "rake-ascoli-diagonal: missing" what (map expression->string lst))))

;;; The conjunct list of a def-predicate hypothesis, unfolded DESTRUCTIVELY.
(define (r11f-unfold! name form)
  (dk-split-all! (dk-landed (lambda () (mac-h name form)))))

;;; One conjunct of a CONVERGES-ALONG hypothesis, read off in a lane (`mac-h'
;;; REPLACES what it unfolds and the predicate is wanted again).
(define (r11f-ca-read! hca)
  (mac-h 'CONVERGES-ALONG hca)
  (dk-split-all!)
  (ass))

;;; The FUN NN NN typing carried by STRICTLY-MONO-NN, landed without consuming
;;; the predicate.
(define (r11f-fun-typing! ps)
  (have! (list 'IN ps '(FUN NN NN))
    (lambda ()
      (mac-h 'STRICTLY-MONO-NN (list 'STRICTLY-MONO-NN ps))
      (dk-split-all!)
      (ass))))

;;; =====================================================================
;;; L1.  ascoli-pointwise-diagonal.
;;;
;;;   POINTWISE-BOUNDED(s, fam)
;;;     =>  forall dseq.  IS-DENSE-SEQ(s, dseq)
;;;           =>  forsome del. STRICTLY-MONO-NN(del)
;;;                            and CONVERGES-ON(s, SUBSEQ(fam, del), dseq)
;;;
;;; The consequent is the sixth antecedent of ascoli-sequential-from-diagonal
;;; (theorem-library/rake-ascoli.scm:213), copied.
;;; =====================================================================

(sp (make-wff
  '(FORALL s
     (FORALL fam
       (IMPLIES (POINTWISE-BOUNDED s fam)
         (FORALL dseq
           (IMPLIES (IS-DENSE-SEQ s dseq)
             (FORSOME del
               (AND (STRICTLY-MONO-NN del)
                    (CONVERGES-ON s (SUBSEQ fam del) dseq))))))))))

(define r11f-landed (dk-peel!))

(define r11f-HPB (dk-pick (dk-head? 'POINTWISE-BOUNDED) "the pointwise-boundedness"))
(define r11f-s   (cadr  r11f-HPB))
(define r11f-fam (caddr r11f-HPB))
(define r11f-HDS (dk-pick (dk-head? 'IS-DENSE-SEQ) "the dense sequence"))
(define r11f-dseq (caddr r11f-HDS))
(define r11f-cod (list 'FUN (list 'PTS r11f-s) 'RR))
(define r11f-X '(INF-SUBSETS NN))

;;; ---- what the two hypotheses carry -------------------------------------

(define r11f-pb-atoms (r11f-unfold! 'POINTWISE-BOUNDED r11f-HPB))
(define r11f-HB
  (r11f-need (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (dk-contains? f 'ABS)))
             "the pointwise bound clause" r11f-pb-atoms))

(define r11f-ds-atoms (r11f-unfold! 'IS-DENSE-SEQ r11f-HDS))

(fact 'rr-is-metric-space)

;;; ---- the coordinate sequences and the step set --------------------------

;; coordinate n of the family, at the n-th point of the dense sequence
(define (r11f-coord n)
  (list 'VNB-LAMBDA 'zi_ 'NN (list (list r11f-fam 'zi_) (list r11f-dseq n))))

;; nxt(k,u) = { b infinite subset of u : coord(k) converges along b }
;; The inner existential is spelled exactly as bounded-block-converges spells
;; its own, so the witness it hands back closes the SEP condition by `ass'.
(define r11f-nxt
  (list 'VNB-LAMBDA '(LIST kn_ un_) (list 'CARTESIAN 'NN r11f-X)
    (list 'SEP 'bn_ r11f-X
      (list 'AND (list 'SUBSET 'bn_ 'un_)
        (list 'FORSOME 'pn_
          (list 'AND (list 'IN 'pn_ 'RR)
                (list 'CONVERGES-ALONG 'RR-MS (r11f-coord 'kn_) 'bn_ 'pn_)))))))

;; binders k, u, y SPELLED AS IN dc-on-nn-pred, so this instance IS its hypothesis
(define r11f-tot
  (list 'FORALL 'k (list 'IMPLIES '(IN k NN)
    (list 'FORALL 'u (list 'IMPLIES (list 'IN 'u r11f-X)
      (list 'FORSOME 'y
        (list 'AND (list 'IN 'y r11f-X)
              (list 'IN 'y (list r11f-nxt 'k 'u)))))))))

(have! r11f-tot
  (lambda ()
    (dk-peel!)
    (let* ((kv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (eq? (caddr f) 'NN)))
                              "the stage")))
           (uv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (equal? (caddr f) r11f-X)))
                              "the current block"))))
      (lam-b)                                   ; kv and uv are typed
      ;; the bound POINTWISE-BOUNDED gives at the point dseq(kv)
      (fact 'fun-apply-type-c r11f-dseq 'NN (list 'PTS r11f-s) kv)
      (let* ((hv  (r11f-coord kv))
             (bdv (dk-skolem! (dk-apply! r11f-HB (list r11f-dseq kv))))
             (hbd (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                            (dk-contains? f bdv)))
                           "the bound clause at this point")))
        (have! (list 'IN hv '(FUN NN RR))
          (lambda ()
            (dk-lam-t!)
            (let ((iv (dk-di-var!)))
              (fact 'fun-apply-type-c r11f-fam 'NN r11f-cod iv)
              (fact 'fun-apply-type-c (list r11f-fam iv) (list 'PTS r11f-s) 'RR
                    (list r11f-dseq kv))
              (ass))))
        (have! (list 'FORALL 'iqv_
                 (list 'IMPLIES '(IN iqv_ NN)
                       (list '<= (list 'ABS (list hv 'iqv_)) bdv)))
          (lambda ()
            (let ((iv (dk-di-var!)))
              (dk-lam-b!)
              (dk-apply! hbd iv)
              (ass))))
        (let ((bv (dk-skolem! (dk-fact! 'bounded-block-converges hv bdv uv))))
          (witness! bv
            (lambda ()
              (dk-conj-close!
               (lambda ()
                 (let ((gl (dk-goal)))
                   (if (and (pair? (caddr gl)) (eq? (car (caddr gl)) 'SEP))
                       (dk-each-leaf! (lambda () (sep-mi))
                                      (lambda () (dk-conj-close! (lambda () (ass)))))
                       (ass))))))))))))

;;; ---- the dependent choice and the tower ---------------------------------

(fact 'nn-is-set)
(fact 'inf-subsets-is-set 'NN)
(fact 'nn-in-inf-subsets)

(define r11f-EX (dk-fact! 'dc-on-nn-pred r11f-X 'NN r11f-nxt))
(define r11f-f  (dk-skolem! r11f-EX))
;; `dk-skolem!' splits only what it landed; split the base/step pair if it stands
(let ((c (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'AND) (dk-contains? f 'succ)))
                   (dk-asms))))
  (if c (dk-split! c)))

(define r11f-fstep
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r11f-f)
                            (dk-contains? f 'succ)))
           "the per-stage step property"))

(define (r11f-Sbody n) (list r11f-f (list 'succ n)))

;; what each rung of the SHIFTED tower carries
(define r11f-HSTEP
  (list 'FORALL 'hn_ (list 'IMPLIES '(IN hn_ NN)
    (list 'AND (list 'SUBSET (r11f-Sbody 'hn_) (list r11f-f 'hn_))
      (list 'FORSOME 'pn_
        (list 'AND (list 'IN 'pn_ 'RR)
              (list 'CONVERGES-ALONG 'RR-MS (r11f-coord 'hn_)
                    (r11f-Sbody 'hn_) 'pn_)))))))

(have! r11f-HSTEP
  (lambda ()
    (let ((nv (dk-di-var!)))
      (fact 'nn-succ-closed nv)
      (fact 'fun-apply-type-c r11f-f 'NN r11f-X nv)
      (let* ((h  (dk-apply! r11f-fstep nv))
             (h2 (car (dk-landed (lambda () (lam-b-h h))))))
        (sep-me h2)
        (ass)))))

(define r11f-shft (list 'VNB-LAMBDA 'sw_ 'NN (r11f-Sbody 'sw_)))

(have! (list 'IN r11f-shft (list 'FUN 'NN r11f-X))
  (lambda ()
    (dk-lam-t!)
    (let ((nv (dk-di-var!)))
      (fact 'nn-succ-closed nv)
      (fact 'fun-apply-type-c r11f-f 'NN r11f-X (list 'succ nv))
      (ass))))

;; the VALUE equation of the shift, proved once: every later citation names
;; f(succ n), which the context types, never the redex (S n).
(define r11f-HSVAL
  (list 'FORALL 'vn_ (list 'IMPLIES '(IN vn_ NN)
         (list '== (list r11f-shft 'vn_) (r11f-Sbody 'vn_)))))

(have! r11f-HSVAL
  (lambda ()
    (dk-di-var!)
    (dk-lam-b!)
    (qrfl)))

(have! (list 'FORALL 'tn_ (list 'IMPLIES '(IN tn_ NN)
         (list 'SUBSET (list r11f-shft (list 'succ 'tn_)) (list r11f-shft 'tn_))))
  (lambda ()
    (let ((kv (dk-di-var!)))
      (fact 'nn-succ-closed kv)
      (dk-lam-b!)
      (dk-split! (dk-apply! r11f-HSTEP (list 'succ kv)))
      (ass))))

;;; ---- the diagonal --------------------------------------------------------

(define r11f-delta (dk-skolem! (dk-fact! 'diagonalization r11f-shft)))
(define r11f-HTAIL
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r11f-delta)
                            (dk-contains? f r11f-shft)))
           "the diagonal tail clause"))

(r11f-fun-typing! r11f-delta)

(define r11f-sub (list 'SUBSEQ r11f-fam r11f-delta))

(have! (list 'IN r11f-sub (list 'FUN 'NN r11f-cod))
  (lambda ()
    (mac 'SUBSEQ)
    (dk-lam-t!)
    (let ((kv (dk-di-var!)))
      (fact 'fun-apply-type-c r11f-delta 'NN 'NN kv)
      (fact 'fun-apply-type-c r11f-fam 'NN r11f-cod (list r11f-delta kv))
      (ass))))

;;; ---- the per-point lane --------------------------------------------------

(define (r11f-conv!)
  (let* ((mv  (dk-di-var!))
         (hgl (caddr (dk-goal)))          ; k |-> (SUBSEQ(fam,delta)(k))(dseq m)
         (two (dk-split! (dk-apply! r11f-HSTEP mv)))
         (exl (r11f-need (dk-head? 'FORSOME) "the rung's limit point" two))
         (pv  (dk-skolem! exl))
         (hca (dk-pick (dk-head? 'CONVERGES-ALONG) "the rung's block convergence"))
         (gsq (caddr hca))                ; i |-> fam(i)(dseq m)
         (blk (cadddr hca))               ; f(succ m)
         (sm  (list r11f-shft mv))
         (fsb (list 'SUBSEQ gsq r11f-delta)))
    ;; TYPE FIRST: the point, and the block the rung converges along
    (fact 'fun-apply-type-c r11f-dseq 'NN (list 'PTS r11f-s) mv)
    (fact 'nn-succ-closed mv)
    (fact 'fun-apply-type-c r11f-f 'NN r11f-X (list 'succ mv))
    ;; the tail of delta past mv lands in blk.  `diagonalization' says (S mv);
    ;; the value equation turns that into f(succ mv), which is typed.
    (dk-apply! r11f-HSVAL mv)
    (let ((htm (dk-apply! r11f-HTAIL mv)))
      (have! (list 'FORALL 'jn_
               (list 'IMPLIES '(IN jn_ NN)
                 (list 'IMPLIES (list '<= mv 'jn_)
                       (list 'IN (list r11f-delta 'jn_) blk))))
        (lambda ()
          (let* ((ls (dk-peel!))
                 (jv (cadr (r11f-need (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                       (eq? (caddr f) 'NN)))
                                      "the tail index" ls))))
            (dk-apply! htm jv)
            (subst (list '= blk sm))
            (ass)))))
    (dk-fact! 'coord-block-estimate 'RR-MS gsq blk pv r11f-delta mv)
    ;; the PTS(RR-MS) typings converges-to-transfer asks for
    (have! (list 'IN gsq (list 'FUN 'NN '(PTS RR-MS)))
      (lambda () (r11f-ca-read! hca)))
    (have! (list 'IN pv '(PTS RR-MS))
      (lambda () (slot 'PTS) (ass)))
    (have! (list 'AND (list 'IN gsq (list 'FUN 'NN '(PTS RR-MS)))
                      (list 'STRICTLY-MONO-NN r11f-delta)))
    (dk-fact! 'subseq-is-fun 'RR-MS gsq r11f-delta)
    (have! (list 'IN hgl (list 'FUN 'NN '(PTS RR-MS)))
      (lambda ()
        (dk-lam-t!)
        (let ((kv (dk-di-var!)))
          (fact 'fun-apply-type-c r11f-delta 'NN 'NN kv)
          (subst (dk-fact! 'subseq-apply r11f-fam r11f-delta kv))
          (fact 'fun-apply-type-c r11f-fam 'NN r11f-cod (list r11f-delta kv))
          (fact 'fun-apply-type-c (list r11f-fam (list r11f-delta kv))
                (list 'PTS r11f-s) 'RR (list r11f-dseq mv))
          (slot 'PTS)
          (ass))))
    ;; the two sequences are POINTWISE equal; only the pointwise equation is
    ;; ever beta-reduced, at a peeled and typed index
    (have! (list 'FORALL 'jn_
             (list 'IMPLIES '(IN jn_ NN)
                   (list '= (list hgl 'jn_) (list fsb 'jn_))))
      (lambda ()
        (let ((jv (dk-di-var!)))
          (fact 'fun-apply-type-c r11f-delta 'NN 'NN jv)
          (fact 'fun-apply-type-c r11f-fam 'NN r11f-cod (list r11f-delta jv))
          (fact 'fun-apply-type-c (list r11f-fam (list r11f-delta jv))
                (list 'PTS r11f-s) 'RR (list r11f-dseq mv))
          (dk-lam-b!)                                      ; the OUTER application
          (subst (dk-fact! 'subseq-apply r11f-fam r11f-delta jv))
          (subst (dk-fact! 'subseq-apply gsq r11f-delta jv))
          (dk-lam-b!)                                      ; gsq at the TYPED index
          (rfl))))
    (fact 'converges-to-transfer 'RR-MS fsb hgl pv)
    (mac 'CONVERGES)
    (witness! pv (lambda () (ass)))))

(witness! r11f-delta
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
           (ass)
           (begin
             (mac 'CONVERGES-ON)
             (dk-conj-close!
              (lambda ()
                (let ((g2 (dk-goal)))
                  (cond ((eq? (car g2) 'IS-METRIC-SPACE) (ass))
                        ((eq? (car g2) 'IN) (ass))
                        (#t (r11f-conv!))))))))))))

(r11f-qed! 'ascoli-pointwise-diagonal)
(topic! 'ascoli-pointwise-diagonal 'topology)
(gloss! 'ascoli-pointwise-diagonal
  "The pointwise diagonal extraction behind Ascoli-Arzela: if the family fam is
   POINTWISE-BOUNDED on s, then for every dense sequence dseq of s there is one
   strictly monotone del such that SUBSEQ(fam, del) converges at EVERY point of
   dseq.  Proven as the RR copy of the refinement tower of
   theorem-library/rake-block-tower.scm: one dependent choice over the infinite
   subsets of NN whose totality is bounded-block-converges (Bolzano-Weierstrass
   along an infinite index block), the index shift S(n) = f(succ n), then
   diagonalization and coord-block-estimate.  No metric subspace structure is
   used: the bound enters only as a bound on a real sequence.")

;;; =====================================================================
;;; L2.  ascoli-arzela-sequential -- THE SUPPORT, stated literally
;;; (theorem-library/ascoli-arzela-statement.scm:120), from L1 and
;;; `ascoli-sequential-from-diagonal' (theorem-library/rake-ascoli.scm).
;;;
;;; The inhabitedness guard is the second antecedent, as that file carries it
;;; since 2026-09-20.
;;; =====================================================================

(sp (make-wff
  (forall-guarded '(s fam)
    (list
      '(IS-COMPACT s)
      '(FORSOME x (IN x (PTS s)))
      '(IN fam (FUN NN (FUN (PTS s) RR)))
      '(FORALL k (IMPLIES (IN k NN) (IS-CONTINUOUS s RR-MS (fam k))))
      '(IS-EQUICONTINUOUS s RR-MS fam)
      '(POINTWISE-BOUNDED s fam))
    (forsome-guarded 'del '(STRICTLY-MONO-NN del)
      (forsome-guarded 'g '(IN g (FUN (PTS s) RR))
        '(AND (IS-CONTINUOUS s RR-MS g)
              (CONVERGES-UNIFORMLY s (SUBSEQ fam del) g)))))))

(define r11f-a-landed (dk-peel!))

(define r11f-a-HPB (dk-pick (dk-head? 'POINTWISE-BOUNDED) "the pointwise-boundedness"))
(define r11f-a-s   (cadr  r11f-a-HPB))
(define r11f-a-fam (caddr r11f-a-HPB))

(fact 'ascoli-pointwise-diagonal r11f-a-s r11f-a-fam)
(fact 'ascoli-sequential-from-diagonal r11f-a-s r11f-a-fam)
(ass)

(r11f-qed! 'ascoli-arzela-sequential)
;; topic! and gloss! for this name stay in theorem-library/ascoli-arzela-statement.scm
;; (the `support' there is what the integrator retires) -- not repeated here.
