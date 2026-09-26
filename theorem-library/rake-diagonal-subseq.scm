;;; theorem-library/rake-diagonal-subseq.scm
;;; ====================================================================
;;; The cross-coordinate DIAGONAL argument, and the sequential Tychonoff
;;; assembly on top of it.  Two supports of theorem-library/seq-compact-product
;;; are proven here:
;;;
;;;   coordinatewise-diagonal-subseq   (seq-compact-product.scm:142)
;;;   seq-compact-countable-product    (seq-compact-product.scm:176)
;;;
;;; L1.  coordinatewise-diagonal-subseq.  The keystone's warrant describes a
;;; construction by dependent choice over the coordinate index.  That is NOT
;;; the route taken here: the tree already owns the three pieces the argument
;;; factors into, and the proof is their assembly.
;;;
;;;   convergence-block-tower  (still ASSERTED, seq-compact-product.scm:91)
;;;       gives a NESTED tower S : NN -> INF-SUBSETS(NN) and a product point L
;;;       with coordinate n of seq convergent ALONG S(n) to L(n);
;;;   diagonalization          (PROVEN, theorem-library/diagonalization.scm)
;;;       turns the nested tower into ONE strictly monotone delta whose whole
;;;       TAIL past k lands in S(k);
;;;   coord-block-estimate     (PROVEN, coord-block-estimate-proof.scm)
;;;       converts "converges along S(n)" + "delta's tail past n is in S(n)"
;;;       into honest CONVERGES-TO of SUBSEQ(coordinate-n sequence, delta).
;;;
;;; The one mechanical obstacle is that coord-block-estimate concludes about
;;; SUBSEQ( i |-> seq(i)(n), delta ) while the support's statement is about
;;; k |-> (SUBSEQ(seq,delta)(k))(n).  The two terms are beta-equal but not
;;; equal, and the redexes sit UNDER the outer binder.  The metric lane's
;;; transfer theorem `converges-to-transfer' (product-convergence.scm) is
;;; exactly the bridge -- pointwise-equal sequences converge alike -- so the
;;; only beta-reduction done here is on the POINTWISE equation, where the index
;;; is a peeled, typed eigenvariable.
;;;
;;; L2.  seq-compact-countable-product is the assembly its own warrant text
;;; describes: unfold SEQ-COMPACT and PRODUCT-METRIC in the goal, read the
;;; carrier off with product-metric-carrier (so the sequence hypothesis lands
;;; already spelled in PRODUCT-CARRIER), take L1's diagonal, and upgrade
;;; coordinatewise convergence to product convergence with
;;; product-convergence-coordinatewise used as a MACETE on the goal (the
;;; tychonoff-proof.scm move), its guards discharged from the context.
;;;
;;; DEFINEDNESS.  (L n) is an application of a variable that is typed only as a
;;; member of PRODUCT-CARRIER, and (ms n) is an application of a bare variable:
;;; neither is certified by pi--defined? on its own.  Both are certified by the
;;; three read-offs of CONVERGES-ALONG -- (IS-METRIC-SPACE (ms n)),
;;; (IN gseq (FUN NN (PTS (ms n)))), (IN (L n) (PTS (ms n))) -- which are
;;; therefore landed BEFORE anything is instantiated at them.  `mac-h' REPLACES
;;; the hypothesis it unfolds and CONVERGES-ALONG is needed intact afterwards,
;;; so each read-off is done inside its own `have!' lane.
;;;
;;; LOAD WINDOW: [466, 455) -- EMPTY as load.scm stands.  (Positions are 0-based
;;; indices into *vnb-files*, load.scm:81.)
;;;   lo = 466: the latest citations are `converges-to-transfer' and
;;;   `product-convergence-coordinatewise', both in theorem-library/product-
;;;   convergence (465).  The others are product-is-metric-space (454),
;;;   product-summable (453, product-metric-carrier), dyadic-weights (448,
;;;   product-metric-default-summable), coord-block-estimate-proof (351),
;;;   diagonalization (310), rake-analysis2 (198, subseq-is-fun); the asserted
;;;   convergence-block-tower is in seq-compact-product (130).
;;;   hi = 455: theorem-library/tychonoff-proof, the ONLY proof citing
;;;   seq-compact-countable-product, loads BEFORE product-convergence.
;;; THE INTEGRATOR MUST MOVE theorem-library/tychonoff-proof to just after this
;;; file: it cites nothing that lands in 456..465, and the only names citing
;;; compact-countable-product after it are the metadata files pss-topics (563)
;;; and reference-topics (565).  Nothing else in the tree cites either support
;;; in a proof; coordinatewise-diagonal-subseq is otherwise named only in
;;; comments and in the `rests-on' list of ascoli-arzela-statement.scm:169.
;;;
;;; Helper prefix: r8i-.
;;; ====================================================================

;;; ---- file-local driver helpers ---------------------------------------

(define (r8i-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-diagonal-subseq: ") (display name)
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
        (error "rake-diagonal-subseq: unfinished" name))))

;;; =====================================================================
;;; L0.  subseq-apply -- MOVED on 2026-09-19 (batch 8-K2) to its own early
;;; home, theorem-library/subseq-apply.scm, which loads just after
;;; theorem-library/equality-basics.  It was written three times in one day
;;; (here, in rake-block-tower.scm as `subseq-value-at', in
;;; rake-lebesgue-number.scm as `subseq-value'); the one copy is cited below by
;;; the name `subseq-apply'.  The original text of this block is in
;;; archive/2026-09-19-batch8/rake-diagonal-subseq.scm.
;;; =====================================================================

;;; =====================================================================
;;; L1.  coordinatewise-diagonal-subseq -- THE SUPPORT, stated literally
;;; (theorem-library/seq-compact-product.scm:142).
;;; =====================================================================

(sp (make-wff
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
         (FORSOME delta
           (AND (STRICTLY-MONO-NN delta)
                (FORSOME L
                  (AND (IN L (PRODUCT-CARRIER ms))
                       (FORALL n (IMPLIES (IN n NN)
                         (CONVERGES-TO (ms n)
                           (VNB-LAMBDA k NN (((SUBSEQ seq delta) k) n))
                           (L n)))))))))))))))

(define r8i-d-landed (dk-peel!))

(define r8i-d-Hseq
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
           "the typing of the product sequence"))
(define r8i-d-seq (cadr r8i-d-Hseq))
(define r8i-d-ms  (cadr (caddr (caddr r8i-d-Hseq))))

;; the tower: S nested, L the product limit point
(define r8i-d-EX  (dk-fact! 'convergence-block-tower r8i-d-ms r8i-d-seq))
(define r8i-d-S   (dk-skolem! r8i-d-EX))
(define r8i-d-EXL (dk-pick (dk-head? 'FORSOME) "the tower's limit point"))
(define r8i-d-L   (dk-skolem! r8i-d-EXL))
(define r8i-d-HCONV
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f 'CONVERGES-ALONG)))
           "the coordinatewise block convergence"))

;; the diagonal: one strictly monotone delta whose tail past k is in S(k)
(define r8i-d-DEX   (dk-fact! 'diagonalization r8i-d-S))
(define r8i-d-delta (dk-skolem! r8i-d-DEX))
(define r8i-d-HTAIL
  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                            (dk-contains? f r8i-d-delta)))
           "the diagonal tail property"))
(define r8i-d-HSM (list 'STRICTLY-MONO-NN r8i-d-delta))

(have! (list 'IN r8i-d-delta '(FUN NN NN))
  (lambda () (mac-h 'strictly-mono-nn r8i-d-HSM) (dk-split-all!) (ass)))

;;; ---- the per-coordinate work -----------------------------------------

;; read one conjunct off CONVERGES-ALONG; destructive, so always in a lane
(define (r8i-ca-read! hca)
  (mac-h 'converges-along hca)
  (dk-split-all!)
  (ass))

;; land  (IN ((seq (delta kv)) nv) (PTS spc))  -- the value typing that both
;; `rfl' (definedness) and the lambda typing lane need
(define (r8i-coord-value! kv spc gsq)
  (fact 'fun-apply-type-c r8i-d-delta 'NN 'NN kv)
  (lam-b-h (dk-fact! 'fun-apply-type-c gsq 'NN (list 'PTS spc)
                     (list r8i-d-delta kv))))

(define (r8i-d-coord!)
  (let* ((nv  (dk-di-var!))
         (g   (dk-goal))
         (spc (cadr g))                       ; (ms nv)
         (hgl (caddr g))                      ; k |-> (SUBSEQ seq delta)(k)(nv)
         (lp  (cadddr g))                     ; (L nv)
         (hca (dk-apply! r8i-d-HCONV nv))     ; CONVERGES-ALONG (ms nv) gsq (S nv) (L nv)
         (gsq (caddr hca))                    ; i |-> (seq i)(nv)
         (blk (cadddr hca))                   ; (S nv)
         (fsb (list 'SUBSEQ gsq r8i-d-delta)))
    ;; the three read-offs -- also the definedness certificates for spc and lp
    (have! (list 'IS-METRIC-SPACE spc) (lambda () (r8i-ca-read! hca)))
    (have! (list 'IN gsq (list 'FUN 'NN (list 'PTS spc))) (lambda () (r8i-ca-read! hca)))
    (have! (list 'IN lp (list 'PTS spc)) (lambda () (r8i-ca-read! hca)))
    ;; the tail of delta past nv lands in S(nv): coord-block-estimate's 4th antecedent
    (dk-apply! r8i-d-HTAIL nv)
    (dk-fact! 'coord-block-estimate spc gsq blk lp r8i-d-delta nv)
    ;; SUBSEQ(gsq,delta) is a sequence of the factor
    (have! (list 'AND (list 'IN gsq (list 'FUN 'NN (list 'PTS spc))) r8i-d-HSM))
    (dk-fact! 'subseq-is-fun spc gsq r8i-d-delta)
    ;; and so is the support's own lambda
    (have! (list 'IN hgl (list 'FUN 'NN (list 'PTS spc)))
      (lambda ()
        (dk-lam-t!)
        (let ((kv (dk-di-var!)))
          (r8i-coord-value! kv spc gsq)
          (subst (dk-fact! 'subseq-apply r8i-d-seq r8i-d-delta kv))
          (ass))))
    ;; the two are pointwise equal
    (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                                   (list '= (list hgl 'j_) (list fsb 'j_))))
      (lambda ()
        (let ((jv (dk-di-var!)))
          (r8i-coord-value! jv spc gsq)
          (lam-b)                                  ; the OUTER application only
          (subst (dk-fact! 'subseq-apply r8i-d-seq r8i-d-delta jv))
          (subst (dk-fact! 'subseq-apply gsq r8i-d-delta jv))
          (lam-b)                                  ; gsq at the TYPED (delta jv)
          (rfl))))
    (fact 'converges-to-transfer spc fsb hgl lp)
    (ass)))

(witness! r8i-d-delta
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (if (eq? (car g) 'STRICTLY-MONO-NN)
             (ass)
             (witness! r8i-d-L
               (lambda ()
                 (dk-conj-close!
                  (lambda ()
                    (let ((g2 (dk-goal)))
                      (if (eq? (car g2) 'IN) (ass) (r8i-d-coord!)))))))))))))

(r8i-qed! 'coordinatewise-diagonal-subseq)
;; topic! for this name is set in theorem-library/pss-topics.scm:197 -- not repeated here.

;;; =====================================================================
;;; L2.  seq-compact-countable-product -- THE SUPPORT, stated literally
;;; (theorem-library/seq-compact-product.scm:176).
;;; =====================================================================

(define r8i-a-wdef '(VNB-LAMBDA n NN (/ 1 (power 2 (+ n 1)))))

(sp (make-wff
  '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SEQ-COMPACT (ms n))))
       (SEQ-COMPACT (PRODUCT-METRIC ms)))))))

(define r8i-a-landed (dk-peel!))
(define r8i-a-ms (cadr (dk-pick (dk-head? 'IS-MS-SEQUENCE) "the factor sequence")))
(define r8i-a-pmw (list 'PRODUCT-METRIC-W r8i-a-ms r8i-a-wdef))

(fact 'product-metric-default-summable)      ; SUMMABLE-WEIGHT wdef
(mac 'SEQ-COMPACT)
(mac 'PRODUCT-METRIC)
(mac 'product-metric-carrier)                ; PTS(PRODUCT-METRIC-W ms w) -> PRODUCT-CARRIER ms

(define (r8i-a-seq!)
  (let* ((fv  (dk-di-var!))
         (EX  (dk-fact! 'coordinatewise-diagonal-subseq r8i-a-ms fv))
         (dl  (dk-skolem! EX))
         (EXL (dk-pick (dk-head? 'FORSOME) "the diagonal's limit point"))
         (lv  (dk-skolem! EXL))
         (fsb (list 'SUBSEQ fv dl))
         (pts (list 'PTS r8i-a-pmw))
         (pca (list 'PRODUCT-CARRIER r8i-a-ms)))
    (have! (list 'IN fv (list 'FUN 'NN pts))
      (lambda () (mac 'product-metric-carrier) (ass)))
    (have! (list 'AND (list 'IN fv (list 'FUN 'NN pts)) (list 'STRICTLY-MONO-NN dl)))
    (dk-fact! 'subseq-is-fun r8i-a-pmw fv dl)
    (have! (list 'IN fsb (list 'FUN 'NN pca))
      (lambda ()
        (fact 'product-metric-carrier r8i-a-ms r8i-a-wdef)
        (subst (list '= pca pts))
        (ass)))
    (witness! dl
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (let ((g (dk-goal)))
             (if (eq? (car g) 'STRICTLY-MONO-NN)
                 (ass)
                 (witness! lv
                   (lambda ()
                     (dk-conj-close!
                      (lambda ()
                        (let ((g2 (dk-goal)))
                          (if (eq? (car g2) 'IN)
                              (ass)
                              (begin (mac 'product-convergence-coordinatewise)
                                     (ass)
                                     (ass-all))))))))))))))))

(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (eq? (car g) 'IS-METRIC-SPACE)
         (begin (fact 'product-is-metric-space r8i-a-ms r8i-a-wdef) (ass))
         (r8i-a-seq!)))))

(r8i-qed! 'seq-compact-countable-product)
;; topic! for this name is set in theorem-library/pss-topics.scm:296 -- not repeated here.

;;; =====================================================================
;;; WHAT IS LEFT: convergence-block-tower (seq-compact-product.scm:91).
;;;
;;; It is now the SOLE leaf of both proofs above, and (through
;;; coordinatewise-diagonal-subseq) of the Ascoli route.  The statement is
;;; sound -- every index is typed, each factor is guarded by SEQ-COMPACT, the
;;; blocks are guarded by INF-SUBSETS(NN), and CONVERGES-ALONG carries its own
;;; IS-METRIC-SPACE / FUN / point typings -- so it is a proof obligation, not a
;;; repair.  The route, with the bricks it wants, so the next agent does not
;;; have to rediscover it:
;;;
;;;   (A) BLOCK-STEP.  t SEQ-COMPACT, h in FUN(NN,PTS t), J in INF-SUBSETS(NN)
;;;       ==> some J_ in INF-SUBSETS(NN) with J_ SUBSET J and h convergent
;;;       ALONG J_.  Enumerate J by e := NN-ENUM(J), apply SEQ-COMPACT to
;;;       h o e, get phi and the limit, put psi := e o phi and
;;;       J_ := SEP m J (FORSOME k in NN. m = psi(k)).
;;;   (B) the tower.  dc-on-nn-pred at X := INF-SUBSETS(NN), a := NN,
;;;       nxt(k,J) := SEP J_ (INF-SUBSETS NN) (J_ SUBSET J and coordinate k of
;;;       seq converges along J_); totality is (A).  S := n |-> aux(succ n) --
;;;       the index shift of theorem-library/block-family-combinatorial-proof,
;;;       which is the model for this whole step.
;;;   (C) the limit L.  A second dc-on-nn-pred, used as COUNTABLE CHOICE (the
;;;       step set ignores its second argument), at
;;;       X := BIG-UNION n NN (PTS (ms n)), base (seq 0)(0),
;;;       nxt(k,u) := SEP p X (CONVERGES-ALONG (ms k) (coord k) (S k) p);
;;;       L := n |-> f(succ n); L in PRODUCT-CARRIER by lam-t + in-sep.
;;;
;;; MISSING BRICKS, in the order they bite:
;;;   * nn-enum-spec (theorem-library/subsequence-capture.scm:37) is still an
;;;     ASSERTED support, so (A) cannot reach `modulo 0' until it is proven.
;;;     It should now be cheap: subsequence-capture is PROVEN
;;;     (rake-subseq-leaves.scm) and makes the SEP non-empty, so the CHOICE is
;;;     the `choose!' / `in-sep!' move of rake-dc-on-nn.scm.
;;;   * "the image of a strictly monotone NN -> NN map is in INF-SUBSETS(NN)".
;;;     Not in the tree.  Infinitude does NOT need CARD arithmetic: take the
;;;     excluded-middle split on (IN (CARD J_) NN) and refute the finite side
;;;     with `nn-finite-subset-bounded' plus `strictly-mono-ge-id'
;;;     (psi(thr+1) >= thr+1 > thr is in J_), the pattern of
;;;     theorem-library/subsequence-principle.scm:220-270.
;;;   * ORDER REFLECTION for a strictly monotone psi: psi(k) >= psi(N) => k >= N.
;;;     Not in the tree either (monotone-inverse.scm is about CCINT).  One
;;;     `nn-le-total' plus the strict-monotone clause.
;;;   * composition typing h o e and the SUBSEQ value equations: `subseq-apply'
;;;     (theorem-library/subseq-apply.scm) plus compose-type-2
;;;     (rake-compose-typing.scm).
;;;   * sethood of BIG-UNION n NN (PTS (ms n)) for (C): the `bu-set' tactic, as
;;;     in product-is-metric-space.scm's pim-carrier-set!.
;;; Estimate: 350-500 lines over the three parts, plus nn-enum-spec.
;;; =====================================================================
