;;; rake-compact-iff-seq-compact.scm -- the FORWARD half of Prop 3.12 (1)=>(3'):
;;; a compact metric space is sequentially compact.
;;;
;;; Three theorems, in dependency order:
;;;
;;;   cluster-point-has-convergent-subseq   (new; the content)
;;;       forall s, f, x.  CLUSTER-POINT(s,f,x)  =>
;;;         forsome phi.  STRICTLY-MONO-NN(phi) and CONVERGES-TO(s, SUBSEQ(f,phi), x)
;;;
;;;   compact-implies-seq-compact           (the forward half of the support
;;;       compact-iff-seq-compact, theorem-library/seq-compact-product.scm:52,
;;;       antecedent copied literally)
;;;       forall s.  IS-METRIC-SPACE s  =>  IS-COMPACT s  =>  SEQ-COMPACT s
;;;
;;; THE STATEMENT compact-iff-seq-compact is NEITHER false NOR underdetermined.
;;; The two species checked (7-H):
;;;   * phi in SEQ-COMPACT is TYPED -- STRICTLY-MONO-NN(phi) has (IN phi (FUN NN NN))
;;;     as its first conjunct (cauchy-subsequence.scm:48), so the existential is
;;;     not over an untyped object;
;;;   * the EMPTY metric space satisfies both sides.  IS-COMPACT: F := {} is a
;;;     finite subcover of every cover, since BIG-UNION over {} is {} = PTS(s).
;;;     SEQ-COMPACT: FUN(NN, {}) is empty (NN is inhabited), so its universal is
;;;     vacuous.  No guard is missing.
;;;
;;; THE ROUTE (forward).  A cluster point is the limit of a subsequence built by
;;; ONE dependent choice, the rake-subseq-leaves.scm `subsequence-capture'
;;; pattern with the step set carrying the radius as well as the index:
;;;
;;;     nxt(k, u) = { y in NN :  u < y  and  d(f y, x) < rad(succ k) }
;;;
;;; where rad is any positive null sequence (null-rr-seq-exists).  nxt(k,u) is
;;; non-empty for every (k,u) -- that is exactly the CLUSTER-POINT property at
;;; eps := rad(succ k) and m := succ u, the `succ u <= y => u < y' step being one
;;; `ineq' once succ u = u + 1 is landed (nn-succ-plus-one) and succ u is typed
;;; in RR (the LUTINS/`ineq' rule: an untyped succ-term poisons the call).
;;; dc-on-nn-pred at X := NN then returns phi : NN -> NN with phi(0) = a (a base
;;; index supplied by the same cluster property at m := 0, eps := rad 0) and
;;; phi(succ k) in nxt(k, phi k).  Reading the SEP membership off each stage
;;; gives BOTH
;;;     phi(k) < phi(succ k)                     -> nn-step-strictly-mono
;;;     d(f(phi(succ k)), x) < rad(succ k)       -> the tail estimate,
;;; and an `ni' induction (whose step does not even use its hypothesis; the base
;;; is the phi(0) = a substitution) lifts the second to
;;;     forall k in NN.  d(f(phi k), x) < rad k.
;;; CONVERGES-TO then needs, for eps > 0, the NULL-RR-SEQ threshold N past which
;;; rad k <= eps; one `ineq' composes the two.  No choice beyond dc-on-nn-pred,
;;; no CARD, no pigeonhole.
;;;
;;; THE CONVERSE (SEQ-COMPACT => IS-COMPACT) IS NOT PROVEN HERE; see the closing
;;; block for exactly what it still needs.
;;;
;;; CITATIONS and load positions (0-based over *vnb-files*, 2026-09-19):
;;;   compact-seq-has-cluster      theorem-library/rake-compact-cluster   297
;;;   null-rr-seq-exists,
;;;   nn-step-strictly-mono        theorem-library/rake-subseq-leaves     305
;;;   nn-succ-plus-one             theorem-library/nn-parity-proof        220
;;;   op-typing (metric-dist-real)                                        207
;;;   subseq-is-fun                theorem-library/rake-analysis2         198
;;;   rr-pos-rr-in-rr              theorem-library/pos-rr-bridges         176
;;;   nn-in-rr                     theorem-library/nn-order-basics        167
;;;   dc-on-nn-pred                theorem-library/rake-dc-on-nn          161
;;;   fun-apply-type-c             theorem-library/fun-apply-type-proof   160
;;;   SEQ-COMPACT (the definition)  theorem-library/seq-compact-product   130
;;;   CLUSTER-POINT, IS-COMPACT    structure-library/compactness           48
;;;   CONVERGES-TO                 structure-library/metric-completeness   44
;;;   STRICTLY-MONO-NN, SUBSEQ,
;;;   NULL-RR-SEQ                  theorem-library/cauchy-subsequence      90
;;;   nn-is-set, nn-zero-in, nn-succ-closed, rr-zero-in, rr-one-in,
;;;   rr-add-closed                number-systems (primitive)
;;;
;;; LOAD WINDOW [306, 454).
;;;   lo = 305, theorem-library/rake-subseq-leaves (null-rr-seq-exists and
;;;   nn-step-strictly-mono), the MAXIMUM over every citation above;
;;;   rake-compact-cluster (297) is the next latest.
;;;   hi = 454, theorem-library/tychonoff-proof, the only file that cites
;;;   compact-iff-seq-compact in a proof (:65 and :78).
;;;   The natural slot is immediately after theorem-library/rake-subseq-leaves.
;;;
;;; No late tactic is used (`interactive', `driver-kit', `ineq' only).
;;;
;;; Helper prefix: r8h-.

;;; ---- file-local driver helpers ----------------------------------------

(define (r8h-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-compact-iff-seq-compact: ") (display name)
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
        (error "rake-compact-iff-seq-compact: unfinished" name))))

;; `ineq' by FORMULA, not by index (the indices are 1-based into the context and
;; a forward assembly renumbers them at every step).
(define (r8h-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r8h-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r8h-ineq . forms) (apply ineq (map r8h-idx forms)))

;; the arguments of the first application of HEAD (a term, here the step
;; lambda) inside FORM.  Both eigenvariables of the totality lane are typed
;; (IN _ NN), so they cannot be told apart in the CONTEXT; they are read off
;; the GOAL, where they sit in the application (nxt k u).
(define (r8h-app-args form head)
  (let loop ((e form))
    (cond ((not (pair? e)) #f)
          ((equal? (car e) head) (cdr e))
          (#t (let scan ((l e))
                (cond ((not (pair? l)) #f)
                      ((loop (car l)))
                      (#t (scan (cdr l)))))))))

(define (r8h-typed-var landed what)
  (let ((h (or (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (eq? (caddr f) 'NN)
                                            (symbol? (cadr f))))
                           landed)
               (error "rake-compact-iff-seq-compact: no NN typing landed" what))))
    (cadr h)))

;;; =====================================================================
;;; cluster-point-has-convergent-subseq
;;;
;;;   forall s, f, x.  CLUSTER-POINT(s, f, x)  =>
;;;     forsome phi.  STRICTLY-MONO-NN(phi)  and  CONVERGES-TO(s, SUBSEQ(f,phi), x)
;;;
;;; The tree had the two halves of Prop 3.12 (3) in different currencies --
;;; CLUSTER-POINT (compactness.scm) and the convergent subsequence
;;; (SEQ-COMPACT, seq-compact-product.scm) -- and nothing joining them.  This is
;;; the join, and it is what the forward half of compact-iff-seq-compact is
;;; missing once compact-seq-has-cluster is in hand.
;;; =====================================================================

(sp (make-wff
  '(FORALL s (FORALL f (FORALL x
     (IMPLIES (CLUSTER-POINT s f x)
       (FORSOME phi
         (AND (STRICTLY-MONO-NN phi)
              (CONVERGES-TO s (SUBSEQ f phi) x)))))))))

(dk-peel!)

(define r8h-cl (dk-pick (dk-head? 'CLUSTER-POINT) "the cluster hypothesis"))
(define r8h-s  (cadr r8h-cl))
(define r8h-f  (caddr r8h-cl))
(define r8h-x  (cadddr r8h-cl))

;; unfold CLUSTER-POINT: IS-METRIC-SPACE s, f : NN -> PTS s, x in PTS s, and the
;; FREQUENCY universal.  `mac-h' CONSUMES the hypothesis, which is fine: every
;; conjunct is wanted separately and nothing below re-reads CLUSTER-POINT.
(dk-split-all! (dk-landed (lambda () (mac-h 'cluster-point r8h-cl))))
(dk-split-all!)

(define r8h-freq
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'POS-RR)
                             (dk-contains? fm 'DIST)))
           "the frequency universal of CLUSTER-POINT"))

;;; ---- a positive null radius sequence ----------------------------------

(define r8h-rad (dk-skolem! (dk-fact! 'null-rr-seq-exists)))
(dk-split-all! (dk-landed (lambda () (mac-h 'null-rr-seq (list 'NULL-RR-SEQ r8h-rad)))))
(dk-split-all!)

(define r8h-rpos
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'POS-RR)
                             (dk-contains? fm r8h-rad)
                             (not (dk-contains? fm 'FORSOME))))
           "the pointwise positivity of rad"))
(define r8h-rtail
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'FORSOME)
                             (dk-contains? fm r8h-rad)))
           "the tail clause of NULL-RR-SEQ"))

;;; ---- the base index a:  d(f a, x) < rad 0 ------------------------------

(fact 'nn-zero-in)                                  ; (IN 0 NN)
(dk-apply! r8h-rpos 0)                              ; POS-RR (rad 0)
(fact 'rr-pos-rr-in-rr (list r8h-rad 0))            ; (rad 0) in RR -- TYPE BEFORE INSTANTIATING
(define r8h-a
  (dk-skolem! (dk-apply! (dk-apply! r8h-freq (list r8h-rad 0)) 0)))
(dk-split-all!)

;;; ---- the step set and its totality -------------------------------------
;;;   nxt(k,u) = { y in NN : u < y and d(f y, x) < rad(succ k) }

(define r8h-nxt
  (list 'VNB-LAMBDA '(LIST k_ u_) '(CARTESIAN NN NN)
        (list 'SEP 'y_ 'NN
              (list 'AND (list '< 'u_ 'y_)
                    (list '< (list (list 'DIST r8h-s) (list r8h-f 'y_) r8h-x)
                          (list r8h-rad '(succ k_)))))))

;; the antecedent of dc-on-nn-pred at X := NN, binders SPELLED AS THERE so the
;; instance IS the support's own hypothesis and `fact' detaches it.
(define r8h-tot
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
      (list 'FORALL 'u
        (list 'IMPLIES '(IN u NN)
          (list 'FORSOME 'y
            (list 'AND '(IN y NN) (list 'IN 'y (list r8h-nxt 'k 'u)))))))))

(have! r8h-tot
  (lambda ()
    (dk-peel!)
    (let* ((args (or (r8h-app-args (dk-goal) r8h-nxt)
                     (error "totality: the step application is not in the goal")))
           (kv   (car args))
           (uv   (cadr args)))
      ;; eps := rad(succ k) is positive and real
      (fact 'nn-succ-closed kv)                     ; (IN (succ k) NN)
      (dk-apply! r8h-rpos (list 'succ kv))          ; POS-RR (rad (succ k))
      (fact 'rr-pos-rr-in-rr (list r8h-rad (list 'succ kv)))
      ;; m := succ u
      (fact 'nn-succ-closed uv)                     ; (IN (succ u) NN)
      (let ((w (dk-skolem!
                (dk-apply! (dk-apply! r8h-freq (list r8h-rad (list 'succ kv)))
                           (list 'succ uv)))))
        (dk-split-all!)
        ;; succ u <= w  =>  u < w.  `ineq' wants succ u typed in RR and the
        ;; succ/+ bridge landed; an untyped succ-term poisons the call.
        (fact 'nn-in-rr uv)
        (fact 'nn-in-rr w)
        (fact 'nn-in-rr (list 'succ uv))
        (fact 'nn-succ-plus-one uv)                 ; (= (succ u) (+ u 1))
        (fact 'rr-zero-in) (fact 'rr-one-in)
        (have! (list 'AND (list 'IN uv 'RR) '(IN 1 RR)))
        (fact 'rr-add-closed uv 1)
        (have! (list '< uv w)
          (lambda ()
            (r8h-ineq (list '<= (list 'succ uv) w)
                      (list '= (list 'succ uv) (list '+ uv 1)))))
        (witness! w
          (lambda ()
            (dk-conj-close!
             (lambda ()
               ;; the two conjuncts of the witness goal: (IN w NN) closes from
               ;; context; (IN w (nxt k u)) wants the beta step and then SEP.
               (if (eq? (caddr (dk-goal)) 'NN)
                   (ass)
                   (begin
                     (lam-b)
                     (for-each (lambda (l)
                                 (dk-focus! l)
                                 (dk-conj-close! (lambda () (ass))))
                               (dk-opened (lambda () (sep-mi))))))))))))))

;;; ---- the reindexing phi -------------------------------------------------

(fact 'nn-is-set)
(define r8h-phi (dk-skolem! (dk-fact! 'dc-on-nn-pred 'NN r8h-a r8h-nxt)))
(dk-split-all!)

(define r8h-stage
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm r8h-phi)
                             (dk-contains? fm 'succ)))
           "the per-stage step property of phi"))

;; read the SEP membership off the stage property at a TYPED k: it lands BOTH
;; phi(k) < phi(succ k) and d(f(phi(succ k)), x) < rad(succ k).
(define (r8h-stage-at! kv)
  (let ((h (dk-apply! r8h-stage kv)))
    (fact 'fun-apply-type-c r8h-phi 'NN 'NN kv)     ; (IN (phi k) NN) -- TYPE BEFORE BETA
    (sep-me (car (dk-landed (lambda () (lam-b-h h)))))
    (dk-split-all!)))

;;; phi is strictly monotone.

(define r8h-lt-step
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
          (list '< (list r8h-phi 'k) (list r8h-phi '(succ k))))))

(have! r8h-lt-step
  (lambda ()
    (let ((kv (dk-di-var!)))
      (r8h-stage-at! kv)
      (ass))))

(fact 'nn-step-strictly-mono r8h-phi)               ; STRICTLY-MONO-NN phi

;;; the tail estimate, lifted to every index by induction on k.  The STEP case
;;; does not use its hypothesis; the BASE is the phi(0) = a substitution.

(define r8h-d-bound
  (list 'FORALL 'k
    (list 'IMPLIES '(IN k NN)
          (list '< (list (list 'DIST r8h-s) (list r8h-f (list r8h-phi 'k)) r8h-x)
                (list r8h-rad 'k)))))

(have! r8h-d-bound
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (memq (car (dk-goal)) '(FORALL IMPLIES))
           ;; STEP
           (let* ((landed (dk-peel!))
                  (kv     (r8h-typed-var landed "the induction variable")))
             (r8h-stage-at! kv)
             (ass))
           ;; BASE: phi(0) = a
           (begin
             (fact 'nn-zero-in)
             (subst (list '= (list r8h-phi 0) r8h-a))
             (ass))))
     (dk-opened (lambda () (ni))))))

;;; ---- assemble ------------------------------------------------------------

(have! (list 'AND (list 'IN r8h-f (list 'FUN 'NN (list 'PTS r8h-s)))
                  (list 'STRICTLY-MONO-NN r8h-phi)))
(fact 'subseq-is-fun r8h-s r8h-f r8h-phi)           ; SUBSEQ(f,phi) : NN -> PTS s

(witness! r8h-phi
  (lambda ()
    (dk-conj-close!
     (lambda ()
       (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
           (ass)
           (begin
             (mac 'CONVERGES-TO)
             (dk-conj-close!
              (lambda ()
                (let ((g (dk-goal)))
                  (cond
                    ((memq (car g) '(IS-METRIC-SPACE IN)) (ass))
                    (#t
                     ;; forall eps>0. forsome N in NN. tail within eps
                     (let* ((landed (dk-peel!))
                            (ev (cadr (or (find-first (dk-head? 'POS-RR) landed)
                                          (error "converges-to: no tolerance landed")))))
                       (fact 'rr-pos-rr-in-rr ev)
                       (let ((bigN (dk-skolem! (dk-apply! r8h-rtail ev))))
                         (dk-split-all!)
                         (let ((tail (dk-pick
                                      (lambda (fm)
                                        (and (pair? fm) (eq? (car fm) 'FORALL)
                                             (dk-contains? fm bigN)
                                             (dk-contains? fm r8h-rad)))
                                      "the tail bound on rad")))
                           (witness! bigN
                             (lambda ()
                               (dk-conj-close!
                                (lambda ()
                                  (if (eq? (car (dk-goal)) 'IN)
                                      (ass)
                                      (let* ((lnd (dk-peel!))
                                             (nv  (r8h-typed-var lnd "the tail index")))
                                        (mac 'SUBSEQ)
                                        (lam-b)
                                        (dk-apply! r8h-d-bound nv)
                                        (have! (list 'AND (list 'IN nv 'NN)
                                                     (list '<= bigN nv)))
                                        (dk-apply! tail nv)
                                        (fact 'fun-apply-type-c r8h-phi 'NN 'NN nv)
                                        (fact 'fun-apply-type-c r8h-f 'NN
                                              (list 'PTS r8h-s) (list r8h-phi nv))
                                        (fact 'metric-dist-real r8h-s
                                              (list r8h-f (list r8h-phi nv)) r8h-x)
                                        (fact 'fun-apply-type-c r8h-rad 'NN 'RR nv)
                                        (r8h-ineq
                                         (list '< (list (list 'DIST r8h-s)
                                                        (list r8h-f (list r8h-phi nv))
                                                        r8h-x)
                                               (list r8h-rad nv))
                                         (list '<= (list r8h-rad nv) ev))))))))))))))))))))))

(r8h-qed! 'cluster-point-has-convergent-subseq)
(topic! 'cluster-point-has-convergent-subseq 'topology)

;;; =====================================================================
;;; compact-implies-seq-compact -- the FORWARD half of the support
;;; compact-iff-seq-compact (theorem-library/seq-compact-product.scm:52); the
;;; antecedent IS-METRIC-SPACE and the conclusion SEQ-COMPACT are copied from
;;; there unchanged.
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (IS-COMPACT s) (SEQ-COMPACT s))))))

(dk-peel!)
(define r8h-cs (cadr (dk-pick (dk-head? 'IS-COMPACT) "the compactness hypothesis")))

(mac 'SEQ-COMPACT)
(dk-conj-close!
 (lambda ()
   (if (eq? (car (dk-goal)) 'IS-METRIC-SPACE)
       (ass)
       (let* ((landed (dk-peel!))
              (fv (cadr (or (find-first (lambda (fm)
                                          (and (pair? fm) (eq? (car fm) 'IN)
                                               (pair? (caddr fm))
                                               (eq? (car (caddr fm)) 'FUN)))
                                        landed)
                            (error "compact-implies-seq-compact: no sequence typing")))))
         ;; a cluster point (compact-seq-has-cluster wants the AND whole)
         (have! (list 'AND (list 'IS-COMPACT r8h-cs)
                      (list 'IN fv (list 'FUN 'NN (list 'PTS r8h-cs)))))
         (let ((xv (dk-skolem! (dk-fact! 'compact-seq-has-cluster r8h-cs fv))))
           ;; x in PTS s, read in a LANE (mac-h consumes CLUSTER-POINT, which
           ;; the next citation still needs)
           (have! (list 'IN xv (list 'PTS r8h-cs))
             (lambda ()
               (dk-split-all!
                (dk-landed (lambda () (mac-h 'cluster-point
                                             (list 'CLUSTER-POINT r8h-cs fv xv)))))
               (dk-split-all!)
               (ass)))
           (let ((phiv (dk-skolem!
                        (dk-fact! 'cluster-point-has-convergent-subseq
                                  r8h-cs fv xv))))
             (witness! phiv
               (lambda ()
                 (dk-conj-close!
                  (lambda ()
                    (if (eq? (car (dk-goal)) 'STRICTLY-MONO-NN)
                        (ass)
                        (witness! xv
                          (lambda ()
                            (dk-conj-close! (lambda () (ass))))))))))))))))

(r8h-qed! 'compact-implies-seq-compact)
(topic! 'compact-implies-seq-compact 'topology)

;;; =====================================================================
;;; THE CONVERSE (SEQ-COMPACT => IS-COMPACT) -- what it still needs.
;;; Nothing below this line is executed.
;;; =====================================================================
;;;
;;; WHAT IS ALREADY PROVEN, and why none of it closes the converse.
;;;   compact-implies-totally-bounded  calculus/compact-tb-proof.scm   PROVEN
;;;   compact-implies-complete         calculus/compact-complete-proof PROVEN
;;;   compact-seq-has-cluster          rake-compact-cluster.scm        PROVEN
;;;   cauchy-cluster-converges         rake-compact-complete.scm       PROVEN
;;;   totally-bounded-has-cauchy-subsequence, subsequence-capture,
;;;   dc-on-nn-pred, nn-step-strictly-mono, null-rr-seq-exists         PROVEN
;;; Every proven arrow runs COMPACT => something.  The tree has no arrow INTO
;;; IS-COMPACT at all: the only ways in are the three asserted equivalences
;;; compact-iff-tb-complete, compact-iff-cluster-point, compact-iff-fip
;;; (structure-library/compactness.scm:74, :84, :99), so the shortest-looking
;;; route -- TOTALLY-BOUNDED + IS-COMPLETE, then compact-iff-tb-complete --
;;; bills an assertion and can never reach `modulo 0'.
;;;
;;; THE ONLY modulo-0 ROUTE is the direct one, and it is three proofs:
;;;
;;;  (C1) seq-compact-implies-totally-bounded.  By contradiction at a radius r
;;;       with no finite r-net: dc-on-nn-pred on PTS(s) with step set
;;;       { y in PTS s : forall i in NN. i <= k => r <= d(g i, y) } -- non-empty
;;;       because the finite set {g 0, ..., g k} (an IMAGE of an NN interval;
;;;       card-image-finite, interval-card-in-nn) is not an r-net.  The
;;;       resulting g has all pairwise distances >= r, so no subsequence of it
;;;       is Cauchy, let alone convergent -- contradicting SEQ-COMPACT.  The
;;;       step set is the one genuinely new shape: the "previous points" bound
;;;       is a universal over an NN segment, not a stored finite set, which is
;;;       what keeps it inside dc-on-nn-pred (no SEP over triples).
;;;
;;;  (C2) lebesgue-number.  The tree has NO Lebesgue number lemma (grep:
;;;       `lebesgue' occurs only in structure-library/measure.scm, unrelated).
;;;       For a seq-compact s and an open cover C: forsome delta. POS-RR delta
;;;       and forall p in PTS s. forsome U in C. BALL(s,p,delta) SUBSET U.
;;;       Proof by contradiction: pick p_n whose 1/(n+1)-ball lies in no member
;;;       (choice over NN, dc-on-nn-pred degenerate or a plain VNB-LAMBDA of
;;;       CHOICE), take a convergent subsequence p_{phi k} -> L (SEQ-COMPACT),
;;;       L in some open U in C so BALL(s,L,eps) SUBSET U (the IS-OPEN
;;;       read-off, metric-open-sets.scm), then for k large both
;;;       d(p_{phi k}, L) < eps/2 and 1/(phi k + 1) < eps/2 (strictly-mono-ge-id
;;;       gives phi k >= k), so the offending ball is inside U -- contradiction.
;;;
;;;  (C3) the assembly.  Given an open cover C: delta from (C2), a finite
;;;       delta/2-net F from (C1), and for each c in F a member U_c of C with
;;;       BALL(s,c,delta) SUBSET U_c.  The subcover is
;;;       IMAGE(c |-> CHOICE {U in C : BALL(s,c,delta) SUBSET U}, F) -- the
;;;       CENTRE-SET pattern of structure-library/compactness.scm, so the
;;;       choice is explicit and `choose!' discharges it; finiteness is
;;;       card-image-finite, and the covering property is "every p is within
;;;       delta/2 of some c in F, hence in BALL(s,c,delta) SUBSET U_c".
;;;
;;; ESTIMATE: (C1) ~250 lines, (C2) ~250, (C3) ~150, plus a BALL-SUBSET
;;; read-off the tree does not have in this shape.  It is a day on its own, and
;;; it is the LAST unproven direction of Prop 3.12 -- once (C1)-(C3) land,
;;; compact-iff-tb-complete and compact-iff-cluster-point become provable too
;;; (their hard halves are exactly these), so the three asserted equivalences
;;; fall together.
;;;
;;; FOR THE INTEGRATOR: compact-iff-seq-compact CANNOT be retired yet -- its
;;; only citer, theorem-library/tychonoff-proof.scm, uses BOTH directions
;;; (:65 rewrites the goal SEQ-COMPACT(ms n) to IS-COMPACT via the `-rev'
;;; macete = the forward half proven here; :78 rewrites the goal
;;; IS-COMPACT(PRODUCT-METRIC ms) to SEQ-COMPACT = the converse).  When it
;;; does go, note that test-suite.scm:3663-3668 pins the NAME
;;; `compact-iff-seq-compact-rev' (the find-thm `-rev' folding check) and will
;;; have to be repointed at another `-iff-' theorem.
;;; =====================================================================
