;;; rake-lebesgue-number.scm -- the Lebesgue number lemma, and the CONVERSE
;;; half of Prop 3.12 (1)<=>(3'): a sequentially compact metric space is
;;; compact.
;;;
;;; Three theorems, in dependency order:
;;;
;;;   lebesgue-number                 (new; the tree had no Lebesgue number)
;;;     forall s. IS-METRIC-SPACE s => SEQ-COMPACT s =>
;;;       forall cov. IS-OPEN-COVER s cov =>
;;;         forsome del. POS-RR del and
;;;           forall p in PTS s. forsome u in cov. BALL(s,p,del) SUBSET u
;;;
;;;   seq-compact-implies-compact     (the CONVERSE half of the support
;;;       compact-iff-seq-compact, theorem-library/seq-compact-product.scm:52)
;;;     forall s. IS-METRIC-SPACE s => SEQ-COMPACT s => IS-COMPACT s
;;;
;;;   compact-iff-seq-compact         (the support's statement, LITERAL)
;;;     forall s. IS-METRIC-SPACE s => (IS-COMPACT s IFF SEQ-COMPACT s)
;;;
;;; VOCABULARY.  "c is an open cover of s" is written with IS-OPEN-COVER, the
;;; predicate IS-COMPACT's own definition quantifies over
;;; (structure-library/compactness.scm:29,:36) -- not with an inlined
;;; "every member open and the union is PTS(s)".  Nothing else is needed: BALL
;;; and SUBSET are already the currency of IS-OPEN (metric-open-sets.scm:41).
;;;
;;; THE STATEMENT OF lebesgue-number, checked for the usual species:
;;;   * the radius is TYPED -- `POS-RR del' carries (IN del RR), 0 <= del and
;;;     del /= 0, so no untyped radius and no del = 0 reading;
;;;   * the EMPTY metric space satisfies it: the inner universal over PTS(s) is
;;;     vacuous and del := 1 serves, so no nonemptiness guard is missing (the
;;;     proof below never needs one either -- it reaches CHOICE only through a
;;;     set the NEGATED conclusion proves inhabited);
;;;   * no CHOICE of a possibly empty class: the only CHOICE is over
;;;     BAD(k) = { p in PTS s : no member of cov contains BALL(s,p,rad k) },
;;;     and the proof is a reductio in which the negated conclusion EXHIBITS a
;;;     member of BAD(k) for every k (r8k-inhab!) before CHOICE is applied;
;;;   * SEQ-COMPACT already contains IS-METRIC-SPACE s, and so does
;;;     IS-OPEN-COVER s cov; the leading IS-METRIC-SPACE antecedent is kept
;;;     because the two theorems below and the support they serve are all
;;;     stated that way.
;;;
;;; THE PROOF of lebesgue-number.  Reductio.  Let rad be a positive null
;;; sequence (null-rr-seq-exists) and
;;;
;;;     BAD(k) = { p in PTS s | forall u in cov. not (BALL(s,p,rad k) subset u) }.
;;;
;;; If no del works then in particular rad(k) does not, which is exactly
;;; "BAD(k) is inhabited" -- r8k-inhab!, three nested reductios (the negated
;;; conclusion is an existential under a universal under an existential, and
;;; `push-not-h' will not cross those alternations; 7-G met the same wall).
;;; CHOICE then gives the sequence
;;;
;;;     g = (k |-> CHOICE(BAD k))  :  NN -> PTS s,
;;;
;;; and NO dependent choice is needed: the k-th choice does not look at the
;;; earlier ones, so a plain VNB-LAMBDA with a CHOICE body, typed by `lam-t'
;;; over the pointwise membership r8k-chosen, is the whole construction.
;;; SEQ-COMPACT gives phi strictly monotone and L in PTS(s) with
;;; SUBSEQ(g,phi) -> L.  L lies in some member u0 of the cover
;;; (open-cover-covers-point), u0 is open, so BALL(s,L,eps) subset u0 for some
;;; eps > 0.  Halve it: h + h = eps.  Take K above both the convergence
;;; threshold for h and the null threshold for h (nn-pair-upper-bound -- NN is
;;; directed, no max functoid needed); then phi(K) >= K (strictly-mono-ge-id)
;;; puts rad(phi K) <= h, while d(g(phi K), L) <= h.  For y in
;;; BALL(s, g(phi K), rad(phi K)),
;;;
;;;     d(L,y) <= d(L, g(phi K)) + d(g(phi K), y) < h + h = eps,
;;;
;;; one `ineq' certificate over the triangle instance, metric-sym and the two
;;; thresholds.  So that ball is inside BALL(s,L,eps) and hence inside u0 --
;;; contradicting the defining property of g(phi K) = CHOICE(BAD(phi K)).
;;;
;;; THE PROOF of seq-compact-implies-compact.  Given a cover cov: del from the
;;; Lebesgue number, a finite del-net F from seq-compact-implies-totally-bounded
;;; (7-J), and one member of cov per net point,
;;;
;;;     SUB = IMAGE(c |-> CHOICE{ u in cov | BALL(s,c,del) subset u }, F).
;;;
;;; SUB is a subset of cov, finite (card-image-finite), and covers: every p is
;;; within del of some net point c, so p lies in BALL(s,c,del), which lies in
;;; the chosen member.  This is the CENTRE-SET pattern of
;;; structure-library/compactness.scm with the choice made explicit, exactly as
;;; in theorem-library/rake-compact-cluster.scm and ptwise-cauchy-unif.scm.
;;;
;;; CITATIONS and the files that install them:
;;;   choice-axiom, class-extensionality, power-set-membership, subset-def
;;;                                          library.scm (primitive)
;;;   image-membership-iff                   structure-library/injection
;;;   IS-OPEN, IS-CLOSED                     structure-library/metric-open-sets
;;;   BALL, IS-R-NET, TOTALLY-BOUNDED        structure-library/metric-topology
;;;   IS-COMPACT, IS-OPEN-COVER              structure-library/compactness
;;;   CONVERGES-TO                           structure-library/metric-completeness
;;;   metric-sym, metric-triangle            structure-library/metric-laws
;;;   metric-dist-real                       theorem-library/op-typing
;;;   fun-apply-type-c                       theorem-library/fun-apply-type-proof
;;;   nn-in-rr, nn-le-trans-guarded,
;;;   nn-pair-upper-bound                    theorem-library/nn-order-basics
;;;   rr-pos-rr-in-rr, rr-lt-of-pos-rr       theorem-library/pos-rr-bridges
;;;   rr-pos-halvable (via dk-halve!)        theorem-library/rr-halving
;;;   subset-trans, subset-mem-fwd,
;;;   subclass-of-set-is-set                 theorem-library/subset-lemmas
;;;   STRICTLY-MONO-NN, SUBSEQ, NULL-RR-SEQ  theorem-library/cauchy-subsequence
;;;   subseq-apply                           theorem-library/subseq-apply
;;;   strictly-mono-ge-id                    theorem-library/rake-algebra
;;;   card-image-finite                      theorem-library/card-image-finite
;;;   ball-sep-unfold, open-cover-covers-point
;;;                                          theorem-library/ball-cover-lemmas
;;;   SEQ-COMPACT                            theorem-library/seq-compact-product
;;;   null-rr-seq-exists                     theorem-library/rake-subseq-leaves
;;;   compact-implies-seq-compact            theorem-library/rake-compact-iff-seq-compact
;;;   seq-compact-implies-totally-bounded    theorem-library/rake-seq-compact-tb
;;;
;;; No late tactic: `ineq', `prop' and the dk- kit only.
;;;
;;; LOAD WINDOW (load.scm line numbers of 2026-09-19 evening):
;;;   lo = 1348, theorem-library/rake-seq-compact-tb (seq-compact-implies-
;;;        totally-bounded, batch 7-J).  The next latest are
;;;        rake-compact-iff-seq-compact at 1345 (compact-implies-seq-compact,
;;;        batch 7-H), rake-subseq-leaves at 1342 (null-rr-seq-exists),
;;;        structure-library/metric-laws at 1300, ball-cover-lemmas at 1262,
;;;        card-image-finite at 1148, seq-compact-product at 508 (SEQ-COMPACT).
;;;   hi = 2431, theorem-library/tychonoff-proof, the ONLY file that cites
;;;        compact-iff-seq-compact in a proof (:65 through the `-rev' macete,
;;;        :78 forward).  theorem-library/pss-topics.scm:295 only `topic!'s it.
;;;   The natural slot is immediately after theorem-library/rake-seq-compact-tb.
;;;
;;; USES THE MACRO bc* (class-extensionality): this file must NOT be compiled --
;;; `compile-vnb!' skips it by the reader test, a by-hand sweep must not.
;;;
;;; Helper prefix: r8k-.

;;; =====================================================================
;;; file-local helpers
;;; =====================================================================

(define (r8k-head? fm h) (and (pair? fm) (eq? (car fm) h)))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (r8k-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit))
            (dk-opened thunk)))

;; `ineq' by FORMULA, not by index (the indices are 1-based into the context
;; and a forward assembly renumbers them at every step).
(define (r8k-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r8k-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r8k-ineq . forms) (apply ineq (map r8k-idx forms)))

;; `lam-b' POSTS THE ARGUMENT TYPING AS A LEAF even when that typing is already
;; in the context: it opens the reduced goal AND one (IN arg dom) obligation per
;; redex, and a driver that walks on leaves the obligations behind -- the parent
;; node is then not grounded and the enclosing `have!' fails with "THUNK left the
;; side goal open", naming the CLAIM and not the leaf.  Run THUNK, close every
;; opened leaf whose goal is a typing already in context, and leave focus on the
;; one leaf that is not.
(define (r8k-close-owed! thunk)
  (let ((opened (dk-opened thunk))
        (main   #f))
    (for-each (lambda (leaf)
                (dk-focus! leaf)
                (if (and (r8k-head? (dk-goal) 'IN) (dk-asm? (dk-goal)))
                    (ass)
                    (set! main leaf)))
              opened)
    (if main (dk-focus! main))
    main))

(define (r8k-lam-b!)
  (or (r8k-close-owed! (lambda () (lam-b)))
      (error "r8k-lam-b!: lam-b left no reduced goal")))

(define (r8k-lam-b-h! eq) (r8k-close-owed! (lambda () (lam-b-h eq))))

;; (IN z (BALL s c r)) in context: open it to its SEP atoms through the PROVEN
;; unfold equation ball-sep-unfold, not through the support ball-membership.
(define (r8k-open-ball-h! mem)
  (let ((sm (dk-landed-1 (lambda () (mac-h 'ball-sep-unfold mem)))))
    (dk-split-all! (dk-landed (lambda () (sep-me sm))))))

;; "pick an element of SETTERM", WIT being the exhibited member and BODY the
;; proof that it belongs.  driver-kit's `choose!' does the same but then
;; CONSUMES the landed membership with `sep-me'; here the membership itself is
;; what is wanted, so the SEP is read apart by the caller, where it is needed.
(define (r8k-choose! setterm wit body)
  (have! (list 'FORSOME 'z_ (list 'IN 'z_ setterm))
         (lambda () (witness! wit body)))
  (dk-fact! 'choice-axiom setterm))

;; (POS-RR d) stays in context (mac-h in a lane -- it REPLACES otherwise);
;; the conjunction and its three atoms land beside it.
(define (r8k-pos-atoms! d)
  (let ((conj (list 'AND (list 'IN d 'RR)
                    (list 'AND (list '<= 0 d) (list 'NOT (list '= 0 d))))))
    (dk-have! conj (lambda () (mac-h 'pos-rr (list 'POS-RR d)) (ass)))
    (dk-split-all! (list conj))
    (have! conj)
    conj))

;; goal (AND (<= a b) (NOT (= a b))) -- the unfolded (< a b): prove the folded
;; form with BODY and split it.
(define (r8k-strict! a b body)
  (let ((lt (list '< a b)))
    (have! lt body)
    (dk-split! (dk-landed-1 (lambda () (mac-h '< lt))))
    (dk-conj-close!)))

;;; =====================================================================
;;; 0.  subseq-value -- MOVED on 2026-09-19 (batch 8-K2).  The value equation
;;; SUBSEQ(f,phi)(k) = f(phi(k)) at a TYPED k was written three times, verbatim,
;;; on 2026-09-19 (here, and as `subseq-value-at' / `subseq-apply' in
;;; rake-block-tower.scm and rake-diagonal-subseq.scm).  It now has ONE early
;;; home, theorem-library/subseq-apply.scm -- wired just after
;;; theorem-library/equality-basics, which is the earliest slot the lemma can
;;; take: SUBSEQ is defined in theorem-library/cauchy-subsequence (load
;;; position 90), BELOW `interactive' (135) and `driver-kit' (139), so the
;;; lemma cannot be proved immediately after its own definition.  The citation
;;; below names `subseq-apply'.  Original text:
;;; archive/2026-09-19-batch8/rake-lebesgue-number.scm.
;;; =====================================================================

;;; =====================================================================
;;; 1.  lebesgue-number
;;; =====================================================================

(define r8k-stmt
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (SEQ-COMPACT s)
       (FORALL cov (IMPLIES (IS-OPEN-COVER s cov)
         (FORSOME del (AND (POS-RR del)
           (FORALL p (IMPLIES (IN p (PTS s))
             (FORSOME u (AND (IN u cov)
                             (SUBSET (BALL s p del) u)))))))))))))

;;; --- the terms the driver computes with -------------------------------
;;; Binders `lpt_' / `lmem_' / `lk_' / `lx_' are spelled so that no `di' in
;;; this file can mint an eigenvariable of the same name: a computed SEP whose
;;; binder collides gets alpha-renamed by capture-avoiding substitution and
;;; every equal? lookup afterwards misses (7-A's trap).

(define (r8k-bad sv cov rad kk)
  (list 'SEP 'lpt_ (list 'PTS sv)
        (list 'FORALL 'lmem_
              (list 'IMPLIES (list 'IN 'lmem_ cov)
                    (list 'NOT (list 'SUBSET
                                     (list 'BALL sv 'lpt_ (list rad kk))
                                     'lmem_))))))

(define (r8k-inhab-form sv cov rad)
  (list 'FORALL 'lk_
        (list 'IMPLIES (list 'IN 'lk_ 'NN)
              (list 'FORSOME 'lx_ (list 'IN 'lx_ (r8k-bad sv cov rad 'lk_))))))

(define (r8k-chosen-form sv cov rad)
  (list 'FORALL 'lk_
        (list 'IMPLIES (list 'IN 'lk_ 'NN)
              (list 'IN (list 'CHOICE (r8k-bad sv cov rad 'lk_))
                    (r8k-bad sv cov rad 'lk_)))))

(define (r8k-gseq sv cov rad)
  (list 'VNB-LAMBDA 'lk_ 'NN (list 'CHOICE (r8k-bad sv cov rad 'lk_))))

;;; --- BAD(k) is inhabited, for every k ---------------------------------
;;; Context: NOTG = (NOT <the conclusion>), RPOS = pointwise positivity of rad.
;;; Three reductios: the conclusion is  forsome del. ... forall p. forsome u ...
;;; and `push-not-h' refuses a universal whose body hides another quantifier.

(define (r8k-inhab! sv cov rad rpos notg)
  (let ((form (r8k-inhab-form sv cov rad)))
    (have! form
      (lambda ()
        (let* ((kv    (dk-di-var!))
               (notex (dk-landed-1 (lambda () (pbc))))   ; goal FALSITY
               (exk   (cadr notex)))
          (dk-apply! rpos kv)                            ; (POS-RR (rad kv))
          (have! (cadr notg)
            (lambda ()
              (witness! (list rad kv)
                (lambda ()
                  (dk-conj-close!
                   (lambda ()
                     (if (r8k-head? (dk-goal) 'POS-RR)
                         (ass)
                         ;; forall p in PTS s. forsome u in cov. ball subset u
                         (let* ((ld   (dk-peel!))
                                (pv   (cadr (car ld)))
                                (notu (dk-landed-1 (lambda () (pbc)))))
                           (have! exk
                             (lambda ()
                               (witness! pv
                                 (lambda ()
                                   (r8k-each-leaf!
                                    (lambda () (sep-mi))
                                    (lambda ()
                                      (if (r8k-head? (dk-goal) 'FORALL)
                                          (let* ((ld2 (dk-peel!))
                                                 (uv  (cadr (car ld2))))
                                            (di)   ; assume the SUBSET; goal FALSITY
                                            (have! (cadr notu)
                                              (lambda ()
                                                (witness! uv (lambda () (dk-conj-close!)))))
                                            (ai notu))
                                          (ass))))))))
                           (ai notex)))))))))
          (ai notg))))
    form))

;;; --- the chosen point of BAD(k) ---------------------------------------

(define (r8k-chosen! sv cov rad inhab)
  (let ((form (r8k-chosen-form sv cov rad)))
    (have! form
      (lambda ()
        (let* ((kv  (dk-di-var!))
               (bad (r8k-bad sv cov rad kv))
               (wv  (dk-skolem! (dk-apply! inhab kv))))
          (r8k-choose! bad wv (lambda () (ass)))
          (ass))))
    form))

;;; --- g : NN -> PTS s ---------------------------------------------------

(define (r8k-type-g! sv cov rad chosen)
  (let* ((gseq (r8k-gseq sv cov rad))
         (ty   (list 'IN gseq (list 'FUN 'NN (list 'PTS sv)))))
    (have! ty
      (lambda ()
        (r8k-each-leaf!
         (lambda () (lam-t))
         (lambda ()
           (if (r8k-head? (dk-goal) 'FORALL)
               (let* ((kv  (dk-di-var!))
                      (bad (r8k-bad sv cov rad kv)))
                 (dk-apply! chosen kv)
                 (dk-split-all!
                  (dk-landed (lambda () (sep-me (list 'IN (list 'CHOICE bad) bad)))))
                 (ass))
               (begin (fact 'nn-is-set) (ass)))))))
    ty))

;;; --- the ball around g(phi K) sits inside u0 ---------------------------
;;; goal (SUBSET (BALL s cx radk) (BALL s L eps)); context carries the triangle
;;; ingredients.  The `ineq' certificate:
;;;   d(L,y) <= d(L,cx) + d(cx,y),  d(L,cx) = d(cx,L) <= h,
;;;   d(cx,y) < radk <= h,  h + h = eps    |-   d(L,y) < eps.

(define (r8k-ball-inside! sv cx lv radk epsv hv)
  (let ((yv (subset-by-element!)))
    (r8k-open-ball-h! (list 'IN yv (list 'BALL sv cx radk)))
    (fact 'metric-dist-real sv cx yv)
    (fact 'metric-dist-real sv lv yv)
    (fact 'metric-dist-real sv lv cx)
    (fact 'metric-dist-real sv cx lv)
    (fact 'metric-triangle sv lv cx yv)
    (fact 'metric-sym sv lv cx)
    (let ((dly  (list (list 'DIST sv) lv yv))
          (dlcx (list (list 'DIST sv) lv cx))
          (dcxl (list (list 'DIST sv) cx lv))
          (dcxy (list (list 'DIST sv) cx yv)))
      (have! (list '< dcxy radk) (lambda () (mac '<) (dk-conj-close!)))
      (mac 'ball-sep-unfold)
      (r8k-each-leaf!
       (lambda () (sep-mi))
       (lambda ()
         (if (r8k-head? (dk-goal) 'IN)
             (ass)
             (r8k-strict!
              dly epsv
              (lambda ()
                (r8k-ineq (list '<= dly (list '+ dlcx dcxy))
                          (list '= dlcx dcxl)
                          (list '<= dcxl hv)
                          (list '< dcxy radk)
                          (list '<= radk hv)
                          (list '= (list '+ hv hv) epsv)
                          (list 'IN dly 'RR)
                          (list 'IN dlcx 'RR)
                          (list 'IN dcxl 'RR)
                          (list 'IN dcxy 'RR)
                          (list 'IN radk 'RR)
                          (list 'IN hv 'RR)
                          (list 'IN epsv 'RR))))))))))

;;; --- the main reductio -------------------------------------------------

(define (r8k-main! sv cov notg)
  (let ((rad (dk-skolem! (dk-fact! 'null-rr-seq-exists))))
    (dk-split-all! (dk-landed (lambda () (mac-h 'null-rr-seq (list 'NULL-RR-SEQ rad)))))
    (dk-split-all!)
    (let* ((rpos (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                            (dk-contains? fm 'POS-RR)
                                            (dk-contains? fm rad)
                                            (not (dk-contains? fm 'FORSOME))))
                          "the pointwise positivity of rad"))
           (rtail (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                             (dk-contains? fm 'FORSOME)
                                             (dk-contains? fm rad)))
                           "the tail clause of NULL-RR-SEQ"))
           (inhab  (r8k-inhab! sv cov rad rpos notg))
           (chosen (r8k-chosen! sv cov rad inhab))
           (gty    (r8k-type-g! sv cov rad chosen))
           (gseq   (r8k-gseq sv cov rad)))
      ;; SEQ-COMPACT at g
      (dk-split-all! (dk-landed (lambda () (mac-h 'seq-compact (list 'SEQ-COMPACT sv)))))
      (dk-split-all!)
      (let* ((sc   (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                              (dk-contains? fm 'STRICTLY-MONO-NN)))
                            "the sequential-compactness law"))
             (phiv (dk-skolem! (dk-apply! sc gseq))))
        (dk-split-all!)
        (let* ((lex (dk-pick (lambda (fm) (and (r8k-head? fm 'FORSOME)
                                               (dk-contains? fm 'CONVERGES-TO)))
                             "the limit existential"))
               (lv  (dk-skolem! lex)))
          (dk-split-all!)
          ;; a member of the cover containing L, and its openness
          (let ((u0 (dk-skolem! (dk-fact! 'open-cover-covers-point sv cov lv))))
            (dk-split-all!)
            (dk-split-all!
             (dk-landed (lambda () (mac-h 'is-open-cover (list 'IS-OPEN-COVER sv cov)))))
            (dk-split-all!)
            (let* ((opens  (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                      (dk-contains? fm 'IS-OPEN)))
                                    "the members-are-open law"))
                   (isopen (dk-apply! opens u0)))
              (dk-split-all! (dk-landed (lambda () (mac-h 'is-open isopen))))
              (dk-split-all!)
              (let* ((ballin (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                        (dk-contains? fm 'BALL)
                                                        (dk-contains? fm u0)))
                                      "the open read-off at u0"))
                     (epsv   (dk-skolem! (dk-apply! ballin lv))))
                (dk-split-all!)
                (fact 'rr-pos-rr-in-rr epsv)
                (let ((hv (dk-halve! epsv)))
                  ;; the convergence threshold for h
                  (dk-split-all!
                   (dk-landed
                    (lambda () (mac-h 'converges-to
                                      (list 'CONVERGES-TO sv (list 'SUBSEQ gseq phiv) lv)))))
                  (dk-split-all!)
                  (let* ((ctail (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                           (dk-contains? fm 'POS-RR)
                                                           (dk-contains? fm 'SUBSEQ)))
                                         "the convergence law"))
                         (n1    (dk-skolem! (dk-apply! ctail hv))))
                    (dk-split-all!)
                    (let* ((cbound (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                              (dk-contains? fm n1)
                                                              (dk-contains? fm 'SUBSEQ)))
                                            "the convergence tail"))
                           (n2     (dk-skolem! (dk-apply! rtail hv))))
                      (dk-split-all!)
                      (let* ((rbound (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                                (dk-contains? fm n2)
                                                                (dk-contains? fm rad)))
                                              "the radius tail"))
                             (kv     (dk-skolem! (dk-fact! 'nn-pair-upper-bound n1 n2))))
                        (dk-split-all!)
                        (r8k-finish! sv cov rad gseq phiv lv u0 epsv hv
                                     cbound rbound chosen kv n2)))))))))))))

(define (r8k-finish! sv cov rad gseq phiv lv u0 epsv hv cbound rbound chosen kv n2)
  ;; phi(K) is a natural, and phi(K) >= K >= n2
  (dk-apply! (dk-fact! 'strictly-mono-ge-id phiv) kv)     ; (<= K (phi K))
  (dk-split-all!
   (dk-landed (lambda () (mac-h 'strictly-mono-nn (list 'STRICTLY-MONO-NN phiv)))))
  (dk-split-all!)
  (fact 'fun-apply-type-c phiv 'NN 'NN kv)                ; (IN (phi K) NN)
  (let* ((pk   (list phiv kv))
         (radk (list rad pk))
         (bad  (r8k-bad sv cov rad pk))
         (cx   (list 'CHOICE bad))
         ;; THE POINT is written as the SUBSEQUENCE VALUE, not as the CHOICE
         ;; term: the convergence estimate already speaks of it in that form,
         ;; and every rewrite below then runs FORWARD along an equation.
         (sx   (list (list 'SUBSEQ gseq phiv) kv))
         (bsx  (list 'BALL sv sx radk))
         (blv  (list 'BALL sv lv epsv)))
    (fact 'nn-le-trans-guarded n2 kv pk)                  ; n2 <= phi K
    (fact 'fun-apply-type-c rad 'NN 'RR pk)               ; (IN (rad (phi K)) RR)
    ;; rad(phi K) <= h   (the NULL-RR-SEQ tail has a CONJUNCTIVE antecedent)
    (have! (list 'AND (list 'IN pk 'NN) (list '<= n2 pk)))
    (dk-apply! rbound pk)
    (dk-apply! cbound kv)                                 ; d(sx, L) <= h
    ;; sx IS the chosen point of BAD(phi K): g(phi K) = CHOICE(BAD(phi K))
    (dk-apply! chosen pk)                                 ; (IN cx bad)
    (have! (list '== (list gseq pk) cx) (lambda () (r8k-lam-b!) (qrfl)))
    (fact 'subseq-apply gseq phiv kv)                     ; sx == g(phi K)
    (have! (list 'IN sx bad)
      (lambda ()
        (subst (list '= sx (list gseq pk)))
        (subst (list '= (list gseq pk) cx))
        (ass)))
    (let* ((l0 (dk-landed (lambda () (sep-me (list 'IN sx bad)))))
           (l1 (append l0 (dk-split-all! l0)))
           (badp (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL) (member fm l1)))
                          "the no-member property of the chosen point"))
           (notsub (dk-apply! badp u0)))
      (have! (list 'SUBSET bsx blv)
        (lambda () (r8k-ball-inside! sv sx lv radk epsv hv)))
      (fact 'subset-trans bsx blv u0)
      (ai notsub))))

(sp (make-wff r8k-stmt))
(define r8k-top (dk-peel!))
(define r8k-sv (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define r8k-cov (caddr (dk-pick (dk-head? 'IS-OPEN-COVER) "the open-cover hypothesis")))
(define r8k-notg (dk-landed-1 (lambda () (pbc))))
(r8k-main! r8k-sv r8k-cov r8k-notg)

(qed 'lebesgue-number)
(topic! 'lebesgue-number 'topology)
(gloss! 'lebesgue-number
  "For a sequentially compact metric space s and an open cover cov of s there
   is a positive number del -- a LEBESGUE NUMBER of the cover -- such that
   every ball of radius del is contained in a single member of the cover.")

;;; =====================================================================
;;; 2.  seq-compact-implies-compact
;;;
;;;   forall s.  IS-METRIC-SPACE s  =>  SEQ-COMPACT s  =>  IS-COMPACT s
;;;
;;; Given a cover cov, let del be its Lebesgue number and F a finite del-net
;;; (seq-compact-implies-totally-bounded).  For each net point c, the set
;;;
;;;     PICK(c) = { u in cov | BALL(s,c,del) subset u }
;;;
;;; is inhabited -- that IS the Lebesgue property at c -- so CHOICE picks a
;;; member and the subcover is the IMAGE of F under c |-> CHOICE(PICK c): the
;;; CENTRE-SET pattern of structure-library/compactness.scm, choice explicit.
;;; It is a subset of cov and finite (card-image-finite), and it covers,
;;; because every point p is within del of some net point c and then lies in
;;; BALL(s,c,del) subset CHOICE(PICK c).
;;; =====================================================================

(define (r8k-pick sv cov delv cc)
  (list 'SEP 'lmem_ cov (list 'SUBSET (list 'BALL sv cc delv) 'lmem_)))

(define (r8k-chi sv cov delv net)
  (list 'VNB-LAMBDA 'lc_ net (list 'CHOICE (r8k-pick sv cov delv 'lc_))))

(define (r8k-picked-form sv cov delv net)
  (list 'FORALL 'lc_
        (list 'IMPLIES (list 'IN 'lc_ net)
              (list 'IN (list 'CHOICE (r8k-pick sv cov delv 'lc_))
                    (r8k-pick sv cov delv 'lc_)))))

;; every net point's PICK set is inhabited, so its CHOICE belongs to it
(define (r8k-picked! sv cov delv net leb)
  (let ((form (r8k-picked-form sv cov delv net)))
    (have! form
      (lambda ()
        (let ((cv (dk-di-var!)))
          (dk-fact! 'subset-mem-fwd net (list 'PTS sv) cv)     ; (IN cv (PTS s))
          (let ((uv (dk-skolem! (dk-apply! leb cv))))
            (dk-split-all!)
            (r8k-choose! (r8k-pick sv cov delv cv) uv
                         (lambda ()
                           (r8k-each-leaf! (lambda () (sep-mi)) (lambda () (ass)))))
            (ass)))))
    form))

;; (IN w SUB) in context: land (IN (CHOICE (PICK c)) cov), the ball inclusion
;; and the equation (= (CHOICE (PICK c)) w).  Returns the net point c.
(define (r8k-sub-mem! sv cov delv net chi sub picked w)
  (let* ((ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff (list 'IN w sub)))))
         (cv (dk-skolem! ex))
         (eqn (dk-pick (lambda (fm) (and (r8k-head? fm '=) (pair? (cadr fm))
                                         (equal? (car (cadr fm)) chi)))
                       "the applied-lambda equation")))
    (r8k-lam-b-h! eqn)                                 ; (= (CHOICE (PICK c)) w)
    (dk-apply! picked cv)
    (let ((pk (r8k-pick sv cov delv cv)))
      (dk-split-all!
       (dk-landed (lambda () (sep-me (list 'IN (list 'CHOICE pk) pk))))))
    cv))

;; (IN w SUB) in context, goal (IN w cov)
(define (r8k-w-in-cov! sv cov delv net chi sub picked w)
  (let ((cv (r8k-sub-mem! sv cov delv net chi sub picked w)))
    (subst (list '= w (list 'CHOICE (r8k-pick sv cov delv cv))))
    (ass)
    cv))

;; goal (SUBSET SUB cov)
(define (r8k-sub-in-cov! sv cov delv net chi sub picked)
  (let ((w (subset-by-element!)))
    (r8k-w-in-cov! sv cov delv net chi sub picked w)))

;; goal (IN v BU) -- v in PTS s lies in the chosen member of its net point
(define (r8k-pts-in-bu! sv cov delv net chi sub picked netlaw v)
  (let ((cv (dk-skolem! (dk-apply! netlaw v))))
    (dk-split-all!)
    (dk-apply! picked cv)
    (let* ((pk (r8k-pick sv cov delv cv))
           (uc (list 'CHOICE pk))
           (bl (list 'BALL sv cv delv)))
      (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN uc pk)))))
      (have! (list 'IN v bl)
        (lambda ()
          (mac 'ball-sep-unfold)
          (r8k-each-leaf! (lambda () (sep-mi)) (lambda () (dk-conj-close!)))))
      (dk-fact! 'subset-mem-fwd bl uc v)               ; (IN v uc)
      (r8k-each-leaf!
       (lambda () (bu-mi uc))
       (lambda ()
         (if (equal? (caddr (dk-goal)) sub)
             (begin
               (mac 'image-membership-iff)
               (witness! cv
                 (lambda ()
                   (r8k-each-leaf!
                    (lambda () (di))
                    (lambda ()
                      (if (r8k-head? (dk-goal) 'IN)
                          (ass)
                          (begin (r8k-lam-b!) (rfl))))))))
             (ass)))))))

;; goal (IS-OPEN-COVER s SUB)
(define (r8k-sub-is-cover! sv cov delv net chi sub picked opens netlaw)
  (mac 'is-open-cover)
  (dk-conj-close!
   (lambda ()
     (let ((g (dk-goal)))
       (cond
         ((r8k-head? g 'IS-METRIC-SPACE) (ass))
         ((r8k-head? g 'FORALL)                       ; members of SUB are open
          (let ((uv (cadr (car (dk-peel!)))))
            (have! (list 'IN uv cov)
              (lambda () (r8k-w-in-cov! sv cov delv net chi sub picked uv)))
            (dk-apply! opens uv)
            (ass)))
         ((r8k-head? g '==)                           ; BIG-UNION == PTS s
          (let ((bu (cadr g)))
            (have! (list '= bu (list 'PTS sv))
              (lambda ()
                (bc* 'class-extensionality)
                (di)
                (let ((v (cadr (cadr (dk-goal)))))
                  (r8k-each-leaf!
                   (lambda () (di))
                   (lambda ()
                     (if (r8k-head? (caddr (dk-goal)) 'PTS)
                         ;; (IN v BU) => (IN v (PTS s))
                         (let* ((landed (dk-landed (lambda () (bu-me (list 'IN v bu)))))
                                (memS (dk-pick (lambda (fm) (and (r8k-head? fm 'IN)
                                                                 (equal? (caddr fm) sub)
                                                                 (member fm landed)))
                                               "the landed member-of-subcover"))
                                (w (cadr memS)))
                           (have! (list 'IN w cov)
                             (lambda () (r8k-w-in-cov! sv cov delv net chi sub picked w)))
                           (dk-apply! opens w)
                           (dk-split-all!
                            (dk-landed (lambda () (mac-h 'is-open (list 'IS-OPEN sv w)))))
                           (dk-split-all!)
                           (dk-fact! 'subset-mem-fwd w (list 'PTS sv) v)
                           (ass))
                         (r8k-pts-in-bu! sv cov delv net chi sub picked netlaw v)))))))
            (subst (list '= bu (list 'PTS sv)))
            (qrfl)))
         (#t (error "r8k-sub-is-cover!: unexpected conjunct"
                    (expression->string g))))))))

;; goal: the finite-subcover existential, for the cover COV
(define (r8k-compact! sv cov)
  (let ((delv (dk-skolem! (dk-fact! 'lebesgue-number sv cov))))
    (dk-split-all!)
    (let ((leb (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                          (dk-contains? fm delv)
                                          (dk-contains? fm 'BALL)))
                        "the Lebesgue property")))
      (dk-split-all!
       (dk-landed (lambda () (mac-h 'is-open-cover (list 'IS-OPEN-COVER sv cov)))))
      (dk-split-all!)
      (let ((opens (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                              (dk-contains? fm 'IS-OPEN)))
                            "the members-are-open law")))
        (dk-fact! 'seq-compact-implies-totally-bounded sv)
        (dk-split-all!
         (dk-landed (lambda () (mac-h 'totally-bounded (list 'TOTALLY-BOUNDED sv)))))
        (dk-split-all!)
        (r8k-pos-atoms! delv)
        (let* ((tb  (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                               (dk-contains? fm 'IS-R-NET)))
                             "the total-boundedness law"))
               (net (dk-skolem! (dk-apply! tb delv))))
          (dk-split-all!)
          (dk-split-all!
           (dk-landed (lambda () (mac-h 'is-r-net
                                        (list 'IS-R-NET sv net (list 'PTS sv) delv)))))
          (dk-split-all!)
          (let ((netlaw (dk-pick (lambda (fm) (and (r8k-head? fm 'FORALL)
                                                   (dk-contains? fm net)
                                                   (dk-contains? fm 'DIST)))
                                 "the net law")))
            (dk-fact! 'subclass-of-set-is-set net (list 'PTS sv))
            (let* ((picked (r8k-picked! sv cov delv net leb))
                   (chi    (r8k-chi sv cov delv net))
                   (sub    (list 'IMAGE chi net)))
              (dk-fact! 'card-image-finite chi net)
              (witness! sub
                (lambda ()
                  (dk-conj-close!
                   (lambda ()
                     (let ((g (dk-goal)))
                       (cond
                         ((r8k-head? g 'SUBSET)
                          (r8k-sub-in-cov! sv cov delv net chi sub picked))
                         ((r8k-head? g 'IN) (ass))
                         (#t (r8k-sub-is-cover! sv cov delv net chi sub picked
                                                opens netlaw)))))))))))))))

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (SEQ-COMPACT s) (IS-COMPACT s))))))
(dk-peel!)
(define r8k2-sv
  (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(have! (list 'IN (list 'PTS r8k2-sv) 'SET)
  (lambda ()
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'is-metric-space (list 'IS-METRIC-SPACE r8k2-sv)))))
    (ass)))
(mac 'IS-COMPACT)
(dk-conj-close!
 (lambda ()
   (if (r8k-head? (dk-goal) 'IS-METRIC-SPACE)
       (ass)
       (let ((cov (caddr (car (dk-peel!)))))
         (r8k-compact! r8k2-sv cov)))))

(qed 'seq-compact-implies-compact)
(topic! 'seq-compact-implies-compact 'topology)

;;; =====================================================================
;;; 3.  compact-iff-seq-compact -- the support's statement, LITERAL
;;;     (theorem-library/seq-compact-product.scm:52).
;;; =====================================================================

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IFF (IS-COMPACT s) (SEQ-COMPACT s))))))
(dk-peel!)
(define r8k3-sv
  (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define r8k3-fwd (dk-fact! 'compact-implies-seq-compact r8k3-sv))
(define r8k3-bwd (dk-fact! 'seq-compact-implies-compact r8k3-sv))
(dk-only! r8k3-fwd r8k3-bwd)
(prop)

(qed 'compact-iff-seq-compact)
(topic! 'compact-iff-seq-compact 'topology)

;;; =====================================================================
;;; FOR THE INTEGRATOR.
;;;
;;; * RETIRE the support compact-iff-seq-compact, theorem-library/
;;;   seq-compact-product.scm:52-60 (the `support' form and its `warrant!').
;;;   The `qed' here prints "re-installing the same statement", so the
;;;   statement is literally the support's.
;;; * SUITE TRAP (reported, not fixed): test-suite.scm:3663-3668 pins the NAME
;;;   `compact-iff-seq-compact-rev'.  That macete is generated from the
;;;   installed theorem either way, so the check should keep passing once the
;;;   support becomes a theorem -- but it is the check to look at first if the
;;;   suite reddens, and theorem-library/tychonoff-proof.scm:65 fires the same
;;;   `-rev' name.
;;; * The bills on the probe (band of 01:57, which has neither of today's two
;;;   new files) named seq-compact-implies-totally-bounded and
;;;   compact-implies-seq-compact as temporary probe-wrapper supports.  Both are
;;;   PROVEN, in files that load below this one (1348 and 1345), so the cold
;;;   load bills `modulo 0' for all four theorems here.
;;; =====================================================================
