;;; rake-seq-compact-tb.scm -- a sequentially compact metric space is totally
;;; bounded (the (C1) leg of Prop 3.12's missing direction; see the closing
;;; block of theorem-library/rake-compact-iff-seq-compact.scm).
;;;
;;;   seq-compact-implies-totally-bounded
;;;     forall s.  IS-METRIC-SPACE s  =>  SEQ-COMPACT s  =>  TOTALLY-BOUNDED s
;;;
;;; The conclusion is literally that of the proven `compact-implies-totally-
;;; bounded' (calculus/compact-tb-proof.scm:24) and the antecedents are curried.
;;;
;;; THE ROUTE.  Unfold TOTALLY-BOUNDED, fix r > 0, and split on the goal
;;; "some finite F is an r-net" with `use-em'.  In the negative branch
;;; push-not-h gives
;;;
;;;     NF:  forall F.  CARD F in NN  =>  NOT IS-R-NET(s, F, PTS s, r).
;;;
;;; THE STATE OF THE RECURSION IS THE FINITE SET OF POINTS CHOSEN SO FAR, not
;;; the last point: dc-on-nn-pred's step sees only (k, u), so a step set that
;;; speaks of "all earlier g i" has to carry them in u.  X := FIN-SUBSETS(PTS s)
;;; (theorem-library/fin-subsets.scm) is a SET, contains EMPTY-SET and is closed
;;; under union, which is every set-theoretic fact this proof needs -- in
;;; particular card-insert and its freshness side condition are never wanted.
;;;
;;;     nxt(k, u) = { v in X : forsome y in PTS s.
;;;                            (forall z in u. r <= d(z,y))  and  v = u u {y} }
;;;
;;; Totality is the ESCAPE lemma: a finite u is not an r-net (NF), so some point
;;; of PTS(s) is at distance >= r from every member of u.  Reading that off NF
;;; needs no negation of a defined predicate under a NOT: the escape existential
;;; is proved by `pbc' plus a GOAL-side `mac' of IS-R-NET, which is where the new
;;; SUBSET conjunct of IS-R-NET (metric-topology.scm, repaired 2026-09-19) is
;;; paid -- and paid for free, u being a subset of PTS(s) by construction.
;;;
;;; dc-on-nn-pred at X, EMPTY-SET, nxt returns FF : NN -> X with FF(0) = {} and
;;; FF(succ k) = FF(k) u {y_k}.  The sequence is read back out of the chain
;;; WITHOUT set subtraction and without a singleton-CHOICE identity:
;;;
;;;     g = VNB-LAMBDA k_ in NN.  CHOICE { y in PTS s :
;;;             y in FF(succ k_)  and  forall z in FF(k_). r <= d(z,y) }
;;;
;;; -- the separation is inhabited by y_k itself, so `choose!' types g and gives
;;; its two properties at once.  With FF(j) subset FF(k) for j <= k (one `ni'
;;; induction over nn-le-succ-cases) the pairwise separation follows: for i < k,
;;; g(i) in FF(succ i) subset FF(k) and g(k) is r-away from everything in FF(k).
;;;
;;; SEQ-COMPACT at g gives phi strictly monotone and L with SUBSEQ(g,phi) -> L.
;;; There is no general converges-implies-cauchy in the tree, so the two-point
;;; estimate is done inline at the indices N and succ N (phi N < phi (succ N) by
;;; strict monotonicity at bt-lt-succ): with eps := r/4 (dk-halve! twice)
;;;     r <= d(g(phi N), g(phi(succ N))) <= d(.,L) + d(L,.) <= 2*(r/4) = r/2,
;;; so r <= 0 by one `ineq', and rr-leq-antisymmetric against 0 <= r contradicts
;;; the r /= 0 of the TOTALLY-BOUNDED guard.
;;;
;;; CITATIONS and load positions (0-based over load.scm's entries, 2026-09-19):
;;;   metric-triangle, metric-sym        structure-library/metric-laws      294
;;;   fin-subsets-membership/-is-set/
;;;     -has-empty/-union-closed         theorem-library/fin-subsets        279
;;;   nn-le-zero-is-zero                 theorem-library/nn-order-proof     233
;;;   nn-lt-succ-le                      theorem-library/finite-surgery     224
;;;   metric-dist-real                   theorem-library/op-typing          207
;;;   subset-refl                        theorem-library/discrete-space     203
;;;   subset-trans, subset-mem-fwd       theorem-library/subset-lemmas      191
;;;   rr-pos-halvable (via dk-halve!)    theorem-library/rr-halving         183
;;;   rr-pos-rr-in-rr, rr-lt-of-pos-rr   theorem-library/pos-rr-bridges     176
;;;   bt-lt-succ                         theorem-library/bt-shims           173
;;;   nn-le-refl                         theorem-library/nn-order-basics    167
;;;   nn-le-succ, nn-le-succ-cases       theorem-library/nn-order-ord       165
;;;   dc-on-nn-pred                      theorem-library/rake-dc-on-nn      161
;;;   fun-apply-type-c                   theorem-library/fun-apply-type-proof 160
;;;   card-singleton                     theorem-library/card-singleton-proof 153
;;;   SEQ-COMPACT (the definition)       theorem-library/seq-compact-product 130
;;;   STRICTLY-MONO-NN, SUBSEQ           theorem-library/cauchy-subsequence  90
;;;   IS-METRIC-SPACE, CONVERGES-TO, IS-R-NET, TOTALLY-BOUNDED, POS-RR  (early)
;;;   choice-axiom, pairing, pairing-membership, membership-implies-sethood,
;;;     union-membership, subset-def                          library.scm      11
;;;   nn-zero-in, nn-succ-closed, rr-zero-in, rr-leq-total,
;;;     rr-leq-reflexive, rr-leq-antisymmetric   number-systems (primitive)   34
;;;
;;; LOAD WINDOW [295, end).  lo = 294, structure-library/metric-laws, the MAXIMUM
;;; over the citations above (fin-subsets at 279 is the next latest).  Nothing in
;;; the tree cites this theorem yet, so no citer forces hi; 7-K (the Lebesgue
;;; number lemma and seq-compact-implies-compact) will cite it and must itself sit
;;; below theorem-library/tychonoff-proof (466), so the natural slot is
;;; immediately after theorem-library/rake-compact-iff-seq-compact (306).
;;;
;;; No late tactic is used: `prop', `push-not-h', `use-em', `use-cases', `ineq'
;;; and the dk- kit all load before the theorem library (`contra' does NOT, and
;;; is not used).
;;;
;;; Helper prefix: r8j-.

;;; ---- file-local driver helpers ----------------------------------------

(define (r8j-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** rake-seq-compact-tb: ") (display name)
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
        (error "rake-seq-compact-tb: unfinished" name))))

(define (r8j-head? fm h) (and (pair? fm) (eq? (car fm) h)))

(define (r8j-mentions? fm sub)
  (let loop ((e fm))
    (cond ((equal? e sub) #t)
          ((pair? e) (or (loop (car e)) (loop (cdr e))))
          (#t #f))))

;; `ineq' by FORMULA rather than by index: the indices are 1-based into the
;; context and every forward step renumbers them.  (Fourth copy in the rake; it
;; belongs in driver-kit.scm.)
(define (r8j-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r8j-idx: not in context" (expression->string form)))
          ((equal? (car l) form) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r8j-ineq . forms) (apply ineq (map r8j-idx forms)))

;; run THUNK (a branching tactic) and visit each opened leaf with VISIT.
(define (r8j-each-leaf! thunk visit)
  (for-each (lambda (leaf) (dk-focus! leaf) (visit)) (dk-opened thunk)))

;; goal (IN t (SEP x DOM p)): `sep-mi' and run BODY on the property leaf.  NOT
;; `in-sep!': that helper demands BOTH leaves by name, and the domain leaf is
;; discharged from the context here, so only one comes back.
(define (r8j-in-sep! dom body)
  (r8j-each-leaf!
   (lambda () (sep-mi))
   (lambda ()
     (let ((g (dk-goal)))
       (if (and (r8j-head? g 'IN) (equal? (caddr g) dom)) (ass) (body))))))

;;; ---- the statement -----------------------------------------------------

(sp (make-wff
  '(FORALL s (IMPLIES (IS-METRIC-SPACE s)
     (IMPLIES (SEQ-COMPACT s) (TOTALLY-BOUNDED s))))))

(define r8j-top (dk-peel!))
(define r8j-s  (cadr (dk-pick (dk-head? 'IS-METRIC-SPACE) "the metric-space hypothesis")))
(define r8j-SC (dk-pick (dk-head? 'SEQ-COMPACT) "the sequential-compactness hypothesis"))
(define r8j-PTS (list 'PTS r8j-s))
(define r8j-X   (list 'FIN-SUBSETS r8j-PTS))

(define (r8j-d a b) (list (list 'DIST r8j-s) a b))

;; forall z_ in U. r <= d(z_, Y)
(define (r8j-sep-clause uterm yterm rv)
  (list 'FORALL 'z_
        (list 'IMPLIES (list 'IN 'z_ uterm)
              (list '<= rv (r8j-d 'z_ yterm)))))

;; the right-hand side of fin-subsets-membership at T.  The inclusion binder is
;; `z', as fin-subsets.scm spells it: `prop' is not alpha-aware.
(define (r8j-fs-conj t)
  (list 'AND (list 'IN t 'SET)
        (list 'AND (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z t) (list 'IN 'z r8j-PTS)))
              (list 'IN (list 'CARD t) 'NN))))

;; goal (IN Y (PAIR Y Y)), for a point Y of PTS(s)
(define (r8j-in-singleton! yv)
  (let ((pr (list 'PAIR yv yv)))
    (fact 'membership-implies-sethood yv r8j-PTS)
    (have! (list 'AND (list 'IN yv 'SET) (list 'IN yv 'SET)))
    (let ((iff (dk-apply! (dk-fact! 'pairing-membership yv yv) yv)))
      (have! (list '= yv yv) (lambda () (rfl)))
      (dk-only! iff (list '= yv yv))
      (prop))))

;;; ---- PTS(s) is a set; the carrier of the recursion ---------------------

(have! (list 'IN r8j-PTS 'SET)
  (lambda ()
    (dk-split-all!
     (dk-landed (lambda () (mac-h 'is-metric-space (list 'IS-METRIC-SPACE r8j-s)))))
    (dk-split-all!)
    (ass)))

(fact 'fin-subsets-is-set r8j-PTS)            ; (IN X SET)
(fact 'fin-subsets-has-empty r8j-PTS)         ; (IN EMPTY-SET X)
(fact 'nn-zero-in)

;;; -----------------------------------------------------------------------
;;; The escape lemma: a finite subset of PTS(s) misses a point by r.
;;; -----------------------------------------------------------------------

(define (r8j-escape-stmt rv)
  (list 'FORALL 'u_
        (list 'IMPLIES (list 'IN 'u_ r8j-X)
              (list 'FORSOME 'p_
                    (list 'AND (list 'IN 'p_ r8j-PTS)
                          (r8j-sep-clause 'u_ 'p_ rv))))))

;; goal (FORSOME c (AND (IN c u) (AND (<= d r) (NOT (= d r))))) at a point PV of
;; PTS(s), with NOTG = NOT(the escape existential at u) in context.
(define (r8j-net-witness! rv pv notg incl)
  (let* ((fa  (dk-landed-find (lambda () (push-not-h notg)) (dk-head? 'FORALL)))
         (nfa (dk-apply! fa pv))
         (ex  (dk-landed-find (lambda () (push-not-h nfa)) (dk-head? 'FORSOME)))
         (cv  (dk-skolem! ex)))                      ; (IN c u), (NOT (<= r d))
    (let* ((dd    (r8j-d cv pv))
           (notle (list 'NOT (list '<= rv dd))))
      (dk-apply! incl cv)                            ; (IN c (PTS s))
      (fact 'metric-dist-real r8j-s cv pv)           ; (IN d RR)
      (have! (list 'AND (list 'IN rv 'RR) (list 'IN dd 'RR)))
      (let ((tot (dk-fact! 'rr-leq-total rv dd)))
        (have! (list '<= dd rv)
          (lambda () (dk-only! tot notle) (prop))))
      (have! (list 'NOT (list '= dd rv))
        (lambda ()
          (di)                                       ; assume d = r; goal FALSITY
          (have! (list '<= rv dd)
            (lambda ()
              (subst (list '= dd rv))
              (fact 'rr-leq-reflexive rv)
              (ass)))
          (ai notle)))
      (witness! cv (lambda () (dk-conj-close! (lambda () (ass))))))))

(define (r8j-escape-lane! rv nf)
  (let* ((landed (dk-peel!))
         (uv     (cadr (car landed))))
    (have! (r8j-fs-conj uv)
      (lambda () (fact 'fin-subsets-membership r8j-PTS uv) (prop)))
    (dk-split-all! (list (r8j-fs-conj uv)))
    (dk-split-all!)
    (let* ((incl (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                            (r8j-mentions? fm uv)
                                            (r8j-mentions? fm 'PTS)))
                          "the inclusion universal of u"))
           (nrn  (dk-apply! nf uv))                  ; NOT (IS-R-NET s u (PTS s) r)
           (notg (dk-landed-1 (lambda () (pbc)))))   ; NOT goal; goal FALSITY
      (have! (list 'IS-R-NET r8j-s uv r8j-PTS rv)
        (lambda ()
          (mac 'IS-R-NET)
          (dk-conj-close!
           (lambda ()
             (if (r8j-head? (dk-goal) 'SUBSET)
                 (let ((w (subset-by-element!)))
                   (dk-apply! incl w)
                   (ass))
                 (let* ((ld (dk-peel!))
                        (pv (cadr (car ld))))
                   (r8j-net-witness! rv pv notg incl)))))))
      (ai nrn))))

;;; -----------------------------------------------------------------------
;;; The step set and its totality.
;;; -----------------------------------------------------------------------

(define (r8j-nxt rv)
  (list 'VNB-LAMBDA '(LIST k_ u_) (list 'CARTESIAN 'NN r8j-X)
        (list 'SEP 'v_ r8j-X
              (list 'FORSOME 'y_
                    (list 'AND (list 'IN 'y_ r8j-PTS)
                          (list 'AND (r8j-sep-clause 'u_ 'y_ rv)
                                (list '= 'v_ (list 'UNION 'u_ (list 'PAIR 'y_ 'y_)))))))))

;; the antecedent of dc-on-nn-pred, binders SPELLED AS THERE so the instance IS
;; the support's own hypothesis and `fact' detaches it.
(define (r8j-tot-stmt nxt)
  (list 'FORALL 'k
        (list 'IMPLIES '(IN k NN)
              (list 'FORALL 'u
                    (list 'IMPLIES (list 'IN 'u r8j-X)
                          (list 'FORSOME 'y
                                (list 'AND (list 'IN 'y r8j-X)
                                      (list 'IN 'y (list nxt 'k 'u)))))))))

;; goal (IN (PAIR p p) X)
(define (r8j-singleton-in-x! pv)
  (let ((pr (list 'PAIR pv pv)))
    (fact 'membership-implies-sethood pv r8j-PTS)        ; (IN p SET)
    (have! (list 'AND (list 'IN pv 'SET) (list 'IN pv 'SET)))
    (fact 'pairing pv pv)                                ; (IN (PAIR p p) SET)
    (have! (r8j-fs-conj pr)
      (lambda ()
        (dk-conj-close!
         (lambda ()
           (let ((g (dk-goal)))
             (cond
               ((and (r8j-head? g 'IN) (eq? (caddr g) 'SET)) (ass))
               ((r8j-head? g 'FORALL)
                (let* ((ld  (dk-peel!))
                       (zv  (cadr (car ld)))
                       (mem (list 'IN zv pr))
                       (iff (dk-apply! (dk-fact! 'pairing-membership pv pv) zv)))
                  (have! (list '= zv pv)
                    (lambda () (dk-only! iff mem) (prop)))
                  (subst (list '= zv pv))
                  (ass)))
               (#t                                       ; (IN (CARD (PAIR p p)) NN)
                (begin
                  (fact 'card-singleton pv)
                  (subst (list '= (list 'CARD pr) (list 'succ 0)))
                  (fact 'nn-succ-closed 0)
                  (ass)))))))))
    (let ((iff (dk-fact! 'fin-subsets-membership r8j-PTS pr)))
      (dk-only! iff (r8j-fs-conj pr))
      (prop))))

(define (r8j-tot-lane! rv nxt esc)
  (let* ((landed (dk-peel!))
         (uv (cadr (dk-pick (lambda (fm) (and (r8j-head? fm 'IN)
                                              (equal? (caddr fm) r8j-X)
                                              (member fm landed)))
                            "the state variable")))
         (pv (dk-skolem! (dk-apply! esc uv))))          ; p in PTS s, separated from u
    (dk-split-all!)
    (let ((pr (list 'PAIR pv pv)))
      (have! (list 'IN pr r8j-X) (lambda () (r8j-singleton-in-x! pv)))
      (fact 'fin-subsets-union-closed r8j-PTS uv pr)    ; (IN (UNION u (PAIR p p)) X)
      (let ((wv (list 'UNION uv pr)))
        (witness! wv
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (if (equal? (caddr (dk-goal)) r8j-X)
                   (ass)
                   (begin
                     (lam-b)
                     (r8j-in-sep! r8j-X
                      (lambda ()
                        (witness! pv
                          (lambda ()
                            (dk-conj-close!
                             (lambda ()
                               (if (r8j-head? (dk-goal) '=) (rfl) (ass))))))))))))))))))

;;; -----------------------------------------------------------------------
;;; Reading the chain: one stage of the recursion.
;;; -----------------------------------------------------------------------

;; At a TYPED index KV, land (IN (FF (succ k)) X) and the separated point y_k
;; with (IN y (PTS s)), (forall z in FF k. r <= d(z,y)) and the equation
;; FF(succ k) = FF k u {y}.  Returns y.
(define (r8j-stage-at! ff stage kv)
  (fact 'fun-apply-type-c ff 'NN r8j-X kv)              ; TYPE BEFORE YOU BETA
  (let* ((h  (dk-apply! stage kv))
         (sm (car (dk-landed (lambda () (lam-b-h h)))))
         (ld (dk-landed (lambda () (sep-me sm))))
         (ex (or (find-first (dk-head? 'FORSOME) ld)
                 (error "r8j-stage-at!: the SEP did not open its existential")))
         (yv (dk-skolem! ex)))
    (dk-split-all!)
    yv))

;; the separation SEP at a stage term KT
(define (r8j-gsep rv ff kt)
  (list 'SEP 'y_ r8j-PTS
        (list 'AND (list 'IN 'y_ (list ff (list 'succ kt)))
              (r8j-sep-clause (list ff kt) 'y_ rv))))

;; land (IN (CHOICE (gsep k)) (gsep k)), split -- the stage's own witness is the
;; inhabitant `choose!' owes.
(define (r8j-choose-at! rv ff stage kv)
  (let ((yv (r8j-stage-at! ff stage kv)))
    (choose! (r8j-gsep rv ff kv) yv
             (lambda ()
               (r8j-in-sep! r8j-PTS
                (lambda ()
                  (dk-conj-close!
                   (lambda ()
                     (if (r8j-head? (dk-goal) 'IN)
                         (begin
                           (subst (list '= (list ff (list 'succ kv))
                                        (list 'UNION (list ff kv) (list 'PAIR yv yv))))
                           (mac 'union-membership)
                           (oi-r)
                           (r8j-in-singleton! yv))
                         (ass))))))))
    (dk-split-all!)))

;;; -----------------------------------------------------------------------
;;; The sequence and the contradiction.
;;; -----------------------------------------------------------------------

(define (r8j-endgame! rv ff mono gv gspec)
  ;; SEQ-COMPACT at g
  (dk-split-all! (dk-landed (lambda () (mac-h 'seq-compact r8j-SC))))
  (dk-split-all!)
  (let* ((seqf (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                          (r8j-mentions? fm 'STRICTLY-MONO-NN)))
                        "the sequential-compactness universal"))
         (ex1  (dk-apply! seqf gv))
         (phiv (dk-skolem! ex1)))
    (dk-split-all!)
    (let* ((ex2 (dk-pick (lambda (fm) (and (r8j-head? fm 'FORSOME)
                                           (r8j-mentions? fm phiv)))
                         "the limit existential"))
           (lv  (dk-skolem! ex2)))
      (dk-split-all!)
      (dk-split-all! (dk-landed (lambda () (mac-h 'strictly-mono-nn
                                                  (list 'STRICTLY-MONO-NN phiv)))))
      (dk-split-all!)
      (dk-split-all! (dk-landed (lambda () (mac-h 'converges-to
                                                  (list 'CONVERGES-TO r8j-s
                                                        (list 'SUBSEQ gv phiv) lv)))))
      (dk-split-all!)
      (let* ((monophi (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                                 (r8j-mentions? fm phiv)
                                                 (dk-contains? fm '<)))
                               "the monotonicity of phi"))
             (conv (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                              (dk-contains? fm 'POS-RR)
                                              (r8j-mentions? fm lv)))
                            "the convergence universal"))
             ;; the value law of SUBSEQ, oriented so `subst' rewrites g(phi n)
             (subv (list 'FORALL 'n_
                         (list 'IMPLIES '(IN n_ NN)
                               (list '= (list gv (list phiv 'n_))
                                     (list (list 'SUBSEQ gv phiv) 'n_))))))
        (have! subv
          (lambda ()
            (let ((nv (dk-di-var!)))
              (fact 'fun-apply-type-c phiv 'NN 'NN nv)
              (fact 'fun-apply-type-c gv 'NN r8j-PTS (list phiv nv))
              (mac 'SUBSEQ)
              (lam-b)
              (rfl))))
        (let* ((h1 (dk-halve! rv))
               (e1 (dk-pick (lambda (fm) (equal? fm (list '= (list '+ h1 h1) rv)))
                            "the halving equation for r"))
               (h2 (dk-halve! h1))
               (e2 (dk-pick (lambda (fm) (equal? fm (list '= (list '+ h2 h2) h1)))
                            "the halving equation for r/2"))
               (bigN (dk-skolem! (dk-apply! conv h2))))
          (dk-split-all!)
          (let* ((tail (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                                  (r8j-mentions? fm bigN)
                                                  (r8j-mentions? fm h2)))
                                "the tail estimate"))
                 (sN (list 'succ bigN)))
            (fact 'nn-succ-closed bigN)
            (fact 'nn-le-refl bigN)
            (fact 'nn-le-succ bigN)
            (fact 'bt-lt-succ bigN)
            (fact 'fun-apply-type-c phiv 'NN 'NN bigN)
            (fact 'fun-apply-type-c phiv 'NN 'NN sN)
            (dk-apply! monophi bigN sN)                   ; phi N < phi (succ N)
            (let* ((iv (list phiv bigN))
                   (kv (list phiv sN))
                   (gi (list gv iv))
                   (gk (list gv kv)))
              (fact 'fun-apply-type-c gv 'NN r8j-PTS iv)
              (fact 'fun-apply-type-c gv 'NN r8j-PTS kv)
              ;; the separation  r <= d(g(phi N), g(phi(succ N)))
              (dk-split-all! (list (dk-apply! gspec iv)))
              (dk-split-all! (list (dk-apply! gspec kv)))
              (fact 'nn-succ-closed iv)
              (fact 'nn-lt-succ-le iv kv)                 ; (<= (succ (phi N)) (phi (succ N)))
              (dk-apply! mono kv (list 'succ iv))         ; FF(succ (phi N)) subset FF(phi(succ N))
              (fact 'subset-mem-fwd (list ff (list 'succ iv)) (list ff kv) gi)
              (let* ((clause (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                                        (r8j-mentions? fm gk)))
                                      "the separation clause at g(phi(succ N))"))
                     (sep (dk-apply! clause gi))          ; (<= r (d gi gk))
                     ;; the two tail estimates, transported off SUBSEQ
                     (est1 (list '<= (r8j-d gi lv) h2))
                     (est2 (list '<= (r8j-d gk lv) h2)))
                (dk-apply! tail bigN)
                (have! est1 (lambda () (subst (dk-apply! subv bigN)) (ass)))
                (dk-apply! tail sN)
                (have! est2 (lambda () (subst (dk-apply! subv sN)) (ass)))
                ;; triangle at L, with the second leg turned round
                (let* ((tri (dk-fact! 'metric-triangle r8j-s gi lv gk))
                       (sym (dk-fact! 'metric-sym r8j-s lv gk))
                       (leg (list '<= (r8j-d lv gk) h2)))
                  (have! leg (lambda () (subst sym) (ass)))
                  (fact 'metric-dist-real r8j-s gi gk)
                  (fact 'metric-dist-real r8j-s gi lv)
                  (fact 'metric-dist-real r8j-s lv gk)
                  (fact 'rr-zero-in)
                  (have! (list '<= rv 0)
                    (lambda ()
                      (r8j-ineq sep tri est1 leg e2 e1)))
                  (have! (list 'AND (list 'IN 0 'RR) (list 'IN rv 'RR)))
                  (have! (list 'AND (list '<= 0 rv) (list '<= rv 0)))
                  (fact 'rr-leq-antisymmetric 0 rv)
                  (dk-only! (list '= 0 rv) (list 'NOT (list '= 0 rv)))
                  (prop))))))))))

(define (r8j-sequence! rv ff stage mono)
  (let* ((lam (list 'VNB-LAMBDA 'k_ 'NN (list 'CHOICE (r8j-gsep rv ff 'k_))))
         (spec (lambda (gv)
                 (list 'FORALL 'k_
                       (list 'IMPLIES '(IN k_ NN)
                             (list 'AND (list 'IN (list gv 'k_) (list ff '(succ k_)))
                                   (r8j-sep-clause (list ff 'k_) (list gv 'k_) rv))))))
         (ex (list 'FORSOME 'g_
                   (list 'AND (list 'IN 'g_ (list 'FUN 'NN r8j-PTS))
                         (spec 'g_)))))
    (have! ex
      (lambda ()
        (witness! lam
          (lambda ()
            (dk-conj-close!
             (lambda ()
               (if (r8j-head? (caddr (dk-goal)) 'FUN)
                   (begin
                     (dk-lam-t!)
                     (let ((kv (dk-di-var!)))
                       (r8j-choose-at! rv ff stage kv)
                       (ass)))
                   (let ((kv (dk-di-var!)))
                     (lam-b)
                     (r8j-choose-at! rv ff stage kv)
                     (dk-conj-close! (lambda () (ass)))))))))))
    (let ((gv (dk-skolem! ex)))
      (dk-split-all!)
      (r8j-endgame! rv ff mono gv
                    (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                               (r8j-mentions? fm gv)
                                               (r8j-mentions? fm ff)))
                             "the specification of g")))))

;;; -----------------------------------------------------------------------
;;; The negative branch, in full.
;;; -----------------------------------------------------------------------

(define (r8j-main! rv nf)
  (let* ((esc (r8j-escape-stmt rv))
         (nxt (r8j-nxt rv))
         (tot (r8j-tot-stmt nxt)))
    (have! esc (lambda () (r8j-escape-lane! rv nf)))
    (have! tot (lambda () (r8j-tot-lane! rv nxt esc)))
    (let ((ff (dk-skolem! (dk-fact! 'dc-on-nn-pred r8j-X 'EMPTY-SET nxt))))
      (dk-split-all!)
      (let* ((stage (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                               (r8j-mentions? fm ff)
                                               (dk-contains? fm 'succ)))
                             "the per-stage property of the chain"))
             (mono1 (list 'FORALL 'k_
                          (list 'IMPLIES '(IN k_ NN)
                                (list 'SUBSET (list ff 'k_) (list ff '(succ k_))))))
             (mono  (list 'FORALL 'k_
                          (list 'IMPLIES '(IN k_ NN)
                                (list 'FORALL 'j_
                                      (list 'IMPLIES '(IN j_ NN)
                                            (list 'IMPLIES '(<= j_ k_)
                                                  (list 'SUBSET (list ff 'j_)
                                                        (list ff 'k_)))))))))
        ;; FF k subset FF (succ k)
        (have! mono1
          (lambda ()
            (let* ((kv (dk-di-var!))
                   (yv (r8j-stage-at! ff stage kv)))
              (subst (list '= (list ff (list 'succ kv))
                           (list 'UNION (list ff kv) (list 'PAIR yv yv))))
              (subset-by-element!)
              (mac 'union-membership)
              (oi-l)
              (ass))))
        ;; FF j subset FF k for j <= k
        (have! mono
          (lambda ()
            (r8j-each-leaf!
             (lambda () (ni))
             (lambda ()
               (if (dk-contains? (dk-goal) 'succ)
                   ;; STEP: k, (IN k NN), the induction hypothesis, j, (IN j NN)
                   ;; and (<= j (succ k)) all land in one greedy peel.
                   (let* ((landed (dk-peel!))
                          (ih (dk-pick (lambda (fm) (and (r8j-head? fm 'FORALL)
                                                         (member fm landed)))
                                       "the induction hypothesis"))
                          (g  (dk-goal))                  ; (SUBSET (ff j) (ff (succ k)))
                          (jv (cadr (cadr g)))
                          (kv (cadr (cadr (caddr g)))))
                     (fact 'nn-succ-closed kv)
                     (dk-apply! mono1 kv)
                     (use-cases (dk-fact! 'nn-le-succ-cases kv jv)
                       (lambda ()                         ; j <= k
                         (dk-apply! ih jv)
                         (fact 'subset-trans (list ff jv) (list ff kv)
                               (list ff (list 'succ kv)))
                         (ass))
                       (lambda ()                         ; j = succ k
                         (subst (list '= jv (list 'succ kv)))
                         (fact 'subset-refl (list ff (list 'succ kv)))
                         (ass))))
                   ;; BASE: j <= 0 forces j = 0
                   (let* ((landed (dk-peel!))
                          (g  (dk-goal))                  ; (SUBSET (ff j) (ff 0))
                          (jv (cadr (cadr g))))
                     (fact 'nn-le-zero-is-zero jv)
                     (subst (list '= jv 0))
                     (fact 'subset-refl (list ff 0))
                     (ass)))))))
        (r8j-sequence! rv ff stage mono)))))

;;; ---- unfold the goal, fix r, and split ---------------------------------

(mac 'TOTALLY-BOUNDED)
(dk-conj-close!
 (lambda ()
   (if (r8j-head? (dk-goal) 'IS-METRIC-SPACE)
       (ass)
       (let* ((landed (dk-peel!))
              (guard  (car landed))
              (rv     (cadr (cadr guard))))
         (have! (list 'POS-RR rv) (lambda () (mac 'pos-rr) (ass)))
         (dk-split-all!)
         (fact 'rr-lt-of-pos-rr rv)
         (let ((g (dk-goal)))
           (use-em g
                   (lambda () (ass))
                   (lambda ()
                     (let ((nf (dk-landed-find (lambda () (push-not-h (list 'NOT g)))
                                               (dk-head? 'FORALL))))
                       (r8j-main! rv nf)))))))))

(r8j-qed! 'seq-compact-implies-totally-bounded)
(topic! 'seq-compact-implies-totally-bounded 'topology)
