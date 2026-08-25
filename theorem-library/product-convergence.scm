;;; product-convergence.scm -- CONVERGENCE IN THE COUNTABLE PRODUCT IS EXACTLY
;;; COORDINATEWISE CONVERGENCE, proven both ways, retiring the asserted
;;; `product-convergence-coordinatewise' of structure-library/product-metric.scm
;;; -- the defining property of the PRODUCT TOPOLOGY, and the rung every later
;;; statement about the countable product stands on.
;;;
;;;   CONVERGES-TO(PRODUCT-METRIC-W(ms,w), seq, L)
;;;     iff  for every n,  CONVERGES-TO(ms(n), k |-> seq(k)(n), L(n)).
;;;
;;; THE TWO HALVES ARE NOT THE SAME ARGUMENT, and neither is the eps/N chase
;;; the retired warrant described.
;;;
;;; (<=) -- the half the warrant called hard ("choose N with the weight tail
;;; below eps/2, then make the first N coordinates small") -- is ONE CITATION.
;;; `dominated-null-series' (theorem-library/dominated-convergence.scm) IS that
;;; argument, stated for an arbitrary dominated pointwise-null family of
;;; nonnegative series: it splits the sum at an index where the dominating
;;; series' tail is small and kills the finite head by pointwise convergence.
;;; Here the dominator is the weight sequence w itself (each term is at most
;;; w(n), `bdd-metric-weight-bound'), the family is u(j)(n) = w(n)*rho_n(seq(j)(n),
;;; L(n)), and the sums are the product distances (`product-metric-dist-converges').
;;; No tail estimate and no finite maximum is written here at all.
;;;
;;; (=>) is the SHARP termwise bound, which the tree acquired only on
;;; 2026-08-23: `series-term-le-sum' (theorem-library/mono-le-limit.scm) says a
;;; term of a nonnegative convergent series is at most its sum, so
;;;
;;;     w(n) * rho_n(seq(j)(n), L(n))  <=  D_w(seq(j), L)
;;;
;;; and the right-hand side is null.  What was missing beside it is a SQUEEZE
;;; (L1 below): nothing in the tree said a nonnegative sequence dominated by a
;;; null one is null.  `rr-null-sum' adds two null sequences and `rr-null-scale'
;;; multiplies one by a constant; neither compares two.
;;;
;;; THE DIVIDING COMPANION TO `rr-scale-eps' IS NOT NEEDED, and that is worth
;;; recording because it was the expected shape of the gap.  Dividing the
;;; estimate by w(n) is `rr-null-scale' AT c = recip(w(n)): the scalar multiple
;;; is already general in c, and w(n) > 0 makes recip(w(n)) a nonnegative real.
;;; The whole reciprocal argument stays inside `rr-scale-eps', where it was
;;; already paid for.
;;;
;;; THE ONE MECHANICAL FINDING (L2, `converges-to-transfer').  Every bridging
;;; theorem in this lane concludes about the LITERAL lambda it builds, and the
;;; literals do not agree.  `converges-dist-null-fwd' at the coordinate sequence
;;; concludes about
;;;
;;;     j |-> (DIST BDD-METRIC(ms(n))) ( (k |-> seq(k)(n)) (j), L(n) )
;;;
;;; -- a beta-REDEX under the binder -- while everything downstream is about
;;; j |-> (DIST ...)(seq(j)(n), L(n)).  `lam-b' cannot reach under the binder,
;;; and the two sequences are not the same term.  The real-sequence lane solved
;;; this long ago by stating every conclusion in TRANSFER form (`rr-null-sum',
;;; `rr-null-scale', `cont-transfer-ptwise-eq'); the METRIC lane had no such
;;; theorem.  `converges-to-transfer' is it, `modulo 0': pointwise-equal
;;; sequences converge alike, in any metric space.  It is used four times below
;;; and is the reason no beta-reduction under a binder appears anywhere here.
;;;
;;; A DEFINEDNESS TRAP, met three times.  `rfl' will not close `t = t' unless
;;; `t' is syntactically self-defined OR the context carries `(IN t _)'
;;; (pi-reflexivity!, primitive-inferences.scm:608) -- `=' is partial, and
;;; `t = t' IS the definedness assertion.  So every pointwise-equality lane
;;; below lands the typing of the term FIRST and beta-reduces second.  The
;;; failure is loud but its message ("goal is not (= a a)") prints the goal,
;;; which reads as `X = X' and looks like a prover bug.
;;;
;;; AND THE DESTRUCTIVE-UNFOLD TRAP, which cost a run: `mac-h' REPLACES the
;;; assumption it unfolds, so unfolding IS-MS-SEQUENCE(ms) and SUMMABLE-WEIGHT(w)
;;; in the main branch deletes the two antecedents every later `fact' in this
;;; file detaches on (`product-term-seq-in-fun', `product-metric-dist-converges',
;;; L3 and L4 themselves).  `pc-setup!' therefore does both unfolds inside
;;; `have!' LANES: the main branch gains the three universals AND keeps both
;;; predicates.  product-summable.scm's `pm-setup!' is destructive and works
;;; only because its citations all precede it.
;;;
;;; WHAT IT COSTS.  `modulo {product-is-metric-space, metric-dist-real,
;;; bdd-metric-is-metric-space, bdd-metric-carrier, bdd-metric-bounded,
;;; bdd-metric-distance, bdd-fn-le-arg, nn-zero-le, nn-le-succ-cases,
;;; rr-le-all-pos-nonpos}' [trust: well-known] -- and NOT ONE of those is about
;;; the product topology.  Four are the bounded-metric supports of
;;; structure-library/bounded-metric.scm plus the scalar `bdd-fn-le-arg', one is
;;; `metric-dist-real' (that a distance is a real number, which every metric
;;; estimate in the tree pays), one is `product-is-metric-space' -- the rung
;;; BELOW this one, still asserted -- and the last three are the NN-order /
;;; archimedean backlog inherited through `dominated-null-series'.  The two
;;; general lemmas L1 and L2 are `modulo 0'.
;;;
;;; Loads after theorem-library/product-summable (the product plumbing),
;;; converges-dist-null (the CONVERGES-TO <-> null-distance bridge, used four
;;; times), bdd-metric-convergence (bdd-metric-converges-fwd/-bwd),
;;; rr-null-scale, mono-le-limit (series-term-le-sum), dominated-convergence
;;; (dominated-null-series) and structure-library/product-metric.

;;; ---- file-local driver helpers (the `pc-' prefix) ---------------------
;;; shared file-local driver helpers for the product-convergence work (pc-)
(define (pc-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (pc-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))
(define (pc-and2! a b) (have! (list 'AND a b) (lambda () (pc-and! (lambda () (ass))))))
(define (pc-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "pc-idx: not in context" form))
          ((equal? (car l) form) i) (else (loop (cdr l) (+ i 1))))))
(define (pc-ineq . forms) (apply ineq (map pc-idx forms)))
(define (pc-eq! e) (have! e (lambda () (crs))) (subst e))
(define (pc-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "pc-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))
(define (pc-fvs forms) (apply append (map free-vars forms)))
(define (pc-skolem! ex)
  (let* ((fv0 (pc-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (pc-fvs (dk-asms)))))
      (if (null? fresh) (error "pc-skolem!: nothing appeared" ex) (car fresh)))))
(define (pc-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 5) (error "pc-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (pc-di-landed-1!)
  (let ((new (pc-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "pc-di-landed-1!: expected 1" (map expression->string new)))))
(define (pc-peel-to! head)
  (let lp ((k 0))
    (if (and (< k 16) (not (eq? (car (dk-goal)) head)))
        (begin (di) (lp (+ k 1))))))
(define (pc-split-h! name form)
  (dk-split! (dk-landed-find (lambda () (mac-h name form))
                             (lambda (f) (eq? (car f) 'AND)))))
(define (pc-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))
(define (pc-has-redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)) #t)
        (else (any-pred pc-has-redex? e))))
(define (pc-beta!)
  (let lp ((n 0))
    (if (and (< n 8) (pc-has-redex? (dk-goal)))
        (begin (lam-b) (lp (+ n 1))))))
(define (pc-converges-to! eps-branch)
  (mac 'converges-to)
  (pc-and!
   (lambda ()
     (let ((gl (dk-goal)))
       (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
             ((eq? (car gl) 'IN) (slot 'PTS) (ass))
             (else (eps-branch)))))))
;;; (IN x TY) where TY mentions PTS(RR-MS): prove it from the RR form by `slot'.
(define (pc-pts-rr! ty x) (have! (list 'IN x ty) (lambda () (slot 'PTS) (ass))))
(define pc-fun-pts-rr '(FUN NN (PTS RR-MS)))
;; the two conjuncts of a context (< a b), landed WITHOUT destroying it
(define (pc-from-lt! a b)
  (let ((lt (list '< a b)))
    (for-each
     (lambda (part)
       (have! part (lambda ()
                     (dk-split! (dk-landed-find (lambda () (mac-h '< lt))
                                                (lambda (f) (eq? (car f) 'AND))))
                     (ass))))
     (list (list '<= a b) (list 'NOT (list '= a b))))))

;;; The two universals inside IS-MS-SEQUENCE and SUMMABLE-WEIGHT, landed
;;; WITHOUT destroying either predicate: `mac-h' REPLACES the assumption it
;;; unfolds, and both are antecedents that later citations still detach on.
(define pc-msu #f) (define pc-wpos #f)
(define (pc-setup! wv msv)
  (set! pc-msu (list 'FORALL 'nx_ (list 'IMPLIES '(IN nx_ NN)
                                        (list 'IS-METRIC-SPACE (list msv 'nx_)))))
  (set! pc-wpos (list 'FORALL 'nx_ (list 'IMPLIES '(IN nx_ NN)
                                         (list '< 0 (list wv 'nx_)))))
  (have! pc-msu (lambda () (mac-h 'is-ms-sequence (list 'IS-MS-SEQUENCE msv)) (ass)))
  (for-each
   (lambda (claim)
     (have! claim (lambda ()
                    (pc-split-h! 'summable-weight (list 'SUMMABLE-WEIGHT wv))
                    (ass))))
   (list pc-wpos (list 'IN wv '(FUN NN RR)) (list 'SERIES-CONVERGES wv))))

;;; =====================================================================
;;; L1.  rr-null-squeeze -- a nonnegative sequence dominated by a null one is
;;; null.  The tree had no comparison between two real sequences at all.  The
;;; SAME threshold works: at n beyond f's, 0 <= h(n) <= f(n) <= |f(n)| <= eps,
;;; and `ineq' chains the four with abs(f(n) - 0) as one atom.
;;; =====================================================================
(sp (make-wff "forall([f in fun(nn,rr), h in fun(nn,rr)],
      converges-to(rr-ms, f, 0) implies
      forall([j_ in nn], 0 <= h(j_) and h(j_) <= f(j_)) implies
      converges-to(rr-ms, h, 0))"))
(di)(di)(di)
(define sq-pt (pc-find 'pointwise
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(pc-split-h! 'converges-to '(CONVERGES-TO RR-MS f 0))
(define sq-tf (pc-find 'ftail
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'f)
                                 (dk-contains? a 'POS-RR)))))
(fact 'rr-zero-in)

(define (sq-index! eps innerf)
  (let ((n_ (cadr (pc-di-landed-1!))))
    (pc-di-landed!)                                   ; bigN <= n_
    (inst+ innerf n_)
    (dk-split! (dk-deepest (lambda () (inst+ sq-pt n_))))
    (fact 'fun-apply-type-c 'f 'NN 'RR n_)
    (fact 'fun-apply-type-c 'h 'NN 'RR n_)
    (let* ((fn (list 'f n_)) (hn (list 'h n_))
           (uf (list '- fn 0)) (uh (list '- hn 0)))
      (mac-h 'rr-ms-dist (list '<= (list (list 'DIST 'RR-MS) fn 0) eps))
      (mac 'rr-ms-dist)
      (fact 'rr-sub-in-rr fn 0)
      (fact 'rr-sub-in-rr hn 0)
      (fact 'rr-abs-closed uf)
      (have! (list '<= 0 uh) (lambda () (pc-ineq (list '<= 0 hn))))
      (fact 'rr-abs-of-nonneg uh)
      (subst (list '= (list 'abs uh) uh))
      (fact 'rr-le-abs uf)
      (pc-ineq (list '<= hn fn)
               (list '<= uf (list 'abs uf))
               (list '<= (list 'abs uf) eps)))))

(define (sq-eps-branch!)
  (let ((eps (cadr (pc-di-landed-1!))))
    (pc-pos-in-rr! eps)
    (let* ((nex   (dk-deepest (lambda () (inst+ sq-tf eps))))
           (bigN  (pc-skolem! nex))
           (innerf (pc-find 'ftailinner
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (let ((b (caddr a)))
                                        (and (pair? b) (eq? (car b) 'IMPLIES)
                                             (dk-contains? (caddr b) bigN))))))))
      (ew bigN)
      (pc-and! (lambda ()
                 (if (eq? (car (dk-goal)) 'IN) (ass)
                     (sq-index! eps innerf)))))))

(mac 'converges-to)
(pc-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (fact 'rr-is-metric-space) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else (sq-eps-branch!))))))
(qed 'rr-null-squeeze)

;;; =====================================================================
;;; L2.  converges-to-transfer -- a sequence pointwise equal to a convergent
;;; one converges to the same limit, in ANY metric space.  The metric lane's
;;; missing transfer form; see the head comment.  One `subst' per index.
;;; =====================================================================
(sp (make-wff "forall([t], is-metric-space(t) implies
      forall([f in fun(nn,pts(t)), h in fun(nn,pts(t)), lv in pts(t)],
        converges-to(t, f, lv) implies
        forall([j_ in nn], h(j_) = f(j_)) implies
        converges-to(t, h, lv)))"))
(pc-peel-to! 'CONVERGES-TO)
(define tr-pt (pc-find 'pointwise
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))
(pc-split-h! 'converges-to '(CONVERGES-TO t f lv))
(define tr-tf (pc-find 'ftail
                (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'f)
                                 (dk-contains? a 'POS-RR)))))

(define (tr-eps-branch!)
  (let ((eps (cadr (pc-di-landed-1!))))
    (let* ((nex   (dk-deepest (lambda () (inst+ tr-tf eps))))
           (bigN  (pc-skolem! nex))
           (innerf (pc-find 'ftailinner
                     (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                      (let ((b (caddr a)))
                                        (and (pair? b) (eq? (car b) 'IMPLIES)
                                             (dk-contains? (caddr b) bigN))))))))
      (ew bigN)
      (pc-and!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN) (ass)
             (let ((n_ (cadr (pc-di-landed-1!))))
               (pc-di-landed!)
               (inst+ innerf n_)
               (inst+ tr-pt n_)
               (subst (list '= (list 'h n_) (list 'f n_)))
               (ass))))))))

(mac 'converges-to)
(pc-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
           ((eq? (car gl) 'IN) (ass))
           (else (tr-eps-branch!))))))
(qed 'converges-to-transfer)


;;; =====================================================================
;;; L3.  product-coord-weighted-null -- coordinate convergence in the factor
;;; makes the WEIGHTED coordinate distance a null real sequence.  The chain is
;;;   ms(n) -> BDD-METRIC(ms(n))          bdd-metric-converges-fwd
;;;         -> a null distance sequence   converges-dist-null-fwd
;;;         -> the plain rho sequence     converges-to-transfer (the redex)
;;;         -> times w(n)                 rr-null-scale.
;;; =====================================================================

(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
       (FORALL lv (IMPLIES (IN lv (PRODUCT-CARRIER ms))
         (FORALL n_ (IMPLIES (IN n_ NN)
           (IMPLIES (CONVERGES-TO (ms n_) (VNB-LAMBDA k NN ((seq k) n_)) (lv n_))
             (CONVERGES-TO RR-MS
               (VNB-LAMBDA j_ NN (* (w n_) ((DIST (BDD-METRIC (ms n_)))
                                            ((seq j_) n_) (lv n_)))) 0))))))))))))))
(pc-peel-to! 'CONVERGES-TO)

;;; every name read off the GOAL and the antecedent, never off the source text
(define f4-wrho   (caddr (dk-goal)))
(define f4-j      (cadr f4-wrho))
(define f4-body   (cadddr f4-wrho))
(define f4-wn     (cadr f4-body))
(define f4-w      (car f4-wn))
(define f4-n      (cadr f4-wn))
(define f4-distapp(caddr f4-body))
(define f4-bdd    (cadr (car f4-distapp)))
(define f4-msn    (cadr f4-bdd))
(define f4-ms     (car f4-msn))
(define f4-seq    (car (car (cadr f4-distapp))))
(define f4-lv     (car (caddr f4-distapp)))
(define f4-lvn    (caddr f4-distapp))
(define f4-rho    (list 'VNB-LAMBDA f4-j 'NN f4-distapp))
(define f4-cs     (caddr (pc-find 'coordhyp
                    (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                     (equal? (cadr a) f4-msn))))))

(pc-setup! f4-w f4-ms)
(inst+ pc-msu f4-n)
(fact 'product-carrier-coord f4-ms f4-lv f4-n)
(fact 'fun-apply-type-c f4-w 'NN 'RR f4-n)
(inst+ pc-wpos f4-n)

;;; the coordinate distance at index jj is a real number (and its arguments
;;; are typed, which is what `rfl' wants for definedness)
(define (f4-coord! jj)
  (fact 'fun-apply-type-c f4-seq 'NN (list 'PRODUCT-CARRIER f4-ms) jj)
  (fact 'product-carrier-coord f4-ms (list f4-seq jj) f4-n)
  (have! (list 'IN (list (list f4-seq jj) f4-n) (list 'PTS f4-bdd))
         (lambda () (mac 'bdd-metric-carrier) (ass))))
(define (f4-rho-real! jj)
  (f4-coord! jj)
  (fact 'metric-dist-real f4-bdd (list (list f4-seq jj) f4-n) f4-lvn))

;;; the coordinate sequence is a sequence in the factor
(have! (list 'IN f4-cs (list 'FUN 'NN (list 'PTS f4-msn)))
  (lambda ()
    (dk-lam-t!)
    (let ((k (cadr (pc-di-landed-1!))))
      (fact 'fun-apply-type-c f4-seq 'NN (list 'PRODUCT-CARRIER f4-ms) k)
      (fact 'product-carrier-coord f4-ms (list f4-seq k) f4-n)
      (pc-beta!)
      (ass))))

;;; ---- into the BOUNDED metric, then into a real null sequence -----------
(fact 'bdd-metric-converges-fwd f4-msn f4-cs f4-lvn)
(fact 'bdd-metric-is-metric-space f4-msn)
(have! (list 'IN f4-cs (list 'FUN 'NN (list 'PTS f4-bdd)))
       (lambda () (mac 'bdd-metric-carrier) (ass)))
(have! (list 'IN f4-lvn (list 'PTS f4-bdd))
       (lambda () (mac 'bdd-metric-carrier) (ass)))
(fact 'converges-dist-null-fwd f4-bdd f4-cs f4-lvn)
(fact 'dist-seq-in-fun f4-bdd f4-cs f4-lvn)
(define f4-dl (caddr (pc-find 'distnull
                 (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                  (eq? (cadr a) 'RR-MS))))))

;;; ---- transfer the beta-redex form to the plain rho sequence ------------
(have! (list 'IN f4-rho '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((jj (cadr (pc-di-landed-1!))))
      (f4-rho-real! jj)
      (ass))))
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(pc-pts-rr! pc-fun-pts-rr f4-rho)
(pc-pts-rr! pc-fun-pts-rr f4-dl)
(pc-pts-rr! '(PTS RR-MS) 0)
(have! (list 'FORALL f4-j (list 'IMPLIES (list 'IN f4-j 'NN)
                                (list '= (list f4-rho f4-j) (list f4-dl f4-j))))
  (lambda ()
    (let ((jj (cadr (pc-di-landed-1!))))
      (f4-rho-real! jj)
      (pc-beta!)
      (rfl))))
(fact 'converges-to-transfer 'RR-MS f4-dl f4-rho 0)

;;; ---- and the weight is a nonnegative scalar ---------------------------
(define (f4-wt! jj)
  (fact 'fun-apply-type-c f4-seq 'NN (list 'PRODUCT-CARRIER f4-ms) jj)
  (fact 'product-carrier-coord f4-ms (list f4-seq jj) f4-n)
  (dk-split! (dk-deepest
    (lambda () (fact 'bdd-metric-weight-bound f4-msn
                     (list (list f4-seq jj) f4-n) f4-lvn f4-wn)))))
(have! (list '<= 0 f4-wn)
  (lambda ()
    (dk-split! (dk-landed-find (lambda () (mac-h '< (list '< 0 f4-wn)))
                               (lambda (f) (eq? (car f) 'AND))))
    (ass)))
(have! (list 'IN f4-wrho '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((jj (cadr (pc-di-landed-1!)))) (f4-wt! jj) (ass))))
(have! (list 'FORALL f4-j (list 'IMPLIES (list 'IN f4-j 'NN)
                                (list '= (list f4-wrho f4-j)
                                         (list '* f4-wn (list f4-rho f4-j)))))
  (lambda ()
    (let ((jj (cadr (pc-di-landed-1!)))) (f4-wt! jj) (pc-beta!) (rfl))))
(fact 'rr-null-scale f4-wn f4-rho f4-wrho)
(ass)
(qed 'product-coord-weighted-null)

;;; =====================================================================
;;; L4.  product-coord-from-weighted-null -- the converse, the same chain
;;; backwards, with the division by w(n) done as rr-null-scale at recip(w(n))
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
       (FORALL lv (IMPLIES (IN lv (PRODUCT-CARRIER ms))
         (FORALL n_ (IMPLIES (IN n_ NN)
           (IMPLIES (CONVERGES-TO RR-MS
                      (VNB-LAMBDA j_ NN (* (w n_) ((DIST (BDD-METRIC (ms n_)))
                                                   ((seq j_) n_) (lv n_)))) 0)
             (CONVERGES-TO (ms n_) (VNB-LAMBDA k NN ((seq k) n_)) (lv n_)))))))))))))))
(pc-peel-to! 'CONVERGES-TO)

(define b4-cs     (caddr (dk-goal)))
(define b4-msn    (cadr (dk-goal)))
(define b4-ms     (car b4-msn))
(define b4-n      (cadr b4-msn))
(define b4-lvn    (cadddr (dk-goal)))
(define b4-lv     (car b4-lvn))
(define b4-wrho   (caddr (pc-find 'wrhonull
                    (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                     (eq? (cadr a) 'RR-MS))))))
(define b4-j      (cadr b4-wrho))
(define b4-body   (cadddr b4-wrho))
(define b4-wn     (cadr b4-body))
(define b4-w      (car b4-wn))
(define b4-distapp(caddr b4-body))
(define b4-bdd    (cadr (car b4-distapp)))
(define b4-seq    (car (car (cadr b4-distapp))))
(define b4-rho    (list 'VNB-LAMBDA b4-j 'NN b4-distapp))

(pc-setup! b4-w b4-ms)
(inst+ pc-msu b4-n)
(fact 'product-carrier-coord b4-ms b4-lv b4-n)
(fact 'fun-apply-type-c b4-w 'NN 'RR b4-n)
(inst+ pc-wpos b4-n)
(fact 'bdd-metric-is-metric-space b4-msn)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)

(define (b4-coord! jj)
  (fact 'fun-apply-type-c b4-seq 'NN (list 'PRODUCT-CARRIER b4-ms) jj)
  (fact 'product-carrier-coord b4-ms (list b4-seq jj) b4-n)
  (have! (list 'IN (list (list b4-seq jj) b4-n) (list 'PTS b4-bdd))
         (lambda () (mac 'bdd-metric-carrier) (ass))))
(define (b4-rho-real! jj)
  (b4-coord! jj)
  (fact 'metric-dist-real b4-bdd (list (list b4-seq jj) b4-n) b4-lvn))
(define (b4-wt! jj)
  (fact 'fun-apply-type-c b4-seq 'NN (list 'PRODUCT-CARRIER b4-ms) jj)
  (fact 'product-carrier-coord b4-ms (list b4-seq jj) b4-n)
  (dk-split! (dk-deepest
    (lambda () (fact 'bdd-metric-weight-bound b4-msn
                     (list (list b4-seq jj) b4-n) b4-lvn b4-wn)))))

;;; the coordinate sequence, in the factor and in its bounded twin
(have! (list 'IN b4-cs (list 'FUN 'NN (list 'PTS b4-msn)))
  (lambda ()
    (dk-lam-t!)
    (let ((k (cadr (pc-di-landed-1!))))
      (fact 'fun-apply-type-c b4-seq 'NN (list 'PRODUCT-CARRIER b4-ms) k)
      (fact 'product-carrier-coord b4-ms (list b4-seq k) b4-n)
      (pc-beta!)
      (ass))))
(have! (list 'IN b4-cs (list 'FUN 'NN (list 'PTS b4-bdd)))
       (lambda () (mac 'bdd-metric-carrier) (ass)))
(have! (list 'IN b4-lvn (list 'PTS b4-bdd))
       (lambda () (mac 'bdd-metric-carrier) (ass)))

;;; ---- divide by the weight:  rho = recip(w(n)) * (w(n) * rho) -----------
(pc-from-lt! 0 b4-wn)
(fact 'rr-pos-ne-zero b4-wn)
(pc-and2! (list 'IN b4-wn 'RR) (list 'NOT (list '= b4-wn 0)))
(fact 'rr-recip-closed b4-wn)
(fact 'rr-recip-inverse b4-wn)
(fact 'rr-recip-pos b4-wn)
(define b4-r (list 'recip b4-wn))
(pc-from-lt! 0 b4-r)
(have! (list 'IN b4-wrho '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((jj (cadr (pc-di-landed-1!)))) (b4-wt! jj) (ass))))
(have! (list 'IN b4-rho '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((jj (cadr (pc-di-landed-1!)))) (b4-rho-real! jj) (ass))))
(have! (list 'FORALL b4-j (list 'IMPLIES (list 'IN b4-j 'NN)
                                (list '= (list b4-rho b4-j)
                                         (list '* b4-r (list b4-wrho b4-j)))))
  (lambda ()
    (let* ((jj (cadr (pc-di-landed-1!)))
           (rho (list (list 'DIST b4-bdd) (list (list b4-seq jj) b4-n) b4-lvn)))
      (b4-rho-real! jj)
      (pc-beta!)
      (pc-eq! (list '= (list '* b4-r (list '* b4-wn rho))
                       (list '* (list '* b4-wn b4-r) rho)))
      (subst (list '= (list '* b4-wn b4-r) 1))
      (crs))))
(fact 'rr-null-scale b4-r b4-wrho b4-rho)

;;; ---- back up through the beta-redex form and the bounded metric --------
(fact 'dist-seq-in-fun b4-bdd b4-cs b4-lvn)
(define b4-dl (list 'VNB-LAMBDA b4-j 'NN
                    (list (list 'DIST b4-bdd) (list b4-cs b4-j) b4-lvn)))
(pc-pts-rr! pc-fun-pts-rr b4-rho)
(pc-pts-rr! pc-fun-pts-rr b4-dl)
(pc-pts-rr! '(PTS RR-MS) 0)
(have! (list 'FORALL b4-j (list 'IMPLIES (list 'IN b4-j 'NN)
                                (list '= (list b4-dl b4-j) (list b4-rho b4-j))))
  (lambda ()
    (let ((jj (cadr (pc-di-landed-1!))))
      (b4-rho-real! jj)
      (pc-beta!)
      (rfl))))
(fact 'converges-to-transfer 'RR-MS b4-rho b4-dl 0)
(fact 'converges-dist-null-bwd b4-bdd b4-cs b4-lvn)
(fact 'bdd-metric-converges-bwd b4-msn b4-cs b4-lvn)
(ass)
(qed 'product-coord-from-weighted-null)

;;; =====================================================================
;;; L5.  coordinatewise convergence gives convergence in the product -- the
;;; half the retired warrant called hard.  It is `dominated-null-series' at
;;; (g, e, u) = (w, the product distances, the coordinate term families).
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
       (FORALL lv (IMPLIES (IN lv (PRODUCT-CARRIER ms))
         (IMPLIES (FORALL n_ (IMPLIES (IN n_ NN)
                    (CONVERGES-TO (ms n_) (VNB-LAMBDA k NN ((seq k) n_)) (lv n_))))
           (CONVERGES-TO (PRODUCT-METRIC-W ms w) seq lv))))))))))))
(pc-peel-to! 'CONVERGES-TO)
(define c4-p    (cadr (dk-goal)))                 ; PRODUCT-METRIC-W(ms, w)
(define c4-ms   (cadr c4-p))
(define c4-w    (caddr c4-p))
(define c4-seq  (caddr (dk-goal)))
(define c4-lv   (cadddr (dk-goal)))
(define c4-coord (pc-find 'coordhyp
                   (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                    (dk-contains? a 'CONVERGES-TO)))))
(define c4-e '())
(define c4-u '())
(set! c4-e (list 'VNB-LAMBDA 'j_ 'NN
                 (list (list 'DIST c4-p) (list c4-seq 'j_) c4-lv)))
(set! c4-u (list 'VNB-LAMBDA 'j_ 'NN
             (list 'VNB-LAMBDA 'n_ 'NN
               (list '* (list c4-w 'n_)
                     (list (list 'DIST (list 'BDD-METRIC (list c4-ms 'n_)))
                           (list (list c4-seq 'j_) 'n_) (list c4-lv 'n_))))))
(define (c4-inner j) (list 'VNB-LAMBDA 'n_ 'NN
                       (list '* (list c4-w 'n_)
                             (list (list 'DIST (list 'BDD-METRIC (list c4-ms 'n_)))
                                   (list (list c4-seq j) 'n_) (list c4-lv 'n_)))))

;;; the product IS a metric space, and its carrier is the product carrier
(fact 'product-is-metric-space c4-ms c4-w)
(have! (list 'IN c4-seq (list 'FUN 'NN (list 'PTS c4-p)))
       (lambda () (mac 'product-metric-carrier) (ass)))
(have! (list 'IN c4-lv (list 'PTS c4-p))
       (lambda () (mac 'product-metric-carrier) (ass)))
(pc-setup! c4-w c4-ms)

;;; the point seq(j) of the product, and the distance to lv, at one index
(define (c4-pt! j)
  (fact 'fun-apply-type-c c4-seq 'NN (list 'PRODUCT-CARRIER c4-ms) j)
  (fact 'fun-apply-type-c c4-seq 'NN (list 'PTS c4-p) j)
  (fact 'metric-dist-real c4-p (list c4-seq j) c4-lv))

;;; ---- the five antecedents of dominated-null-series at (w, e, u) --------
(have! (list 'IN c4-e '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j (cadr (pc-di-landed-1!)))) (c4-pt! j) (ass))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'IN (list c4-u 'j_) '(FUN NN RR))))
  (lambda ()
    (let ((j (cadr (pc-di-landed-1!))))
      (pc-beta!)
      (fact 'fun-apply-type-c c4-seq 'NN (list 'PRODUCT-CARRIER c4-ms) j)
      (fact 'product-term-seq-in-fun c4-ms c4-w (list c4-seq j) c4-lv)
      (ass))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
           (list 'AND (list '<= 0 (list (list c4-u 'j_) 'i_))
                      (list '<= (list (list c4-u 'j_) 'i_) (list c4-w 'i_)))))))
  (lambda ()
    (let* ((typs (pc-di-landed!))
           (j (cadr (car typs)))
           (i (cadr (if (pair? (cdr typs)) (cadr typs) (car (pc-di-landed!))))))
      (pc-beta!)
      (inst+ pc-msu i)
      (fact 'fun-apply-type-c c4-seq 'NN (list 'PRODUCT-CARRIER c4-ms) j)
      (fact 'product-carrier-coord c4-ms (list c4-seq j) i)
      (fact 'product-carrier-coord c4-ms c4-lv i)
      (fact 'fun-apply-type-c c4-w 'NN 'RR i)
      (inst+ pc-wpos i)
      (pc-from-lt! 0 (list c4-w i))
      (dk-split! (dk-deepest
        (lambda () (fact 'bdd-metric-weight-bound (list c4-ms i)
                         (list (list c4-seq j) i) (list c4-lv i) (list c4-w i)))))
      (pc-and! (lambda () (ass))))))
(have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
         (list 'CONVERGES-TO 'RR-MS
               (list 'VNB-LAMBDA 'j_ 'NN (list (list c4-u 'j_) 'i_)) 0)))
  (lambda ()
    (let* ((i (cadr (pc-di-landed-1!)))
           (m (list 'VNB-LAMBDA 'j_ 'NN (list (list c4-u 'j_) i))))
      (inst+ c4-coord i)
      (let* ((land (dk-deepest
                    (lambda () (fact 'product-coord-weighted-null
                                     c4-ms c4-w c4-seq c4-lv i))))
             (tgt (caddr land)))
        (inst+ pc-msu i)
        (fact 'product-carrier-coord c4-ms c4-lv i)
        (fact 'fun-apply-type-c c4-w 'NN 'RR i)
        (inst+ pc-wpos i)
        (pc-from-lt! 0 (list c4-w i))
        (fact 'rr-is-metric-space)
        (fact 'rr-zero-in)
        (let ((wt! (lambda (j)
                     (fact 'fun-apply-type-c c4-seq 'NN
                           (list 'PRODUCT-CARRIER c4-ms) j)
                     (fact 'product-carrier-coord c4-ms (list c4-seq j) i)
                     (dk-split! (dk-deepest
                       (lambda () (fact 'bdd-metric-weight-bound (list c4-ms i)
                                        (list (list c4-seq j) i) (list c4-lv i)
                                        (list c4-w i))))))))
          (have! (list 'IN tgt '(FUN NN RR))
            (lambda () (dk-lam-t!)
                    (let ((j (cadr (pc-di-landed-1!)))) (wt! j) (ass))))
          (have! (list 'IN m '(FUN NN RR))
            (lambda () (dk-lam-t!)
                    (let ((j (cadr (pc-di-landed-1!)))) (pc-beta!) (wt! j) (ass))))
          (pc-pts-rr! pc-fun-pts-rr tgt)
          (pc-pts-rr! pc-fun-pts-rr m)
          (pc-pts-rr! '(PTS RR-MS) 0)
          (have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                    (list '= (list m 'j_) (list tgt 'j_))))
            (lambda ()
              (let ((j (cadr (pc-di-landed-1!)))) (wt! j) (pc-beta!) (rfl))))
          (fact 'converges-to-transfer 'RR-MS tgt m 0)
          (ass))))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'SERIES-CONVERGES-TO (list c4-u 'j_) (list c4-e 'j_))))
  (lambda ()
    (let ((j (cadr (pc-di-landed-1!))))
      (pc-beta!)
      (fact 'fun-apply-type-c c4-seq 'NN (list 'PRODUCT-CARRIER c4-ms) j)
      (fact 'product-metric-dist-converges c4-ms c4-w (list c4-seq j) c4-lv)
      (ass))))
(fact 'dominated-null-series c4-w c4-e c4-u)
(fact 'converges-dist-null-bwd c4-p c4-seq c4-lv)
(ass)
(qed 'product-convergence-coordinatewise-bwd)

;;; =====================================================================
;;; L6.  convergence in the product gives coordinatewise convergence -- the
;;; sharp termwise bound (series-term-le-sum) plus the squeeze L1.
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
       (FORALL lv (IMPLIES (IN lv (PRODUCT-CARRIER ms))
         (IMPLIES (CONVERGES-TO (PRODUCT-METRIC-W ms w) seq lv)
           (FORALL n_ (IMPLIES (IN n_ NN)
             (CONVERGES-TO (ms n_) (VNB-LAMBDA k NN ((seq k) n_)) (lv n_)))))))))))))))
(pc-peel-to! 'CONVERGES-TO)
(define d4-msn  (cadr (dk-goal)))
(define d4-ms   (car d4-msn))
(define d4-n    (cadr d4-msn))
(define d4-cs   (caddr (dk-goal)))
(define d4-lvn  (cadddr (dk-goal)))
(define d4-lv   (car d4-lvn))
(define d4-hyp  (pc-find 'prodconv
                  (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                   (pair? (cadr a))
                                   (eq? (car (cadr a)) 'PRODUCT-METRIC-W)))))
(define d4-p    (cadr d4-hyp))
(define d4-w    (caddr d4-p))
(define d4-seq  (caddr d4-hyp))
(define d4-e    (list 'VNB-LAMBDA 'j_ 'NN
                      (list (list 'DIST d4-p) (list d4-seq 'j_) d4-lv)))
(define d4-wrho (list 'VNB-LAMBDA 'j_ 'NN
                  (list '* (list d4-w d4-n)
                        (list (list 'DIST (list 'BDD-METRIC d4-msn))
                              (list (list d4-seq 'j_) d4-n) d4-lvn))))

(pc-setup! d4-w d4-ms)
(fact 'product-is-metric-space d4-ms d4-w)
(have! (list 'IN d4-seq (list 'FUN 'NN (list 'PTS d4-p)))
       (lambda () (mac 'product-metric-carrier) (ass)))
(have! (list 'IN d4-lv (list 'PTS d4-p))
       (lambda () (mac 'product-metric-carrier) (ass)))
(fact 'converges-dist-null-fwd d4-p d4-seq d4-lv)
(inst+ pc-msu d4-n)
(fact 'product-carrier-coord d4-ms d4-lv d4-n)
(fact 'fun-apply-type-c d4-w 'NN 'RR d4-n)
(inst+ pc-wpos d4-n)
(pc-from-lt! 0 (list d4-w d4-n))
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)

;;; everything the index j owes: seq(j) is a point of the product, its n-th
;;; weighted coordinate distance is real and nonnegative, and the series of
;;; those converges to the product distance.
(define (d4-at! j)
  (fact 'fun-apply-type-c d4-seq 'NN (list 'PRODUCT-CARRIER d4-ms) j)
  (fact 'fun-apply-type-c d4-seq 'NN (list 'PTS d4-p) j)
  (fact 'product-carrier-coord d4-ms (list d4-seq j) d4-n)
  (fact 'metric-dist-real d4-p (list d4-seq j) d4-lv)
  (dk-split! (dk-deepest
    (lambda () (fact 'bdd-metric-weight-bound d4-msn
                     (list (list d4-seq j) d4-n) d4-lvn (list d4-w d4-n))))))

(have! (list 'IN d4-e '(FUN NN RR))
  (lambda () (dk-lam-t!)
          (let ((j (cadr (pc-di-landed-1!)))) (d4-at! j) (ass))))
(have! (list 'IN d4-wrho '(FUN NN RR))
  (lambda () (dk-lam-t!)
          (let ((j (cadr (pc-di-landed-1!)))) (d4-at! j) (ass))))

;;; the termwise bound: a term of the defining series is at most its sum
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'AND (list '<= 0 (list d4-wrho 'j_))
                    (list '<= (list d4-wrho 'j_) (list d4-e 'j_)))))
  (lambda ()
    (let* ((j (cadr (pc-di-landed-1!))))
      (d4-at! j)
      (fact 'product-term-seq-in-fun d4-ms d4-w (list d4-seq j) d4-lv)
      (let* ((land (dk-deepest
                    (lambda () (fact 'product-metric-dist-converges
                                     d4-ms d4-w (list d4-seq j) d4-lv))))
             (trm (cadr land))                     ; the term sequence lambda
             (sum (caddr land)))                   ; (DIST P)(seq(j), lv)
        (have! (list 'FORALL 'i_ (list 'IMPLIES '(IN i_ NN)
                  (list '<= 0 (list trm 'i_))))
          (lambda ()
            (let ((i (cadr (pc-di-landed-1!))))
              (pc-beta!)
              (inst+ pc-msu i)
              (fact 'product-carrier-coord d4-ms (list d4-seq j) i)
              (fact 'product-carrier-coord d4-ms d4-lv i)
              (fact 'fun-apply-type-c d4-w 'NN 'RR i)
              (inst+ pc-wpos i)
              (pc-from-lt! 0 (list d4-w i))
              (dk-split! (dk-deepest
                (lambda () (fact 'bdd-metric-weight-bound (list d4-ms i)
                                 (list (list d4-seq j) i) (list d4-lv i)
                                 (list d4-w i)))))
              (ass))))
        (fact 'series-term-le-sum trm sum d4-n)
        (pc-and!
         (lambda ()
           (pc-beta!)
           (if (equal? (cadr (dk-goal)) 0) (ass)
               (begin
                 (have! (list '= (cadr (dk-goal)) (list trm d4-n))
                        (lambda () (pc-beta!) (rfl)))
                 (subst (list '= (cadr (dk-goal)) (list trm d4-n)))
                 (ass)))))))))
(fact 'rr-null-squeeze d4-e d4-wrho)
(fact 'product-coord-from-weighted-null d4-ms d4-w d4-seq d4-lv d4-n)
(ass)
(qed 'product-convergence-coordinatewise-fwd)

;;; =====================================================================
;;; L7.  product-convergence-coordinatewise -- the IFF, assembled by `prop',
;;; which treats both sides as opaque atoms and discharges through the kernel
;;; rules, so the assembly costs no trust.  Statement VERBATIM from the support
;;; this file retires (structure-library/product-metric.scm).
;;; =====================================================================
(sp (make-wff '(FORALL ms (IMPLIES (IS-MS-SEQUENCE ms)
   (FORALL w (IMPLIES (SUMMABLE-WEIGHT w)
     (FORALL seq (IMPLIES (IN seq (FUN NN (PRODUCT-CARRIER ms)))
       (FORALL lv (IMPLIES (IN lv (PRODUCT-CARRIER ms))
         (IFF (CONVERGES-TO (PRODUCT-METRIC-W ms w) seq lv)
              (FORALL n_ (IMPLIES (IN n_ NN)
                (CONVERGES-TO (ms n_) (VNB-LAMBDA k NN ((seq k) n_)) (lv n_)))))))))))))))
(pc-peel-to! 'IFF)
(define e4-g   (dk-goal))
(define e4-lhs (cadr e4-g))
(define e4-rhs (caddr e4-g))
(define e4-p   (cadr e4-lhs))
(define e4-ms  (cadr e4-p))
(define e4-w   (caddr e4-p))
(define e4-seq (caddr e4-lhs))
(define e4-lv  (cadddr e4-lhs))
;; each citation in its OWN lane: `fact' lands its whole instantiation chain,
;; and `prop' counts the atoms of the WHOLE context.
(have! (list 'IMPLIES e4-lhs e4-rhs)
  (lambda () (fact 'product-convergence-coordinatewise-fwd e4-ms e4-w e4-seq e4-lv)
          (ass)))
(have! (list 'IMPLIES e4-rhs e4-lhs)
  (lambda () (fact 'product-convergence-coordinatewise-bwd e4-ms e4-w e4-seq e4-lv)
          (ass)))
(prop)
(qed 'product-convergence-coordinatewise)

;;; -----------------------------------------------------------------------
(topic! 'rr-null-squeeze 'analysis)
(alias! 'rr-null-squeeze "a nonnegative sequence below a null one is null")
(topic! 'converges-to-transfer 'analysis)
(alias! 'converges-to-transfer
        "pointwise-equal sequences converge to the same limit")
(topic! 'product-coord-weighted-null 'constructions)
(alias! 'product-coord-weighted-null
        "coordinate convergence makes the weighted coordinate distance null")
(topic! 'product-coord-from-weighted-null 'constructions)
(alias! 'product-coord-from-weighted-null
        "a null weighted coordinate distance is coordinate convergence")
(topic! 'product-convergence-coordinatewise-fwd 'constructions)
(alias! 'product-convergence-coordinatewise-fwd
        "convergence in the product is convergence in every coordinate")
(topic! 'product-convergence-coordinatewise-bwd 'constructions)
(alias! 'product-convergence-coordinatewise-bwd
        "coordinatewise convergence is convergence in the product")
(topic! 'product-convergence-coordinatewise 'constructions)
(alias! 'product-convergence-coordinatewise
        "the product topology"
        "a sequence converges in the product metric exactly when it converges in every coordinate")
