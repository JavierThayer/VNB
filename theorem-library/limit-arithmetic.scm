;;; limit-arithmetic.scm -- THE TWO LIMIT LAWS THE SERIES AND PRODUCT LANES
;;; WERE MISSING: `<=' carried across TWO limits, and the limit of a pointwise
;;; sum.  Plus the series readings of the second.
;;;
;;;   rr-limit-le                f(n) <= g(n) for every n, f -> L, g -> M
;;;                              =>  L <= M
;;;   rr-limit-add               f -> L, g -> M, h(n) = f(n) + g(n) pointwise
;;;                              =>  h -> L + M
;;;   series-converges-to-converges   a series with a sum converges
;;;   series-converges-to-add    the same, at the partial-sum sequence
;;;   series-limit-add           SERIES-LIMIT(h) = SERIES-LIMIT(f) + SERIES-LIMIT(g)
;;;
;;; WHY THE TREE DID NOT HAVE THEM.  The two nearest facts each carry a
;;; CONSTANT on one side.  `rr-limit-abs-le' (dominated-convergence.scm) bounds
;;; a limit by a uniform bound on the terms; `rr-mono-le-limit' (mono-le-limit.scm,
;;; directly above) bounds a TERM by its own limit.  Neither compares two
;;; sequences that both move.  Likewise `rr-null-sum' adds two sequences that
;;; both converge to ZERO -- which is where the argument is easy, because the
;;; two estimates are already about the same point -- and dominated-convergence's
;;; own header records the gap in as many words: "The signed case wants
;;; lim(f+g) = lim f + lim g and is NOT here."
;;;
;;; NEITHER NEEDED A NEW MECHANISM, and that is the finding.  Both are the
;;; eps/2 pattern the two files above already run, with the SAME three moving
;;; parts: `rr-pos-halvable' splits eps, the binary MAX (`nn-max-closed',
;;; `rr-le-max-left/-right') merges the two thresholds, and one `ineq' call
;;; chains the resulting linear facts.
;;;
;;;   rr-limit-le    L - M = (L - f(n)) + (f(n) - g(n)) + (g(n) - M).  The
;;;                  middle term is <= 0 by hypothesis and the outer two are
;;;                  each <= eps/2 beyond max(N_f, N_g), so L - M <= eps for
;;;                  every eps > 0 and `rr-le-all-pos-nonpos' collapses it.
;;;                  NO CASE SPLIT and no negation -- the same reason
;;;                  mono-le-limit.scm gives for not arguing by contradiction:
;;;                  CONVERGES-TO is stated with a NON-strict `dist <= eps',
;;;                  so a contradiction route has to halve eps anyway AND
;;;                  manufacture `M < L' from `not (L <= M)'.
;;;   rr-limit-add   `rr-null-sum' verbatim with L and M in place of the two
;;;                  zeros; the one extra step is bringing
;;;                  (f(n) + g(n)) - (L + M) and (f(n) - L) + (g(n) - M) to a
;;;                  common shape with `crs' before the triangle inequality,
;;;                  because `ineq' reads abs(x) as an opaque ATOM and the two
;;;                  spellings are unrelated to it until the ARGUMENTS agree.
;;;
;;; STATED WITH THE LIMITS TYPED IN FRONT.  `forall([f in fun(nn,rr), ...,
;;; lv in rr, mv in rr], ...)' rather than reading (IN lv RR) off CONVERGES-TO
;;; by `slot-h' at each use -- rr-limit-abs-le's shape, and it makes a citation
;;; one `fact' with all arguments named.  Every caller has the typing: it is
;;; one `slot-h' from CONVERGES-TO, or `series-limit-in-rr'.
;;;
;;; THE SUM LEMMAS ARE IN TRANSFER FORM -- the conclusion is about any `h'
;;; agreeing pointwise with f + g, not about the literal
;;; (VNB-LAMBDA j_ NN (+ (f j_) (g j_)).  dominated-convergence.scm's design
;;; note 3 is the argument, and it applies here twice over: `series-limit-add'
;;; cites `rr-limit-add' at the three PARTIAL-SUM sequences, which are lambdas,
;;; and in literal form that citation would need a beta under a binder.
;;;
;;; WHAT IS DELIBERATELY NOT HERE: a congruence law for SERIES-LIMIT.
;;; "f(n) = g(n) for every n in NN implies SERIES-LIMIT(f) = SERIES-LIMIT(g)"
;;; needs NO lemma.  `fun-domain-extensionality' (library.scm, PRIMITIVE) gives
;;; f = g from the pointwise agreement once both are typed into FUN(NN) -- one
;;; `mac-h' of `fun-codomain-iff' per side -- and the conclusion is then one
;;; `subst' plus `qrfl'.  Measured: five lines, `modulo 0'.  (In the `=' rather
;;; than `==' form the goal is (= t t), which is DEFINEDNESS, so it wants
;;; `series-limit-in-rr' -- i.e. convergence -- in the context before `rfl'.)
;;; The standing rule of 2026-05-27 is that per-operator congruence /
;;; replacement lemmas are rejected as PSS entries precisely because they are
;;; consequences of that axiom; chain through it at the point of use.
;;; `finsum-congruence' was dropped for this reason and `poly-zero.scm' is the
;;; worked example of the citation.
;;;
;;; WHAT IT COSTS.  rr-limit-add, series-converges-to-converges and
;;; series-converges-to-add are `modulo 0'.  rr-limit-le bills
;;; `{rr-le-all-pos-nonpos}' [well-known] -- the archimedean-flavoured support
;;; of order-predicates.scm, the SAME single leaf rr-mono-le-limit pays and for
;;; the same step.  series-limit-add bills it too, inherited through
;;; `series-limit-in-rr' / `rr-limit-unique'.
;;;
;;; Loads after theorem-library/mono-le-limit (its neighbour and the file whose
;;; driver this one follows), dominated-convergence (rr-limit-unique,
;;; series-limit-converges-to, series-limit-in-rr, series-partial-sum-add),
;;; comparison-test-proof (series-partial-sum-seq-apply / -seq-in-fun),
;;; rr-halving (rr-pos-halvable), rr-max-basics, rr-min-basics (nn-max-closed),
;;; rr-abs-basics (rr-abs-bound, rr-abs-closed, rr-abs-triangle-c),
;;; binary-minus-laws (rr-sub-in-rr), nn-order-basics (nn-in-rr),
;;; order-predicates (rr-le-all-pos-nonpos), rr-ms-dist, fun-apply-type-proof
;;; and driver-kit.

;;; ---- file-local driver helpers (the `lmt-' prefix) ------------------
;;;
;;; NOT `la-': structure-library/linear-arith.scm defines `la-find' (:85) and
;;; `la-uniq' (:33), and `ineq' calls both.  A file-local `(define (la-find
;;; what pred) ...)' rebinds it, and the failure is a long way from the cause:
;;; the oracle finds its Farkas certificate, then `fm-prove' calls
;;; (la-find con-contradictory? cs) with the arguments in the OTHER order and
;;; dies with "The object ((con () 0 lt ...) ...) is not applicable" -- inside a
;;; `have!' lane, so what is reported is "THUNK left the side goal open".
;;; `clobber-guard' does NOT catch this: it fires when a procedure binding is
;;; replaced by a NON-procedure, and here a procedure replaced a procedure.

;;; Select a hypothesis by CONTENT and ERROR on a miss.
(define (lmt-find what pred)
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "lmt-find: no context formula" what))
          ((pred (car l)) (car l))
          (else (loop (cdr l))))))

;;; `ineq' wants 1-based assumption indices, named ONE BY ONE.
(define (lmt-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "lmt-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (lmt-ineq . forms) (apply ineq (map lmt-idx forms)))

(define (lmt-fvs forms) (apply append (map free-vars forms)))

;;; Skolemize a FORSOME already in the CONTEXT -- `obtain' recognises only an
;;; existential its own lane landed.  A miss ERRORS.
(define (lmt-skolem! ex)
  (let* ((fv0 (lmt-fvs (dk-asms)))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (let ((fresh (filter (lambda (v) (not (memq v fv0))) (lmt-fvs (dk-asms)))))
      (if (null? fresh) (error "lmt-skolem!: no eigenvariable appeared for" ex)
          (car fresh)))))

;;; `di' until an ASSUMPTION lands -- never a `di' count.
(define (lmt-di-landed!)
  (let loop ((n 0))
    (let ((new (dk-landed* (lambda () (di)))))
      (cond ((pair? new) new)
            ((> n 4) (error "lmt-di-landed!: di landed no assumption"))
            (else (loop (+ n 1)))))))
(define (lmt-di-landed-1!)
  (let ((new (lmt-di-landed!)))
    (if (null? (cdr new)) (car new)
        (error "lmt-di-landed-1!: expected 1 landing"
               (map expression->string new)))))

;;; Peel the whole leading FORALL/IMPLIES prefix.  `di' is greedy over a
;;; GUARDED binder list -- one call lands every typing of `forall([f in ...,
;;; g in ...], ...)' at once -- so the landings are read back by CONTENT
;;; below, never counted.
(define (lmt-peel!)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 14))
          (begin (di) (loop (+ n 1)))
          #t))))

;;; di-split an AND goal to its leaves and run CLOSER on each.
(define (lmt-and! closer)
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'AND))
        (for-each (lambda (k) (dk-focus! k) (lmt-and! closer))
                  (dk-opened (lambda () (di))))
        (closer))))

;;; (IN x RR) off a POS-RR, on a SIDE branch: `mac-h' REPLACES the hypothesis
;;; and the eps universal above still wants it.
(define (lmt-pos-in-rr! x)
  (have! (list 'IN x 'RR)
    (lambda ()
      (mac-h 'pos-rr (list 'POS-RR x))
      (dk-split! (list 'AND (list 'IN x 'RR)
                       (list 'AND (list '<= 0 x) (list 'NOT (list '= 0 x)))))
      (ass))))

;;; The inner (FORALL n_ ... (<= thr n_) => ...) of a skolemized eps-N clause,
;;; discriminated on its THRESHOLD and captured while the context is clean:
;;; once `rr-le-max-left' has been cited, its own partly-peeled chain is a
;;; FORALL mentioning the same threshold and a shape test picks that instead.
(define (lmt-inner thr)
  (lmt-find thr (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                                (let ((b (caddr a)))
                                  (and (pair? b) (eq? (car b) 'IMPLIES)
                                       (dk-contains? (caddr b) thr)))))))

;;; The eps-N clause of an unfolded CONVERGES-TO, named by the SEQUENCE it is
;;; about.  Both clauses in a two-limit proof have the same shape, so the
;;; discriminator is the function symbol, never the shape alone.
(define (lmt-tail-of s)
  (lmt-find s (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a s)
                              (dk-contains? a 'POS-RR)))))

;;; =====================================================================
;;; L1.  rr-limit-le -- `<=' passes to the limits.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), lv in rr, mv in rr],
     forall([n_ in nn], f(n_) <= g(n_)) implies
     converges-to(rr-ms, f, lv) implies converges-to(rr-ms, g, mv) implies
     lv <= mv)"))
(lmt-peel!)
(define ll-cf (lmt-find 'conv-f (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                                (eq? (caddr a) 'f)))))
(define ll-cg (lmt-find 'conv-g (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                                (eq? (caddr a) 'g)))))
(define ll-pt (lmt-find 'pointwise
  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                   (dk-contains? a 'f) (dk-contains? a 'g)))))

(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to ll-cf))
                           (lambda (a) (eq? (car a) 'AND))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to ll-cg))
                           (lambda (a) (eq? (car a) 'AND))))
(define ll-tf (lmt-tail-of 'f))
(define ll-tg (lmt-tail-of 'g))
(define ll-diff '(- lv mv))

;;; for every eps > 0:  L - M <= eps,  witnessed at n = max(N_f, N_g).
(have! (list 'FORALL 'eps (list 'IMPLIES '(POS-RR eps) (list '<= ll-diff 'eps)))
  (lambda ()
    (let* ((eps (cadr (lmt-di-landed-1!)))
           (hex (dk-fact! 'rr-pos-halvable eps))
           (d   (lmt-skolem! hex))
           (exf (dk-deepest (lambda () (inst+ ll-tf d))))
           (nf  (lmt-skolem! exf))
           (inf (lmt-inner nf))                    ; captured BEFORE the max facts
           (exg (dk-deepest (lambda () (inst+ ll-tg d))))
           (ng  (lmt-skolem! exg))
           (ing (lmt-inner ng))
           (bnd (list 'MAX nf ng)))
      (fact 'nn-max-closed nf ng)
      (fact 'nn-in-rr nf) (fact 'nn-in-rr ng) (fact 'nn-in-rr bnd)
      (fact 'rr-le-max-left nf ng)
      (fact 'rr-le-max-right nf ng)
      (inst+ inf bnd)
      (inst+ ing bnd)
      (inst+ ll-pt bnd)
      (fact 'fun-apply-type-c 'f 'NN 'RR bnd)
      (fact 'fun-apply-type-c 'g 'NN 'RR bnd)
      ;; rr-abs-bound is GUARDED on the bound being real: type eps and d FIRST,
      ;; or the rewrite posts the typing as a spawned leaf nobody closes.
      (lmt-pos-in-rr! eps)
      (lmt-pos-in-rr! d)
      (fact 'rr-sub-in-rr (list 'f bnd) 'lv)
      (fact 'rr-sub-in-rr (list 'g bnd) 'mv)
      (fact 'rr-abs-closed (list '- (list 'f bnd) 'lv))
      (fact 'rr-abs-closed (list '- (list 'g bnd) 'mv))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'f bnd) 'lv) d))
      (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'g bnd) 'mv) d))
      (dk-split! (dk-landed-1
        (lambda () (mac-h 'rr-abs-bound
          (list '<= (list 'abs (list '- (list 'f bnd) 'lv)) d)))))
      (dk-split! (dk-landed-1
        (lambda () (mac-h 'rr-abs-bound
          (list '<= (list 'abs (list '- (list 'g bnd) 'mv)) d)))))
      ;; L - M = (L - f(n)) + (f(n) - g(n)) + (g(n) - M), all linear.
      (lmt-ineq (list '<= (list '- d) (list '- (list 'f bnd) 'lv))
               (list '<= (list 'f bnd) (list 'g bnd))
               (list '<= (list '- (list 'g bnd) 'mv) d)
               (list '= (list '+ d d) eps)))))

(fact 'rr-sub-in-rr 'lv 'mv)
(fact 'rr-le-all-pos-nonpos ll-diff)
(lmt-ineq (list '<= ll-diff 0))
(qed 'rr-limit-le)
(topic! 'rr-limit-le 'analysis)
(alias! 'rr-limit-le
        "a termwise inequality passes to the limits"
        "if f(n) <= g(n) for all n then lim f <= lim g")

;;; =====================================================================
;;; L2.  rr-limit-add -- the limit of a pointwise sum, in TRANSFER form.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr),
                       lv in rr, mv in rr],
     forall([j_ in nn], h(j_) = f(j_) + g(j_)) implies
     converges-to(rr-ms, f, lv) implies converges-to(rr-ms, g, mv) implies
     converges-to(rr-ms, h, lv + mv))"))
(lmt-peel!)
(define ad-cf (lmt-find 'conv-f (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                                (eq? (caddr a) 'f)))))
(define ad-cg (lmt-find 'conv-g (lambda (a) (and (pair? a) (eq? (car a) 'CONVERGES-TO)
                                                (eq? (caddr a) 'g)))))
(define ad-pt (lmt-find 'pointwise
  (lambda (a) (and (pair? a) (eq? (car a) 'FORALL) (dk-contains? a 'h)))))

(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to ad-cf))
                           (lambda (a) (eq? (car a) 'AND))))
(dk-split! (dk-landed-find (lambda () (mac-h 'converges-to ad-cg))
                           (lambda (a) (eq? (car a) 'AND))))
(define ad-tf (lmt-tail-of 'f))
(define ad-tg (lmt-tail-of 'g))
(have! '(AND (IN lv RR) (IN mv RR)))
(fact 'rr-add-closed 'lv 'mv)

(define (ad-eps-branch!)
  (let* ((eps (cadr (lmt-di-landed-1!)))
         (hex (dk-fact! 'rr-pos-halvable eps))
         (d   (lmt-skolem! hex))
         (exf (dk-deepest (lambda () (inst+ ad-tf d))))
         (nf  (lmt-skolem! exf))
         (inf (lmt-inner nf))
         (exg (dk-deepest (lambda () (inst+ ad-tg d))))
         (ng  (lmt-skolem! exg))
         (ing (lmt-inner ng))
         (bnd (list 'MAX nf ng)))
    (fact 'nn-max-closed nf ng)
    (ew bnd)
    (lmt-and!
     (lambda ()
       (if (eq? (car (dk-goal)) 'IN) (ass)
           (let* ((memb (lmt-di-landed-1!))
                  (n_   (cadr memb)))
             (lmt-di-landed!)                      ; the (<= max n_) hypothesis
             (fact 'nn-in-rr nf) (fact 'nn-in-rr ng)
             (fact 'nn-in-rr bnd) (fact 'nn-in-rr n_)
             (fact 'rr-le-max-left nf ng)
             (fact 'rr-le-max-right nf ng)
             (have! (list '<= nf n_)
               (lambda () (lmt-ineq (list '<= nf bnd) (list '<= bnd n_))))
             (have! (list '<= ng n_)
               (lambda () (lmt-ineq (list '<= ng bnd) (list '<= bnd n_))))
             (inst+ inf n_) (inst+ ing n_) (inst+ ad-pt n_)
             (fact 'fun-apply-type-c 'f 'NN 'RR n_)
             (fact 'fun-apply-type-c 'g 'NN 'RR n_)
             (fact 'fun-apply-type-c 'h 'NN 'RR n_)
             (subst (list '= (list 'h n_) (list '+ (list 'f n_) (list 'g n_))))
             (have! (list 'AND (list 'IN (list 'f n_) 'RR) (list 'IN (list 'g n_) 'RR)))
             (fact 'rr-add-closed (list 'f n_) (list 'g n_))
             ;; rr-ms-dist is GUARDED: every argument typed BEFORE the rewrite.
             (mac 'rr-ms-dist)
             (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'f n_) 'lv) d))
             (mac-h 'rr-ms-dist (list '<= (list '(DIST RR-MS) (list 'g n_) 'mv) d))
             ;; `ineq' reads abs(x) as an ATOM, so abs((f+g)-(L+M)) and
             ;; abs(f-L) + abs(g-M) are unrelated until the ARGUMENTS agree.
             (let ((uf (list '- (list 'f n_) 'lv))
                   (ug (list '- (list 'g n_) 'mv))
                   (lhs (list '- (list '+ (list 'f n_) (list 'g n_)) '(+ lv mv))))
               (have! (list '= lhs (list '+ uf ug)) (lambda () (crs)))
               (subst (list '= lhs (list '+ uf ug)))
               (fact 'rr-sub-in-rr (list 'f n_) 'lv)
               (fact 'rr-sub-in-rr (list 'g n_) 'mv)
               (fact 'rr-abs-closed uf) (fact 'rr-abs-closed ug)
               (fact 'rr-abs-closed (list '+ uf ug))
               (fact 'rr-abs-triangle-c uf ug)
               (lmt-pos-in-rr! eps)
               (lmt-pos-in-rr! d)
               (lmt-ineq (list '<= (list 'abs (list '+ uf ug))
                                  (list '+ (list 'abs uf) (list 'abs ug)))
                        (list '<= (list 'abs uf) d)
                        (list '<= (list 'abs ug) d)
                        (list '= (list '+ d d) eps)))))))))

(mac 'converges-to)
(lmt-and!
 (lambda ()
   (let ((gl (dk-goal)))
     (cond ((eq? (car gl) 'IS-METRIC-SPACE) (ass))
           ((eq? (car gl) 'IN) (slot 'PTS) (ass))
           (else (ad-eps-branch!))))))
(qed 'rr-limit-add)
(topic! 'rr-limit-add 'analysis)
(alias! 'rr-limit-add
        "the limit of a pointwise sum is the sum of the limits")

;;; =====================================================================
;;; L3.  series-converges-to-converges -- a series with a sum converges.
;;; The existential intro nothing in the tree had written down, and what
;;; L5 needs to apply `series-limit-converges-to' to the SUM sequence.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), lv in rr],
     series-converges-to(f, lv) implies series-converges(f))"))
(lmt-peel!)
(mac-h 'series-converges-to '(SERIES-CONVERGES-TO f lv))
(mac 'series-converges)
(mac 'converges)
(ew 'lv)
(ass)
(qed 'series-converges-to-converges)
(topic! 'series-converges-to-converges 'analysis)
(alias! 'series-converges-to-converges "a series with a sum converges")

;;; =====================================================================
;;; L4.  series-converges-to-add -- L2 read at the PARTIAL-SUM sequences.
;;; `series-partial-sum-add' (dominated-convergence.scm) says the partial sums
;;; add; L2 says their limits do.
;;; =====================================================================

(define (lmt-psq s) (list 'VNB-LAMBDA 'k 'NN (list 'SERIES-PARTIAL-SUM s 'k)))

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr),
                       lv in rr, mv in rr],
     forall([i_ in nn], h(i_) = f(i_) + g(i_)) implies
     series-converges-to(f, lv) implies series-converges-to(g, mv) implies
     series-converges-to(h, lv + mv))"))
(lmt-peel!)
(mac-h 'series-converges-to '(SERIES-CONVERGES-TO f lv))
(mac-h 'series-converges-to '(SERIES-CONVERGES-TO g mv))
(fact 'series-partial-sum-seq-in-fun 'f)
(fact 'series-partial-sum-seq-in-fun 'g)
(fact 'series-partial-sum-seq-in-fun 'h)
;; the pointwise hypothesis L2 wants, in the LAMBDA language: one `mac' of the
;; beta rule turns all three applied lambdas into SERIES-PARTIAL-SUM.
(have! (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
         (list '= (list (lmt-psq 'h) 'k_)
                  (list '+ (list (lmt-psq 'f) 'k_) (list (lmt-psq 'g) 'k_)))))
  (lambda ()
    (let ((k (cadr (lmt-di-landed-1!))))
      (mac 'series-partial-sum-seq-apply)
      (fact 'series-partial-sum-add k 'f 'g 'h)
      (ass))))
(fact 'rr-limit-add (lmt-psq 'f) (lmt-psq 'g) (lmt-psq 'h) 'lv 'mv)
(mac 'series-converges-to)
(ass)
(qed 'series-converges-to-add)
(topic! 'series-converges-to-add 'analysis)
(alias! 'series-converges-to-add "the sum of a termwise sum of series")

;;; =====================================================================
;;; L5.  series-limit-add -- the same in SERIES-LIMIT form.  L4 gives h a sum;
;;; `series-limit-converges-to' gives it the sum SERIES-LIMIT(h); uniqueness
;;; (`rr-limit-unique') identifies them.
;;; =====================================================================

(sp (make-wff "forall([f in fun(nn,rr), g in fun(nn,rr), h in fun(nn,rr)],
     forall([i_ in nn], h(i_) = f(i_) + g(i_)) implies
     series-converges(f) implies series-converges(g) implies
     series-limit(h) = series-limit(f) + series-limit(g))"))
(lmt-peel!)
(fact 'series-limit-converges-to 'f)
(fact 'series-limit-converges-to 'g)
(fact 'series-limit-in-rr 'f)
(fact 'series-limit-in-rr 'g)
(define lm-sum '(+ (SERIES-LIMIT f) (SERIES-LIMIT g)))
(have! '(AND (IN (SERIES-LIMIT f) RR) (IN (SERIES-LIMIT g) RR)))
(fact 'rr-add-closed '(SERIES-LIMIT f) '(SERIES-LIMIT g))
(fact 'series-converges-to-add 'f 'g 'h '(SERIES-LIMIT f) '(SERIES-LIMIT g))
(fact 'series-converges-to-converges 'h lm-sum)
(fact 'series-limit-converges-to 'h)
(fact 'series-limit-in-rr 'h)
;; both readings of "h has that sum", unfolded on SIDE branches -- `mac-h' is
;; destructive and each SERIES-CONVERGES-TO is still wanted as itself.
(have! (list 'CONVERGES-TO 'RR-MS (lmt-psq 'h) '(SERIES-LIMIT h))
  (lambda () (mac-h 'series-converges-to '(SERIES-CONVERGES-TO h (SERIES-LIMIT h)))
             (ass)))
(have! (list 'CONVERGES-TO 'RR-MS (lmt-psq 'h) lm-sum)
  (lambda () (mac-h 'series-converges-to (list 'SERIES-CONVERGES-TO 'h lm-sum))
             (ass)))
(fact 'series-partial-sum-seq-in-fun 'h)
(fact 'rr-limit-unique (lmt-psq 'h) '(SERIES-LIMIT h) lm-sum)
(ass)
(qed 'series-limit-add)
(topic! 'series-limit-add 'analysis)
(alias! 'series-limit-add
        "the sum of a termwise sum of series is the sum of the sums")
