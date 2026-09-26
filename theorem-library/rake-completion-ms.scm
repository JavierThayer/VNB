;;; rake-completion-ms.scm -- BATCH 5c-Q of the 2026-09-18 rake:
;;; completion-is-metric-space (structure-library/metric-completion.scm:107,
;;; asserted `well-known').  PROVEN `modulo 0'.  The statement is the support's,
;;; copied from the support site and unchanged:
;;;
;;;     forall M.  IS-METRIC-SPACE(M)  =>  IS-METRIC-SPACE(COMPLETION(M))
;;;
;;; COMPLETION(M) = [ QUOTIENT(CAUCHY-SETOID M), COMPLETION-DIST(M) ] -- the
;;; Cauchy sequences of M modulo null distance, with the metric that sends a
;;; pair of classes to the IOTA "the real that the distance sequence of SOME
;;; pair of representatives converges to".
;;;
;;; =====================================================================
;;; THE ONE MISSING BRICK, and it was the one batch O named.
;;;
;;; rake-setoid2.scm's header ("THE TWO LEFT") says this leaf is not a grind
;;; away: it needs d-hat to DENOTE at an arbitrary pair of classes, i.e.
;;; "DIST-SEQ(M,f,g) is a CAUCHY real sequence for any two Cauchy f, g",
;;; followed by the completeness of RR.  That is `r7q-dist-seq-cauchy' below,
;;; and it is exactly `rko2-quad' -- the quadrilateral inequality batch O
;;; proved -- read at the two Cauchy thresholds:
;;;
;;;     | d(f_m,g_m) - d(f_n,g_n) |  <=  d(f_m,f_n) + d(g_m,g_n)  <=  e/2 + e/2
;;;
;;; with the threshold max(N_f, N_g).  Everything else in this file is that
;;; brick plus the limit laws the tree already has.
;;;
;;; THE STAGES, each its own theorem, each probed to `modulo 0' before the next:
;;;
;;;   r7q-cseq-cauchy          a member of CSEQ(M) is a Cauchy sequence
;;;   r7q-dist-seq-cauchy      THE BRICK: DIST-SEQ(M,f,g) is Cauchy in RR-MS
;;;   r7q-dist-seq-converges   ... hence CONVERGES (rr-complete)
;;;   r7q-dist-seq-sym         DIST-SEQ(M,g,f) has the same limit -- at ANY
;;;                            limit, where `rko2-null-sym' has only limit 0
;;;   r7q-null-transfer        a sequence at null distance from a convergent
;;;                            one converges to the same limit, in ANY metric
;;;                            space (d(h_j,L) <= d(h_j,f_j) + d(f_j,L))
;;;   r7q-quad-null            moving both endpoints by null distances moves
;;;                            the distance sequence by a null distance
;;;   r7q-limit-indep          REPRESENTATIVE-INDEPENDENCE of the limit
;;;   r7q-iota-dhat / r7q-dhat-iota   d-hat(x,y) IS the description (both
;;;                            orientations: `subst' rewrites left to right)
;;;   r7q-dist-value           d-hat([f],[g]) = L whenever DIST-SEQ(M,f,g) -> L
;;;                            -- the workhorse, `iota-d' with both obligations
;;;                            discharged by r7q-limit-indep + metric-limit-unique
;;;   r7q-rr-pts               (== RR (PTS RR-MS))
;;;   r7q-dhat-in-rr           d-hat is real-valued
;;;   r7q-dhat-self-zero / -nonneg / -zero-eq / -sym / -triangle
;;;                            the five metric laws, in the limit
;;;   completion-is-metric-space   THE LEAF
;;;
;;; The four metric laws pass to the limit through the laws the tree has and
;;; needed no eps/delta of their own: NONNEGATIVITY is `rr-limit-le' against
;;; the constant zero sequence (EMBED-SEQ RR-MS 0); the TRIANGLE inequality is
;;; `rr-limit-add' on the two summand sequences then `rr-limit-le'; SYMMETRY is
;;; `converges-to-transfer' through `metric-sym' (r7q-dist-seq-sym); and
;;; SEPARATION OF POINTS is `class-eq-iff' at the Cauchy setoid -- d-hat = 0
;;; says the distance sequence is null, which IS the relation CREL.
;;;
;;; =====================================================================
;;; MECHANICS WORTH KEEPING.
;;;
;;; * `dk-lam-t!' DIFFS `proof-leaves' GLOBALLY, so it is wrong when sibling
;;;   conjuncts of the same goal are still open: driving the FUN-typing
;;;   conjunct of IS-METRIC-SPACE with it closed the LENGTH conjunct's node by
;;;   `ass' instead of the lambda's sethood leaf, and left a DUPLICATE open
;;;   node carrying the LENGTH goal -- the original was grounded, the twin was
;;;   not, and `qed' reported an open leaf whose goal the driver had just
;;;   closed.  `dk-opened' returns exactly what the tactic opened; use it
;;;   whenever more than one leaf is in play (r7q-dist-typing! below).
;;; * `cartesian-decompose' is a PROCEDURAL macete with no theorem-table entry,
;;;   so `mac-h' cannot name it (`unknown theorem/macete').  Fire it with `mac'
;;;   on the GOAL while the membership is still the ANTECEDENT -- it descends
;;;   through connectives and binders (finsum-fiber.scm's note) -- then peel and
;;;   skolemize the two components.
;;; * `arith' errors (safe-car of ()) on the ground goal `2 = 2' that
;;;   `(mac 'COMPLETION) (len-r)' leaves; `rfl' closes it.  bdd-metric-basics.scm
;;;   ends the same conjunct with `arith', so that call is on borrowed time.
;;; * `ineq' certifies an atom only from a STANDALONE (IN t RR): the Cauchy
;;;   brick's final estimate needs `(fact 'rr-pos-rr-in-rr 'eps)' beside
;;;   `dk-halve!', which types the HALF and not eps itself.
;;; * A `have!' lane whose thunk BETA-REDUCES must land the typings of the
;;;   REDUCED terms: `rfl' certifies the term it is handed, and after
;;;   `r7q-beta!' the summand is d(f_j, lv), not the unreduced lambda
;;;   application whose typing the lane had cited.
;;;
;;; =====================================================================
;;; LOAD WINDOW  [ after theorem-library/rake-setoid2, end ).
;;;
;;;   lo -- the LATEST citation is theorem-library/rake-setoid2 (position 435 in
;;;     load.scm as of 2026-09-18): rko2-quad, rko2-dist-seq-at,
;;;     rko2-dist-seq-type, rko2-cseq-unfold, rko2-cseq-in-fun, rko2-null-refl,
;;;     rko2-const-seq-converges, rko2-class-eq-null, rko2-crel-intro,
;;;     rko2-cauchy-setoid-rel, rko2-completion-dist, cauchy-setoid-is-setoid,
;;;     class-eq-iff, class-in-quotient, quotient-rep.  Next latest, in order:
;;;     theorem-library/product-convergence (434: rr-null-squeeze,
;;;     converges-to-transfer), theorem-library/converges-dist-null (431:
;;;     converges-dist-null-fwd/-bwd, dist-seq-in-fun),
;;;     theorem-library/limit-arithmetic (415: rr-limit-le, rr-limit-add),
;;;     theorem-library/dominated-convergence (410: rr-null-sum),
;;;     theorem-library/metric-limit-unique (290), theorem-library/rr-complete-proof
;;;     (289: rr-complete), theorem-library/rr-metric-space-proof (287:
;;;     rr-is-metric-space), theorem-library/rake-analysis-typing (277:
;;;     rkt-completion-pts, rkt-cauchy-setoid-pts, rkt-class-is-set,
;;;     rkt-embed-seq-in-fun), structure-library/metric-laws (275: metric-pos,
;;;     metric-sym, metric-triangle, metric-zero-eq), theorem-library/op-typing
;;;     (200: metric-dist-real), theorem-library/rr-abs-basics (176:
;;;     rr-abs-closed, rr-abs-nonneg), theorem-library/pos-rr-bridges (175:
;;;     rr-pos-rr-in-rr, rr-lt-of-pos-rr, through dk-halve!),
;;;     theorem-library/rake-setoid (163: quotient-is-set),
;;;     theorem-library/pair-tuple-sethood (162: pair-in-cartesian),
;;;     theorem-library/fun-apply-type-proof (160: fun-apply-type-c),
;;;     theorem-library/binary-minus-laws (159: rr-sub-in-rr), driver-kit (138),
;;;     structure-library/metric-completeness (44: complete-cauchy-converges,
;;;     `definitional'), number-systems (34: rr-add-closed, rr-zero-in,
;;;     nn-zero-in, nn-max-closed, nn-in-rr, rr-le-max-left/-right) and the base
;;;     theory (cartesian-decompose, cartesian-set-iff, apply-tupling-2,
;;;     equality-symmetry).
;;;   hi -- END.  Nothing proven in the tree cites completion-is-metric-space;
;;;     outside its own definition site the name occurs only in `topic!' lines
;;;     (pss-topics.scm, reference-topics.scm) and in comments.
;;;
;;; SITE TO RETIRE: structure-library/metric-completion.scm:107
;;;   (the `support' form and its `warrant!' at :110).
;;;
;;; NOT DONE, and it is the next rung: completion-is-complete
;;; (metric-completion.scm:120).  It presupposes this leaf, and the diagonal
;;; argument wants a CHOICE of a representative term within 1/2^k of each class
;;; -- `cauchy-rapid-subsequence' (itself asserted, and batch S's report says it
;;; chains to the asserted `dc-on-nn-pred') is the shape it needs.  With
;;; r7q-dist-value and r7q-limit-indep in hand the ANALYTIC half is no longer
;;; the obstacle; the recursive choice is.
;;;
;;; Helper prefix `r7q-'.  All helpers are file-local.


(define (r7q-hyp h what) (dk-pick (dk-head? h) what))
(define (r7q-find pred what) (dk-pick pred what))
(define (r7q-in-head h)
  (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
                   (eq? (car (caddr f)) h))))
(define (r7q-goal-head? n h) (eq? (car (dk-goal-of n)) h))
(define (r7q-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "r7q-idx: not in context" (expression->string f)))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (r7q-ineq . forms) (apply ineq (map r7q-idx forms)))

;;; ---------------------------------------------------------------- S0
;;; a member of CSEQ(M) is a Cauchy sequence.
(sp (make-wff '(FORALL M (FORALL f_ (IMPLIES (IN f_ (CSEQ M))
   (IS-CAUCHY-SEQ M f_))))))
(dk-peel!)
(mac-h 'rko2-cseq-unfold (r7q-hyp 'IN "f_ in CSEQ"))
(sep-me (r7q-find (r7q-in-head 'SEP) "the CSEQ membership as a SEP"))
(dk-split-all!)
(ass)
(qed 'r7q-cseq-cauchy)
(topic! 'r7q-cseq-cauchy 'analysis)

;;; ---------------------------------------------------------------- S1
;;; DIST-SEQ(M,f,g) is a CAUCHY real sequence for Cauchy f, g.
(define (r7q-dseq f g) (list 'DIST-SEQ 'M f g))
(define (r7q-dm x y) (list '(DIST M) x y))

;; the eps-universal of the unfolded IS-CAUCHY-SEQ for the sequence SQ
(define (r7q-cauchy-tail! sq)
  (dk-split-all! (dk-landed* (lambda () (mac-h 'IS-CAUCHY-SEQ
                                               (list 'IS-CAUCHY-SEQ 'M sq)))))
  (r7q-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                             (dk-contains? a 'POS-RR)
                             (dk-contains? a sq)))
            "the eps-universal"))

;; the inner (FORALL m ... (FORALL n_ ... (AND thr m, thr n_) => ...)) clause
(define (r7q-inner thr sq)
  (r7q-find (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)
                             (dk-contains? a thr) (dk-contains? a sq)
                             (not (dk-contains? a 'POS-RR))))
            "the skolemized inner clause"))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
   (FORALL f_ (IMPLIES (IN f_ (CSEQ M))
     (FORALL g_ (IMPLIES (IN g_ (CSEQ M))
       (IS-CAUCHY-SEQ RR-MS (DIST-SEQ M f_ g_))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rko2-cseq-in-fun 'M 'f_)
(fact 'rko2-cseq-in-fun 'M 'g_)
(fact 'rko2-dist-seq-type 'M 'f_ 'g_)
(fact 'r7q-cseq-cauchy 'M 'f_)
(fact 'r7q-cseq-cauchy 'M 'g_)
(define r7q-tf (r7q-cauchy-tail! 'f_))
(define r7q-tg (r7q-cauchy-tail! 'g_))
(mac 'IS-CAUCHY-SEQ)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (cond
       ((eq? (car g) 'IS-METRIC-SPACE) (ass))
       ((eq? (car g) 'IN) (slot 'PTS) (ass))
       (#t
        (di) (di)                             ; eps, POS-RR(eps)
        (fact 'rr-pos-rr-in-rr 'eps)
        (let* ((d   (dk-halve! 'eps))
               (ef  (dk-deepest (lambda () (inst+ r7q-tf d))))
               (nf  (dk-skolem! ef))
               (inf (r7q-inner nf 'f_))
               (eg  (dk-deepest (lambda () (inst+ r7q-tg d))))
               (ng  (dk-skolem! eg))
               (ing (r7q-inner ng 'g_))
               (bnd (list 'MAX nf ng)))
          (fact 'nn-max-closed nf ng)
          (fact 'nn-in-rr nf) (fact 'nn-in-rr ng) (fact 'nn-in-rr bnd)
          (fact 'rr-le-max-left nf ng)
          (fact 'rr-le-max-right nf ng)
          (ew bnd)
          (dk-conj-close!
           (lambda ()
             (if (eq? (car (dk-goal)) 'IN) (ass)
                 (begin
                 (dk-peel!)
                 (let* ((pr (dk-pick (dk-head? 'AND) "the two threshold bounds"))
                        (m_ (caddr (cadr pr)))
                        (n_ (caddr (caddr pr))))
                   (dk-split! pr)
                   (fact 'nn-in-rr m_) (fact 'nn-in-rr n_)
                   (dk-have! (list '<= nf m_)
                     (lambda () (r7q-ineq (list '<= nf bnd) (list '<= bnd m_))))
                   (dk-have! (list '<= nf n_)
                     (lambda () (r7q-ineq (list '<= nf bnd) (list '<= bnd n_))))
                   (dk-have! (list '<= ng m_)
                     (lambda () (r7q-ineq (list '<= ng bnd) (list '<= bnd m_))))
                   (dk-have! (list '<= ng n_)
                     (lambda () (r7q-ineq (list '<= ng bnd) (list '<= bnd n_))))
                   (dk-have! (list 'AND (list '<= nf m_) (list '<= nf n_)))
                   (dk-have! (list 'AND (list '<= ng m_) (list '<= ng n_)))
                   (dk-apply! inf m_ n_)
                   (dk-apply! ing m_ n_)
                   (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) m_)
                   (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) n_)
                   (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) m_)
                   (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) n_)
                   (let* ((fm (list 'f_ m_)) (fn (list 'f_ n_))
                          (gm (list 'g_ m_)) (gn (list 'g_ n_))
                          (dfg-m (r7q-dm fm gm)) (dfg-n (r7q-dm fn gn)))
                     (fact 'metric-dist-real 'M fm gm)
                     (fact 'metric-dist-real 'M fn gn)
                     (fact 'metric-dist-real 'M fm fn)
                     (fact 'metric-dist-real 'M gm gn)
                     (mac 'rko2-dist-seq-at)
                     (mac 'rr-ms-dist)
                     (fact 'rr-sub-in-rr dfg-m dfg-n)
                     (fact 'rr-abs-closed (list '- dfg-m dfg-n))
                     (fact 'rko2-quad 'M fm gm fn gn)
                     (r7q-ineq
                      (list '<= (list 'abs (list '- dfg-m dfg-n))
                            (list '+ (r7q-dm fm fn) (r7q-dm gm gn)))
                      (list '<= (r7q-dm fm fn) d)
                      (list '<= (r7q-dm gm gn) d)
                      (list '= (list '+ d d) 'eps))))))))))))))
(qed 'r7q-dist-seq-cauchy)
(topic! 'r7q-dist-seq-cauchy 'analysis)

;;; ---------------------------------------------------------------- S2
;;; hence it converges: RR is complete.
(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
   (FORALL f_ (IMPLIES (IN f_ (CSEQ M))
     (FORALL g_ (IMPLIES (IN g_ (CSEQ M))
       (CONVERGES RR-MS (DIST-SEQ M f_ g_))))))))))
(dk-peel!)
(fact 'r7q-dist-seq-cauchy 'M 'f_ 'g_)
(fact 'rr-complete)
(fact 'complete-cauchy-converges 'RR-MS '(DIST-SEQ M f_ g_))
(ass)
(qed 'r7q-dist-seq-converges)
(topic! 'r7q-dist-seq-converges 'analysis)

;;; ---------------------------------------------------------------- S3
;;; the distance sequence is symmetric, at ANY limit (rko2-null-sym is the
;;; limit-0 case).
(define (r7q-redex? t)
  (and (pair? t)
       (or (and (pair? (car t)) (eq? (caar t) 'VNB-LAMBDA))
           (let lp ((l t))
             (and (pair? l) (or (r7q-redex? (car l)) (lp (cdr l))))))))
(define (r7q-beta!)
  (let lp () (if (r7q-redex? (dk-goal)) (begin (lam-b) (lp)))))

(define (r7q-limit-in-rr-ms! conv)
  (dk-have! (list 'IN (cadddr conv) '(PTS RR-MS))
            (lambda ()
              (dk-split-all! (dk-landed* (lambda () (mac-h 'CONVERGES-TO conv))))
              (ass))))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
   (FORALL f_ (IMPLIES (IN f_ (FUN NN (PTS M)))
     (FORALL g_ (IMPLIES (IN g_ (FUN NN (PTS M)))
       (FORALL lv (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv)
                           (CONVERGES-TO RR-MS (DIST-SEQ M g_ f_) lv)))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(r7q-limit-in-rr-ms! '(CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv))
(dk-have! '(IN (DIST-SEQ M f_ g_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (fact 'rko2-dist-seq-type 'M 'f_ 'g_) (ass)))
(dk-have! '(IN (DIST-SEQ M g_ f_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (fact 'rko2-dist-seq-type 'M 'g_ 'f_) (ass)))
(dk-have! '(FORALL j_ (IMPLIES (IN j_ NN)
             (= ((DIST-SEQ M g_ f_) j_) ((DIST-SEQ M f_ g_) j_))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j_)
      (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) j_)
      (mac 'rko2-dist-seq-at)
      (fact 'metric-sym 'M (list 'g_ j_) (list 'f_ j_))
      (ass))))
(fact 'converges-to-transfer 'RR-MS '(DIST-SEQ M f_ g_) '(DIST-SEQ M g_ f_) 'lv)
(ass)
(qed 'r7q-dist-seq-sym)
(topic! 'r7q-dist-seq-sym 'analysis)

;;; ---------------------------------------------------------------- S4
;;; rr-add-closed has an AND antecedent, which `fact' will not split.
(define (r7q-add-in-rr! x y)
  (dk-have! (list 'AND (list 'IN x 'RR) (list 'IN y 'RR)))
  (fact 'rr-add-closed x y))

;;; A sequence at NULL DISTANCE from a convergent one converges to the same
;;; limit, in ANY metric space.  d(h_j, lv) <= d(h_j, f_j) + d(f_j, lv), and
;;; both summands are null.
(define r7q-nt-a '(DIST-SEQ t h_ f_))
(define r7q-nt-b '(VNB-LAMBDA j_ NN ((DIST t) (f_ j_) lv)))
(define r7q-nt-t '(VNB-LAMBDA j_ NN ((DIST t) (h_ j_) lv)))
(define r7q-nt-s (list 'VNB-LAMBDA 'j_ 'NN
                       (list '+ (list r7q-nt-a 'j_) (list r7q-nt-b 'j_))))

(sp (make-wff '(FORALL t (IMPLIES (IS-METRIC-SPACE t)
   (FORALL f_ (IMPLIES (IN f_ (FUN NN (PTS t)))
     (FORALL h_ (IMPLIES (IN h_ (FUN NN (PTS t)))
       (FORALL lv (IMPLIES (IN lv (PTS t))
         (IMPLIES (CONVERGES-TO t f_ lv)
           (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ t f_ h_) 0)
                    (CONVERGES-TO t h_ lv)))))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(dk-have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'r7q-dist-seq-sym 't 'f_ 'h_ 0)
(fact 'converges-dist-null-fwd 't 'f_ 'lv)
(fact 'rko2-dist-seq-type 't 'h_ 'f_)
(fact 'dist-seq-in-fun 't 'f_ 'lv)
(fact 'dist-seq-in-fun 't 'h_ 'lv)
(dk-have! (list 'IN r7q-nt-s '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c r7q-nt-a 'NN 'RR j_)
      (fact 'fun-apply-type-c r7q-nt-b 'NN 'RR j_)
      (r7q-add-in-rr! (list r7q-nt-a j_) (list r7q-nt-b j_))
      (ass))))
(dk-have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
            (list '= (list r7q-nt-s 'j_)
                  (list '+ (list r7q-nt-a 'j_) (list r7q-nt-b 'j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS t) j_)
      (fact 'fun-apply-type-c r7q-nt-a 'NN 'RR j_)
      (fact 'metric-dist-real 't (list 'f_ j_) 'lv)
      (r7q-beta!)
      (r7q-add-in-rr! (list r7q-nt-a j_) (list '(DIST t) (list 'f_ j_) 'lv))
      (rfl))))
(fact 'rr-null-sum r7q-nt-a r7q-nt-b r7q-nt-s)
(dk-have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
            (list 'AND (list '<= 0 (list r7q-nt-t 'j_))
                  (list '<= (list r7q-nt-t 'j_) (list r7q-nt-s 'j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS t) j_)
      (fact 'fun-apply-type-c 'h_ 'NN '(PTS t) j_)
      (r7q-beta!)
      (mac 'rko2-dist-seq-at)
      (fact 'metric-pos 't (list 'h_ j_) 'lv)
      (fact 'metric-triangle 't (list 'h_ j_) (list 'f_ j_) 'lv)
      (dk-conj-close! (lambda () (ass))))))
(fact 'rr-null-squeeze r7q-nt-s r7q-nt-t)
(fact 'converges-dist-null-bwd 't 'h_ 'lv)
(ass)
(qed 'r7q-null-transfer)
(topic! 'r7q-null-transfer 'analysis)

;;; ---------------------------------------------------------------- S5
;;; apply a macete to the goal until it stops firing.
(define (r7q-mac*! name)
  (let lp ((n 0))
    (let ((g (dk-goal)))
      (quietly (lambda () (mac name)))
      (if (and (< n 6) (not (equal? g (dk-goal)))) (lp (+ n 1))))))

;;; THE QUADRILATERAL ESTIMATE IN THE LIMIT: moving both endpoints by null
;;; distances moves the distance sequence by a null distance.
(define r7q-qn-a '(DIST-SEQ M f_ p_))
(define r7q-qn-b '(DIST-SEQ M g_ q_))
(define r7q-qn-t '(DIST-SEQ RR-MS (DIST-SEQ M f_ g_) (DIST-SEQ M p_ q_)))
(define r7q-qn-s (list 'VNB-LAMBDA 'j_ 'NN
                       (list '+ (list r7q-qn-a 'j_) (list r7q-qn-b 'j_))))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
   (FORALL f_ (IMPLIES (IN f_ (FUN NN (PTS M)))
     (FORALL g_ (IMPLIES (IN g_ (FUN NN (PTS M)))
       (FORALL p_ (IMPLIES (IN p_ (FUN NN (PTS M)))
         (FORALL q_ (IMPLIES (IN q_ (FUN NN (PTS M)))
           (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ p_) 0)
             (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M g_ q_) 0)
               (CONVERGES-TO RR-MS
                  (DIST-SEQ RR-MS (DIST-SEQ M f_ g_) (DIST-SEQ M p_ q_))
                  0)))))))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(dk-have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'rko2-dist-seq-type 'M 'f_ 'g_)
(fact 'rko2-dist-seq-type 'M 'p_ 'q_)
(fact 'rko2-dist-seq-type 'M 'f_ 'p_)
(fact 'rko2-dist-seq-type 'M 'g_ 'q_)
(dk-have! '(IN (DIST-SEQ M f_ g_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (ass)))
(dk-have! '(IN (DIST-SEQ M p_ q_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (ass)))
(fact 'rko2-dist-seq-type 'RR-MS '(DIST-SEQ M f_ g_) '(DIST-SEQ M p_ q_))
(dk-have! (list 'IN r7q-qn-s '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c r7q-qn-a 'NN 'RR j_)
      (fact 'fun-apply-type-c r7q-qn-b 'NN 'RR j_)
      (r7q-add-in-rr! (list r7q-qn-a j_) (list r7q-qn-b j_))
      (ass))))
(dk-have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
            (list '= (list r7q-qn-s 'j_)
                  (list '+ (list r7q-qn-a 'j_) (list r7q-qn-b 'j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c r7q-qn-a 'NN 'RR j_)
      (fact 'fun-apply-type-c r7q-qn-b 'NN 'RR j_)
      (r7q-beta!)
      (r7q-add-in-rr! (list r7q-qn-a j_) (list r7q-qn-b j_))
      (rfl))))
(fact 'rr-null-sum r7q-qn-a r7q-qn-b r7q-qn-s)
(dk-have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
            (list 'AND (list '<= 0 (list r7q-qn-t 'j_))
                  (list '<= (list r7q-qn-t 'j_) (list r7q-qn-s 'j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (for-each (lambda (s) (fact 'fun-apply-type-c s 'NN '(PTS M) j_))
                (list 'f_ 'g_ 'p_ 'q_))
      (let ((d1 (list '(DIST M) (list 'f_ j_) (list 'g_ j_)))
            (d2 (list '(DIST M) (list 'p_ j_) (list 'q_ j_))))
        (fact 'metric-dist-real 'M (list 'f_ j_) (list 'g_ j_))
        (fact 'metric-dist-real 'M (list 'p_ j_) (list 'q_ j_))
        (fact 'metric-dist-real 'M (list 'f_ j_) (list 'p_ j_))
        (fact 'metric-dist-real 'M (list 'g_ j_) (list 'q_ j_))
        (r7q-beta!)
        (r7q-mac*! 'rko2-dist-seq-at)
        (mac 'rr-ms-dist)
        (fact 'rr-sub-in-rr d1 d2)
        (fact 'rr-abs-closed (list '- d1 d2))
        (dk-conj-close!
         (lambda ()
           (if (equal? (cadr (dk-goal)) 0)
               (begin (fact 'rr-abs-nonneg (list '- d1 d2)) (ass))
               (begin (fact 'rko2-quad 'M (list 'f_ j_) (list 'g_ j_)
                            (list 'p_ j_) (list 'q_ j_))
                      (ass)))))))))
(fact 'rr-null-squeeze r7q-qn-s r7q-qn-t)
(ass)
(qed 'r7q-quad-null)
(topic! 'r7q-quad-null 'analysis)

;;; ---------------------------------------------------------------- S6
;;; REPRESENTATIVE-INDEPENDENCE of the limit.
(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
   (FORALL f_ (IMPLIES (IN f_ (FUN NN (PTS M)))
     (FORALL g_ (IMPLIES (IN g_ (FUN NN (PTS M)))
       (FORALL p_ (IMPLIES (IN p_ (FUN NN (PTS M)))
         (FORALL q_ (IMPLIES (IN q_ (FUN NN (PTS M)))
           (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ p_) 0)
             (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M g_ q_) 0)
               (FORALL lv
                 (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv)
                          (CONVERGES-TO RR-MS (DIST-SEQ M p_ q_) lv)))))))))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'r7q-quad-null 'M 'f_ 'g_ 'p_ 'q_)
(fact 'rko2-dist-seq-type 'M 'f_ 'g_)
(fact 'rko2-dist-seq-type 'M 'p_ 'q_)
(dk-have! '(IN (DIST-SEQ M f_ g_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (ass)))
(dk-have! '(IN (DIST-SEQ M p_ q_) (FUN NN (PTS RR-MS)))
          (lambda () (slot 'PTS) (ass)))
(r7q-limit-in-rr-ms! '(CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv))
(fact 'r7q-null-transfer 'RR-MS '(DIST-SEQ M f_ g_) '(DIST-SEQ M p_ q_) 'lv)
(ass)
(qed 'r7q-limit-indep)
(topic! 'r7q-limit-indep 'analysis)

;;; ---------------------------------------------------------------- S7
;;; THE DESCRIPTION, read off the COMPLETION pair.  d-hat(x,y) IS the IOTA of
;;; COMPLETION-DIST's body at the pair [x,y]; both orientations, because
;;; `subst' rewrites left to right.
(define (r7q-iota x y)
  (list 'IOTA 'dval
    (list 'FORSOME 'f (list 'FORSOME 'g
      (list 'AND '(IN f (CSEQ M))
        (list 'AND '(IN g (CSEQ M))
          (list 'AND (list '= x '(CLASS (CAUCHY-SETOID M) f))
            (list 'AND (list '= y '(CLASS (CAUCHY-SETOID M) g))
              '(CONVERGES-TO RR-MS (DIST-SEQ M f g) dval)))))))))

(define (r7q-nth*!)
  (let lp ((n 0))
    (let ((g (dk-goal)))
      (quietly (lambda () (nth-r)))
      (if (and (< n 6) (not (equal? g (dk-goal)))) (lp (+ n 1))))))

(define (r7q-open-dhat!)
  (fact 'pair-in-cartesian '(QUOTIENT (CAUCHY-SETOID M))
        '(QUOTIENT (CAUCHY-SETOID M)) 'x_ 'y_)
  (mac 'rko2-completion-dist)
  (fact 'apply-tupling-2 '(COMPLETION-DIST M) 'x_ 'y_)
  (subst '(== ((COMPLETION-DIST M) x_ y_) ((COMPLETION-DIST M) (LIST x_ y_))))
  (mac 'COMPLETION-DIST)
  (lam-b)
  (r7q-nth*!)
  (qrfl))

(sp (make-wff (list 'FORALL 'M (list 'FORALL 'x_ (list 'FORALL 'y_
   (list 'IMPLIES '(IN x_ (QUOTIENT (CAUCHY-SETOID M)))
     (list 'IMPLIES '(IN y_ (QUOTIENT (CAUCHY-SETOID M)))
       (list '== (r7q-iota 'x_ 'y_) '((DIST (COMPLETION M)) x_ y_)))))))))
(dk-peel!)
(r7q-open-dhat!)
(qed 'r7q-iota-dhat)
(topic! 'r7q-iota-dhat 'plumbing)

(sp (make-wff (list 'FORALL 'M (list 'FORALL 'x_ (list 'FORALL 'y_
   (list 'IMPLIES '(IN x_ (QUOTIENT (CAUCHY-SETOID M)))
     (list 'IMPLIES '(IN y_ (QUOTIENT (CAUCHY-SETOID M)))
       (list '== '((DIST (COMPLETION M)) x_ y_) (r7q-iota 'x_ 'y_)))))))))
(dk-peel!)
(r7q-open-dhat!)
(qed 'r7q-dhat-iota)
(topic! 'r7q-dhat-iota 'plumbing)

;;; ---------------------------------------------------------------- S8
;;; THE VALUE OF d-hat AT A PAIR OF CLASSES.
(define r7q-cu '(CLASS (CAUCHY-SETOID M) f_))
(define r7q-cv '(CLASS (CAUCHY-SETOID M) g_))

;; from  [f_] = [a2], [g_] = [b2]  and  DIST-SEQ(M,f_,g_) -> lv:
;; DIST-SEQ(M,a2,b2) -> lv.
(define (r7q-transport! a2 b2)
  (fact 'rko2-cseq-in-fun 'M a2)
  (fact 'rko2-cseq-in-fun 'M b2)
  (fact 'rko2-class-eq-null 'M 'f_ a2)
  (fact 'rko2-class-eq-null 'M 'g_ b2)
  (fact 'r7q-limit-indep 'M 'f_ 'g_ a2 b2 'lv))

(define (r7q-exist-leaf!)
  (let ((g (dk-goal)))
    (cond ((eq? (car g) 'FORSOME) (ew 'g_) (dk-conj-close! r7q-exist-leaf!))
          ((eq? (car g) '=) (fact 'rkt-class-is-set 'M (caddr (caddr g))) (rfl))
          (#t (ass)))))

(define (r7q-skolem-pair!)
  (let* ((a2 (dk-skolem! (r7q-hyp 'FORSOME "the property, outer")))
         (b2 (dk-skolem! (r7q-hyp 'FORSOME "the property, inner"))))
    (list a2 b2)))

(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'f_ (list 'IMPLIES '(IN f_ (CSEQ M))
     (list 'FORALL 'g_ (list 'IMPLIES '(IN g_ (CSEQ M))
       (list 'FORALL 'lv (list 'IMPLIES '(CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv)
         (list '= (list '(DIST (COMPLETION M)) r7q-cu r7q-cv) 'lv)))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'rko2-cseq-in-fun 'M 'f_)
(fact 'rko2-cseq-in-fun 'M 'g_)
(r7q-limit-in-rr-ms! '(CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) lv))
(dk-have! '(IN f_ (PTS (CAUCHY-SETOID M)))
          (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(dk-have! '(IN g_ (PTS (CAUCHY-SETOID M)))
          (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(fact 'class-in-quotient '(CAUCHY-SETOID M) 'f_)
(fact 'class-in-quotient '(CAUCHY-SETOID M) 'g_)
(fact 'r7q-dhat-iota 'M r7q-cu r7q-cv)
(subst (list '== (list '(DIST (COMPLETION M)) r7q-cu r7q-cv) (r7q-iota r7q-cu r7q-cv)))
(let* ((it (cadr (dk-goal)))
       (ls (dk-opened (lambda () (iota-d it)))))
  ;; (1) the description's property, granted
  (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) '=)) ls))
  (let* ((pr (r7q-skolem-pair!))
         (a2 (car pr)) (b2 (cadr pr)))
    (r7q-limit-in-rr-ms!
     (list 'CONVERGES-TO 'RR-MS (list 'DIST-SEQ 'M a2 b2) it))
    (r7q-transport! a2 b2)
    (fact 'metric-limit-unique 'RR-MS (list 'DIST-SEQ 'M a2 b2) it 'lv)
    (ass))
  ;; (2) existence and uniqueness
  (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORSOME)) ls))
  (ew 'lv)
  (let ((cs (dk-opened (lambda () (di)))))
    ;; existence at lv, with f_ and g_ as the representatives
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORSOME)) cs))
    (ew 'f_)
    (dk-conj-close! r7q-exist-leaf!)
    ;; uniqueness
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORALL)) cs))
    (dk-peel!)
    (let* ((pr (r7q-skolem-pair!))
           (a2 (car pr)) (b2 (cadr pr)))
      (r7q-transport! a2 b2)
      (fact 'metric-limit-unique 'RR-MS (list 'DIST-SEQ 'M a2 b2) 'lv (caddr (dk-goal)))
      (ass))))
(qed 'r7q-dist-value)
(topic! 'r7q-dist-value 'analysis)

;;; ---------------------------------------------------------------- S9
;;; THE METRIC LAWS ON THE QUOTIENT.
(sp (make-wff '(== RR (PTS RR-MS))))
(slot 'PTS) (qrfl)
(qed 'r7q-rr-pts)
(topic! 'r7q-rr-pts 'plumbing)

(define r7q-q '(QUOTIENT (CAUCHY-SETOID M)))
(define (r7q-cls a) (list 'CLASS '(CAUCHY-SETOID M) a))
(define (r7q-dhat x y) (list '(DIST (COMPLETION M)) x y))

;; (IN x RR) from (IN x (PTS RR-MS))
(define (r7q-in-rr! x)
  (dk-have! (list 'IN x 'RR) (lambda () (mac 'r7q-rr-pts) (ass))))

;; a REPRESENTATIVE of a class x: returns a with (IN a (CSEQ M)),
;; (IN a (FUN NN (PTS M))) and (= x (CLASS (CAUCHY-SETOID M) a)) in context.
(define (r7q-rep! x)
  (fact 'quotient-rep '(CAUCHY-SETOID M) x)
  (let ((a (dk-skolem!
            (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME)
                                      (dk-contains? f x)))
                     "the representative existential"))))
    (dk-have! (list 'IN a '(CSEQ M))
      (lambda () (mac-h 'rkt-cauchy-setoid-pts
                        (list 'IN a '(PTS (CAUCHY-SETOID M))))
                 (ass)))
    (fact 'rko2-cseq-in-fun 'M a)
    a))

;; the LIMIT of the distance sequence of two Cauchy sequences, with the value
;; equation (= d-hat([a],[b]) l) and (IN l RR) landed beside it.
(define (r7q-limit-of! a b)
  (fact 'r7q-dist-seq-converges 'M a b)
  (let* ((cv (list 'CONVERGES 'RR-MS (list 'DIST-SEQ 'M a b)))
         (ex (dk-landed-1 (lambda () (mac-h 'CONVERGES cv))))
         (l  (dk-skolem! ex)))
    (r7q-limit-in-rr-ms! (list 'CONVERGES-TO 'RR-MS (list 'DIST-SEQ 'M a b) l))
    (r7q-in-rr! l)
    (fact 'r7q-dist-value 'M a b l)
    l))

;;; L1 -- d-hat is real-valued.
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r7q-q)
       (list 'IN (r7q-dhat 'x_ 'y_) 'RR)))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(let* ((a (r7q-rep! 'x_))
       (b (r7q-rep! 'y_)))
  (subst (list '= 'x_ (r7q-cls a)))
  (subst (list '= 'y_ (r7q-cls b)))
  (let ((l (r7q-limit-of! a b)))
    (subst (list '= (r7q-dhat (r7q-cls a) (r7q-cls b)) l))
    (ass)))
(qed 'r7q-dhat-in-rr)
(topic! 'r7q-dhat-in-rr 'analysis)

;;; L2 -- d-hat(x,x) = 0.
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list '= (r7q-dhat 'x_ 'x_) 0)))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(let ((a (r7q-rep! 'x_)))
  (subst (list '= 'x_ (r7q-cls a)))
  (fact 'rko2-null-refl 'M a)
  (fact 'r7q-dist-value 'M a a 0)
  (ass))
(qed 'r7q-dhat-self-zero)
(topic! 'r7q-dhat-self-zero 'analysis)

;;; L3 -- d-hat is nonnegative: the limit of nonnegative reals.
(define r7q-zseq '(EMBED-SEQ RR-MS 0))
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r7q-q)
       (list '<= 0 (r7q-dhat 'x_ 'y_))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(dk-have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'rkt-embed-seq-in-fun 'RR-MS 0)
(dk-have! (list 'IN r7q-zseq '(FUN NN RR)) (lambda () (mac 'r7q-rr-pts) (ass)))
(fact 'rko2-const-seq-converges 'RR-MS 0)
(let* ((a (r7q-rep! 'x_))
       (b (r7q-rep! 'y_)))
  (subst (list '= 'x_ (r7q-cls a)))
  (subst (list '= 'y_ (r7q-cls b)))
  (let ((l (r7q-limit-of! a b)))
    (subst (list '= (r7q-dhat (r7q-cls a) (r7q-cls b)) l))
    (fact 'rko2-dist-seq-type 'M a b)
    (dk-have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                (list '<= (list r7q-zseq 'n_) (list (list 'DIST-SEQ 'M a b) 'n_))))
      (lambda ()
        (let ((n_ (dk-di-var!)))
          (fact 'fun-apply-type-c a 'NN '(PTS M) n_)
          (fact 'fun-apply-type-c b 'NN '(PTS M) n_)
          (mac 'EMBED-SEQ)
          (r7q-beta!)
          (mac 'rko2-dist-seq-at)
          (fact 'metric-pos 'M (list a n_) (list b n_))
          (ass))))
    (fact 'rr-limit-le r7q-zseq (list 'DIST-SEQ 'M a b) 0 l)
    (ass)))
(qed 'r7q-dhat-nonneg)
(topic! 'r7q-dhat-nonneg 'analysis)

;;; L4 -- d-hat(x,y) = 0 identifies x and y: null distance IS the relation.
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r7q-q)
       (list 'IMPLIES (list '= (r7q-dhat 'x_ 'y_) 0) '(= x_ y_))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(let* ((a (r7q-rep! 'x_))
       (b (r7q-rep! 'y_))
       (ca (r7q-cls a))
       (cb (r7q-cls b)))
  (let ((l (r7q-limit-of! a b)))
    (fact 'equality-symmetry 'x_ ca)
    (fact 'equality-symmetry 'y_ cb)
    (dk-have! (list '= (r7q-dhat ca cb) 0)
      (lambda () (subst (list '= ca 'x_)) (subst (list '= cb 'y_)) (ass)))
    (fact 'equality-symmetry (r7q-dhat ca cb) l)
    (dk-have! (list '= l 0)
      (lambda () (subst (list '= l (r7q-dhat ca cb))) (ass)))
    (fact 'equality-symmetry l 0)
    (dk-have! (list 'CONVERGES-TO 'RR-MS (list 'DIST-SEQ 'M a b) 0)
      (lambda () (subst (list '= 0 l)) (ass)))
    (dk-have! (list 'CSEQ-EQUIV 'M a b) (lambda () (mac 'CSEQ-EQUIV) (ass)))
    (fact 'rko2-crel-intro 'M a b)
    (dk-have! (list 'IN (list 'LIST a b) '(REL (CAUCHY-SETOID M)))
      (lambda () (mac 'rko2-cauchy-setoid-rel) (ass)))
    (dk-have! (list 'RELATED '(CAUCHY-SETOID M) a b)
      (lambda () (mac 'RELATED) (ass)))
    (let* ((iff (dk-fact! 'class-eq-iff '(CAUCHY-SETOID M) a b))
           (ims (dk-landed (lambda () (ai iff)))))
      (detach! (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                              (pair? (caddr f))
                                              (eq? (car (caddr f)) '=)))
                             ims)
                   (error "r7q: no (RELATED => =) direction of class-eq-iff"))))
    (subst (list '= 'x_ ca))
    (subst (list '= 'y_ cb))
    (ass)))
(qed 'r7q-dhat-zero-eq)
(topic! 'r7q-dhat-zero-eq 'analysis)

;;; L5 -- symmetry.
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r7q-q)
       (list '= (r7q-dhat 'x_ 'y_) (r7q-dhat 'y_ 'x_))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(let* ((a (r7q-rep! 'x_))
       (b (r7q-rep! 'y_)))
  (subst (list '= 'x_ (r7q-cls a)))
  (subst (list '= 'y_ (r7q-cls b)))
  (let ((l (r7q-limit-of! a b)))
    (fact 'r7q-dist-seq-sym 'M a b l)
    (fact 'r7q-dist-value 'M b a l)
    (subst (list '= (r7q-dhat (r7q-cls a) (r7q-cls b)) l))
    (subst (list '= (r7q-dhat (r7q-cls b) (r7q-cls a)) l))
    (rfl)))
(qed 'r7q-dhat-sym)
(topic! 'r7q-dhat-sym 'analysis)

;;; L6 -- the triangle inequality, passed to the limit through rr-limit-add
;;; and rr-limit-le.
(sp (make-wff (list 'FORALL 'M (list 'IMPLIES '(IS-METRIC-SPACE M)
   (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ r7q-q)
     (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ r7q-q)
       (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ r7q-q)
         (list '<= (r7q-dhat 'x_ 'z_)
               (list '+ (r7q-dhat 'x_ 'y_) (r7q-dhat 'y_ 'z_)))))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'rr-is-metric-space)
(let* ((a (r7q-rep! 'x_))
       (b (r7q-rep! 'y_))
       (c (r7q-rep! 'z_)))
  (subst (list '= 'x_ (r7q-cls a)))
  (subst (list '= 'y_ (r7q-cls b)))
  (subst (list '= 'z_ (r7q-cls c)))
  (let* ((l1 (r7q-limit-of! a c))
         (l2 (r7q-limit-of! a b))
         (l3 (r7q-limit-of! b c))
         (dac (list 'DIST-SEQ 'M a c))
         (dab (list 'DIST-SEQ 'M a b))
         (dbc (list 'DIST-SEQ 'M b c))
         (ssum (list 'VNB-LAMBDA 'j_ 'NN
                     (list '+ (list dab 'j_) (list dbc 'j_)))))
    (subst (list '= (r7q-dhat (r7q-cls a) (r7q-cls c)) l1))
    (subst (list '= (r7q-dhat (r7q-cls a) (r7q-cls b)) l2))
    (subst (list '= (r7q-dhat (r7q-cls b) (r7q-cls c)) l3))
    (fact 'rko2-dist-seq-type 'M a b)
    (fact 'rko2-dist-seq-type 'M b c)
    (fact 'rko2-dist-seq-type 'M a c)
    (dk-have! (list 'IN ssum '(FUN NN RR))
      (lambda ()
        (dk-lam-t!)
        (let ((j_ (dk-di-var!)))
          (fact 'fun-apply-type-c dab 'NN 'RR j_)
          (fact 'fun-apply-type-c dbc 'NN 'RR j_)
          (r7q-add-in-rr! (list dab j_) (list dbc j_))
          (ass))))
    (dk-have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
                (list '= (list ssum 'j_)
                      (list '+ (list dab 'j_) (list dbc 'j_)))))
      (lambda ()
        (let ((j_ (dk-di-var!)))
          (fact 'fun-apply-type-c dab 'NN 'RR j_)
          (fact 'fun-apply-type-c dbc 'NN 'RR j_)
          (r7q-beta!)
          (r7q-add-in-rr! (list dab j_) (list dbc j_))
          (rfl))))
    (fact 'rr-limit-add dab dbc ssum l2 l3)
    (r7q-add-in-rr! l2 l3)
    (dk-have! (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                (list '<= (list dac 'n_) (list ssum 'n_))))
      (lambda ()
        (let ((n_ (dk-di-var!)))
          (fact 'fun-apply-type-c a 'NN '(PTS M) n_)
          (fact 'fun-apply-type-c b 'NN '(PTS M) n_)
          (fact 'fun-apply-type-c c 'NN '(PTS M) n_)
          (r7q-beta!)
          (r7q-mac*! 'rko2-dist-seq-at)
          (fact 'metric-triangle 'M (list a n_) (list b n_) (list c n_))
          (ass))))
    (fact 'rr-limit-le dac ssum l1 (list '+ l2 l3))
    (ass)))
(qed 'r7q-dhat-triangle)
(topic! 'r7q-dhat-triangle 'analysis)

;;; ---------------------------------------------------------------- S10
;;; THE LEAF: completion-is-metric-space.
(define (r7q-split-goal!)
  (let walk ((n (proof-state-focus *ps*)) (acc '()))
    (dk-focus! n)
    (let ((g (dk-goal)))
      (if (and (pair? g) (eq? (car g) 'AND))
          (let loop ((ks (dk-opened (lambda () (di)))) (acc acc))
            (if (null? ks) acc (loop (cdr ks) (walk (car ks) acc))))
          (cons n acc)))))

(define (r7q-drive!)
  (let loop ((fuel 80))
    (let ((n (find-first (lambda (n)
                           (let ((g (dk-goal-of n)))
                             (and (not (sequent-node-grounded? n))
                                  (pair? g) (memq (car g) '(FORALL IMPLIES AND)))))
                         (proof-leaves))))
      (if (and n (> fuel 0)) (begin (dk-focus! n) (di) (loop (- fuel 1))) #t))))

;; the FUN-typing conjunct: the description denotes at every pair of classes.
(define (r7q-dist-typing!)
  (mac 'rko2-completion-dist)
  (mac 'COMPLETION-DIST)
  ;; NOT `dk-lam-t!': it diffs `proof-leaves' GLOBALLY, and with three sibling
  ;; conjuncts still open its "new leaf" set is not the two `lam-t' opened --
  ;; it closed the LENGTH conjunct's node by `ass' instead, leaving a duplicate
  ;; open node with that goal and a `qed' that could not see why.  `dk-opened'
  ;; returns exactly what the tactic opened.
  (let ((ls (dk-opened (lambda () (lam-t)))))
    (dk-focus! (any-pred (lambda (nn) (let ((g (dk-goal-of nn)))
                                        (and (pair? g) (eq? (car g) 'IN)
                                             (eq? (caddr g) 'SET))))
                         ls))
    (ass)
    (dk-focus! (any-pred (lambda (nn) (eq? (car (dk-goal-of nn)) 'FORALL)) ls)))
  ;; `cartesian-decompose' is a PROCEDURAL macete: it has no theorem-table
  ;; entry, so `mac-h' cannot name it.  Fire it on the GOAL while the
  ;; membership is still the ANTECEDENT (finsum-fiber.scm's note).
  (mac 'cartesian-decompose)
  (dk-peel!)
  (let* ((c1 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the first component")))
         (c2 (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the second component")))
         (eqn (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                        (equal? (caddr f) (list 'LIST c1 c2))))
                       "the pair equation")))
    (subst eqn)
    (r7q-nth*!)
    (mac 'r7q-iota-dhat)
    (fact 'r7q-dhat-in-rr 'M c1 c2)
    (ass)))

;; the five metric laws, dispatched on the shape of the leaf.
(define (r7q-law!)
  (let ((g (dk-goal)))
    (cond
      ((and (eq? (car g) '=) (equal? (caddr g) 0))
       (fact 'r7q-dhat-self-zero 'M (cadr (cadr g))) (ass))
      ((and (eq? (car g) '<=) (equal? (cadr g) 0))
       (let ((r (caddr g))) (fact 'r7q-dhat-nonneg 'M (cadr r) (caddr r))) (ass))
      ((and (eq? (car g) '=) (symbol? (cadr g)) (symbol? (caddr g)))
       (fact 'r7q-dhat-zero-eq 'M (cadr g) (caddr g)) (ass))
      ((eq? (car g) '=)
       (fact 'r7q-dhat-sym 'M (cadr (cadr g)) (caddr (cadr g))) (ass))
      ((eq? (car g) '<=)
       (let* ((lhs (cadr g)) (rhs (caddr g))
              (u (cadr lhs)) (w (caddr lhs)) (v (caddr (cadr rhs))))
         (fact 'r7q-dhat-triangle 'M u v w) (ass)))
      (#t (error "r7q-law!: unexpected leaf" (expression->string g))))))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-METRIC-SPACE (COMPLETION M))))))
(di) (di)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'quotient-is-set '(CAUCHY-SETOID M))
(dk-have! (list 'IN (list 'CARTESIAN r7q-q r7q-q) 'SET)
  (lambda () (mac 'cartesian-set-iff) (dk-conj-close! (lambda () (ass)))))
(mac 'IS-METRIC-SPACE)
(mac 'rkt-completion-pts)
(define r7q-cs (r7q-split-goal!))
(for-each
 (lambda (n)
   (if (not (sequent-node-grounded? n))
       (begin
         (dk-focus! n)
         (let ((g (dk-goal)))
           (cond
             ((and (eq? (car g) '=) (pair? (cadr g)) (eq? (car (cadr g)) 'LENGTH))
              (mac 'COMPLETION) (len-r) (rfl))
             ((and (eq? (car g) 'IN) (equal? (caddr g) 'SET)) (ass))
             ((eq? (car g) 'IN) (r7q-dist-typing!))
             (#t 'is-metric-later))))))
 r7q-cs)
(dk-focus-goal! "is-metric(")
(mac 'is-metric)
(r7q-drive!)
(for-each (lambda (n)
            (if (not (sequent-node-grounded? n))
                (begin (dk-focus! n) (r7q-law!))))
          (proof-leaves))
(qed 'completion-is-metric-space)
(topic! 'completion-is-metric-space 'constructions)
