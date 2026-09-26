;;; rake-setoid2.scm -- BATCH O of the 2026-09-17 rake: the SETOID quotient and
;;; the METRIC COMPLETION.  Twelve of the thirteen asserted leaves of the batch
;;; are PROVEN here; the thirteenth is a STATEMENT DEFECT and is recorded below.
;;; Every statement is its support's statement UNCHANGED (copied from the
;;; support site, never read off the theorem table).
;;;
;;; PART I -- structure-library/setoid.scm, all nine, all `modulo 0':
;;;   class-self :90   class-subset-carrier :99   class-eq-iff :111
;;;   class-disjoint :125   class-in-quotient :137   quotient-rep :148
;;;   descend-computes :182   quotient-universal :201   descend2-computes :258
;;;
;;; PART II -- structure-library/metric-completion.scm:
;;;   cauchy-setoid-is-setoid :74   PROVEN `modulo 0'.
;;;   embed-isometry          :151  STATEMENT WRONG.  The corrected statement is
;;;                                 PROVEN here as `embed-isometry (installed under the ORIGINAL name since 2026-09-17: the support's term was restated to ((EMBED M) u), the integrator's call)'.
;;;   completion-is-metric-space :110  NOT attempted -- see THE TWO LEFT below.
;;;   completion-is-complete     :123  NOT attempted -- the diagonal argument.
;;;
;;; =====================================================================
;;; PART I.  THE PROJECTION IS THE POINT.
;;;
;;; Every one of the nine setoid leaves is reflexivity, symmetry or transitivity
;;; of REL dressed in CLASS/QUOTIENT clothing.  Projecting the three laws ONCE --
;;; `rko2-refl', `rko2-sym', `rko2-trans', stated over the RELATED sugar -- turns
;;; "mac-h IS-SETOID, split, mac-h IS-EQUIVALENCE, split, pick the right conjunct
;;; by shape" (five DESTRUCTIVE lines that delete the IS-SETOID hypothesis every
;;; later `fact' needs) into one `fact'.  That is subtype-laws.scm's
;;; `stl--project!' shape with one extra step: the conjunct is stated over the RAW
;;; relation `(IN (LIST a b) (REL s))' and the leaves want the sugar `RELATED', so
;;; `mac' bridges the goal side and `rko2-related-unfold' the hypothesis side --
;;; `def-functoid' installs a rewrite macete and NO theorem, so `mac-h' cannot
;;; unfold RELATED in an assumption without it (the mac-h trap, CLAUDE.md).
;;;
;;; `rko2-trans' is CURRIED -- RELATED(a,b) => RELATED(b,c) => RELATED(a,c) --
;;; because the is-equivalence conjunct has an AND antecedent and `fact' will not
;;; split one.
;;;
;;; THE THREE CONJUNCTS ARE PICKED BY THE DEPTH OF THEIR UNIVERSAL PREFIX
;;; (`rko2-depth': refl 1, sym 2, trans 3), never by a symbol they contain -- all
;;; three mention exactly PTS, REL and LIST.
;;;
;;; SET EQUALITY GOES THROUGH `class-extensionality', the unconditional NBG axiom,
;;; not `extensionality': no sethood premise has to be produced, so class-eq-iff
;;; and class-disjoint never mention `(IN (CLASS s a) SET)'.
;;;
;;; =====================================================================
;;; PART II.  THE COMPLETION.
;;;
;;; `cauchy-setoid-is-setoid' says CREL(M) -- null distance -- is an equivalence
;;; relation on the Cauchy sequences.  The three laws are proved over the
;;; SEQUENCES first (`rko2-null-refl' / `-sym' / `-trans') and then dressed in the
;;; CREL/SEP clothing by `rko2-crel-intro' / `rko2-crel-elim', for the same reason
;;; Part I projects first: the dressing is bookkeeping and the mathematics is not.
;;;
;;;   REFLEXIVE   d(f_n,f_n) = 0 for every n, so the distance sequence is the
;;;               constant 0 and N := 0 serves every eps.  `metric-self-zero'
;;;               twice -- once in M, once in RR-MS, where it retires the
;;;               `abs(0-0)' detour that `rr-ms-dist' would otherwise open.
;;;   SYMMETRIC   DIST-SEQ(M,g,f) and DIST-SEQ(M,f,g) agree pointwise by
;;;               `metric-sym', and `converges-to-transfer' carries the limit
;;;               across.  No eps/delta at all.
;;;   TRANSITIVE  `rr-null-sum' makes the pointwise sum of the two null sequences
;;;               null and `rr-null-squeeze' presses d(f_n,h_n) between 0 and it.
;;;               Both are stated in TRANSFER form -- about any sequence agreeing
;;;               pointwise -- so the explicit VNB-LAMBDA is typed by `lam-t' and
;;;               fed straight in.
;;;
;;; `rko2-quad', the QUADRILATERAL inequality |d(a,b) - d(c,e)| <= d(a,c)+d(b,e),
;;; is the one piece of real content the tree did not have.  It is four
;;; `metric-triangle' instances, two `metric-sym' rewrites and one `ineq'; the
;;; absolute value comes off with `rr-abs-bound'.  On it stands
;;; `rko2-dist-converges' -- "the metric is continuous": f -> a and g -> b imply
;;; d(f_n,g_n) -> d(a,b) -- which is what every representative-independence
;;; argument about the completion needs and is stated here in full generality.
;;;
;;; ---------------------------------------------------------------------
;;; THE STATEMENT DEFECT: embed-isometry (metric-completion.scm:151).
;;;
;;; The support says
;;;
;;;     d_hat( EMBED(M,u), EMBED(M,v) )  =  d(u,v)
;;;
;;; and `EMBED' is a ONE-parameter def-functoid: `EMBED(M)' IS the map, and
;;; `embed-in-fun' (rake-analysis-typing.scm) types exactly `(IN (EMBED M) (FUN
;;; (PTS M) (PTS (COMPLETION M))))'.  In VNB an n-ary application is application
;;; to the TUPLE, not currying -- `apply-tupling-2' says `(f a b) == (f [a,b])' --
;;; so the term written in the support is NOT `((EMBED M) u)'.  It is EMBED at the
;;; PAIR, and it denotes something:
;;;
;;;     (EMBED M u) == (EMBED [M,u])
;;;                 == VNB-LAMBDA w in PTS([M,u]). CLASS(CAUCHY-SETOID([M,u]),
;;;                                                      EMBED-SEQ([M,u], w))
;;;
;;; -- the embedding of the "metric space" [M,u], whose point set PTS([M,u]) is M
;;; itself.  Both are PROVEN in the control scratchpad/rko2/ctrl.scm, `modulo 0'.
;;; So the support's left-hand side applies the completion's metric to two
;;; FUNCTIONS, not to two points of the completion; nothing types it, and the
;;; right-hand side d(u,v) is a real.  `mac EMBED' declines on the support's term
;;; ("macete not applicable: embed") while it fires on the corrected one.
;;;
;;; The corrected statement -- the support's, with `(EMBED M u)' replaced by
;;; `((EMBED M) u)' and nothing else changed -- is PROVEN below as
;;; `embed-isometry-applied', `modulo 0'.  The route:
;;;   * `rko2-completion-dist' reads d_hat off the COMPLETION pair;
;;;   * one `apply-tupling-2' turns d_hat(x,y) into d_hat([x,y]) so that
;;;     COMPLETION-DIST -- a lambda over ONE pair variable -- can beta-reduce;
;;;   * `iota-d' posts existence-and-uniqueness for the description, and both
;;;     halves are the SAME lemma: any representative f of [const u] satisfies
;;;     f -> u (`rko2-class-eq-null' then `rko2-const-equiv-converges'), so
;;;     `rko2-dist-converges' sends d(f_n,g_n) -> d(u,v) and
;;;     `metric-limit-unique' pins the description.
;;; No new support and no guard: the defect is in the TERM, not in the content.
;;;
;;; ---------------------------------------------------------------------
;;; THE TWO LEFT, and what each is waiting on.
;;;
;;; completion-is-metric-space (:110).  NOT a grind away -- it needs one thing
;;; this batch did not build: d_hat DENOTES at an ARBITRARY pair of classes.
;;; That is "DIST-SEQ(M,f,g) is a CAUCHY real sequence for any two Cauchy f, g"
;;; (immediate from `rko2-quad': |d(f_m,g_m) - d(f_n,g_n)| <= d(f_m,f_n) +
;;; d(g_m,g_n), and both terms are small past the two Cauchy thresholds) followed
;;; by `rr-cauchy-converges'.  With that lemma, representative-independence is
;;; `rko2-dist-converges' + `metric-limit-unique' exactly as in
;;; `embed-isometry-applied', and the four metric laws pass to the limit through
;;; `rr-limit-le' / `rr-limit-add' (nonnegativity and the triangle inequality),
;;; `rko2-null-sym' (symmetry) and `class-eq-iff' at the Cauchy setoid together
;;; with `metric-limit-unique' (separation of points).  Everything named is
;;; PROVEN; the one missing brick is the Cauchyness of DIST-SEQ.
;;;
;;; completion-is-complete (:123).  The diagonal argument, and it is a different
;;; order of work: it needs a CHOICE of a representative term within 1/2^k of each
;;; class -- so a lambda built by IOTA or CHOICE over k -- plus the fact that the
;;; diagonal is Cauchy in M and that its class is the limit of the given sequence
;;; of classes.  Nothing in this batch touches it, and it should not be attempted
;;; before completion-is-metric-space: IS-COMPLETE(COMPLETION M) presupposes
;;; IS-METRIC-SPACE(COMPLETION M), which is the leaf above.
;;;
;;; =====================================================================
;;; LOAD WINDOW [after theorem-library/product-convergence, end).
;;;
;;;   lo -- the LATEST citation is theorem-library/product-convergence
;;;     (`rr-null-squeeze', `converges-to-transfer'; position 417 in load.scm as
;;;     of 2026-09-17).  Next latest, in order:
;;;     theorem-library/converges-dist-null (414: converges-dist-null-fwd/-bwd,
;;;     dist-seq-apply, dist-seq-in-fun), theorem-library/dominated-convergence
;;;     (398: rr-null-sum), theorem-library/metric-limit-unique (281),
;;;     theorem-library/rr-metric-space-proof (278: rr-is-metric-space),
;;;     theorem-library/rake-analysis-typing (268: rkt-cseq-is-set,
;;;     rkt-cauchy-setoid-pts, rkt-class-is-set, rkt-embed-seq-in-fun,
;;;     rkt-embed-seq-in-cseq), structure-library/metric-laws (266: metric-pos,
;;;     metric-self-zero, metric-sym, metric-triangle),
;;;     theorem-library/op-typing (200: metric-dist-real),
;;;     theorem-library/rr-abs-basics (179: rr-abs-bound),
;;;     theorem-library/pos-rr-bridges (178: rr-lt-of-pos-rr),
;;;     theorem-library/rake-setoid (166: class-unfold, proj-unfold,
;;;     quotient-unfold, respects-unfold, respects2-unfold, class-is-set,
;;;     descend-in-fun), theorem-library/pair-tuple-sethood (165:
;;;     pair-in-cartesian), theorem-library/fun-apply-type-proof (163:
;;;     fun-apply-type-c), theorem-library/binary-minus-laws (162: rr-sub-in-rr),
;;;     driver-kit (140: use-em and the dk- kit), structure-library/injection
;;;     (83: image-membership-iff), structure-library/setoid (25),
;;;     number-systems (34: rr-add-closed, rr-zero-in, nn-zero-in) and the base
;;;     theory (class-extensionality, fun-domain-extensionality, fun-codomain-iff,
;;;     power-set-membership, intersection-membership, empty-set-has-no-members,
;;;     subset-def, equality-symmetry, apply-tupling-2, cartesian-set-iff).
;;;   hi -- END.  NOTHING PROVEN in the tree cites any of the thirteen leaves.
;;;     Outside their own definition sites the only occurrences are `topic!' lines
;;;     in theorem-library/pss-topics.scm, `reference-topics.scm', comments in
;;;     structure-library/ringoid.scm, and
;;;     theorem-library/ringoid-quotient-ring-proof.scm -- which is NOT named in
;;;     load.scm and so is never loaded.
;;;
;;;   PART I ALONE would take [after theorem-library/rake-setoid, end); it is the
;;;   completion half that forces lo up to product-convergence.  Splitting the
;;;   file at the PART II banner is mechanical -- no helper and no citation
;;;   crosses it except the four `rko2-related-*' theorems of Part I, which
;;;   `rko2-class-eq-null' uses.
;;;
;;; SITES TO RETIRE -- the `support' form and its `warrant!' (scratchpad/retire.py
;;; takes the name; the line given is the `support' line).  Keep the `gloss!' of
;;; quotient-universal and the `notation!' block of metric-completion.scm.
;;;   structure-library/setoid.scm:90   class-self
;;;   structure-library/setoid.scm:99   class-subset-carrier
;;;   structure-library/setoid.scm:111  class-eq-iff
;;;   structure-library/setoid.scm:125  class-disjoint
;;;   structure-library/setoid.scm:137  class-in-quotient
;;;   structure-library/setoid.scm:148  quotient-rep
;;;   structure-library/setoid.scm:182  descend-computes
;;;   structure-library/setoid.scm:201  quotient-universal
;;;   structure-library/setoid.scm:258  descend2-computes
;;;   structure-library/metric-completion.scm:74   cauchy-setoid-is-setoid
;;;   structure-library/metric-completion.scm:151  embed-isometry -- NOT to be
;;;     retired on this file's account.  It is the DEFECTIVE statement, and the
;;;     user's call is whether to repair the term -- in which case
;;;     `embed-isometry-applied' below IS the repair, character for character --
;;;     or to leave it standing.
;;;
;;; Helper prefix `rko2-'.  All helpers are file-local.

(define (rko2-hyp h what) (dk-pick (dk-head? h) what))
(define (rko2-find pred what) (dk-pick pred what))
(define (rko2-in-head h)
  (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
                   (eq? (car (caddr f)) h))))
(define (rko2-goal-head? n h) (eq? (car (dk-goal-of n)) h))
(define (rko2-eq-to c)
  (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (caddr f) c))))
(define (rko2-foralls f)
  (cond ((not (pair? f)) 0)
        ((eq? (car f) 'FORALL) (+ 1 (rko2-foralls (caddr f))))
        (#t (apply + (map rko2-foralls (cdr f))))))
(define (rko2-depth n)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL) (= (rko2-foralls f) n))))
(define (rko2-equiv-conjuncts!)
  (mac-h 'IS-SETOID (rko2-hyp 'IS-SETOID "the IS-SETOID hypothesis"))
  (dk-split-all!)
  (mac-h 'IS-EQUIVALENCE (rko2-hyp 'IS-EQUIVALENCE "the is-equivalence conjunct"))
  (dk-split-all!))

;; hypothesis (IN x (CLASS s a)) -> (IN x (PTS s)) and (RELATED s a x)
(define (rko2-class-open! mem)
  (mac-h 'class-unfold mem)
  (sep-me (rko2-find (lambda (f) (and ((rko2-in-head 'SEP) f) (equal? (cadr f) (cadr mem))))
                     "the class membership, as a SEP"))
  (dk-split-all!))

;; hypothesis (IN c (QUOTIENT s)) -> a representative a, with (= (CLASS s a) c)
(define (rko2-rep! mem)
  (let ((c (cadr mem)))
    (mac-h 'quotient-unfold mem)
    (mac-h 'image-membership-iff
           (rko2-find (lambda (f) (and ((rko2-in-head 'IMAGE) f) (equal? (cadr f) c)))
                      "the image membership"))
    (let ((a (dk-skolem! (rko2-hyp 'FORSOME "the representative existential"))))
      (mac-h 'proj-unfold (rko2-find (rko2-eq-to c) "the PROJ equation"))
      (lam-b-h (rko2-find (rko2-eq-to c) "the beta redex"))
      a)))

(sp (make-wff '(FORALL s (FORALL a_ (FORALL b_
   (IFF (RELATED s a_ b_) (IN (LIST a_ b_) (REL s))))))))
(di) (mac 'RELATED) (prop)
(qed 'rko2-related-unfold)
(topic! 'rko2-related-unfold 'plumbing)

(sp (make-wff (forall-guarded '(s) '((IS-SETOID s))
  (forall-guarded '(a_) '((IN a_ (PTS s))) '(RELATED s a_ a_)))))
(dk-peel!)
(mac 'RELATED)
(let ((cs (rko2-equiv-conjuncts!)))
  (dk-apply! (or (any-pred (rko2-depth 1) cs) (error "rko2: no refl conjunct")) 'a_)
  (ass))
(qed 'rko2-refl)
(topic! 'rko2-refl 'plumbing)

(sp (make-wff (forall-guarded '(s) '((IS-SETOID s))
  (forall-guarded '(a_ b_) '((IN a_ (PTS s)) (IN b_ (PTS s)))
    '(IMPLIES (RELATED s a_ b_) (RELATED s b_ a_))))))
(dk-peel!)
(mac-h 'rko2-related-unfold (rko2-hyp 'RELATED "the RELATED hypothesis"))
(mac 'RELATED)
(let ((cs (rko2-equiv-conjuncts!)))
  (dk-apply! (or (any-pred (rko2-depth 2) cs) (error "rko2: no sym conjunct")) 'a_ 'b_)
  (ass))
(qed 'rko2-sym)
(topic! 'rko2-sym 'plumbing)

(sp (make-wff (forall-guarded '(s) '((IS-SETOID s))
  (forall-guarded '(a_ b_ c_)
      '((IN a_ (PTS s)) (IN b_ (PTS s)) (IN c_ (PTS s)))
    '(IMPLIES (RELATED s a_ b_) (IMPLIES (RELATED s b_ c_) (RELATED s a_ c_)))))))
(dk-peel!)
(mac-h 'rko2-related-unfold
       (rko2-find (lambda (f) (and (pair? f) (eq? (car f) 'RELATED)
                                   (eq? (cadddr f) 'b_))) "a ~ b"))
(mac-h 'rko2-related-unfold
       (rko2-find (lambda (f) (and (pair? f) (eq? (car f) 'RELATED)
                                   (eq? (cadddr f) 'c_))) "b ~ c"))
(mac 'RELATED)
(let ((cs (rko2-equiv-conjuncts!)))
  (have! '(AND (IN (LIST a_ b_) (REL s)) (IN (LIST b_ c_) (REL s))))
  (dk-apply! (or (any-pred (rko2-depth 3) cs) (error "rko2: no trans conjunct")) 'a_ 'b_ 'c_)
  (ass))
(qed 'rko2-trans)
(topic! 'rko2-trans 'plumbing)

;;; ---------------- class-self
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (IN a (CLASS s a))))))))
(dk-peel!)
(mac 'CLASS)
(let ((ls (dk-opened (lambda () (sep-mi)))))
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) ls))
  (ass)
  (dk-focus! (any-pred (lambda (n) (not (rko2-goal-head? n 'IN))) ls))
  (fact 'rko2-refl 's 'a)
  (ass))
(qed 'class-self)
(topic! 'class-self 'plumbing)

;;; ---------------- class-in-quotient
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (IN (CLASS s a) (QUOTIENT s))))))))
(dk-peel!)
(mac 'QUOTIENT)
(mac 'image-membership-iff)
(ew 'a)
(let ((cs (dk-opened (lambda () (di)))))
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) cs))
  (ass)
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) cs))
  (mac 'PROJ) (lam-b)
  (fact 'class-is-set 's 'a)
  (rfl))
(qed 'class-in-quotient)
(topic! 'class-in-quotient 'plumbing)

;;; ---------------- quotient-rep
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL x (IMPLIES (IN x (QUOTIENT s))
       (FORSOME a (AND (IN a (PTS s)) (= x (CLASS s a))))))))))
(dk-peel!)
(let ((aa (rko2-rep! (rko2-find (rko2-in-head 'QUOTIENT) "x in the quotient"))))
  (ew aa)
  (let ((cs (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) cs))
    (ass)
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) cs))
    (fact 'equality-symmetry (list 'CLASS 's aa) 'x)
    (ass)))
(qed 'quotient-rep)
(topic! 'quotient-rep 'set-quotient)

;;; ---------------- class-subset-carrier
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (SUBSET (CLASS s a) (PTS s))))))))
(dk-peel!)
(mac 'subset-def)
(dk-peel!)
(mac-h 'class-unfold (rko2-hyp 'IN "the class membership"))
(sep-me (rko2-find (rko2-in-head 'SEP) "the class membership as a SEP"))
(dk-split-all!)
(ass)
(qed 'class-subset-carrier)
(topic! 'class-subset-carrier 'plumbing)
(topic! 'class-subset-carrier 'plumbing)

;;; ---------------- class-eq-iff
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (FORALL b (IMPLIES (IN b (PTS s))
         (IFF (= (CLASS s a) (CLASS s b))
              (RELATED s a b))))))))))
(dk-peel!)
(let ((bs (dk-opened (lambda () (di)))))
  ;; (=>) equal classes: a in [a] = [b], so b ~ a, so a ~ b.
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'RELATED)) bs))
  (have! '(IN a (CLASS s b))
         (lambda ()
           (fact 'equality-symmetry '(CLASS s a) '(CLASS s b))
           (subst '(= (CLASS s b) (CLASS s a)))
           (fact 'class-self 's 'a)
           (ass)))
  (rko2-class-open! '(IN a (CLASS s b)))
  (fact 'rko2-sym 's 'b 'a)
  (ass)
  ;; (<=) a ~ b: the two separations have the same members.
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) bs))
  (have! '(FORALL x_ (IFF (IN x_ (CLASS s a)) (IN x_ (CLASS s b))))
    (lambda ()
      (di)
      (let ((ds (dk-opened (lambda () (di)))))
        (for-each
         (lambda (nd)
           (dk-focus! nd)
           (let* ((g (dk-goal))                     ; (IN x_ (CLASS s ?))
                  (tgt (caddr (caddr g)))           ; the target's representative
                  (src (if (eq? tgt 'a) 'b 'a)))
             (rko2-class-open! (list 'IN 'x_ (list 'CLASS 's src)))
             ;; from src ~ x_ and tgt ~ src  get  tgt ~ x_
             (if (eq? tgt 'b)
                 (fact 'rko2-sym 's 'a 'b)          ; b ~ a
                 (begin))                            ; a ~ b already in context
             (fact 'rko2-trans 's tgt src 'x_)
             (mac 'CLASS)
             (for-each (lambda (n2) (dk-focus! n2) (ass))
                       (dk-opened (lambda () (sep-mi))))))
         ds))))
  (fact 'class-extensionality '(CLASS s a) '(CLASS s b))
  (ass))
(qed 'class-eq-iff)
(topic! 'class-eq-iff 'set-quotient)

;;; ---------------- class-disjoint
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL a (IMPLIES (IN a (PTS s))
       (FORALL b (IMPLIES (IN b (PTS s))
         (OR (= (CLASS s a) (CLASS s b))
             (= (INTERSECTION (CLASS s a) (CLASS s b)) EMPTY-SET))))))))))
(dk-peel!)
(use-em '(RELATED s a b)
  (lambda ()
    (oi-l)
    (let* ((iffm (dk-fact! 'class-eq-iff 's 'a 'b))
           (ims  (dk-landed (lambda () (ai iffm)))))
      (detach! (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                              (pair? (caddr f)) (eq? (car (caddr f)) '=)))
                             ims)
                   (error "rko2: no (=> RELATED (= ...)) direction")))
      (ass)))
  (lambda ()
    (oi-r)
    (have! '(FORALL x_ (IFF (IN x_ (INTERSECTION (CLASS s a) (CLASS s b)))
                            (IN x_ EMPTY-SET)))
      (lambda ()
        (di)
        (let ((ds (dk-opened (lambda () (di)))))
          (dk-focus! (any-pred (lambda (n) (eq? (caddr (dk-goal-of n)) 'EMPTY-SET)) ds))
          (mac-h 'intersection-membership
                 '(IN x_ (INTERSECTION (CLASS s a) (CLASS s b))))
          (dk-split-all!)
          (rko2-class-open! '(IN x_ (CLASS s a)))
          (rko2-class-open! '(IN x_ (CLASS s b)))
          (fact 'rko2-sym 's 'b 'x_)
          (fact 'rko2-trans 's 'a 'x_ 'b)
          (pbc)
          (ai (rko2-find (lambda (f) (and (pair? f) (eq? (car f) 'NOT)
                                          (pair? (cadr f)) (eq? (car (cadr f)) 'RELATED)))
                         "the excluded-middle negation"))
          (dk-focus! (any-pred (lambda (n) (not (eq? (caddr (dk-goal-of n)) 'EMPTY-SET))) ds))
          (fact 'empty-set-has-no-members 'x_)
          (pbc)
          (ai '(NOT (IN x_ EMPTY-SET))))))
    (fact 'class-extensionality '(INTERSECTION (CLASS s a) (CLASS s b)) 'EMPTY-SET)
    (ass)))
(qed 'class-disjoint)
(topic! 'class-disjoint 'set-quotient)

;;; f(a) = f(a') for a' in [a]: the RESPECTS instance, on the current leaf.
;;; DESTRUCTIVE of the RESPECTS hypothesis (mac-h replaces what it unfolds).
(define (rko2-respects! a a2)
  (let ((ru (dk-landed-1
             (lambda () (mac-h 'respects-unfold
                               (rko2-hyp 'RESPECTS "the RESPECTS hypothesis"))))))
    (dk-apply! ru a a2)))

;;; ---------------- descend-computes
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (PTS s) Z)) (RESPECTS s f))
         (FORALL a (IMPLIES (IN a (PTS s))
           (= ((DESCEND s f) (CLASS s a)) (f a)))))))))))
(dk-peel!)
(dk-split-all!)
(fact 'class-in-quotient 's 'a)
(mac 'DESCEND)
(lam-b)
(let* ((it  (cadr (dk-goal)))
       (ls2 (dk-opened (lambda () (iota-d it)))))
  ;; (1) the defining property, granted
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) ls2))
  (let ((a1 (dk-skolem! (rko2-hyp 'FORSOME "the granted defining property"))))
    (rko2-class-open! (list 'IN a1 (list 'CLASS 's 'a)))
    (rko2-respects! 'a a1)
    (subst (list '= it (list 'f a1)))
    (fact 'equality-symmetry (list 'f 'a) (list 'f a1))
    (ass))
  ;; (2) existence and uniqueness of the description
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORSOME)) ls2))
  (ew '(f a))
  (let ((cs (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORSOME)) cs))
    (ew 'a)
    (let ((es (dk-opened (lambda () (di)))))
      (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) es))
      (fact 'class-self 's 'a)
      (ass)
      (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) es))
      (fact 'fun-apply-type-c 'f '(PTS s) 'Z 'a)
      (rfl))
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORALL)) cs))
    (dk-peel!)
    (let ((a2 (dk-skolem! (rko2-hyp 'FORSOME "the competing description"))))
      (rko2-class-open! (list 'IN a2 (list 'CLASS 's 'a)))
      (rko2-respects! 'a a2)
      (subst (list '= (caddr (dk-goal)) (list 'f a2)))
      (ass))))
(qed 'descend-computes)
(topic! 'descend-computes 'set-quotient)

;; goal (IN (ff a b) cod) for ff : CARTESIAN(dom,dom) -> cod -- op-typing's bridge.
(define (rko2-app2-close! ff a b dom cod)
  (fact 'apply-tupling-2 ff a b)
  (subst (list '== (list ff a b) (list ff (list 'LIST a b))))
  (fact 'pair-in-cartesian dom dom a b)
  (fact 'fun-apply-type-c ff (list 'CARTESIAN dom dom) cod (list 'LIST a b))
  (ass))
(define (rko2-app2-have! ff a b dom cod)
  (have! (list 'IN (list ff a b) cod)
         (lambda () (rko2-app2-close! ff a b dom cod))))

;; f(a,b) = f(a2,b2) from a ~ a2, b ~ b2.  DESTRUCTIVE of the RESPECTS2 hypothesis.
(define (rko2-respects2! a b a2 b2)
  (let ((ru (dk-landed-1
             (lambda () (mac-h 'respects2-unfold
                               (rko2-hyp 'RESPECTS2 "the RESPECTS2 hypothesis"))))))
    (have! (list 'AND (list 'RELATED 's a a2) (list 'RELATED 's b b2))
           (lambda () (dk-conj-close! (lambda () (ass)))))
    (dk-apply! ru a b a2 b2)))

;;; ---------------- descend2-computes
(sp (make-wff
  (forall-guarded '(s) '((IS-SETOID s))
    (forall-guarded '(Z f)
        '((IN f (FUN (CARTESIAN (PTS s) (PTS s)) Z)) (RESPECTS2 s f))
      (forall-guarded '(a b) '((IN a (PTS s)) (IN b (PTS s)))
        '(= ((DESCEND2 s f) (CLASS s a) (CLASS s b)) (f a b)))))))
(dk-peel!)
(fact 'class-in-quotient 's 'a)
(fact 'class-in-quotient 's 'b)
(mac 'DESCEND2)
(lam-b)
(let* ((it  (cadr (dk-goal)))
       (ls2 (dk-opened (lambda () (iota-d it)))))
  ;; (1) the defining property, granted
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) ls2))
  (let* ((a1 (dk-skolem! (rko2-hyp 'FORSOME "the granted property, outer")))
         (b1 (dk-skolem! (rko2-hyp 'FORSOME "the granted property, inner"))))
    (rko2-class-open! (list 'IN a1 (list 'CLASS 's 'a)))
    (rko2-class-open! (list 'IN b1 (list 'CLASS 's 'b)))
    (rko2-respects2! 'a 'b a1 b1)
    (subst (list '= it (list 'f a1 b1)))
    (fact 'equality-symmetry (list 'f 'a 'b) (list 'f a1 b1))
    (ass))
  ;; (2) existence and uniqueness
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORSOME)) ls2))
  (rko2-app2-have! 'f 'a 'b '(PTS s) 'Z)
  (ew '(f a b))
  (let ((cs (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORSOME)) cs))
    (ew 'a)
    (let ((es (dk-opened (lambda () (di)))))
      (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) es))
      (fact 'class-self 's 'a)
      (ass)
      (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORSOME)) es))
      (ew 'b)
      (let ((fs (dk-opened (lambda () (di)))))
        (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) fs))
        (fact 'class-self 's 'b)
        (ass)
        (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n '=)) fs))
        (rfl)))
    (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'FORALL)) cs))
    (dk-peel!)
    (let* ((a2 (dk-skolem! (rko2-hyp 'FORSOME "the competitor, outer")))
           (b2 (dk-skolem! (rko2-hyp 'FORSOME "the competitor, inner"))))
      (rko2-class-open! (list 'IN a2 (list 'CLASS 's 'a)))
      (rko2-class-open! (list 'IN b2 (list 'CLASS 's 'b)))
      (rko2-respects2! 'a 'b a2 b2)
      (subst (list '= (caddr (dk-goal)) (list 'f a2 b2)))
      (ass))))
(qed 'descend2-computes)
(topic! 'descend2-computes 'set-quotient)

;;; ---------------- quotient-universal
(sp (make-wff '(FORALL s (IMPLIES (IS-SETOID s)
     (FORALL Z (FORALL f
       (IMPLIES (AND (IN f (FUN (PTS s) Z)) (RESPECTS s f))
         (FORSOME g
           (AND (IN g (FUN (QUOTIENT s) Z))
             (AND
               (FORALL a (IMPLIES (IN a (PTS s))
                 (= (g (CLASS s a)) (f a))))
               (FORALL g_
                 (IMPLIES (AND (IN g_ (FUN (QUOTIENT s) Z))
                               (FORALL a (IMPLIES (IN a (PTS s))
                                 (= (g_ (CLASS s a)) (f a)))))
                          (= g_ g)))))))))))))
(dk-peel!)
(fact 'descend-in-fun 's 'Z 'f)
(ew '(DESCEND s f))
(let ((bs (dk-opened (lambda () (di)))))
  ;; (1) the typing
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'IN)) bs))
  (ass)
  ;; (2) factorization and uniqueness
  (dk-focus! (any-pred (lambda (n) (rko2-goal-head? n 'AND)) bs))
  (let ((cs (dk-opened (lambda () (di)))))
    ;; (2a) g([a]) = f(a)
    (dk-focus! (car (filter (lambda (n)
                              (let ((g (dk-goal-of n)))
                                (eq? (quantifier-var g) 'a))) cs)))
    (dk-peel!)
    (fact 'descend-computes 's 'Z 'f 'a)
    (ass)
    ;; (2b) uniqueness
    (dk-focus! (car (filter (lambda (n)
                              (let ((g (dk-goal-of n)))
                                (eq? (quantifier-var g) 'g_))) cs)))
    (let ((rko2-gfact
           (or (any-pred (dk-head? 'FORALL) (dk-split-all! (dk-peel!)))
               (error "rko2: no factorization hypothesis for g_"))))
    (have! '(IN g_ (FUN (QUOTIENT s)))
           (lambda () (mac-h 'fun-codomain-iff '(IN g_ (FUN (QUOTIENT s) Z)))
                      (dk-split-all!) (ass)))
    (have! '(IN (DESCEND s f) (FUN (QUOTIENT s)))
           (lambda () (mac-h 'fun-codomain-iff '(IN (DESCEND s f) (FUN (QUOTIENT s) Z)))
                      (dk-split-all!) (ass)))
    (have! '(FORALL x_ (IMPLIES (IN x_ (QUOTIENT s))
              (= (g_ x_) ((DESCEND s f) x_))))
      (lambda ()
        (dk-peel!)
        (let ((aa (dk-skolem! (dk-fact! 'quotient-rep 's 'x_))))
          (subst (list '= 'x_ (list 'CLASS 's aa)))
          (fact 'descend-computes 's 'Z 'f aa)
          (subst (list '= (list (list 'DESCEND 's 'f) (list 'CLASS 's aa)) (list 'f aa)))
          (dk-apply! rko2-gfact aa)
          (ass))))
    (fact 'fun-domain-extensionality '(QUOTIENT s) 'g_ '(DESCEND s f))
    (ass))))
(qed 'quotient-universal)
(topic! 'quotient-universal 'set-quotient)


;;; ==========================================================================
;;; PART II -- THE COMPLETION (structure-library/metric-completion.scm)
;;; ==========================================================================


;; (The two pair projections were re-proved here as `rko2-nth-pair-1' and
;; `rko2-nth-pair-2'; REMOVED 2026-09-20, batch 11: they were alpha-equal to
;; `nth1-pair' (theorem-library/mat-basics.scm:121) and `nth2-pair'
;; (theorem-library/tuple-extensionality.scm:108), both of which load long
;; before this file.  The four citations below name those.)

(sp (make-wff '(FORALL M (== (CSEQ M) (SEP f_ (FUN NN (PTS M)) (IS-CAUCHY-SEQ M f_))))))
(di) (mac 'CSEQ) (qrfl)
(qed 'rko2-cseq-unfold)
(topic! 'rko2-cseq-unfold 'plumbing)

(sp (make-wff '(FORALL M (FORALL f_ (IMPLIES (IN f_ (CSEQ M))
   (IN f_ (FUN NN (PTS M))))))))
(dk-peel!)
(mac-h 'rko2-cseq-unfold (rko2-hyp 'IN "f_ in CSEQ"))
(sep-me (rko2-find (rko2-in-head 'SEP) "the CSEQ membership as a SEP"))
(dk-split-all!)
(ass)
(qed 'rko2-cseq-in-fun)
(topic! 'rko2-cseq-in-fun 'analysis)

(sp (make-wff '(FORALL M (== (DIST (COMPLETION M)) (COMPLETION-DIST M)))))
(di) (mac 'COMPLETION) (slot 'DIST) (nth-r) (qrfl)
(qed 'rko2-completion-dist)
(topic! 'rko2-completion-dist 'plumbing)

(sp (make-wff '(FORALL M (== (REL (CAUCHY-SETOID M)) (CREL M)))))
(di) (mac 'CAUCHY-SETOID) (slot 'REL) (nth-r) (qrfl)
(qed 'rko2-cauchy-setoid-rel)
(topic! 'rko2-cauchy-setoid-rel 'plumbing)

(sp (make-wff '(FORALL M (== (CREL M)
   (SEP p_ (CARTESIAN (CSEQ M) (CSEQ M)) (CSEQ-EQUIV M (NTH 1 p_) (NTH 2 p_)))))))
(di) (mac 'CREL) (qrfl)
(qed 'rko2-crel-unfold)
(topic! 'rko2-crel-unfold 'plumbing)

(sp (make-wff '(FORALL M (FORALL p_ (FORALL q_
   (IMPLIES (IN p_ (CSEQ M)) (IMPLIES (IN q_ (CSEQ M))
     (IMPLIES (CSEQ-EQUIV M p_ q_) (IN (LIST p_ q_) (CREL M))))))))))
(dk-peel!)
(mac 'CREL)
(for-each (lambda (rko2-leaf)
            (dk-focus! rko2-leaf)
            (if (eq? (car (dk-goal)) 'IN)
                (begin (fact 'pair-in-cartesian '(CSEQ M) '(CSEQ M) 'p_ 'q_) (ass))
                (begin (mac 'nth1-pair) (mac 'nth2-pair) (ass))))
          (dk-opened (lambda () (sep-mi))))
(qed 'rko2-crel-intro)
(topic! 'rko2-crel-intro 'plumbing)

(sp (make-wff '(FORALL M (FORALL p_ (FORALL q_
   (IMPLIES (IN (LIST p_ q_) (CREL M)) (CSEQ-EQUIV M p_ q_)))))))
(dk-peel!)
(mac-h 'rko2-crel-unfold (rko2-hyp 'IN "the CREL membership"))
(sep-me (rko2-find (rko2-in-head 'SEP) "the CREL membership as a SEP"))
(dk-split-all!)
(mac-h 'nth1-pair (rko2-hyp 'CSEQ-EQUIV "the null-distance body"))
(mac-h 'nth2-pair (rko2-hyp 'CSEQ-EQUIV "the null-distance body"))
(ass)
(qed 'rko2-crel-elim)
(topic! 'rko2-crel-elim 'plumbing)

;;; the length conjunct and the two sethoods
(sp (make-wff '(FORALL M (= (LENGTH (CAUCHY-SETOID M)) 2))))
(di) (mac 'CAUCHY-SETOID) (len-r) (rfl)
(qed 'rko2-cauchy-setoid-length)
(topic! 'rko2-cauchy-setoid-length 'plumbing)

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M) (IN (CREL M) SET)))))
(dk-peel!)
(fact 'rkt-cseq-is-set 'M)
(mac 'CREL) (sep-set) (mac 'cartesian-set-iff) (prop)
(qed 'rko2-crel-is-set)
(topic! 'rko2-crel-is-set 'plumbing)


;; rr-add-closed has an AND antecedent, which `fact' will not split.
(define (rko2-add-in-rr! x y)
  (have! (list 'AND (list 'IN x 'RR) (list 'IN y 'RR)))
  (fact 'rr-add-closed x y))

(sp (make-wff '(FORALL M (FORALL f_ (FORALL g_
   (== (DIST-SEQ M f_ g_) (VNB-LAMBDA n_ NN ((DIST M) (f_ n_) (g_ n_)))))))))
(di) (mac 'DIST-SEQ) (qrfl)
(qed 'rko2-dist-seq-unfold)
(topic! 'rko2-dist-seq-unfold 'plumbing)

(sp (make-wff '(FORALL M (FORALL f_ (FORALL g_
   (IMPLIES (IS-METRIC-SPACE M)
     (IMPLIES (IN f_ (FUN NN (PTS M)))
       (IMPLIES (IN g_ (FUN NN (PTS M)))
         (IN (DIST-SEQ M f_ g_) (FUN NN RR))))))))))
(dk-peel!)
(mac 'DIST-SEQ)
(dk-lam-t!)
(let ((n_ (dk-di-var!)))
  (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) n_)
  (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) n_)
  (fact 'metric-dist-real 'M (list 'f_ n_) (list 'g_ n_))
  (ass))
(qed 'rko2-dist-seq-type)
(topic! 'rko2-dist-seq-type 'analysis)

(sp (make-wff (forall-guarded '(M f_ g_ n_) '((IN n_ NN))
   '(== ((DIST-SEQ M f_ g_) n_) ((DIST M) (f_ n_) (g_ n_))))))
(dk-peel!)
(mac 'DIST-SEQ) (lam-b) (qrfl)
(qed 'rko2-dist-seq-at)
(topic! 'rko2-dist-seq-at 'plumbing)

;;; d(f_n, f_n) -> 0: the null-distance relation is REFLEXIVE.
(sp (make-wff '(FORALL M (FORALL f_ (IMPLIES (IS-METRIC-SPACE M)
   (IMPLIES (IN f_ (FUN NN (PTS M)))
     (CONVERGES-TO RR-MS (DIST-SEQ M f_ f_) 0)))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(have! '(IN (DIST-SEQ M f_ f_) (FUN NN (PTS RR-MS)))
       (lambda () (slot 'PTS) (fact 'rko2-dist-seq-type 'M 'f_ 'f_) (ass)))
(mac 'CONVERGES-TO)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (car (dk-goal)) 'FORALL))
       (ass)
       (begin
         (di) (di)
         (fact 'nn-zero-in)
         (ew 0)
         (for-each
          (lambda (rko2-leaf)
            (dk-focus! rko2-leaf)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (let ((n_ (dk-di-var!)))
                  (di)
                  (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) n_)
                  (mac 'rko2-dist-seq-at)
                  (fact 'metric-self-zero 'M (list 'f_ n_))
                  (subst (list '= (list (list 'DIST 'M) (list 'f_ n_) (list 'f_ n_)) 0))
                  (fact 'metric-self-zero 'RR-MS 0)
                  (subst '(= ((DIST RR-MS) 0 0) 0))
                  (fact 'rr-lt-of-pos-rr 'eps)
                  (dk-split! (dk-landed-1 (lambda () (mac-h '< '(< 0 eps)))))
                  (ass))))
          (dk-opened (lambda () (di))))))))
(qed 'rko2-null-refl)
(topic! 'rko2-null-refl 'analysis)

;;; SYMMETRY of the null-distance relation.
(sp (make-wff '(FORALL M (FORALL f_ (FORALL g_ (IMPLIES (IS-METRIC-SPACE M)
   (IMPLIES (IN f_ (FUN NN (PTS M)))
     (IMPLIES (IN g_ (FUN NN (PTS M)))
       (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) 0)
                (CONVERGES-TO RR-MS (DIST-SEQ M g_ f_) 0))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(have! '(IN (DIST-SEQ M f_ g_) (FUN NN (PTS RR-MS)))
       (lambda () (slot 'PTS) (fact 'rko2-dist-seq-type 'M 'f_ 'g_) (ass)))
(have! '(IN (DIST-SEQ M g_ f_) (FUN NN (PTS RR-MS)))
       (lambda () (slot 'PTS) (fact 'rko2-dist-seq-type 'M 'g_ 'f_) (ass)))
(have! '(FORALL j_ (IMPLIES (IN j_ NN)
          (= ((DIST-SEQ M g_ f_) j_) ((DIST-SEQ M f_ g_) j_))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j_)
      (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) j_)
      (mac 'rko2-dist-seq-at)
      (fact 'metric-sym 'M (list 'g_ j_) (list 'f_ j_))
      (ass))))
(fact 'converges-to-transfer 'RR-MS '(DIST-SEQ M f_ g_) '(DIST-SEQ M g_ f_) 0)
(ass)
(qed 'rko2-null-sym)
(topic! 'rko2-null-sym 'analysis)

;;; TRANSITIVITY of the null-distance relation.
(define rko2-bsum
  '(VNB-LAMBDA j_ NN (+ ((DIST-SEQ M f_ g_) j_) ((DIST-SEQ M g_ h_) j_))))

(sp (make-wff '(FORALL M (FORALL f_ (FORALL g_ (FORALL h_
   (IMPLIES (IS-METRIC-SPACE M)
     (IMPLIES (IN f_ (FUN NN (PTS M)))
       (IMPLIES (IN g_ (FUN NN (PTS M)))
         (IMPLIES (IN h_ (FUN NN (PTS M)))
           (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) 0)
             (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M g_ h_) 0)
                      (CONVERGES-TO RR-MS (DIST-SEQ M f_ h_) 0)))))))))))))
(dk-peel!)
(fact 'rko2-dist-seq-type 'M 'f_ 'g_)
(fact 'rko2-dist-seq-type 'M 'g_ 'h_)
(fact 'rko2-dist-seq-type 'M 'f_ 'h_)
;; the pointwise sum is a real sequence
(have! (list 'IN rko2-bsum '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c '(DIST-SEQ M f_ g_) 'NN 'RR j_)
      (fact 'fun-apply-type-c '(DIST-SEQ M g_ h_) 'NN 'RR j_)
      (rko2-add-in-rr! (list '(DIST-SEQ M f_ g_) j_) (list '(DIST-SEQ M g_ h_) j_))
      (ass))))
;; ... and it is the pointwise sum
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list '= (list rko2-bsum 'j_)
               '(+ ((DIST-SEQ M f_ g_) j_) ((DIST-SEQ M g_ h_) j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c '(DIST-SEQ M f_ g_) 'NN 'RR j_)
      (fact 'fun-apply-type-c '(DIST-SEQ M g_ h_) 'NN 'RR j_)
      (rko2-add-in-rr! (list '(DIST-SEQ M f_ g_) j_) (list '(DIST-SEQ M g_ h_) j_))
      (lam-b)
      (rfl))))
(fact 'rr-null-sum '(DIST-SEQ M f_ g_) '(DIST-SEQ M g_ h_) rko2-bsum)
;; the triangle bound, pointwise
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'AND '(<= 0 ((DIST-SEQ M f_ h_) j_))
               (list '<= '((DIST-SEQ M f_ h_) j_) (list rko2-bsum 'j_)))))
  (lambda ()
    (let ((j_ (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j_)
      (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) j_)
      (fact 'fun-apply-type-c 'h_ 'NN '(PTS M) j_)
      (fact 'fun-apply-type-c '(DIST-SEQ M f_ g_) 'NN 'RR j_)
      (fact 'fun-apply-type-c '(DIST-SEQ M g_ h_) 'NN 'RR j_)
      (rko2-add-in-rr! (list '(DIST-SEQ M f_ g_) j_) (list '(DIST-SEQ M g_ h_) j_))
      (lam-b)
      (mac 'rko2-dist-seq-at)
      (for-each
       (lambda (rko2-leaf)
         (dk-focus! rko2-leaf)
         (if (equal? (cadr (dk-goal)) 0)
             (begin (fact 'metric-pos 'M (list 'f_ j_) (list 'h_ j_)) (ass))
             (begin (fact 'metric-triangle 'M (list 'f_ j_) (list 'g_ j_) (list 'h_ j_))
                    (ass))))
       (dk-opened (lambda () (di)))))))
(fact 'rr-null-squeeze rko2-bsum '(DIST-SEQ M f_ h_))
(ass)
(qed 'rko2-null-trans)
(topic! 'rko2-null-trans 'analysis)

;;; ---------------- cauchy-setoid-is-setoid

;; goal (CSEQ-EQUIV M p q), with the CONVERGES-TO in context
(define (rko2-equiv-from-null! p q)
  (have! (list 'CSEQ-EQUIV 'M p q) (lambda () (mac 'CSEQ-EQUIV) (ass))))

(define (rko2-equiv-leaf!)
  (let ((g (dk-goal)))
    (cond
     ;; (a) CREL is a relation ON CSEQ
     ((eq? (car g) 'IN)
      (mac 'power-set-membership)
      (dk-conj-close!
       (lambda ()
         (if (eq? (car (dk-goal)) 'IN)
             (ass)
             (let ((mem (car (dk-peel!))))
               (mac-h 'rko2-crel-unfold mem)
               (sep-me (rko2-find (rko2-in-head 'SEP) "the CREL membership as a SEP"))
               (dk-split-all!)
               (ass))))))
     ;; (b) reflexive
     ((= (rko2-foralls g) 1)
      (dk-peel!)
      (let ((u (cadr (cadr (dk-goal)))))
        (fact 'rko2-cseq-in-fun 'M u)
        (have! (list 'CSEQ-EQUIV 'M u u)
               (lambda () (mac 'CSEQ-EQUIV) (fact 'rko2-null-refl 'M u) (ass)))
        (fact 'rko2-crel-intro 'M u u)
        (ass)))
     ;; (c) symmetric
     ((= (rko2-foralls g) 2)
      (dk-peel!)
      (let* ((gg (dk-goal))
             (v  (cadr (cadr gg)))
             (u  (caddr (cadr gg))))
        (fact 'rko2-cseq-in-fun 'M u)
        (fact 'rko2-cseq-in-fun 'M v)
        (fact 'rko2-crel-elim 'M u v)
        (mac-h 'CSEQ-EQUIV (list 'CSEQ-EQUIV 'M u v))
        (fact 'rko2-null-sym 'M u v)
        (rko2-equiv-from-null! v u)
        (fact 'rko2-crel-intro 'M v u)
        (ass)))
     ;; (d) transitive
     (#t
      (let* ((landed (dk-peel!))
             (gg (dk-goal))
             (u  (cadr (cadr gg)))
             (w  (caddr (cadr gg)))
             (cj (or (any-pred (dk-head? 'AND) landed)
                     (error "rko2: no AND antecedent in the transitivity conjunct")))
             (v  (caddr (cadr (cadr cj)))))
        (dk-split-all! (list cj))
        (fact 'rko2-cseq-in-fun 'M u)
        (fact 'rko2-cseq-in-fun 'M v)
        (fact 'rko2-cseq-in-fun 'M w)
        (fact 'rko2-crel-elim 'M u v)
        (fact 'rko2-crel-elim 'M v w)
        (mac-h 'CSEQ-EQUIV (list 'CSEQ-EQUIV 'M u v))
        (mac-h 'CSEQ-EQUIV (list 'CSEQ-EQUIV 'M v w))
        (fact 'rko2-null-trans 'M u v w)
        (rko2-equiv-from-null! u w)
        (fact 'rko2-crel-intro 'M u w)
        (ass))))))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (IS-SETOID (CAUCHY-SETOID M))))))
(dk-peel!)
(fact 'rkt-cseq-is-set 'M)
(fact 'rko2-crel-is-set 'M)
(fact 'rko2-cauchy-setoid-length 'M)
(mac 'IS-SETOID)
(mac 'rkt-cauchy-setoid-pts)
(mac 'rko2-cauchy-setoid-rel)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (car (dk-goal)) 'IS-EQUIVALENCE))
       (ass)
       (begin (mac 'IS-EQUIVALENCE)
              (dk-conj-close! (lambda () (rko2-equiv-leaf!)))))))
(qed 'cauchy-setoid-is-setoid)
(topic! 'cauchy-setoid-is-setoid 'set-quotient)


(define (rko2-d x y) (list '(DIST M) x y))
(define (rko2-dist-real! x y) (fact 'metric-dist-real 'M x y))
;; `ineq' takes 1-BASED context INDICES, not formulas (ineq-oracle.scm:206).
(define (rko2-idx f)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "rko2-idx: not in context" f))
          ((equal? (car l) f) i)
          (#t (loop (cdr l) (+ i 1))))))
(define (rko2-ineq . forms) (apply ineq (map rko2-idx forms)))

;;; the QUADRILATERAL inequality:  |d(a,b) - d(c,e)| <= d(a,c) + d(b,e).
(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(a_ b_ c_ e_)
      '((IN a_ (PTS M)) (IN b_ (PTS M)) (IN c_ (PTS M)) (IN e_ (PTS M)))
    '(<= (abs (- ((DIST M) a_ b_) ((DIST M) c_ e_)))
         (+ ((DIST M) a_ c_) ((DIST M) b_ e_)))))))
(dk-peel!)
(for-each (lambda (p) (rko2-dist-real! (car p) (cadr p)))
          '((a_ b_) (c_ e_) (a_ c_) (b_ e_) (c_ b_) (e_ b_) (c_ a_) (a_ e_)))
(fact 'metric-triangle 'M 'a_ 'c_ 'b_)
(fact 'metric-triangle 'M 'c_ 'e_ 'b_)
(fact 'metric-triangle 'M 'c_ 'a_ 'e_)
(fact 'metric-triangle 'M 'a_ 'b_ 'e_)
(fact 'metric-sym 'M 'e_ 'b_)
(fact 'metric-sym 'M 'c_ 'a_)
(fact 'rr-sub-in-rr (rko2-d 'a_ 'b_) (rko2-d 'c_ 'e_))
(have! (list 'AND (list 'IN (rko2-d 'a_ 'c_) 'RR) (list 'IN (rko2-d 'b_ 'e_) 'RR)))
(fact 'rr-add-closed (rko2-d 'a_ 'c_) (rko2-d 'b_ 'e_))
(let* ((x (list '- (rko2-d 'a_ 'b_) (rko2-d 'c_ 'e_)))
       (c (list '+ (rko2-d 'a_ 'c_) (rko2-d 'b_ 'e_)))
       (iffm (dk-fact! 'rr-abs-bound x c))
       (ims (dk-landed (lambda () (ai iffm)))))
  (have! (list 'AND (list '<= (list '- c) x) (list '<= x c))
         (lambda ()
           (dk-conj-close!
            (lambda ()
              (rko2-ineq
               (list '<= (rko2-d 'a_ 'b_) (list '+ (rko2-d 'a_ 'c_) (rko2-d 'c_ 'b_)))
               (list '<= (rko2-d 'c_ 'b_) (list '+ (rko2-d 'c_ 'e_) (rko2-d 'e_ 'b_)))
               (list '<= (rko2-d 'c_ 'e_) (list '+ (rko2-d 'c_ 'a_) (rko2-d 'a_ 'e_)))
               (list '<= (rko2-d 'a_ 'e_) (list '+ (rko2-d 'a_ 'b_) (rko2-d 'b_ 'e_)))
               (list '= (rko2-d 'e_ 'b_) (rko2-d 'b_ 'e_))
               (list '= (rko2-d 'c_ 'a_) (rko2-d 'a_ 'c_)))))))
  (detach! (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                          (pair? (caddr f)) (eq? (car (caddr f)) '<=)
                                          (pair? (cadr (caddr f)))
                                          (eq? (car (cadr (caddr f))) 'abs)))
                         ims)
              (error "rko2: no abs-bound direction")))
  (ass))
(qed 'rko2-quad)
(topic! 'rko2-quad 'analysis)

(define (rko2-redex? t)                 ; does the term hold a beta redex?
  (and (pair? t)
       (or (and (pair? (car t)) (eq? (caar t) 'VNB-LAMBDA))
           (let lp ((l t))
             (and (pair? l) (or (rko2-redex? (car l)) (lp (cdr l))))))))
(define (rko2-beta!)                    ; beta to exhaustion, never a no-op call
  (let lp () (if (rko2-redex? (dk-goal)) (begin (lam-b) (lp)))))


(define rko2-lf '(VNB-LAMBDA j_ NN ((DIST M) (f_ j_) a_)))
(define rko2-lg '(VNB-LAMBDA j_ NN ((DIST M) (g_ j_) b_)))
(define rko2-ls (list 'VNB-LAMBDA 'j_ 'NN (list '+ (list rko2-lf 'j_) (list rko2-lg 'j_))))
(define rko2-lt '(VNB-LAMBDA j_ NN ((DIST RR-MS) ((DIST-SEQ M f_ g_) j_) ((DIST M) a_ b_))))

(sp (make-wff (forall-guarded '(M) '((IS-METRIC-SPACE M))
  (forall-guarded '(f_ g_ a_ b_)
      '((IN f_ (FUN NN (PTS M))) (IN g_ (FUN NN (PTS M)))
        (IN a_ (PTS M)) (IN b_ (PTS M)))
    '(IMPLIES (CONVERGES-TO M f_ a_)
       (IMPLIES (CONVERGES-TO M g_ b_)
         (CONVERGES-TO RR-MS (DIST-SEQ M f_ g_) ((DIST M) a_ b_))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'metric-dist-real 'M 'a_ 'b_)
(have! '(IN ((DIST M) a_ b_) (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'rko2-dist-seq-type 'M 'f_ 'g_)
(have! '(IN (DIST-SEQ M f_ g_) (FUN NN (PTS RR-MS))) (lambda () (slot 'PTS) (ass)))
(fact 'converges-dist-null-fwd 'M 'f_ 'a_)
(fact 'converges-dist-null-fwd 'M 'g_ 'b_)
(fact 'dist-seq-in-fun 'M 'f_ 'a_)
(fact 'dist-seq-in-fun 'M 'g_ 'b_)
(fact 'dist-seq-in-fun 'RR-MS '(DIST-SEQ M f_ g_) '((DIST M) a_ b_))
;; the pointwise sum of the two null distance sequences
(have! (list 'IN rko2-ls '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j (dk-di-var!)))
      (fact 'fun-apply-type-c rko2-lf 'NN 'RR j)
      (fact 'fun-apply-type-c rko2-lg 'NN 'RR j)
      (rko2-add-in-rr! (list rko2-lf j) (list rko2-lg j))
      (ass))))
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list '= (list rko2-ls 'j_) (list '+ (list rko2-lf 'j_) (list rko2-lg 'j_)))))
  (lambda ()
    (let ((j (dk-di-var!)))
      (fact 'fun-apply-type-c rko2-lf 'NN 'RR j)
      (fact 'fun-apply-type-c rko2-lg 'NN 'RR j)
      (rko2-add-in-rr! (list rko2-lf j) (list rko2-lg j))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j)
      (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) j)
      (fact 'metric-dist-real 'M (list 'f_ j) 'a_)
      (fact 'metric-dist-real 'M (list 'g_ j) 'b_)
      (rko2-add-in-rr! (list '(DIST M) (list 'f_ j) 'a_)
                       (list '(DIST M) (list 'g_ j) 'b_))
      (rko2-beta!)
      (rfl))))
(fact 'rr-null-sum rko2-lf rko2-lg rko2-ls)
;; the squeeze
(have! (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
         (list 'AND (list '<= 0 (list rko2-lt 'j_))
               (list '<= (list rko2-lt 'j_) (list rko2-ls 'j_)))))
  (lambda ()
    (let ((j (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j)
      (fact 'fun-apply-type-c 'g_ 'NN '(PTS M) j)
      (fact 'metric-dist-real 'M (list 'f_ j) (list 'g_ j))
      (fact 'fun-apply-type-c '(DIST-SEQ M f_ g_) 'NN 'RR j)
      (have! (list 'IN (list '(DIST-SEQ M f_ g_) j) '(PTS RR-MS))
             (lambda () (slot 'PTS) (ass)))
      (rko2-beta!)
      (for-each
       (lambda (rko2-leaf)
         (dk-focus! rko2-leaf)
         (if (equal? (cadr (dk-goal)) 0)
             (begin (fact 'metric-pos 'RR-MS (list '(DIST-SEQ M f_ g_) j) '((DIST M) a_ b_))
                    (ass))
             (begin (mac 'rko2-dist-seq-at)
                    (mac 'rr-ms-dist)
                    (fact 'rko2-quad 'M (list 'f_ j) (list 'g_ j) 'a_ 'b_)
                    (ass))))
       (dk-opened (lambda () (di)))))))
(fact 'rr-null-squeeze rko2-ls rko2-lt)
(fact 'converges-dist-null-bwd 'RR-MS '(DIST-SEQ M f_ g_) '((DIST M) a_ b_))
(ass)
(qed 'rko2-dist-converges)
(topic! 'rko2-dist-converges 'analysis)

;;; A. the constant sequence converges to its point
(sp (make-wff '(FORALL M (FORALL u_ (IMPLIES (IS-METRIC-SPACE M)
   (IMPLIES (IN u_ (PTS M))
     (CONVERGES-TO M (EMBED-SEQ M u_) u_)))))))
(dk-peel!)
(fact 'rkt-embed-seq-in-fun 'M 'u_)
(mac 'CONVERGES-TO)
(dk-conj-close!
 (lambda ()
   (if (not (eq? (car (dk-goal)) 'FORALL))
       (ass)
       (begin
         (di) (di)
         (fact 'nn-zero-in)
         (ew 0)
         (for-each
          (lambda (rko2-leaf)
            (dk-focus! rko2-leaf)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (begin
                  (dk-di-var!)
                  (di)
                  (mac 'EMBED-SEQ)
                  (lam-b)
                  (fact 'metric-self-zero 'M 'u_)
                  (subst '(= ((DIST M) u_ u_) 0))
                  (fact 'rr-lt-of-pos-rr 'eps)
                  (dk-split! (dk-landed-1 (lambda () (mac-h '< '(< 0 eps)))))
                  (ass))))
          (dk-opened (lambda () (di))))))))
(qed 'rko2-const-seq-converges)
(topic! 'rko2-const-seq-converges 'analysis)

;;; B. equal classes in the Cauchy setoid are null-distance apart
(sp (make-wff '(FORALL M (FORALL p_ (FORALL q_ (IMPLIES (IS-METRIC-SPACE M)
   (IMPLIES (IN p_ (CSEQ M)) (IMPLIES (IN q_ (CSEQ M))
     (IMPLIES (= (CLASS (CAUCHY-SETOID M) p_) (CLASS (CAUCHY-SETOID M) q_))
              (CONVERGES-TO RR-MS (DIST-SEQ M p_ q_) 0))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(have! '(IN p_ (PTS (CAUCHY-SETOID M))) (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(have! '(IN q_ (PTS (CAUCHY-SETOID M))) (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(let* ((iffm (dk-fact! 'class-eq-iff '(CAUCHY-SETOID M) 'p_ 'q_))
       (ims  (dk-landed (lambda () (ai iffm)))))
  (detach! (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES)
                                          (pair? (caddr f)) (eq? (car (caddr f)) 'RELATED)))
                         ims)
               (error "rko2: no (= => RELATED) direction of class-eq-iff"))))
(mac-h 'rko2-related-unfold '(RELATED (CAUCHY-SETOID M) p_ q_))
(mac-h 'rko2-cauchy-setoid-rel '(IN (LIST p_ q_) (REL (CAUCHY-SETOID M))))
(fact 'rko2-crel-elim 'M 'p_ 'q_)
(mac-h 'CSEQ-EQUIV '(CSEQ-EQUIV M p_ q_))
(ass)
(qed 'rko2-class-eq-null)
(topic! 'rko2-class-eq-null 'analysis)

;;; C. a Cauchy sequence at null distance from the constant sequence at u
;;;    converges to u
(sp (make-wff '(FORALL M (FORALL u_ (FORALL f_ (IMPLIES (IS-METRIC-SPACE M)
   (IMPLIES (IN u_ (PTS M)) (IMPLIES (IN f_ (FUN NN (PTS M)))
     (IMPLIES (CONVERGES-TO RR-MS (DIST-SEQ M (EMBED-SEQ M u_) f_) 0)
              (CONVERGES-TO M f_ u_))))))))))
(dk-peel!)
(fact 'rr-is-metric-space)
(fact 'rr-zero-in)
(have! '(IN 0 (PTS RR-MS)) (lambda () (slot 'PTS) (ass)))
(fact 'rkt-embed-seq-in-fun 'M 'u_)
(fact 'rko2-dist-seq-type 'M '(EMBED-SEQ M u_) 'f_)
(have! '(IN (DIST-SEQ M (EMBED-SEQ M u_) f_) (FUN NN (PTS RR-MS)))
       (lambda () (slot 'PTS) (ass)))
(fact 'dist-seq-in-fun 'M 'f_ 'u_)
(have! '(IN (VNB-LAMBDA j_ NN ((DIST M) (f_ j_) u_)) (FUN NN (PTS RR-MS)))
       (lambda () (slot 'PTS) (ass)))
(have! '(FORALL j_ (IMPLIES (IN j_ NN)
          (= ((VNB-LAMBDA j_ NN ((DIST M) (f_ j_) u_)) j_)
             ((DIST-SEQ M (EMBED-SEQ M u_) f_) j_))))
  (lambda ()
    (let ((j (dk-di-var!)))
      (fact 'fun-apply-type-c 'f_ 'NN '(PTS M) j)
      (mac 'rko2-dist-seq-at)
      (mac 'EMBED-SEQ)
      (rko2-beta!)
      (fact 'metric-sym 'M (list 'f_ j) 'u_)
      (ass))))
(fact 'converges-to-transfer 'RR-MS '(DIST-SEQ M (EMBED-SEQ M u_) f_)
      '(VNB-LAMBDA j_ NN ((DIST M) (f_ j_) u_)) 0)
(fact 'converges-dist-null-bwd 'M 'f_ 'u_)
(ass)
(qed 'rko2-const-equiv-converges)
(topic! 'rko2-const-equiv-converges 'analysis)

;;; ---------------- embed-isometry (THE APPLICATION CORRECTED -- see header)
;;; given representatives f1, g1 of [const u] and [const v], the real distance
;;; sequence converges to d(u,v).
(define (rko2-embed-limit! f1 g1)
  (fact 'rko2-cseq-in-fun 'M f1)
  (fact 'rko2-cseq-in-fun 'M g1)
  (fact 'rko2-class-eq-null 'M '(EMBED-SEQ M u) f1)
  (fact 'rko2-class-eq-null 'M '(EMBED-SEQ M v) g1)
  (fact 'rko2-const-equiv-converges 'M 'u f1)
  (fact 'rko2-const-equiv-converges 'M 'v g1)
  (fact 'rko2-dist-converges 'M f1 g1 'u 'v))

(define (rko2-exist-leaf!)
  (let ((g (dk-goal)))
    (cond ((eq? (car g) 'FORSOME)
           (ew '(EMBED-SEQ M v))
           (dk-conj-close! rko2-exist-leaf!))
          ((eq? (car g) 'IN) (ass))
          ((eq? (car g) '=)
           (fact 'rkt-class-is-set 'M (caddr (caddr g)))
           (rfl))
          (#t
           (fact 'rko2-const-seq-converges 'M 'u)
           (fact 'rko2-const-seq-converges 'M 'v)
           (fact 'rko2-dist-converges 'M '(EMBED-SEQ M u) '(EMBED-SEQ M v) 'u 'v)
           (ass)))))

(sp (make-wff '(FORALL M (IMPLIES (IS-METRIC-SPACE M)
     (FORALL u (IMPLIES (IN u (PTS M))
       (FORALL v (IMPLIES (IN v (PTS M))
         (= ((DIST (COMPLETION M)) ((EMBED M) u) ((EMBED M) v))
            ((DIST M) u v))))))))))
(dk-peel!)
(fact 'cauchy-setoid-is-setoid 'M)
(fact 'rkt-embed-seq-in-fun 'M 'u)
(fact 'rkt-embed-seq-in-fun 'M 'v)
(fact 'rkt-embed-seq-in-cseq 'M 'u)
(fact 'rkt-embed-seq-in-cseq 'M 'v)
(fact 'metric-dist-real 'M 'u 'v)
(have! '(IN (EMBED-SEQ M u) (PTS (CAUCHY-SETOID M)))
       (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(have! '(IN (EMBED-SEQ M v) (PTS (CAUCHY-SETOID M)))
       (lambda () (mac 'rkt-cauchy-setoid-pts) (ass)))
(fact 'class-in-quotient '(CAUCHY-SETOID M) '(EMBED-SEQ M u))
(fact 'class-in-quotient '(CAUCHY-SETOID M) '(EMBED-SEQ M v))
(mac 'rko2-completion-dist)
(mac 'EMBED)
(rko2-beta!)
(let* ((cu '(CLASS (CAUCHY-SETOID M) (EMBED-SEQ M u)))
       (cv '(CLASS (CAUCHY-SETOID M) (EMBED-SEQ M v)))
       (q  '(QUOTIENT (CAUCHY-SETOID M))))
  (fact 'apply-tupling-2 '(COMPLETION-DIST M) cu cv)
  (subst (list '== (list '(COMPLETION-DIST M) cu cv)
               (list '(COMPLETION-DIST M) (list 'LIST cu cv))))
  (fact 'pair-in-cartesian q q cu cv)
  (mac 'COMPLETION-DIST)
  (lam-b)
  (nth-r)
  (let* ((it  (cadr (dk-goal)))
         (ls2 (dk-opened (lambda () (iota-d it)))))
    ;; (1) the description's property, granted
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) '=)) ls2))
    (let* ((a1 (dk-skolem! (rko2-hyp 'FORSOME "the granted property, outer")))
           (b1 (dk-skolem! (rko2-hyp 'FORSOME "the granted property, inner"))))
      ;; 2026-09-18 (LUTINS instantiation): metric-limit-unique is cited at the
      ;; IOTA term, which is never certified defined by shape.  The property
      ;; `iota-d' granted carries the typing one unfold down -- CONVERGES-TO's
      ;; third conjunct is (IN L (PTS s)) -- so read it out in a `have!' LANE
      ;; (`mac-h' is destructive and the CONVERGES-TO is used again below).
      (have! (list 'IN it '(PTS RR-MS))
             (lambda ()
               (dk-split! (dk-landed-1
                           (lambda () (mac-h 'CONVERGES-TO
                                             (list 'CONVERGES-TO 'RR-MS
                                                   (list 'DIST-SEQ 'M a1 b1) it)))))
               (ass)))
      (rko2-embed-limit! a1 b1)
      (fact 'metric-limit-unique 'RR-MS (list 'DIST-SEQ 'M a1 b1) it '((DIST M) u v))
      (ass))
    ;; (2) existence and uniqueness
    (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORSOME)) ls2))
    (ew '((DIST M) u v))
    (let ((cs (dk-opened (lambda () (di)))))
      (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORSOME)) cs))
      (ew '(EMBED-SEQ M u))
      (dk-conj-close! rko2-exist-leaf!)
      (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'FORALL)) cs))
      (dk-peel!)
      (let* ((a2 (dk-skolem! (rko2-hyp 'FORSOME "the competitor, outer")))
             (b2 (dk-skolem! (rko2-hyp 'FORSOME "the competitor, inner"))))
        (rko2-embed-limit! a2 b2)
        (fact 'metric-limit-unique 'RR-MS (list 'DIST-SEQ 'M a2 b2)
              '((DIST M) u v) (caddr (dk-goal)))
        (ass)))))
(qed 'embed-isometry)
(topic! 'embed-isometry 'constructions)
(gloss! 'embed-isometry
  "The canonical embedding of a metric space in its completion preserves
   distance: d_hat((EMBED M)(u), (EMBED M)(v)) = d(u,v).  This is the support
   `embed-isometry' (structure-library/metric-completion.scm) with its left-hand
   side corrected -- that statement writes EMBED(M,u), which in VNB is EMBED
   applied to the PAIR [M,u] and not the map EMBED(M) applied to u.")
(alias! 'embed-isometry "the completion embeds a metric space isometrically")
(gloss! 'rko2-quad
  "The quadrilateral inequality: the distance between two points changes by at
   most the sum of the distances the endpoints move.")
(gloss! 'rko2-dist-converges
  "The metric is continuous in both arguments along sequences: if f converges to
   a and g to b, the real sequence of distances d(f_n, g_n) converges to d(a,b).")
