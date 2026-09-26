;;; rake-algebra.scm -- BATCH D of the 2026-09-17 rake: seven asserted leaves of
;;; the PSS, PROVEN.  Every statement here is its support's statement UNCHANGED.
;;;
;;;   ring-carr-in-set          structure-library/ring.scm:147
;;;   ideal-elt-in-carrier      structure-library/ideal.scm:102
;;;   principal-ideal-in-ideal  structure-library/ideal.scm:110
;;;   diagonal-off-entry        structure-library/mat-equiv.scm:218
;;;   ring-add-right-id         structure-library/matrix.scm:385
;;;   span-add-one-membership   theorem-library/hahn-banach-proof.scm:21 (add-to-pss)
;;;   strictly-mono-ge-id       theorem-library/cauchy-subsequence.scm:59
;;;
;;; Two auxiliary theorems are installed beside them:
;;;   span-add-one-unfold       the functoid's unfolding equation, the thing
;;;                             `mac-h' needs (a def-functoid installs a MACETE,
;;;                             not a theorem).  poly-membership.scm's recipe.
;;;   strictly-mono-ge-id-ind   the same fact with the NN variable OUTERMOST, so
;;;                             that `ni' fires on it; the support's own binder
;;;                             order puts `phi' first, and `di' is greedy.
;;;
;;; THE SHAPES.  Five of the seven are one recipe each and none has content:
;;;   * a CONJUNCT of a defining IFF, re-quantified (ring-carr-in-set,
;;;     ideal-elt-in-carrier, diagonal-off-entry) -- `mac-h' the IS-X unfold,
;;;     `dk-split-all!', then `ass' or one `dk-apply!'.  subtype-laws.scm's
;;;     `stl--project!' is the model.
;;;   * SEP MEMBERSHIP of a def-functoid (span-add-one-membership) -- prove the
;;;     unfolding equation by `(di) (mac 'SPAN-ADD-ONE) (qrfl)', then read the
;;;     membership apart with `sep-me' / assemble it with `sep-mi'.
;;;   * ring algebra (principal-ideal-in-ideal, ring-add-right-id) -- one
;;;     absorption / commutation citation and one `subst'.
;;; Only strictly-mono-ge-id needs an induction.
;;;
;;; LOAD WINDOW [215, 284).
;;;   lo = 215: the latest citation is `nn-lt-succ-le'
;;;             (theorem-library/finite-surgery, position 214).  Next latest are
;;;             co-le-lt-trans (175), bt-lt-succ (173), nn-in-rr (167),
;;;             nn-order-ord's nn-zero-le (165), fun-apply-type-c (162).
;;;   hi = 284: theorem-library/subseq-convergence-proof cites
;;;             strictly-mono-ge-id; it is the earliest PROVEN citer of any of
;;;             the seven.  (The others: ring-add-right-id 301, ring-carr-in-set
;;;             324, diagonal-off-entry 359, span-add-one-membership 436 --
;;;             hahn-banach-proof, which asserts it and then uses it at :144;
;;;             the two ideal leaves have no loaded citer at all.)
;;;
;;; Helper prefix `rka-'.  All helpers are file-local.

(define (rka-hyp head what) (dk-pick (dk-head? head) what))
(define (rka-find pred what) (dk-pick pred what))
(define (rka-in-head h)
  (lambda (f) (and (pair? f) (eq? (car f) 'IN) (pair? (caddr f))
                   (eq? (car (caddr f)) h))))

;;; =====================================================================
;;; ring-carr-in-set -- the carrier of a ring is a set.
;;; The `(carriers CARR)' slot of declare-structure RING contributes the
;;; conjunct (IN (CARR r) SET) verbatim to the IS-RING iff, so splitting the
;;; unfolded hypothesis puts the goal in the context.
;;; =====================================================================
(sp (make-wff '(FORALL r (IMPLIES (IS-RING r) (IN (CARR r) SET)))))
(dk-peel!)
(mac-h 'IS-RING (rka-hyp 'IS-RING "the IS-RING hypothesis"))
(dk-split-all!)
(ass)
(qed 'ring-carr-in-set)
(topic! 'ring-carr-in-set 'algebra)

;;; =====================================================================
;;; ideal-elt-in-carrier -- an element of an ideal lies in the carrier.
;;; IS-IDEAL has (SUBSET I (CARR s)) as a conjunct; `subset-def' turns it into
;;; the membership universal, instantiated at x.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL I (FORALL x
     (IMPLIES (IS-IDEAL s I) (IMPLIES (IN x I) (IN x (CARR s)))))))))
(dk-peel!)
(mac-h 'IS-IDEAL (rka-hyp 'IS-IDEAL "the IS-IDEAL hypothesis"))
(dk-split-all!)
(let ((x (cadr (dk-goal))))                       ; goal is (IN x (CARR s))
  (mac-h 'subset-def (rka-hyp 'SUBSET "the SUBSET conjunct"))
  (dk-apply! (rka-hyp 'FORALL "the unfolded subset universal") x))
(ass)
(qed 'ideal-elt-in-carrier)
(topic! 'ideal-elt-in-carrier 'algebra)

;;; =====================================================================
;;; principal-ideal-in-ideal -- b in I implies (b) subset I.
;;; principal-ideal-membership decomposes x as r.b with r in the carrier;
;;; IS-IDEAL's multiplicative-absorption conjunct puts r.b in I; one `subst'
;;; of the decomposition turns the goal into that.
;;; =====================================================================
(sp (make-wff '(FORALL s (FORALL I (FORALL b
     (IMPLIES (IS-IDEAL s I) (IMPLIES (IN b I)
       (FORALL x (IMPLIES (IN x (PRINCIPAL-IDEAL s b)) (IN x I))))))))))
(dk-peel!)
(let* ((mem (rka-find (rka-in-head 'PRINCIPAL-IDEAL) "x in the principal ideal"))
       (x   (cadr mem))
       (s   (cadr (caddr mem)))
       (b   (caddr (caddr mem))))
  (mac-h 'principal-ideal-membership mem)
  (dk-split-all!)
  (let ((r0 (dk-skolem! (rka-hyp 'FORSOME "the decomposition existential"))))
    (mac-h 'IS-IDEAL (rka-hyp 'IS-IDEAL "the IS-IDEAL hypothesis"))
    (dk-split-all!)
    (dk-apply! (rka-find (lambda (f)
                           (and (pair? f) (eq? (car f) 'FORALL)
                                (string-search-forward "mul" (expression->string f) 0)))
                         "the multiplicative-absorption conjunct")
               r0 b)
    (subst (list '= x (list (list 'MUL s) r0 b)))))
(ass)
(qed 'principal-ideal-in-ideal)
(topic! 'principal-ideal-in-ideal 'algebra)

;;; =====================================================================
;;; diagonal-off-entry -- off the diagonal, a diagonal matrix has zero entries.
;;; IS-DIAGONAL's body IS the statement; only the index guards are curried
;;; differently, and `dk-apply!' detaches them from the peeled context.
;;; =====================================================================
(sp (make-wff '(FORALL A (FORALL m (FORALL n (FORALL D
     (IMPLIES (IS-DIAGONAL A m n D)
     (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (NOT (= i j))
       (= (ENTRY D i j) (ZERO A))))))))))))))
(dk-peel!)
(let* ((e (cadr (dk-goal)))                       ; (ENTRY D i j)
       (i (caddr e)) (j (cadddr e)))
  (mac-h 'IS-DIAGONAL (rka-hyp 'IS-DIAGONAL "the IS-DIAGONAL hypothesis"))
  (dk-apply! (rka-hyp 'FORALL "the unfolded diagonal universal") i j))
(ass)
(qed 'diagonal-off-entry)
(topic! 'diagonal-off-entry 'linear-algebra)

;;; =====================================================================
;;; ring-add-right-id -- a + 0 = a.
;;; ring-add-comm at (a, ZERO s) rewrites the goal to ring-add-left-id's
;;; statement; ring-zero-in is the typing the commutation wants.
;;; =====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s)) (= ((ADD s) a (ZERO s)) a)))))))
(dk-peel!)
(let* ((g   (dk-goal))                            ; (= ((ADD s) a (ZERO s)) a)
       (lhs (cadr g))
       (s   (cadr (car lhs)))
       (a   (caddr g)))
  (fact 'ring-zero-in s)
  (fact 'ring-add-comm s a (list 'ZERO s))
  (fact 'ring-add-left-id s a)
  (subst (list '= lhs (list (list 'ADD s) (list 'ZERO s) a))))
(ass)
(qed 'ring-add-right-id)
(topic! 'ring-add-right-id 'algebra)

;;; =====================================================================
;;; span-add-one-unfold -- SPAN-ADD-ONE(m,s,v) as a citable equation.
;;; `def-functoid' installs a rewrite macete and no theorem, so `mac' unfolds
;;; SPAN-ADD-ONE in a GOAL and `mac-h' cannot unfold it in an ASSUMPTION.  The
;;; equation IS provable -- the macete applies to a goal that is the equation --
;;; and the resulting THEOREM is what mac-h rebuilds its rule from.
;;; `==', not `=': a bare SEP term is not syntactically defined, so `rfl' would
;;; owe a definedness witness it does not need.  (poly-membership.scm, 2026-08-20.)
;;; =====================================================================
(sp (make-wff '(FORALL m (FORALL s (FORALL v
   (== (SPAN-ADD-ONE m s v)
       (SEP y_ (VEC m)
         (FORSOME x_ (AND (IN x_ s)
           (FORSOME r_ (AND (IN r_ RR)
             (= y_ ((VADD m) x_ ((ACT m) r_ v))))))))))))))
(di) (mac 'SPAN-ADD-ONE) (qrfl)
(qed 'span-add-one-unfold)
(gloss! 'span-add-one-unfold
  "SPAN-ADD-ONE(m,s,v) is the separation { y in VEC(m) : y = x + r.v for some
   x in s and some real r }, as a citable equation.  Cite it with mac-h to open
   a membership in a hypothesis.")
(topic! 'span-add-one-unfold 'plumbing)

;;; =====================================================================
;;; span-add-one-membership -- w lies in s + RR.v iff w is a vector that so
;;; decomposes.  Forward: rewrite the hypothesis into the SEP and `sep-me' it.
;;; Backward: unfold the GOAL and discharge sep-mi's two obligations.
;;; The two sides spell the inner binder differently (`y_' in the statement,
;;; `x_' in the functoid body); `ass' is alpha-aware, which is why each leaf is
;;; closed by `ass' rather than handed to `prop'.
;;; =====================================================================
(sp (make-wff '(FORALL m (FORALL s (FORALL v (FORALL w_
   (IFF (IN w_ (SPAN-ADD-ONE m s v))
        (AND (IN w_ (VEC m))
             (FORSOME y_ (AND (IN y_ s)
               (FORSOME r_ (AND (IN r_ RR)
                 (= w_ ((VADD m) y_ ((ACT m) r_ v)))))))))))))))
(di)
(let ((ls (dk-opened (lambda () (di)))))
  (dk-focus! (any-pred (lambda (n) (eq? (car (dk-goal-of n)) 'AND)) ls))
  (mac-h 'span-add-one-unfold
         (rka-find (rka-in-head 'SPAN-ADD-ONE) "w_ in SPAN-ADD-ONE"))
  (sep-me (rka-find (rka-in-head 'SEP) "w_ in the SEP"))
  (dk-conj-close! (lambda () (ass)))
  (dk-focus! (any-pred (lambda (n) (not (eq? (car (dk-goal-of n)) 'AND))) ls))
  (dk-split! (rka-hyp 'AND "the decomposition conjunction"))
  (mac 'SPAN-ADD-ONE)
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (sep-mi)))))
(qed 'span-add-one-membership)
(topic! 'span-add-one-membership 'analysis)

;;; =====================================================================
;;; strictly-mono-ge-id-ind -- the induction, with k OUTERMOST.
;;; `ni' tests the goal's SHAPE -- literally (FORALL n (IMPLIES (IN n NN) ...))
;;; at the top -- and the support quantifies phi first, so the induction has to
;;; be stated with the binders swapped and the support derived from it.
;;;   base   0 <= phi(0): phi(0) is in NN (fun-apply-type-c) and 0 is least.
;;;   step   k <= phi(k) (IH) and phi(k) < phi(succ k) (monotonicity at
;;;          k < succ k) give k < phi(succ k) by co-le-lt-trans over RR, and
;;;          nn-lt-succ-le turns that into succ k <= phi(succ k).
;;; =====================================================================
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN)
   (FORALL phi (IMPLIES (STRICTLY-MONO-NN phi) (<= k_ (phi k_))))))))
(let ((ls (dk-opened (lambda () (ni)))))
  ;; base: the leaf whose leading binder is phi (the step's is the NN variable)
  (dk-focus! (any-pred (lambda (n) (eq? (quantifier-var (dk-goal-of n)) 'phi)) ls))
  (dk-peel!)
  (let ((ph (car (caddr (dk-goal)))))             ; goal is (<= 0 (phi 0))
    (mac-h 'STRICTLY-MONO-NN (rka-hyp 'STRICTLY-MONO-NN "the monotonicity hypothesis"))
    (dk-split-all!)
    (fact 'nn-zero-in)
    (fact 'fun-apply-type-c ph 'NN 'NN 0)
    (fact 'nn-zero-le (list ph 0))
    (ass))
  ;; step
  (dk-focus! (any-pred (lambda (n) (not (eq? (quantifier-var (dk-goal-of n)) 'phi))) ls))
  (dk-peel!)
  (let* ((g  (dk-goal))                           ; (<= (succ k) (phi (succ k)))
         (sk (cadr g))
         (k  (cadr sk))
         (ph (car (caddr g)))
         (ih (rka-find (lambda (f)
                         (and (pair? f) (eq? (car f) 'FORALL)
                              (string-search-forward "strictly-mono"
                                                     (expression->string f) 0)))
                       "the induction hypothesis")))
    (dk-apply! ih ph)                             ; k <= phi(k)
    (mac-h 'STRICTLY-MONO-NN (rka-hyp 'STRICTLY-MONO-NN "the monotonicity hypothesis"))
    ;; take the monotonicity universal from the SPLIT, not from a later search:
    ;; the facts below land universals of their own (bt-lt-succ's, in particular).
    (let ((mono (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)))
                          (dk-split-all!))))
      (if (not mono) (error "rake-algebra: no monotonicity universal in the split"))
      (fact 'nn-succ-closed k)
      (fact 'fun-apply-type-c ph 'NN 'NN k)
      (fact 'fun-apply-type-c ph 'NN 'NN sk)
      (fact 'bt-lt-succ k)
      (dk-apply! mono k sk))                      ; phi(k) < phi(succ k)
    (fact 'nn-in-rr k)
    (fact 'nn-in-rr (list ph k))
    (fact 'nn-in-rr (list ph sk))
    (fact 'co-le-lt-trans k (list ph k) (list ph sk))
    (fact 'nn-lt-succ-le k (list ph sk))
    (ass)))
(qed 'strictly-mono-ge-id-ind)
(gloss! 'strictly-mono-ge-id-ind
  "k <= phi(k) for a strictly monotone phi : NN -> NN, stated with the NN
   variable outermost so that `ni' fires on it.  strictly-mono-ge-id is this
   theorem with the binders in the order the library cites them.")
(topic! 'strictly-mono-ge-id-ind 'inequalities)

;;; =====================================================================
;;; strictly-mono-ge-id -- the support's own binder order.
;;; =====================================================================
(sp (make-wff '(FORALL phi (IMPLIES (STRICTLY-MONO-NN phi)
     (FORALL k (IMPLIES (IN k NN) (<= k (phi k))))))))
(dk-peel!)
(let* ((g (dk-goal)) (k (cadr g)) (ph (car (caddr g))))
  (fact 'strictly-mono-ge-id-ind k ph))
(ass)
(qed 'strictly-mono-ge-id)
(topic! 'strictly-mono-ge-id 'inequalities)
