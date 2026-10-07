;;; caratheodory.scm -- THE CARATHEODORY CONSTRUCTION, PROVEN.
;;; Agent MEASURE-1, 2026-10-07 (scratchpad/triage/MEASURE-1.md).  Library:
;;; measure.  Helper prefix cth-.  16 theorems, every one `modulo 0'.
;;;
;;; THE FIVE SUPPORTS of structure-library/measure.scm, proven under their old
;;; names with their statements UNCHANGED (Thayer, Construction of Measures,
;;; Chapter 4, Sec. 1, pp. 30-32):
;;;   outer-measure-binary-subadditive      Def. 4.1(3) at the padded sequence
;;;                                         a, b, {}, {}, ... (the mechanics of
;;;                                         measure-laws' measure-finitely-additive)
;;;   caratheodory-null-measurable          Remark 4.3
;;;   caratheodory-superadditive-suffices   Eq. (75)
;;;   caratheodory-measurable-sigma-algebra Prop. 4.4, first half
;;;   caratheodory-measure                  Prop. 4.4, second half
;;;
;;; THE OTHER ELEVEN.  difference-unfold (DIFFERENCE is a def-functoid, so its
;;; unfold equation is proven to be usable on a hypothesis); eight set-algebra
;;; identities by class extensionality (inter-complement-in-shift,
;;; complement-in-complement-in-union, complement-in-empty-set,
;;; union-inter-complement-in-split, inter-complement-in-ambient,
;;; complement-in-complement-in-ambient, inter-of-subset,
;;; complement-in-of-subset-empty); outer-measure-split-le (mu(A) <=
;;; mu(A n E) + mu(A \ E) for every E, the sentence before (75));
;;; caratheodory-prefix-split (below).
;;;
;;; THE ROUTE TO PROP. 4.4, AND WHERE IT LEAVES THE NOTES.  The notes prove that
;;; the measurable sets are closed under binary unions, hence form an algebra,
;;; then prove Lemma 4.5 by induction over finite disjoint families and pass to
;;; the limit.  This file needs no algebra-of-sets closure at all.  For a
;;; sequence f of measurable sets, with U_n = f_0 u ... u f_{n-1} and the
;;; disjointified D_k = f_k \ U_k (the refinement of measure-laws.scm),
;;;     caratheodory-prefix-split:  mu(A) = sum_{k<n} mu(A n D_k) + mu(A \ U_n)
;;; for every test set A, by induction on n, the step being the measurability
;;; of f_n ALONE at the test set A \ U_n:  (A \ U_n) n f_n = A n D_n and
;;; (A \ U_n) \ f_n = A \ U_{n+1}.  Then:
;;;   * countable unions (sigma-algebra): P_n + mu(A \ U) <= mu(A) for every n
;;;     (monotonicity), the supremum over n moves past `+' by esup-eplus-le
;;;     (P_n nondecreasing, the other sequence constant), and mu(A n U) <=
;;;     sum_k mu(A n D_k) is countable subadditivity, the A n D_k covering A n U
;;;     (disjointify-union); (75) closes it.  This is the notes' final display
;;;     of the proof of 4.4, with the limit spelled as a supremum.
;;;   * countable additivity (measure): the test set is U itself; for pairwise
;;;     disjoint f, f_k lies inside U n D_k, so sum_k mu(f_k) <= sum_k mu(U n D_k)
;;;     <= mu(U); the other inequality is subadditivity.  The notes: "follows
;;;     immediately from the lemma by taking A = X".
;;;   * omega and complements: the set identities above and eplus-comm.
;;;
;;; LOAD WINDOW: after "theorem-library/integral-convergence" (load.scm 3472),
;;; whose esup-eplus-le the countable step cites; every other citation is at or
;;; before measure-laws (3386).  hi: nothing in the tree cites the five supports
;;; (grep, 2026-10-07); keep it before pss-topics (3586).  Suggested slot:
;;; immediately after "theorem-library/integral-convergence", in load.scm and in
;;; libraries.sexp (library measure).
;;;
;;; RETIRE, after wiring: structure-library/measure.scm, the five supports
;;; (support + warrant! + topic! + gloss! each): caratheodory-measurable-sigma-algebra
;;; (:238), caratheodory-measure (:255), caratheodory-null-measurable (:271),
;;; caratheodory-superadditive-suffices (:287), outer-measure-binary-subadditive (:309).
;;; Their glosses are not repeated here; the integrator moves them with the retirement.
;;; ====================================================================

;;; =====================================================================
;;; (0) file-local kit.
;;; =====================================================================

(define cth-pw '(POWER omega))

;;; the five conjuncts of IS-OUTER-MEASURE(omega, mu), landed (hypothesis kept)
(define (cth-om-parts!)
  (let* ((iff (dk-cite! 'is-outer-measure 'omega 'mu))
         (rhs (caddr iff))
         (cs (let loop ((r rhs) (acc '()))
               (if (and (pair? r) (eq? (car r) 'AND))
                   (loop (caddr r) (cons (cadr r) acc))
                   (reverse (cons r acc))))))
    (map (lambda (c) (dk-project! c 'IS-OUTER-MEASURE '(IS-OUTER-MEASURE omega mu))) cs)))

;;; (IN (mu x) RR-POS-STAR), with (IN x (POWER omega)) in context
(define (cth-mu-type! x)
  (if (not (dk-asm? (list 'IN (list 'mu x) 'RR-POS-STAR)))
      (fact 'fun-apply-type-c 'mu cth-pw 'RR-POS-STAR x)))

;;; (IN x (POWER omega)) from (SUBSET x y) and (IN y (POWER omega)) in context
(define (cth-pow-sub! x y)
  (if (not (dk-asm? (list 'IN x cth-pw)))
      (begin
        (fact 'power-mem-sethood 'omega y)
        (fact 'subclass-of-set-is-set x y)
        (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ x) (list 'IN 'z_ 'omega)))
          (lambda ()
            (let ((zv (dk-di-var!)))
              (fact 'subset-mem-fwd x y zv)
              (fact 'power-mem-in 'omega y zv)
              (ass))))
        (fact 'power-mem-intro 'omega x))))

;;; (IN x (POWER omega)) from (SUBSET x omega) in context (omega in SET too)
(define (cth-sub-pow! x)
  (if (not (dk-asm? (list 'IN x cth-pw)))
      (begin
        (fact 'subclass-of-set-is-set x 'omega)
        (dk-have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ x) (list 'IN 'z_ 'omega)))
          (lambda ()
            (let ((zv (dk-di-var!)))
              (fact 'subset-mem-fwd x 'omega zv)
              (ass))))
        (fact 'power-mem-intro 'omega x))))

;;; (SUBSET (INTERSECTION x y) y)
(define (cth-inter-sub-r! x y)
  (let ((ix (list 'INTERSECTION x y)))
    (dk-have! (list 'SUBSET ix y)
      (lambda ()
        (mac 'subset-def)
        (let ((zv (dk-di-var!)))
          (mac-h 'intersection-membership (list 'IN zv ix))
          (dk-split-all!)
          (ass))))))

;;; (AND p q) in context from p, q in context
(define (cth-and2! p q)
  (dk-have! (list 'AND p q) (lambda () (dk-conj-close! dk-ass!))))

;;; x = y in [0, +inf] from x <= y, y <= x, both typed
(define (cth-antisymm! x y)
  (cth-and2! (list 'IN x 'RR-POS-STAR) (list 'IN y 'RR-POS-STAR))
  (cth-and2! (list '<= x y) (list '<= y x))
  (fact 'rr-pos-star-le-antisymm x y))

;;; x <= z from x <= y, y <= z, all typed
(define (cth-trans! x y z)
  (dk-have! (list 'AND (list 'IN x 'RR-POS-STAR)
                  (list 'AND (list 'IN y 'RR-POS-STAR) (list 'IN z 'RR-POS-STAR)))
            (lambda () (dk-conj-close! dk-ass!)))
  (cth-and2! (list '<= x y) (list '<= y z))
  (fact 'rr-pos-star-le-trans x y z))

;;; class extensionality, the membership iff proven by unfolding the set
;;; operations MACS under the binder and `prop' (with PRE run after the peel,
;;; to land the extra facts prop needs: (lambda (w) ...)).
(define cth-mac-heads
  '((intersection-membership . INTERSECTION) (complement-in-membership . COMPLEMENT-IN)
    (union-membership . UNION)))
(define (cth-has-in-head? x h)
  (and (pair? x)
       (or (and (eq? (car x) 'IN) (pair? (cdr x)) (pair? (cddr x))
                (pair? (caddr x)) (eq? (car (caddr x)) h))
           (let loop ((xs x))
             (and (pair? xs)
                  (or (cth-has-in-head? (car xs) h) (loop (cdr xs))))))))
(define (cth-unfold-sets!)
  (let loop ((fuel 12))
    (let ((m (find-first (lambda (p) (cth-has-in-head? (dk-goal) (cdr p))) cth-mac-heads)))
      (if (and m (> fuel 0))
          (begin (mac (car m)) (loop (- fuel 1)))))))
(define (cth-ext! lhs rhs macs pre)
  (dk-have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ lhs) (list 'IN 'w_ rhs)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (cth-unfold-sets!)
        (pre w)
        (prop))))
  (fact 'class-extensionality lhs rhs))

;;; =====================================================================
;;; (1) set algebra and the DIFFERENCE unfold.
;;; =====================================================================

;;; DIFFERENCE is a def-functoid: `mac-h' cannot unfold it in a hypothesis by
;;; name, so the unfold equation is proven (one line, CLAUDE.md).
(sp (make-wff '(FORALL u_ (FORALL b_ (== (DIFFERENCE u_ b_) (COMPLEMENT-IN u_ b_))))))
(di)
(mac 'DIFFERENCE)
(qrfl)
(qed 'difference-unfold)
(topic! 'difference-unfold 'plumbing)

(define cth-set-macs '(intersection-membership complement-in-membership union-membership))

;;; (A \ U) n E = A n (E \ U)
(sp (make-wff '(FORALL a_ (FORALL u_ (FORALL e_
      (= (INTERSECTION (COMPLEMENT-IN a_ u_) e_) (INTERSECTION a_ (COMPLEMENT-IN e_ u_))))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs (lambda (w) #t))
  (ass))
(qed 'inter-complement-in-shift)
(topic! 'inter-complement-in-shift 'set-quotient)

;;; (A \ U) \ E = A \ (U u E)
(sp (make-wff '(FORALL a_ (FORALL u_ (FORALL e_
      (= (COMPLEMENT-IN (COMPLEMENT-IN a_ u_) e_) (COMPLEMENT-IN a_ (UNION u_ e_))))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs (lambda (w) #t))
  (ass))
(qed 'complement-in-complement-in-union)
(topic! 'complement-in-complement-in-union 'set-quotient)

;;; A \ {} = A
(sp (make-wff '(FORALL a_ (= (COMPLEMENT-IN a_ EMPTY-SET) a_))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs
            (lambda (w) (fact 'empty-set-has-no-members w)))
  (ass))
(qed 'complement-in-empty-set)
(topic! 'complement-in-empty-set 'set-quotient)

;;; A = (A n E) u (A \ E)
(sp (make-wff '(FORALL a_ (FORALL e_
      (= a_ (UNION (INTERSECTION a_ e_) (COMPLEMENT-IN a_ e_)))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs (lambda (w) #t))
  (ass))
(qed 'union-inter-complement-in-split)
(topic! 'union-inter-complement-in-split 'set-quotient)

;;; for T inside OMEGA:  T n (OMEGA \ E) = T \ E  and  T \ (OMEGA \ E) = T n E
(sp (make-wff '(FORALL t_ (FORALL om_ (FORALL e_ (IMPLIES (SUBSET t_ om_)
      (= (INTERSECTION t_ (COMPLEMENT-IN om_ e_)) (COMPLEMENT-IN t_ e_))))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs
            (lambda (w) (fact 'subset-mem-fwd 't_ 'om_ w)))
  (ass))
(qed 'inter-complement-in-ambient)
(topic! 'inter-complement-in-ambient 'set-quotient)

(sp (make-wff '(FORALL t_ (FORALL om_ (FORALL e_ (IMPLIES (SUBSET t_ om_)
      (= (COMPLEMENT-IN t_ (COMPLEMENT-IN om_ e_)) (INTERSECTION t_ e_))))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs
            (lambda (w) (fact 'subset-mem-fwd 't_ 'om_ w)))
  (ass))
(qed 'complement-in-complement-in-ambient)
(topic! 'complement-in-complement-in-ambient 'set-quotient)

;;; for T inside OMEGA:  T n OMEGA = T  and  T \ OMEGA = {}
(sp (make-wff '(FORALL t_ (FORALL om_ (IMPLIES (SUBSET t_ om_)
      (= (INTERSECTION t_ om_) t_))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs
            (lambda (w) (fact 'subset-mem-fwd 't_ 'om_ w)))
  (ass))
(qed 'inter-of-subset)
(topic! 'inter-of-subset 'set-quotient)

(sp (make-wff '(FORALL t_ (FORALL om_ (IMPLIES (SUBSET t_ om_)
      (= (COMPLEMENT-IN t_ om_) EMPTY-SET))))))
(dk-peel!)
(let ((gl (dk-goal)))
  (cth-ext! (cadr gl) (caddr gl) cth-set-macs
            (lambda (w) (fact 'subset-mem-fwd 't_ 'om_ w) (fact 'empty-set-has-no-members w)))
  (ass))
(qed 'complement-in-of-subset-empty)
(topic! 'complement-in-of-subset-empty 'set-quotient)

;;; =====================================================================
;;; (2) outer-measure-binary-subadditive -- Def. 4.1(3) at the padded
;;;     sequence a, b, {}, {}, ...  (the mechanics of measure-laws.scm's
;;;     measure-finitely-additive, with countable SUBadditivity in place of
;;;     additivity).
;;; =====================================================================

;;; copies of measure-laws.scm's local IF helpers (file-local there)
(define (cth-find-if x)
  (cond ((not (pair? x)) #f)
        ((eq? (car x) 'IF) x)
        (#t (let loop ((xs x))
              (cond ((null? xs) #f)
                    ((not (pair? xs)) #f)
                    ((cth-find-if (car xs)) => (lambda (r) r))
                    (#t (loop (cdr xs))))))))

(define (cth-if-eq! true? ifterm closer)
  (let* ((c      (cadr ifterm))
         (val    (if true? (caddr ifterm) (cadddr ifterm)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (<= (length conds) 1) (= 1 (length mains))))
        (error "cth-if-eq!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (if (pair? conds) (begin (dk-focus! (car conds)) (closer)))
    (dk-focus! (car mains))
    (list '= ifterm val)))

(define (cth-transfer! eqn rel lhs)
  (let ((val (caddr eqn)) (ifterm (cadr eqn)))
    (dk-have! (list rel lhs val)
              (lambda () (subst (list '= val ifterm)) (ass)))))

(define (cth-ssq-facts! qv)
  (let ((sq (list 'succ qv)))
    (fact 'nn-succ-closed qv)
    (fact 'nn-succ-closed sq)
    (fact 'nn-zero-in)
    (fact 'nn-succ-nonzero sq)
    (fact 'nn-succ-nonzero qv)
    (dk-have! (list 'NOT (list '= (list 'succ sq) '(succ 0)))
      (lambda ()
        (di)
        (fact 'nn-succ-inj sq 0)
        (ai (list 'NOT (list '= sq 0)))))))

(define cth-fam '(VNB-LAMBDA mk_ NN (IF (= mk_ 0) a_ (IF (= mk_ (succ 0)) b_ EMPTY-SET))))

(sp (make-wff (forall-guarded '(omega mu a_ b_)
                  '((IS-OUTER-MEASURE omega mu)
                    (IN a_ (POWER omega))
                    (IN b_ (POWER omega)))
    '(<= (mu (UNION a_ b_)) (eplus (mu a_) (mu b_))))))
(dk-peel!)
(let* ((parts (cth-om-parts!))
       (sub (list-ref parts 4))
       (g cth-fam)
       (s0 '(succ 0))
       (uab '(UNION a_ b_)))
  (fact 'power-empty-in 'omega)
  (fact 'nn-zero-in)
  (fact 'nn-succ-closed 0)
  (fact 'nn-succ-nonzero 0)
  ;; g in FUN(NN, POWER omega)
  (dk-have! (list 'IN g (list 'FUN 'NN cth-pw))
    (lambda ()
      (dk-lam-t!)
      (dk-peel!)
      (let ((ift (cth-find-if (dk-goal))))
        (dk-case-if! ift
          (lambda (t1 v1)
            (if t1 (ass)
                (dk-case-if! (cth-find-if (dk-goal)) (lambda (t2 v2) (ass)))))))))
  (let* ((ch (dk-apply! sub g))
         (bu (cadr (cadr ch)))
         (hl (cadr (caddr ch))))
    ;; BU = a u b
    (dk-have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ bu) (list 'IN 'w_ uab)))
      (lambda ()
        (let ((w (dk-di-var! (lambda (gl) (cadr (cadr gl))))))
          (for-each
            (lambda (l)
              (dk-focus! l)
              (if (equal? (dk-goal) (list 'IN w uab))
                  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bu)))))
                         (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'NN))) landed))
                         (app (find-first (lambda (f) (not (eq? f ein))) landed)))
                    (dk-lam-b-h! app)
                    (let ((ife (dk-pick (lambda (f) (and (eq? (car f) 'IN) (eq? (cadr f) w)
                                                         (pair? (caddr f)) (eq? (car (caddr f)) 'IF)))
                                        "w in IF")))
                      (mac 'union-membership)
                      (let ((ift (caddr ife)))
                        (use-em (cadr ift)
                          (lambda ()
                            (cth-transfer! (cth-if-eq! #t ift dk-ass!) 'IN w)
                            (oi-l) (ass))
                          (lambda ()
                            (let* ((e1 (cth-if-eq! #f ift dk-ass!))
                                   (ift2 (caddr e1)))
                              (cth-transfer! e1 'IN w)
                              (use-em (cadr ift2)
                                (lambda ()
                                  (cth-transfer! (cth-if-eq! #t ift2 dk-ass!) 'IN w)
                                  (oi-r) (ass))
                                (lambda ()
                                  (cth-transfer! (cth-if-eq! #f ift2 dk-ass!) 'IN w)
                                  (fact 'empty-set-has-no-members w)
                                  (ai (list 'NOT (list 'IN w 'EMPTY-SET)))))))))))
                  (let ((orf (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN w uab))))))
                    (for-each
                      (lambda (m)
                        (dk-focus! m)
                        (let* ((a-side (dk-asm? (list 'IN w 'a_)))
                               (k (if a-side 0 s0)))
                          (for-each
                            (lambda (n)
                              (dk-focus! n)
                              (if (equal? (dk-goal) (list 'IN k 'NN))
                                  (ass)
                                  (begin
                                    (dk-lam-b!)
                                    (if a-side
                                        (dk-if-branch! #t (cth-find-if (dk-goal)) (lambda () (rfl))
                                                       dk-ass!)
                                        (dk-if-branch! #f (cth-find-if (dk-goal)) #f
                                          (lambda ()
                                            (dk-if-branch! #t (cth-find-if (dk-goal)) (lambda () (rfl))
                                                           dk-ass!)))))))
                            (dk-opened (lambda () (bu-mi k))))))
                      (dk-opened (lambda () (ai orf)))))))
            (dk-opened (lambda () (di)))))))
    (fact 'class-extensionality bu uab)
    ;; h = n |-> mu(g n): typed, and its values
    (dk-have! (list 'IN hl '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-t!)
        (dk-peel!)
        (let ((kv (cadr (cadr (cadr (dk-goal))))))
          (dk-fact! 'fun-apply-type-c g 'NN cth-pw kv)
          (fact 'fun-apply-type-c 'mu cth-pw 'RR-POS-STAR (list g kv))
          (ass))))
    (dk-have! (list 'FORALL 'q (list 'IMPLIES '(IN q NN) (list '= (list hl '(succ (succ q))) 0)))
      (lambda ()
        (let ((qv (dk-di-var!)))
          (cth-ssq-facts! qv)
          (dk-lam-b!)
          (dk-if-branch! #f (cth-find-if (dk-goal)) #f
            (lambda ()
              (dk-if-branch! #f (cth-find-if (dk-goal)) #f
                dk-ass!))))))
    (cth-mu-type! 'a_)
    (cth-mu-type! 'b_)
    (dk-have! (list '= (list hl 0) '(mu a_))
      (lambda ()
        (dk-lam-b!)
        (dk-if-branch! #t (cth-find-if (dk-goal)) (lambda () (rfl)) (lambda () (rfl)))))
    (dk-have! (list '= (list hl s0) '(mu b_))
      (lambda ()
        (dk-lam-b!)
        (dk-if-branch! #f (cth-find-if (dk-goal)) #f
          (lambda ()
            (dk-if-branch! #t (cth-find-if (dk-goal)) (lambda () (rfl)) (lambda () (rfl)))))))
    (fact 'esum-nn-two-support hl)
    (subst (list '= uab bu))
    (subst (list '= '(mu a_) (list hl 0)))
    (subst (list '= '(mu b_) (list hl s0)))
    (subst (list '= (list 'eplus (list hl 0) (list hl s0)) (list 'ESUM hl)))
    (ass)))
(qed 'outer-measure-binary-subadditive)
(topic! 'outer-measure-binary-subadditive 'inequalities)

;;; =====================================================================
;;; (3) outer-measure-split-le -- the half of (74) that holds for EVERY E:
;;;     mu(A) <= mu(A n E) + mu(A \ E)  (the notes, the sentence before (75)).
;;; =====================================================================

(sp (make-wff '(FORALL omega (FORALL mu (FORALL a_ (FORALL es
   (IMPLIES (IS-OUTER-MEASURE omega mu)
     (IMPLIES (IN a_ (POWER omega))
       (IMPLIES (IN es (POWER omega))
         (<= (mu a_) (eplus (mu (INTERSECTION a_ es)) (mu (COMPLEMENT-IN a_ es)))))))))))))
(dk-peel!)
(let* ((parts (cth-om-parts!))
       (x '(INTERSECTION a_ es))
       (y '(COMPLEMENT-IN a_ es))
       (u (list 'UNION x y)))
  (fact 'power-inter-closed 'omega 'a_ 'es)
  (fact 'complement-in-subset 'es 'a_)
  (cth-pow-sub! y 'a_)
  (fact 'union-inter-complement-in-split 'a_ 'es)
  (fact 'outer-measure-binary-subadditive 'omega 'mu x y)
  (cth-mu-type! 'a_)
  (dk-congr! (list '= 'a_ u) (lambda (t) (list 'mu t)))
  (subst (list '= '(mu a_) (list 'mu u)))
  (ass))
(qed 'outer-measure-split-le)
(topic! 'outer-measure-split-le 'inequalities)

;;; =====================================================================
;;; (4) caratheodory-null-measurable -- Remark 4.3.
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega mu es)
                  '((IS-OUTER-MEASURE omega mu)
                    (SUBSET es omega)
                    (= (mu es) 0))
    '(IS-CARATHEODORY-MEASURABLE omega mu es))))
(dk-peel!)
(let* ((parts (cth-om-parts!))
       (mono (list-ref parts 3)))
  (cth-sub-pow! 'es)
  (mac 'IS-CARATHEODORY-MEASURABLE)
  (mac 'DIFFERENCE)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'SUBSET)
          (ass)
          (let* ((av (dk-di-var!))
                 (x (list 'INTERSECTION av 'es)) (y (list 'COMPLEMENT-IN av 'es))
                 (mx (list 'mu x)) (my (list 'mu y)) (ma (list 'mu av)))
            (fact 'power-inter-closed 'omega av 'es)
            (cth-inter-sub-r! av 'es)
            (dk-apply! mono x 'es)
            (cth-mu-type! x)
            (dk-have! (list '<= mx 0) (lambda () (subst '(= 0 (mu es))) (ass)))
            (fact 'rr-pos-star-nonneg mx)
            (fact 'zero-in-rr-pos-star)
            (cth-antisymm! mx 0)
            (fact 'complement-in-subset 'es av)
            (cth-pow-sub! y av)
            (cth-mu-type! y)
            (cth-mu-type! av)
            (dk-apply! mono y av)
            (fact 'outer-measure-split-le 'omega 'mu av 'es)
            (subst (list '= mx 0))
            (fact 'eplus-zero-left my)
            (subst (list '= (list 'eplus 0 my) my))
            (dk-have! (list '<= ma my)
              (lambda ()
                (subst (list '= my (list 'eplus 0 my)))
                (subst (list '= 0 mx))
                (ass)))
            (cth-antisymm! ma my)
            (ass))))))
(qed 'caratheodory-null-measurable)
(topic! 'caratheodory-null-measurable 'set-quotient)

;;; =====================================================================
;;; (5) caratheodory-superadditive-suffices -- Eq. (75).
;;; =====================================================================

(sp (make-wff (forall-guarded '(omega mu es)
                  (list '(IS-OUTER-MEASURE omega mu)
                        '(SUBSET es omega)
                        (forall-guarded '(a_) '((IN a_ (POWER omega)))
                          '(<= (eplus (mu (INTERSECTION a_ es))
                                      (mu (DIFFERENCE a_ es)))
                               (mu a_))))
    '(IS-CARATHEODORY-MEASURABLE omega mu es))))
(dk-peel!)
(let* ((parts (cth-om-parts!))
       (hyp (dk-pick (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f 'DIFFERENCE)))
                     "the superadditivity hypothesis")))
  (cth-sub-pow! 'es)
  (mac 'IS-CARATHEODORY-MEASURABLE)
  (mac 'DIFFERENCE)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'SUBSET)
          (ass)
          (let* ((av (dk-di-var!))
                 (x (list 'INTERSECTION av 'es)) (y (list 'COMPLEMENT-IN av 'es))
                 (mx (list 'mu x)) (my (list 'mu y)) (ma (list 'mu av))
                 (sm (list 'eplus mx my)))
            (dk-apply! hyp av)
            (fact 'difference-unfold av 'es)
            (dk-have! (list '<= sm ma)
              (lambda () (subst (list '= y (list 'DIFFERENCE av 'es))) (ass)))
            (fact 'power-inter-closed 'omega av 'es)
            (fact 'complement-in-subset 'es av)
            (cth-pow-sub! y av)
            (cth-mu-type! x) (cth-mu-type! y) (cth-mu-type! av)
            (fact 'outer-measure-split-le 'omega 'mu av 'es)
            (cth-and2! (list 'IN mx 'RR-POS-STAR) (list 'IN my 'RR-POS-STAR))
            (fact 'eplus-closed mx my)
            (cth-antisymm! ma sm)
            (ass))))))
(qed 'caratheodory-superadditive-suffices)
(topic! 'caratheodory-superadditive-suffices 'set-quotient)

;;; =====================================================================
;;; (6) caratheodory-prefix-split -- the finite form of the notes' Lemma
;;;     4.5, in the shape the countable step needs.  For a sequence f of
;;;     measurable sets, U_n = f_0 u ... u f_{n-1} and the disjointified
;;;     D_k = f_k \ U_k, every test set A splits as
;;;         mu(A) = sum_{k<n} mu(A n D_k) + mu(A \ U_n).
;;;     Induction on n; the step is the measurability of f_n ALONE, applied to
;;;     the test set A \ U_n, so no algebra-of-sets closure is needed:
;;;         (A \ U_n) n f_n = A n D_n,   (A \ U_n) \ f_n = A \ U_{n+1}.
;;; =====================================================================

(define cth-C '(CARATHEODORY-SETS omega mu))
(define (cth-seg n) (list 'ORD-SEGMENT n))
(define (cth-useg fv kv) (list 'BIG-UNION 'uj_ (cth-seg kv) (list fv 'uj_)))
(define (cth-dterm fv kv) (list 'COMPLEMENT-IN (list fv kv) (cth-useg fv kv)))
(define (cth-fs f s) (list 'FINSUM 'RR-POS-STAR-ADD-MONOID f s))

;;; (IN x C) in context: land (IN x (POWER omega)) and the measurability
(define (cth-in-C! x)
  (if (not (dk-asm? (list 'IN x cth-pw)))
      (let* ((iff (dk-fact! 'caratheodory-sets-membership 'omega 'mu x))
             (a (cadr iff)) (b (caddr iff)))
        (ai iff)
        (detach! (list 'IMPLIES a b))
        (dk-split-all! (list (dk-ctx-form b))))))

;;; f in FUN(NN, C), k in NN in context: f k in C, in POWER omega, measurable;
;;; D_k in POWER omega; and, when AV is given, A n D_k in POWER omega with its mu typed.
(define (cth-fk! fv kv . av)
  (let* ((fk (list fv kv)) (uk (cth-useg fv kv)) (dk (cth-dterm fv kv)))
    (if (not (dk-asm? (list 'IN fk cth-C)))
        (fact 'fun-apply-type-c fv 'NN cth-C kv))
    (cth-in-C! fk)
    (if (not (dk-asm? (list 'SUBSET dk fk)))
        (fact 'complement-in-subset uk fk))
    (cth-pow-sub! dk fk)
    (if (pair? av)
        (let ((ik (list 'INTERSECTION (car av) dk)))
          (if (not (dk-asm? (list 'IN ik cth-pw)))
              (fact 'power-inter-closed 'omega (car av) dk))
          (cth-mu-type! ik)))))

;;; the summand sequence k |-> mu(A n D_k), typed
(define (cth-sseq fv av)
  (list 'VNB-LAMBDA 'ck_ 'NN
        (list 'mu (list 'INTERSECTION av
                        (list 'COMPLEMENT-IN (list fv 'ck_)
                              (list 'BIG-UNION 'uj_ '(ORD-SEGMENT ck_) (list fv 'uj_)))))))
(define (cth-sseq-type! fv av)
  (let ((sq (cth-sseq fv av)))
    (if (not (dk-asm? (list 'IN sq '(FUN NN RR-POS-STAR))))
        (dk-have! (list 'IN sq '(FUN NN RR-POS-STAR))
          (lambda ()
            (dk-lam-t!)
            (dk-peel!)
            (let ((kv (cadr (cadr (caddr (cadr (cadr (dk-goal))))))))
              (cth-fk! fv kv av)
              (ass)))))
    sq))

;;; the step-leaf idiom of measure-laws.scm
(define (cth-step-open!)
  (let* ((landed (dk-landed (lambda () (di))))
         (nin (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN))) landed))
         (ih  (dk-landed-1 (lambda () (di)))))
    (dk-peel!)
    (list (cadr nin) ih)))
(define (cth-base-leaf? l) (dk-contains? (dk-goal-of l) '(ORD-SEGMENT 0)))

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
  (FORALL omega (FORALL mu (FORALL f (FORALL a_
   (IMPLIES (IS-OUTER-MEASURE omega mu)
    (IMPLIES (IN f (FUN NN (CARATHEODORY-SETS omega mu)))
     (IMPLIES (IN a_ (POWER omega))
      (= (mu a_)
         (eplus (FINSUM RR-POS-STAR-ADD-MONOID
                  (VNB-LAMBDA ck_ NN (mu (INTERSECTION a_ (COMPLEMENT-IN (f ck_) (BIG-UNION uj_ (ORD-SEGMENT ck_) (f uj_))))))
                  (ORD-SEGMENT n))
                (mu (COMPLEMENT-IN a_ (BIG-UNION uj_ (ORD-SEGMENT n) (f uj_)))))))))))))))))
(for-each
  (lambda (l)
    (dk-focus! l)
    (if (cth-base-leaf? l)
        (begin
          (dk-peel!)
          (let* ((gl (dk-goal))
                 (av (cadr (cadr gl)))
                 (e  (caddr gl))
                 (p0 (cadr e)) (sq (caddr p0))
                 (c0 (caddr e)) (u0 (caddr (cadr c0)))
                 (fv (car (cadddr u0)))
                 (ma (list 'mu av)))
            (cth-om-parts!)
            (fact 'rps-prefix-zero sq)
            (fact 'bu-seg-zero fv)
            (fact 'complement-in-empty-set av)
            (subst (list '= p0 0))
            (subst (list '= u0 'EMPTY-SET))
            (subst (list '= (list 'COMPLEMENT-IN av 'EMPTY-SET) av))
            (cth-mu-type! av)
            (fact 'eplus-zero-left ma)
            (subst (list '= (list 'eplus 0 ma) ma))
            (rfl)))
        (let* ((r (cth-step-open!)) (nv (car r)) (ih (cadr r))
               (gl (dk-goal))
               (av (cadr (cadr gl)))
               (e  (caddr gl))
               (p1 (cadr e)) (sq (caddr p1))
               (c1 (caddr e)) (u1 (caddr (cadr c1)))
               (fv (car (cadddr u1)))
               (fn (list fv nv))
               (un (cth-useg fv nv))
               (dn (cth-dterm fv nv))
               (in (list 'INTERSECTION av dn))
               (pn (cth-fs sq (cth-seg nv)))
               (tt (list 'COMPLEMENT-IN av un))
               (r1 (list 'INTERSECTION tt fn))
               (r2 (list 'COMPLEMENT-IN tt fn))
               (mr1 (list 'mu r1)) (mr2 (list 'mu r2))
               (mcl (list 'FORALL 'a_ (list 'IMPLIES '(IN a_ (POWER omega))
                      (list '= '(mu a_) (list 'eplus (list 'mu (list 'INTERSECTION 'a_ fn))
                                                      (list 'mu (list 'DIFFERENCE 'a_ fn))))))))
          (cth-om-parts!)
          (cth-sseq-type! fv av)
          (fact 'rps-prefix-succ sq nv)
          (fact 'rps-prefix-type sq nv)
          (cth-fk! fv nv av)
          (dk-have! (list '= (list sq nv) (list 'mu in))
                    (lambda () (dk-lam-b!) (rfl)))
          (dk-apply! ih 'omega 'mu fv av)
          (fact 'bu-seg-succ nv cth-C fv)
          ;; the test set A \ U_n, split by f_n
          (fact 'complement-in-subset un av)
          (cth-pow-sub! tt av)
          (dk-project! mcl 'IS-CARATHEODORY-MEASURABLE
                       (list 'IS-CARATHEODORY-MEASURABLE 'omega 'mu fn))
          (dk-apply! mcl tt)
          (fact 'difference-unfold tt fn)
          (dk-have! (list '= (list 'mu tt) (list 'eplus mr1 mr2))
                    (lambda () (subst (list '= r2 (list 'DIFFERENCE tt fn))) (ass)))
          (fact 'inter-complement-in-shift av un fn)
          (fact 'complement-in-complement-in-union av un fn)
          (fact 'power-inter-closed 'omega tt fn)
          (fact 'complement-in-subset fn tt)
          (cth-pow-sub! r2 tt)
          (cth-mu-type! r1)
          (cth-mu-type! r2)
          ;; assemble
          (subst (list '= p1 (list 'eplus pn (list sq nv))))
          (subst (list '= (list sq nv) (list 'mu in)))
          (subst (list '= u1 (list 'UNION un fn)))
          (subst (list '= in r1))
          (subst (list '= (list 'COMPLEMENT-IN av (list 'UNION un fn)) r2))
          (dk-have! (list 'AND (list 'IN pn 'RR-POS-STAR)
                          (list 'AND (list 'IN mr1 'RR-POS-STAR) (list 'IN mr2 'RR-POS-STAR)))
                    (lambda () (dk-conj-close! dk-ass!)))
          (fact 'eplus-assoc pn mr1 mr2)
          (subst (list '= (list 'eplus (list 'eplus pn mr1) mr2) (list 'eplus pn (list 'eplus mr1 mr2))))
          (subst (list '= (list 'eplus mr1 mr2) (list 'mu tt)))
          (ass))))
  (dk-opened (lambda () (ni))))
(qed 'caratheodory-prefix-split)
(topic! 'caratheodory-prefix-split 'set-quotient)

;;; =====================================================================
;;; (7) caratheodory-measurable-sigma-algebra -- Prop. 4.4, first half.
;;;     omega and complements by the set algebra; a countable union U of
;;;     measurable f_k by (75): for a test set A and every n,
;;;         P_n + mu(A \ U) <= P_n + mu(A \ U_n) = mu(A)     (prefix-split)
;;;     with P_n = sum_{k<n} mu(A n D_k); the sup over n is moved past `+'
;;;     by esup-eplus-le (P_n nondecreasing, the second sequence constant),
;;;     and mu(A n U) <= sum_k mu(A n D_k) is countable subadditivity, the
;;;     A n D_k covering A n U (disjointify-union).  The notes route the
;;;     countable step through finite unions and Lemma 4.5; the prefix form
;;;     above needs neither.
;;; =====================================================================

;;; DOM f = NN and f in FUN(DOM f, RR-POS-STAR) (copy of measure-laws' mlw-dom!)
(define (cth-dom! fv)
  (fact 'nn-is-set)
  (dk-project! (list 'IN fv '(FUN NN)) 'fun-codomain-iff (list 'IN fv '(FUN NN RR-POS-STAR)))
  (cth-and2! (list 'IN fv '(FUN NN)) '(IN NN SET))
  (fact 'dom-of-fun 'NN fv)
  (dk-split-all! (list (dk-ctx-form (list 'AND (list 'IN (list 'DOM fv) 'SET)
                                          (list '= (list 'DOM fv) 'NN)))))
  (dk-have! (list 'IN fv (list 'FUN (list 'DOM fv) 'RR-POS-STAR))
            (lambda () (subst (list '= (list 'DOM fv) 'NN)) (ass))))

;;; (IN (ESUM f) RR-POS-STAR) for f in FUN(NN, RR-POS-STAR)
(define (cth-esum-type! fv)
  (cth-dom! fv)
  (fact 'esum-in fv))

;;; t = phi(k) is in IMAGE(phi, NN) (copy of measure-laws' mlw-in-image!)
(define (cth-in-image! phi kv tm)
  (let* ((iff (dk-fact! 'image-membership-iff phi 'NN tm))
         (lhs (cadr iff)) (rhs (caddr iff)))
    (dk-have! rhs
      (lambda ()
        (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond ((equal? g (list 'IN tm 'SET))
                     (fact 'membership-implies-sethood tm 'RR-POS-STAR) (ass))
                    ((eq? (car g) 'FORSOME)
                     (ew kv)
                     (dk-conj-close!
                       (lambda ()
                         (if (equal? (dk-goal) (list 'IN kv 'NN)) (ass)
                             (begin (dk-lam-b!) (rfl))))))
                    (#t (ass))))))))
    (ai iff)
    (detach! (list 'IMPLIES rhs lhs))))

;;; (SUBSET (IMAGE phi NN) RR-POS-STAR), phi in FUN(NN, RR-POS-STAR) in context;
;;; lands also ESUP's upper-bound law and its typing.  Returns the ESUP term.
(define (cth-esup-of! phi)
  (let* ((img (list 'IMAGE phi 'NN)) (sv (list 'ESUP img)))
    (dk-have! (list 'SUBSET img 'RR-POS-STAR)
      (lambda ()
        (mac 'subset-def)
        (let ((wv (dk-di-var!)))
          (fact 'image-subset-codomain 'NN 'RR-POS-STAR phi wv)
          (ass))))
    (fact 'esup-in img)
    (fact 'esup-upper img)
    sv))

;;; x <= ESUP(IMAGE phi NN) for x = phi(k), x typed, k in NN
(define (cth-le-esup! phi kv tm)
  (let* ((img (list 'IMAGE phi 'NN)) (sv (list 'ESUP img)))
    (cth-in-image! phi kv tm)
    (inst+ (dk-pick (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f img)
                                     (dk-contains? f sv) (dk-contains? f '<=)))
                    "esup-upper")
           tm)
    (list '<= tm sv)))

;;; (SUBSET x omega) from (IN x (POWER omega))
(define (cth-pow-subset! x)
  (dk-have! (list 'SUBSET x 'omega)
    (lambda ()
      (mac 'subset-def)
      (let ((zv (dk-di-var!)))
        (fact 'power-mem-in 'omega x zv)
        (ass)))))

;;; prove the focus goal (IN x C): POW proves (IN x (POWER omega)), MEAS the measurability
(define (cth-into-C! pow meas)
  (mac 'caratheodory-sets-membership)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'IN) (pow) (meas)))))

;;; f in FUN(NN, C) gives f in FUN(NN, POWER omega)
(define (cth-f-pow! fv)
  (dk-project! (list 'IN fv '(FUN NN)) 'fun-codomain-iff (list 'IN fv (list 'FUN 'NN cth-C)))
  (dk-have! (list 'IN fv (list 'FUN 'NN cth-pw))
    (lambda ()
      (mac 'fun-codomain-iff)
      (dk-conj-close!
        (lambda ()
          (if (eq? (car (dk-goal)) 'IN)
              (ass)
              (let ((kv (dk-di-var!)))
                (fact 'fun-apply-type-c fv 'NN cth-C kv)
                (cth-in-C! (list fv kv))
                (ass))))))))

;;; the measurability clause of IS-CARATHEODORY-MEASURABLE(omega, mu, es), landed
(define (cth-mclause es)
  (list 'FORALL 'cta_ (list 'IMPLIES '(IN cta_ (POWER omega))
    (list '= '(mu cta_) (list 'eplus (list 'mu (list 'INTERSECTION 'cta_ es))
                                      (list 'mu (list 'DIFFERENCE 'cta_ es)))))))
;;; at the test set T: (= (mu T) (eplus (mu (T n es)) (mu (T \ es)))), COMPLEMENT-IN form
(define (cth-split-at! es tv)
  (let* ((mcl (cth-mclause es))
         (r1 (list 'INTERSECTION tv es)) (r2 (list 'COMPLEMENT-IN tv es))
         (claim (list '= (list 'mu tv) (list 'eplus (list 'mu r1) (list 'mu r2)))))
    (dk-project! mcl 'IS-CARATHEODORY-MEASURABLE
                 (list 'IS-CARATHEODORY-MEASURABLE 'omega 'mu es))
    (dk-apply! mcl tv)
    (fact 'difference-unfold tv es)
    (dk-have! claim (lambda () (subst (list '= r2 (list 'DIFFERENCE tv es))) (ass)))
    claim))

;;; omega in C
(define (cth-omega-in-C!)
  (cth-into-C!
    (lambda () (fact 'power-whole-in 'omega) (ass))
    (lambda ()
      (mac 'IS-CARATHEODORY-MEASURABLE)
      (mac 'DIFFERENCE)
      (dk-conj-close!
        (lambda ()
          (if (eq? (car (dk-goal)) 'SUBSET)
              (begin (fact 'subset-refl 'omega) (ass))
              (let* ((av (dk-di-var!)) (ma (list 'mu av)))
                (cth-pow-subset! av)
                (fact 'inter-of-subset av 'omega)
                (fact 'complement-in-of-subset-empty av 'omega)
                (subst (list '= (list 'INTERSECTION av 'omega) av))
                (subst (list '= (list 'COMPLEMENT-IN av 'omega) 'EMPTY-SET))
                (subst '(= (mu EMPTY-SET) 0))
                (cth-mu-type! av)
                (fact 'eplus-zero-right ma)
                (subst (list '= (list 'eplus ma 0) ma))
                (rfl))))))))

;;; the complement clause, on its focus leaf
(define (cth-compl-clause!)
  (let* ((av (dk-di-var!)) (ca (list 'COMPLEMENT-IN 'omega av)))
    (cth-in-C! av)
    (cth-into-C!
      (lambda () (fact 'power-complement-closed 'omega av) (ass))
      (lambda ()
        (mac 'IS-CARATHEODORY-MEASURABLE)
        (mac 'DIFFERENCE)
        (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'SUBSET)
                (begin (fact 'complement-in-subset av 'omega) (ass))
                (let* ((tv (dk-di-var!))
                       (x (list 'INTERSECTION tv av)) (y (list 'COMPLEMENT-IN tv av))
                       (mx (list 'mu x)) (my (list 'mu y)))
                  (cth-pow-subset! tv)
                  (fact 'inter-complement-in-ambient tv 'omega av)
                  (fact 'complement-in-complement-in-ambient tv 'omega av)
                  (subst (list '= (list 'INTERSECTION tv ca) y))
                  (subst (list '= (list 'COMPLEMENT-IN tv ca) x))
                  (cth-split-at! av tv)
                  (fact 'power-inter-closed 'omega tv av)
                  (fact 'complement-in-subset av tv)
                  (cth-pow-sub! y tv)
                  (cth-mu-type! x) (cth-mu-type! y)
                  (cth-and2! (list 'IN mx 'RR-POS-STAR) (list 'IN my 'RR-POS-STAR))
                  (fact 'eplus-comm mx my)
                  (subst (list '= (list 'eplus my mx) (list 'eplus mx my)))
                  (ass)))))))))

;;; A \ U is inside A \ U_n
(define (cth-tail-subset! av fv nv)
  (let* ((bu (list 'BIG-UNION 'n_ 'NN (list fv 'n_)))
         (un (cth-useg fv nv))
         (cu (list 'COMPLEMENT-IN av bu)) (cun (list 'COMPLEMENT-IN av un)))
    (dk-have! (list 'SUBSET cu cun)
      (lambda ()
        (mac 'subset-def)
        (let ((zv (dk-di-var!)))
          (mac-h 'complement-in-membership (list 'IN zv cu))
          (dk-split-all!)
          (mac 'complement-in-membership)
          (dk-conj-close!
            (lambda ()
              (if (eq? (car (dk-goal)) 'NOT)
                  (let* ((pos (dk-landed-1 (lambda () (di))))
                         (landed (dk-landed (lambda () (bu-me pos))))
                         (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (not (equal? (cadr f) zv)))) landed))
                         (jv (cadr ein)))
                    (fact 'ord-segment-nn-subset nv jv)
                    (dk-have! (list 'IN zv bu)
                      (lambda () (for-each (lambda (n) (dk-focus! n) (ass))
                                           (dk-opened (lambda () (bu-mi jv))))))
                    (ai (list 'NOT (list 'IN zv bu))))
                  (ass)))))))
    (list 'SUBSET cu cun)))

;;; the union clause, on its focus leaf
(define (cth-union-clause!)
  (let* ((parts (cth-om-parts!))
         (mono (list-ref parts 3))
         (sub (list-ref parts 4))
         (fv (dk-di-var!))
         (bu (list 'BIG-UNION 'n_ 'NN (list fv 'n_))))
    (cth-f-pow! fv)
    (fact 'power-fun-union-closed 'omega fv)
    (cth-pow-subset! bu)
    (cth-into-C!
      (lambda () (ass))
      (lambda ()
        (let ((hyp (list 'FORALL 'a_ (list 'IMPLIES '(IN a_ (POWER omega))
                     (list '<= (list 'eplus (list 'mu (list 'INTERSECTION 'a_ bu))
                                            (list 'mu (list 'DIFFERENCE 'a_ bu)))
                           '(mu a_))))))
          (dk-have! hyp
            (lambda ()
              (let ((av (dk-di-var!)))
                (mac 'DIFFERENCE)
                (cth-union-core! av fv bu mono sub))))
          (fact 'caratheodory-superadditive-suffices 'omega 'mu bu)
          (ass))))))

;;; eplus(mu(A n U), mu(A \ U)) <= mu(A), on the focus leaf
(define (cth-union-core! av fv bu mono sub)
  (let* ((sq (cth-sseq-type! fv av))
         (ma (list 'mu av))
         (cu (list 'COMPLEMENT-IN av bu)) (c (list 'mu cu))
         (xu (list 'INTERSECTION av bu)) (mxu (list 'mu xu))
         (ul (list 'VNB-LAMBDA 'pn_ 'NN (cth-fs sq '(ORD-SEGMENT pn_))))
         (vl (list 'VNB-LAMBDA 'vn_ 'NN c))
         (g  (list 'VNB-LAMBDA 'gk_ 'NN
                   (list 'INTERSECTION av
                         (list 'COMPLEMENT-IN (list fv 'gk_)
                               (list 'BIG-UNION 'uj_ '(ORD-SEGMENT gk_) (list fv 'uj_)))))))
    (cth-mu-type! av)
    (fact 'complement-in-subset bu av)
    (cth-pow-sub! cu av)
    (cth-mu-type! cu)
    (fact 'power-inter-closed 'omega av bu)
    (cth-mu-type! xu)
    (fact 'nn-zero-in)
    ;; (A)
    ;; for every n:  P_n + mu(A \ U) <= mu(A)
    (let ((claim (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
                   (list '<= (list 'eplus (list ul 'n) (list vl 'n)) ma)))))
      (dk-have! claim
        (lambda ()
          (let* ((nv (dk-di-var!))
                 (pn (cth-fs sq (cth-seg nv)))
                 (un (cth-useg fv nv))
                 (cun (list 'COMPLEMENT-IN av un))
                 (mcun (list 'mu cun)))
            (dk-lam-b!)
            (fact 'caratheodory-prefix-split nv 'omega 'mu fv av)
            (fact 'rps-prefix-type sq nv)
            (cth-tail-subset! av fv nv)
            (fact 'complement-in-subset un av)
            (cth-pow-sub! cun av)
            (cth-mu-type! cun)
            (dk-apply! mono cu cun)
            (fact 'rr-pos-star-le-refl pn)
            (dk-have! (list 'AND (list 'IN pn 'RR-POS-STAR)
                            (list 'AND (list 'IN c 'RR-POS-STAR)
                                  (list 'AND (list 'IN pn 'RR-POS-STAR) (list 'IN mcun 'RR-POS-STAR))))
                      (lambda () (dk-conj-close! dk-ass!)))
            (cth-and2! (list '<= pn pn) (list '<= c mcun))
            (fact 'eplus-mono pn c pn mcun)
            (subst (list '= ma (list 'eplus pn mcun)))
            (ass)))))
    ;; (B)
    ;; the two sequences: typed, nondecreasing; esup-eplus-le
    (dk-have! (list 'IN ul '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-t!)
        (dk-peel!)
        (let ((kv (cadr (cadddr (cadr (dk-goal))))))
          (fact 'rps-prefix-type sq kv)
          (ass))))
    (dk-have! (list 'IN vl '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-t!)
        (dk-peel!)
        (ass)))
    (dk-have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list '<= (list ul 'n) (list ul '(succ n)))))
      (lambda ()
        (let* ((nv (dk-di-var!))
               (pn (cth-fs sq (cth-seg nv))))
          (fact 'nn-succ-closed nv)
          (dk-lam-b!)
          (fact 'rps-prefix-succ sq nv)
          (fact 'rps-prefix-type sq nv)
          (fact 'fun-apply-type-c sq 'NN 'RR-POS-STAR nv)
          (subst (list '= (cth-fs sq (cth-seg (list 'succ nv))) (list 'eplus pn (list sq nv))))
          (cth-and2! (list 'IN pn 'RR-POS-STAR) (list 'IN (list sq nv) 'RR-POS-STAR))
          (fact 'eplus-le-left pn (list sq nv))
          (ass))))
    (dk-have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list '<= (list vl 'n) (list vl '(succ n)))))
      (lambda ()
        (let ((nv (dk-di-var!)))
          (fact 'nn-succ-closed nv)
          (dk-lam-b!)
          (fact 'rr-pos-star-le-refl c)
          (ass))))
    (fact 'esup-eplus-le ul vl ma)
    (let* ((su (cth-esup-of! ul))
           (sv (cth-esup-of! vl)))
      ;; (C)
    ;; ESUM S <= sup_n P_n
      (dk-have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list '<= (cth-fs sq '(ORD-SEGMENT n)) su)))
        (lambda ()
          (let* ((nv (dk-di-var!)) (pn (cth-fs sq (cth-seg nv))))
            (fact 'rps-prefix-type sq nv)
            (cth-le-esup! ul nv pn)
            (ass))))
      (fact 'esum-nn-le-of-prefixes sq su)
      ;; (D)
    ;; mu(A \ U) <= sup of the constant sequence
      (cth-le-esup! vl 0 c)
      ;; (E)
    ;; mu(A n U) <= ESUM S, by countable subadditivity at g
      (dk-have! (list 'IN g (list 'FUN 'NN cth-pw))
        (lambda ()
          (dk-lam-t!)
          (dk-peel!)
          (let ((kv (cadr (cadr (caddr (cadr (dk-goal)))))))
            (cth-fk! fv kv av)
            (ass))))
      (let* ((ch (dk-apply! sub g))
             (bug (cadr (cadr ch)))
             (hl (cadr (caddr ch)))
             (dl (list 'VNB-LAMBDA 'bk_ 'NN (list 'COMPLEMENT-IN (list fv 'bk_)
                         (list 'BIG-UNION 'uj_ '(ORD-SEGMENT bk_) (list fv 'uj_)))))
             (bud (list 'BIG-UNION 'n_ 'NN (list dl 'n_))))
        (fact 'disjointify-union fv cth-C)
        (dk-have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ bug) (list 'IN 'w_ xu)))
          (lambda ()
            (let ((w (dk-di-var! (lambda (gl) (cadr (cadr gl))))))
              (for-each
                (lambda (l)
                  (dk-focus! l)
                  (if (equal? (dk-goal) (list 'IN w xu))
                      (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bug)))))
                             (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'NN))) landed))
                             (ev (cadr ein))
                             (app (find-first (lambda (f) (not (eq? f ein))) landed)))
                        (cth-fk! fv ev av)
                        (dk-lam-b-h! app)
                        (let ((ii (list 'IN w (list 'INTERSECTION av (cth-dterm fv ev)))))
                          (mac-h 'intersection-membership ii)
                          (dk-split-all!)
                          (mac-h 'complement-in-membership (list 'IN w (cth-dterm fv ev)))
                          (dk-split-all!)
                          (mac 'intersection-membership)
                          (dk-conj-close!
                            (lambda ()
                              (if (equal? (dk-goal) (list 'IN w av))
                                  (ass)
                                  (for-each (lambda (n) (dk-focus! n) (ass))
                                            (dk-opened (lambda () (bu-mi ev)))))))))
                      (begin
                        (mac-h 'intersection-membership (list 'IN w xu))
                        (dk-split-all!)
                        (dk-have! (list 'IN w bud)
                          (lambda () (subst (list '= bud bu)) (ass)))
                        (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bud)))))
                               (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'NN))) landed))
                               (ev (cadr ein))
                               (app (find-first (lambda (f) (not (eq? f ein))) landed)))
                          (cth-fk! fv ev av)
                          (dk-lam-b-h! app)
                          (for-each
                            (lambda (n)
                              (dk-focus! n)
                              (if (equal? (dk-goal) (list 'IN ev 'NN))
                                  (ass)
                                  (begin
                                    (dk-lam-b!)
                                    (mac 'intersection-membership)
                                    (dk-conj-close! dk-ass!))))
                            (dk-opened (lambda () (bu-mi ev))))))))
                (dk-opened (lambda () (di)))))))
        (fact 'class-extensionality bug xu)
        ;; hl <= S termwise
        (dk-have! (list 'IN hl '(FUN NN RR-POS-STAR))
          (lambda ()
            (dk-lam-t!)
            (dk-peel!)
            (let ((kv (cadr (cadr (cadr (dk-goal))))))
              (fact 'fun-apply-type-c g 'NN cth-pw kv)
              (cth-mu-type! (list g kv))
              (ass))))
        (dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '<= (list hl 'k) (list sq 'k))))
          (lambda ()
            (let ((kv (dk-di-var!)))
              (cth-fk! fv kv av)
              (dk-lam-b!)
              (fact 'rr-pos-star-le-refl (list 'mu (list 'INTERSECTION av (cth-dterm fv kv))))
              (ass))))
        (fact 'esum-nn-le-termwise hl sq)
        (cth-esum-type! hl)
        (cth-esum-type! sq)
        (dk-have! (list '<= mxu (list 'ESUM hl))
          (lambda () (subst (list '= xu bug)) (ass)))
        (cth-trans! mxu (list 'ESUM hl) (list 'ESUM sq))
        (cth-trans! mxu (list 'ESUM sq) su)
        ;; (F) and (G)
        (dk-have! (list 'AND (list 'IN mxu 'RR-POS-STAR)
                        (list 'AND (list 'IN c 'RR-POS-STAR)
                              (list 'AND (list 'IN su 'RR-POS-STAR) (list 'IN sv 'RR-POS-STAR))))
                  (lambda () (dk-conj-close! dk-ass!)))
        (cth-and2! (list '<= mxu su) (list '<= c sv))
        (fact 'eplus-mono mxu c su sv)
        (cth-and2! (list 'IN mxu 'RR-POS-STAR) (list 'IN c 'RR-POS-STAR))
        (fact 'eplus-closed mxu c)
        (cth-and2! (list 'IN su 'RR-POS-STAR) (list 'IN sv 'RR-POS-STAR))
        (fact 'eplus-closed su sv)
        (cth-trans! (list 'eplus mxu c) (list 'eplus su sv) ma)
        (ass)))))

(sp (make-wff (forall-guarded '(omega mu) '((IS-OUTER-MEASURE omega mu))
    '(IS-SIGMA-ALGEBRA omega (CARATHEODORY-SETS omega mu)))))
(dk-peel!)
(cth-om-parts!)
(mac 'IS-SIGMA-ALGEBRA)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((equal? g '(IN omega SET)) (ass))
            ((eq? (car g) 'SUBSET)
             (mac 'subset-def)
             (let ((zv (dk-di-var!))) (cth-in-C! zv) (ass)))
            ((eq? (car g) 'IN) (cth-omega-in-C!))
            ((dk-contains? g 'BIG-UNION) (cth-union-clause!))
            (#t (cth-compl-clause!))))))
(qed 'caratheodory-measurable-sigma-algebra)
(topic! 'caratheodory-measurable-sigma-algebra 'set-quotient)

;;; =====================================================================
;;; (8) caratheodory-measure -- Prop. 4.4, second half.  The notes: "countable
;;;     additivity of mu*|A follows immediately from the lemma by taking A = X".
;;;     Here the test set is the union U itself: for pairwise disjoint f_k,
;;;     f_k is inside U n D_k (D_k = f_k \ U_k, and f_k misses U_k), so
;;;     sum_k mu(f_k) <= sum_k mu(U n D_k) <= mu(U) by prefix-split; the other
;;;     inequality is countable subadditivity of the outer measure.
;;; =====================================================================

(define cth-res '(RES mu (CARATHEODORY-SETS omega mu)))

;;; (= ((RES mu C) x) (mu x)), with (IN x C) in context
(define (cth-res! x)
  (dk-have! (list 'AND (list 'IN 'mu (list 'FUN cth-pw))
                  (list 'AND (list 'SUBSET cth-C cth-pw) (list 'IN x cth-C)))
            (lambda () (dk-conj-close! dk-ass!)))
  (fact 'res-apply cth-pw cth-C 'mu x))

;;; f_k is inside U n D_k, for a pairwise disjoint f (DD the disjointness)
(define (cth-fk-in-trace! fv kv bu dd)
  (let* ((fk (list fv kv)) (uk (cth-useg fv kv))
         (ik (list 'INTERSECTION bu (cth-dterm fv kv))))
    (dk-have! (list 'SUBSET fk ik)
      (lambda ()
        (mac 'subset-def)
        (let ((zv (dk-di-var!)))
          (cth-unfold-sets!)
          (dk-conj-close!
            (lambda ()
              (let ((g (dk-goal)))
                (cond ((equal? g (list 'IN zv bu))
                       (for-each (lambda (n) (dk-focus! n) (ass))
                                 (dk-opened (lambda () (bu-mi kv)))))
                      ((eq? (car g) 'NOT)
                       (let* ((pos (dk-landed-1 (lambda () (di))))
                              (landed (dk-landed (lambda () (bu-me pos))))
                              (ein (find-first (lambda (f) (and (eq? (car f) 'IN) (not (equal? (cadr f) zv))))
                                               landed))
                              (jv (cadr ein))
                              (ij (list 'INTERSECTION (list fv jv) fk)))
                         (fact 'ord-segment-nn-subset kv jv)
                         (let ((iff (dk-fact! 'seg-mem-lt kv jv)))
                           (ai iff)
                           (detach! (list 'IMPLIES (cadr iff) (caddr iff))))
                         (fact 'nn-in-rr kv)
                         (fact 'nn-in-rr jv)
                         (dk-have! (list 'NOT (list '= jv kv))
                           (lambda ()
                             (di)
                             (dk-have! (list '< kv kv)
                               (lambda () (dk-ineq! (list 'IN jv 'RR) (list 'IN kv 'RR)
                                                    (list '= jv kv) (list '< jv kv))))
                             (fact 'rr-lt-irrefl kv)
                             (ai (list 'NOT (list '< kv kv)))))
                         (dk-apply! dd jv kv)
                         (dk-have! (list 'IN zv ij)
                           (lambda () (mac 'intersection-membership) (dk-conj-close! dk-ass!)))
                         (dk-have! (list 'IN zv 'EMPTY-SET)
                           (lambda () (subst (list '= 'EMPTY-SET ij)) (ass)))
                         (fact 'empty-set-has-no-members zv)
                         (ai (list 'NOT (list 'IN zv 'EMPTY-SET)))))
                      (#t (ass)))))))))
    (list 'SUBSET fk ik)))

;;; countable additivity of RES(mu, C), on its focus leaf
(define (cth-cadd! mono sub)
  (dk-peel!)
  (let* ((gl (dk-goal))
         (lhs (cadr gl))
         (bu (cadr lhs))
         (fv (car (cadddr bu)))
         (lr (cadr (caddr gl)))
         (lm (list 'VNB-LAMBDA 'n_ 'NN (list 'mu (list fv 'n_))))
         (mbu (list 'mu bu))
         (dd (dk-pick (lambda (f) (and (eq? (car f) 'FORALL) (dk-contains? f 'INTERSECTION)
                                       (dk-contains? f fv)))
                      "disjointness of f")))
    (fact 'sigma-algebra-union-closed 'omega cth-C fv)
    (cth-res! bu)
    (cth-in-C! bu)
    (cth-mu-type! bu)
    (cth-f-pow! fv)
    ;; the summands of RES(mu, C) are those of mu
    (dk-have! (list 'IN lr '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-t!)
        (dk-peel!)
        (let ((kv (cadr (cadr (cadr (dk-goal))))))
          (fact 'fun-apply-type-c fv 'NN cth-C kv)
          (fact 'fun-apply-type-c cth-res cth-C 'RR-POS-STAR (list fv kv))
          (ass))))
    (dk-have! (list 'IN lm '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-t!)
        (dk-peel!)
        (let ((kv (cadr (cadr (cadr (dk-goal))))))
          (fact 'fun-apply-type-c fv 'NN cth-pw kv)
          (cth-mu-type! (list fv kv))
          (ass))))
    (dk-project! (list 'IN lr '(FUN NN)) 'fun-codomain-iff (list 'IN lr '(FUN NN RR-POS-STAR)))
    (dk-project! (list 'IN lm '(FUN NN)) 'fun-codomain-iff (list 'IN lm '(FUN NN RR-POS-STAR)))
    (dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x NN) (list '= (list lr 'x) (list lm 'x))))
      (lambda ()
        (let ((xv (dk-di-var!)))
          (fact 'fun-apply-type-c fv 'NN cth-C xv)
          (cth-in-C! (list fv xv))
          (cth-mu-type! (list fv xv))
          (cth-res! (list fv xv))
          (if (not (dk-lam-b!)) (ass)))))
    (fact 'fun-domain-extensionality 'NN lr lm)
    (subst (list '= lhs mbu))
    (subst (list '= lr lm))
    ;; <= : countable subadditivity
    (dk-apply! sub fv)
    ;; >= : sum_k mu(f_k) <= sum_k mu(U n D_k) <= mu(U)
    (let ((sq (cth-sseq-type! fv bu)))
      (dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '<= (list lm 'k) (list sq 'k))))
        (lambda ()
          (let* ((kv (dk-di-var!))
                 (fk (list fv kv))
                 (ik (list 'INTERSECTION bu (cth-dterm fv kv))))
            (cth-fk! fv kv bu)
            (cth-mu-type! fk)
            (dk-lam-b!)
            (cth-fk-in-trace! fv kv bu dd)
            (dk-apply! mono fk ik)
            (ass))))
      (fact 'esum-nn-le-termwise lm sq)
      (dk-have! (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list '<= (cth-fs sq '(ORD-SEGMENT n)) mbu)))
        (lambda ()
          (let* ((nv (dk-di-var!))
                 (pn (cth-fs sq (cth-seg nv)))
                 (un (cth-useg fv nv))
                 (cun (list 'COMPLEMENT-IN bu un))
                 (mcun (list 'mu cun)))
            (fact 'caratheodory-prefix-split nv 'omega 'mu fv bu)
            (fact 'rps-prefix-type sq nv)
            (fact 'complement-in-subset un bu)
            (cth-pow-sub! cun bu)
            (cth-mu-type! cun)
            (cth-and2! (list 'IN pn 'RR-POS-STAR) (list 'IN mcun 'RR-POS-STAR))
            (fact 'eplus-le-left pn mcun)
            (subst (list '= mbu (list 'eplus pn mcun)))
            (ass))))
      (fact 'esum-nn-le-of-prefixes sq mbu)
      (cth-esum-type! lm)
      (cth-esum-type! sq)
      (cth-trans! (list 'ESUM lm) (list 'ESUM sq) mbu)
      (cth-antisymm! mbu (list 'ESUM lm))
      (ass))))

(sp (make-wff (forall-guarded '(omega mu) '((IS-OUTER-MEASURE omega mu))
    '(IS-MEASURE omega
                 (CARATHEODORY-SETS omega mu)
                 (RES mu (CARATHEODORY-SETS omega mu))))))
(dk-peel!)
(let* ((parts (cth-om-parts!))
       (mono (list-ref parts 3))
       (sub (list-ref parts 4)))
  (fact 'caratheodory-measurable-sigma-algebra 'omega 'mu)
  (dk-project! (list 'SUBSET cth-C cth-pw) 'IS-SIGMA-ALGEBRA (list 'IS-SIGMA-ALGEBRA 'omega cth-C))
  (dk-project! (list 'IN 'mu (list 'FUN cth-pw)) 'fun-codomain-iff
               (list 'IN 'mu (list 'FUN cth-pw 'RR-POS-STAR)))
  (cth-and2! (list 'IN 'mu (list 'FUN cth-pw 'RR-POS-STAR)) (list 'SUBSET cth-C cth-pw))
  (fact 'res-codomain cth-pw cth-C 'RR-POS-STAR 'mu)
  (mac 'IS-MEASURE)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond ((eq? (car g) 'IS-SIGMA-ALGEBRA) (ass))
              ((eq? (car g) 'IN) (ass))
              ((eq? (car g) '=)
               (fact 'sigma-algebra-empty-in 'omega cth-C)
               (cth-res! 'EMPTY-SET)
               (subst (list '= (list cth-res 'EMPTY-SET) '(mu EMPTY-SET)))
               (ass))
              (#t (cth-cadd! mono sub)))))))
(qed 'caratheodory-measure)
(topic! 'caratheodory-measure 'set-quotient)

;;; The glosses of the five statements, carried over from structure-library/measure.scm
;;; when the supports were retired (2026-10-07); the warrants are history.
(gloss!   'outer-measure-binary-subadditive
  "An outer measure is subadditive on PAIRS: mu(a union b) <= mu(a) + mu(b).
   NOT literally the source's statement -- Def. 4.1(3) (p. 30) states COUNTABLE
   subadditivity, over a sequence.  The binary case is the instance whose
   sequence is a, b, empty, empty, ... , and it is stated separately because
   the countable form cannot be used on two sets without first building that
   sequence.  Both sources use the binary form silently (Thayer does so in the
   very next paragraph, to get inequality (75)).")
(gloss!   'caratheodory-null-measurable
  "Every set of outer measure zero is Caratheodory measurable.  Thayer
   Remark 4.3 (p. 30), stated there as 'every set E such that mu*(E) = 0 is
   measurable'; VNB adds the explicit hypothesis that es is a subset of omega,
   which the source carries implicitly by working inside P(X).")
(gloss!   'caratheodory-superadditive-suffices
  "Only one of the two inequalities has to be checked: if the two pieces of
   every test set together weigh AT MOST the test set, then es is Caratheodory
   measurable, the reverse inequality being automatic from subadditivity.
   Thayer states this as the displayed inequality (75) in the paragraph after
   Def. 4.2 (p. 30) -- an unnumbered remark, so the citation is to the
   equation, not to a numbered result.  This is the working form of the
   measurability test and the reason it is stated at all.")
(gloss!   'caratheodory-measurable-sigma-algebra
  "Caratheodory's theorem, first half: the sets that split every test set
   additively for an outer measure mu form a sigma-algebra on omega.  Thayer
   Prop. 4.4 (p. 30) states both halves in one sentence ('the mu* measurable
   sets form a (non-empty) sigma-algebra A and mu*|A is a countably additive
   measure'); VNB splits it into this and caratheodory-measure, because the
   two conclusions are about different objects and a proof will want them
   separately.  Rudin does not carry the Caratheodory construction in
   Chapter 1, so no Rudin number is given.")
(gloss!   'caratheodory-measure
  "Caratheodory's theorem, second half: the restriction of the outer measure
   mu to the sigma-algebra of its measurable sets is a countably additive
   measure.  Thayer Prop. 4.4 (p. 30), written there as mu*|A; VNB writes the
   restriction with the kernel's RES head.  See
   caratheodory-measurable-sigma-algebra for why the source's one statement is
   two here.")
