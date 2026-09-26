;;; rake-combinatorics2.scm -- BATCH U of the 2026-09-18 rake (batch 5, the
;;; off-bill supports): finite combinatorics.  Every statement is copied
;;; LITERALLY from its support site; the sites are named beside each proof.
;;; Six results, all `proven modulo 0'.
;;;
;;;   interval-card         structure-library/matrix.scm:135      (support)
;;;   choose-in-nn          structure-library/injection.scm:281   (support)
;;;   injection-from-empty  structure-library/injection.scm:168   (AXIOM, unwarranted)
;;;   permutations-zero     structure-library/injection.scm:238   (support)
;;;   fibrewise-finite      NEW -- the content of infinite pigeonhole
;;;   pigeonhole-infinite   theorem-library/pigeonhole.scm:24     (support)
;;;
;;; LOAD WINDOW [256, end) -- the file may occupy any slot in it.
;;;   lo = 256: the latest citations are `succ-nn-ord', `card-power-nn',
;;;             `choose-set-unfold' and `subset-of-empty-is-empty', all PROVEN
;;;             in theorem-library/rake-combinatorics (position 255).  Next
;;;             latest: card-union-nn (card-inequalities, 254), interval-succ-
;;;             insert (rake-finsum-laws2, 246), card-subset-nn (242),
;;;             nn-succ-le-antisym (nn-order-via-rr, 220), interval-membership
;;;             (171), interval-1-0-empty (mat-basics, 169), nn-le-refl
;;;             (nn-order-basics, 168), fun-apply-type-c (fun-apply-type-proof,
;;;             162), card-singleton (card-singleton-proof, 155), interval-in-set
;;;             (interval-basics, 151), eq-sym (equality-basics, 148).  Everything
;;;             else is primitive or definitional (theory.scm, number-systems,
;;;             ordinals, cardinality, injection, matrix).
;;;   hi = end: NO leaf proven here has a citer anywhere in the tree -- these are
;;;             the off-bill supports.  (`interval-card' is NOT `interval-card-in-nn',
;;;             which is a different, heavily cited support and is untouched.)
;;;
;;; Helper prefix `r5u-'.  All helpers are file-local.

;;; ---------------------------------------------------------------------
;;; Helpers
;;; ---------------------------------------------------------------------

(define (r5u-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r5u: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r5u: proof not complete" name))))

;; `fact' of a membership IFF lands BOTH the instance and the universal, and
;; dk-deepest cannot separate them; name the instance by its left-hand side.
;; (iff-for retired 2026-09-25: the kit's `iff-for')

;;; =====================================================================
;;; (1) interval-card -- structure-library/matrix.scm:135
;;;       forall n in NN.  CARD(INTERVAL(1, n)) = n
;;;
;;; NN induction.  Base: interval-1-0-empty + card-empty.  Step:
;;; interval-succ-insert turns INTERVAL(1, succ n) into
;;; INTERVAL(1,n) u {succ n}; succ n is NOT in INTERVAL(1,n) (it would make
;;; succ n <= n), so card-insert bumps the cardinal by succ_ORD, and
;;; succ-nn-ord identifies that with succ on NN.
;;; =====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (CARD (INTERVAL 1 n)) n)))))
(let* ((R    (use-induction))
       (base (cdr (assq 'base R)))
       (step (cdr (assq 'step R)))
       (v    (cdr (assq 'var  R)))
       (sn   (list 'succ v))
       (ivl  (list 'INTERVAL 1 v)))
  (dk-focus! base)
  (fact 'interval-1-0-empty)
  (subst '(= (INTERVAL 1 0) EMPTY-SET))
  (fact 'card-empty)
  (ass)
  (dk-focus! step)
  (fact 'interval-succ-insert v)
  (subst (list '= (list 'INTERVAL 1 sn) (list 'UNION ivl (list 'PAIR sn sn))))
  (fact 'interval-in-set 1 v)
  (fact 'nn-succ-closed v)
  (fact 'membership-implies-sethood sn 'NN)
  (have! (list 'NOT (list 'IN sn ivl))
    (lambda ()
      (di)
      (fact 'interval-membership 1 v sn)
      ;; NOT (succ n <= n).  `nn-succ-not-le' says this in one line but is
      ;; proven only at poly-degree-laws (load position 317); nn-le-refl +
      ;; nn-succ-le-antisym say it at 220, which is what keeps this file's
      ;; window open from 256.
      (fact 'nn-le-refl sn)
      (fact 'nn-succ-le-antisym v sn)
      (dk-only! (iff-for (list 'IN sn ivl))
                (list 'IN sn ivl)
                (list 'NOT (list '<= sn v)))
      (prop)))
  (have! (list 'AND (list 'IN sn 'SET) (list 'NOT (list 'IN sn ivl))))
  ;; card-insert asks that the set being extended be FINITE since 2026-09-18
  ;; (structure-library/cardinality.scm).  Here that is the induction
  ;; hypothesis itself: CARD(INTERVAL(1,n)) = n, and n is in NN.
  (have! (list 'IN (list 'CARD ivl) 'NN)
         (lambda () (subst (list '= (list 'CARD ivl) v)) (ass)))
  (fact 'card-insert ivl sn)
  (subst (list '= (list 'CARD (list 'UNION ivl (list 'PAIR sn sn)))
                  (list 'succ_ORD (list 'CARD ivl))))
  (subst (list '= (list 'CARD ivl) v))
  (fact 'nn-subset-ord v)
  (fact 'ord-succ-in v)
  (fact 'succ-nn-ord v)
  (subst (list '= sn (list 'succ_ORD v)))
  (rfl))
(r5u-check! 'interval-card)
(qed 'interval-card)
(topic! 'interval-card 'combinatorial)

;;; =====================================================================
;;; (2) choose-in-nn -- structure-library/injection.scm:281
;;;       forall n, m in NN.  CHOOSE(n, m) in NN
;;;
;;; CHOOSE(n,m) = CARD(CHOOSE-SET(n,m)) and CHOOSE-SET(n,m) is a separation
;;; over POWER(ORD-SEGMENT n), which is finite by card-power-nn (proven,
;;; rake-combinatorics.scm) off card-segment.  card-subset-nn then types the
;;; cardinal of the subset.
;;; =====================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN) (FORALL m (IMPLIES (IN m NN) (IN (CHOOSE n m) NN)))))))
(dk-peel!)
(let* ((g   (dk-goal))                      ; (IN (CHOOSE n m) NN)
       (ch  (cadr g))
       (nv  (cadr ch))
       (mv  (caddr ch))
       (seg (list 'ORD-SEGMENT nv))
       (P   (list 'POWER seg))
       (CS  (list 'CHOOSE-SET nv mv))
       (sub (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ CS) (list 'IN 'z_ P)))))
  (mac 'CHOOSE)
  (fact 'nn-subset-ord nv)
  (fact 'ord-segment-is-set nv)
  (fact 'power-set seg)
  (fact 'card-segment nv)
  (have! (list 'IN (list 'CARD seg) 'NN)
         (lambda () (subst (list '= (list 'CARD seg) nv)) (ass)))
  (have! (list 'AND (list 'IN seg 'SET) (list 'IN (list 'CARD seg) 'NN)))
  (fact 'card-power-nn seg)
  (have! (list 'IN CS 'SET)
         (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
  (have! sub
         (lambda ()
           (di)
           (let ((zz (cadr (dk-goal))))
             (mac-h 'choose-set-unfold (list 'IN zz CS))
             (sep-me (list 'IN zz (list 'SEP 'A P (list '= (list 'CARD 'A) mv))))
             (ass))))
  (have! (list 'AND (list 'IN P 'SET) (list 'IN (list 'CARD P) 'NN)))
  (have! (list 'AND (list 'IN CS 'SET) sub))
  (fact 'card-subset-nn P CS)
  (ass))
(r5u-check! 'choose-in-nn)
(qed 'choose-in-nn)
(topic! 'choose-in-nn 'combinatorial)

;;; =====================================================================
;;; (3) injection-from-empty (AUX -- structure-library/injection.scm:167 is an
;;;     UNWARRANTED AXIOM, i.e. `trust: none' to any citer)
;;;       forall C in SET.  CARD(INJECTION(EMPTY-SET, C)) = succ 0
;;;
;;; The empty domain has exactly one function into C, so INJECTION(EMPTY-SET,C)
;;; is the singleton {L} where L is the identity VNB-LAMBDA on EMPTY-SET:
;;; `fun-domain-extensionality' collapses any two functions with domain
;;; EMPTY-SET (the pointwise hypothesis is vacuous), and `lam-t' exhibits L.
;;; No `fun-no-junk' and no skolemization are needed -- the singleton does not
;;; have to be EMPTY-SET, only to BE a singleton.
;;; =====================================================================
(define r5u-lam '(VNB-LAMBDA x_ EMPTY-SET x_))

;; the vacuously-true universal over EMPTY-SET: peel it and refute the guard.
(define (r5u-vacuous!)
  (let* ((landed (dk-peel!))
         (g (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (eq? (caddr f) 'EMPTY-SET)))
                    landed)))
    (if (null? g) (error "r5u-vacuous!: no EMPTY-SET guard landed" landed))
    ;; TRIM before `prop': in a deep context its atom cap drops the very pair
    ;; P / NOT P it needs and it reports a countermodel (CLAUDE.md).
    (fact 'empty-set-has-no-members (cadr (car g)))
    (dk-only! (car g) (list 'NOT (car g)))
    (prop)))

(sp (make-wff
 '(FORALL C (IMPLIES (IN C SET) (= (CARD (INJECTION EMPTY-SET C)) (succ 0))))))
(di)
(let* ((cv  (caddr (cadr (cadr (dk-goal)))))
       (L   r5u-lam)
       (inj (list 'INJECTION 'EMPTY-SET cv))
       (fnc (list 'FUN 'EMPTY-SET cv))
       (fn1 (list 'FUN 'EMPTY-SET))
       (pr  (list 'PAIR L L)))
  (fact 'empty-set-is-set)
  ;; L is a function EMPTY-SET -> C
  (have! (list 'IN L fnc)
    (lambda ()
      (for-each (lambda (leaf)
                  (dk-focus! leaf)
                  (if (equal? (dk-goal) '(in empty-set set))
                      (ass)
                      (r5u-vacuous!)))
                (dk-opened (lambda () (lam-t))))))
  (have! (list 'AND (list 'IN L fnc) (list 'IN 'EMPTY-SET 'SET)))
  (fact 'fun-elements-are-sets 'EMPTY-SET cv L)     ; (IN L SET)
  (have! (list 'IN L fn1)
    (lambda ()
      (fact 'fun-codomain-iff 'EMPTY-SET cv L)
      (dk-only! (iff-for (list 'IN L fnc)) (list 'IN L fnc))
      (prop)))
  ;; INJECTION(EMPTY-SET, C) = {L}
  (have! (list '= inj pr)
    (lambda ()
      (bc* 'class-extensionality)
      (di)
      (let ((xv (cadr (cadr (dk-goal)))))
        (have! (list 'AND (list 'IN L 'SET) (list 'IN L 'SET)))
        (fact 'pairing-membership L L)
        (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                          (equal? (caddr (cadr (caddr f))) pr)))
                         "the pairing universal")
                xv)
        (let ((pm (iff-for (list 'IN xv pr))))
          ;; ->
          (have! (list 'IMPLIES (list 'IN xv inj) (list 'IN xv pr))
            (lambda ()
              (di)
              (fact 'injection-membership-iff 'EMPTY-SET cv xv)
              (have! (list 'IN xv fnc)
                (lambda ()
                  (dk-only! (iff-for (list 'IN xv inj)) (list 'IN xv inj))
                  (prop)))
              (have! (list 'IN xv fn1)
                (lambda ()
                  (fact 'fun-codomain-iff 'EMPTY-SET cv xv)
                  (dk-only! (iff-for (list 'IN xv fnc)) (list 'IN xv fnc))
                  (prop)))
              (have! (list 'FORALL 'w_ (list 'IMPLIES (list 'IN 'w_ 'EMPTY-SET)
                                             (list '= (list xv 'w_) (list L 'w_))))
                     r5u-vacuous!)
              (fact 'fun-domain-extensionality 'EMPTY-SET xv L)
              (dk-only! pm (list '= xv L))
              (prop)))
          ;; <-
          (have! (list 'IMPLIES (list 'IN xv pr) (list 'IN xv inj))
            (lambda ()
              (di)
              (have! (list '= xv L)
                     (lambda () (dk-only! pm (list 'IN xv pr)) (prop)))
              (subst (list '= xv L))
              (fact 'injection-membership-iff 'EMPTY-SET cv L)
              (let* ((iff  (iff-for (list 'IN L inj)))
                     (body (caddr iff))
                     (injv (caddr body)))
                (have! injv r5u-vacuous!)
                (have! body)
                (dk-only! iff body)
                (prop))))
          (dk-only! (list 'IMPLIES (list 'IN xv inj) (list 'IN xv pr))
                    (list 'IMPLIES (list 'IN xv pr) (list 'IN xv inj)))
          (prop)))))
  (subst (list '= inj pr))
  (fact 'card-singleton L)
  (ass))
(r5u-check! 'injection-from-empty)
(qed 'injection-from-empty)
(topic! 'injection-from-empty 'combinatorial)

;;; =====================================================================
;;; (4) permutations-zero -- structure-library/injection.scm:238
;;;       CARD(PERMUTATIONS(0)) = succ 0
;;; =====================================================================
(sp (make-wff '(= (CARD (PERMUTATIONS 0)) (succ 0))))
(mac 'PERMUTATIONS)
(fact 'ord-segment-zero)
(subst '(= (ORD-SEGMENT 0) EMPTY-SET))
(fact 'empty-set-is-set)
(fact 'injection-from-empty 'EMPTY-SET)
(ass)
(r5u-check! 'permutations-zero)
(qed 'permutations-zero)
(topic! 'permutations-zero 'combinatorial)

;;; =====================================================================
;;; (5) fibrewise-finite (AUX) and (6) pigeonhole-infinite
;;;     -- theorem-library/pigeonhole.scm:24
;;;
;;; The content is the contrapositive: a set whose points are classified by
;;; the elements of a FINITE set, with every fibre finite, is finite.  That is
;;; `fibrewise-finite', by finite-set-induction on the value set.
;;;
;;; THE ONE DESIGN POINT.  The classifying map is NOT asked to be a member of
;;; FUN(t_, g_); only the POINTWISE condition `forall y in t_. p_(y) in g_' is.
;;; With a FUN typing the induction step is blocked outright -- it passes to
;;; the subset t_ \ (fibre over the new point), and the tree has no RESTRICTION
;;; of a set-function to a subset (CLAUDE.md, "Two things the tree does NOT
;;; have").  The pointwise condition restricts for free, which is what makes
;;; the induction go through with no new machinery.
;;; =====================================================================
(define (r5u-close-all! thunk)
  (for-each (lambda (l) (dk-focus! l) (ass)) (dk-opened thunk)))

(define (r5u-landed-in landed dom)
  (let ((h (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) dom))) landed)))
    (if (null? h) (error "r5u-landed-in: nothing landed in" (expression->string dom)))
    (cadr (car h))))

;;; ---- the fibre, the class body, the class -----------------------------
(define (r5u-fib pv T c) (list 'SEP 'x T (list '= (list pv 'x) c)))

(define (r5u-body pv gg)
  (list 'FORALL 't_
    (list 'IMPLIES
      (list 'AND (list 'IN 't_ 'SET)
            (list 'AND
                  (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ 't_) (list 'IN (list pv 'y_) gg)))
                  (list 'FORALL 'c_ (list 'IMPLIES (list 'IN 'c_ gg)
                                          (list 'IN (list 'CARD (r5u-fib pv 't_ 'c_)) 'NN)))))
      (list 'IN (list 'CARD 't_) 'NN))))

(define (r5u-cls pv) (list 'COMP 'g_ (r5u-body pv 'g_)))

(define (r5u-step-formula cls)
  (list 'FORALL 'bigs_
    (list 'IMPLIES (list 'AND (list 'IN 'bigs_ 'SET)
                         (list 'AND (list 'IN (list 'CARD 'bigs_) 'NN) (list 'IN 'bigs_ cls)))
      (list 'FORALL 'k_
        (list 'IMPLIES (list 'AND (list 'IN 'k_ 'SET) (list 'NOT (list 'IN 'k_ 'bigs_)))
          (list 'IN (list 'UNION 'bigs_ (list 'PAIR 'k_ 'k_)) cls))))))

(define (r5u-h1? tv U)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                   (let ((b (caddr f)))
                     (and (pair? b) (eq? (car b) 'IMPLIES)
                          (pair? (cadr b)) (eq? (car (cadr b)) 'IN)
                          (equal? (caddr (cadr b)) tv)
                          (pair? (caddr b)) (eq? (car (caddr b)) 'IN)
                          (equal? (caddr (caddr b)) U))))))

(define (r5u-h2? U)
  (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                   (let ((b (caddr f)))
                     (and (pair? b) (eq? (car b) 'IMPLIES)
                          (pair? (cadr b)) (eq? (car (cadr b)) 'IN)
                          (equal? (caddr (cadr b)) U)
                          (pair? (caddr b)) (eq? (car (caddr b)) 'IN)
                          (pair? (cadr (caddr b))) (eq? (car (cadr (caddr b))) 'CARD))))))

;; (IN c0 (PAIR c0 c0)) and (IN c0 (UNION G (PAIR c0 c0)))
(define (r5u-union-right! G c0)
  (let* ((pk (list 'PAIR c0 c0))
         (U  (list 'UNION G pk)))
    (have! (list 'IN c0 pk)
      (lambda ()
        (have! (list 'AND (list 'IN c0 'SET) (list 'IN c0 'SET)))
        (fact 'pairing-membership c0 c0)
        (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                          (equal? (caddr (cadr (caddr f))) pk)))
                         "the pairing universal")
                c0)
        (have! (list '= c0 c0) (lambda () (rfl)))
        (dk-only! (iff-for (list 'IN c0 pk)) (list '= c0 c0))
        (prop)))
    (have! (list 'IN c0 U)
      (lambda ()
        (fact 'union-membership G pk c0)
        (dk-only! (iff-for (list 'IN c0 U)) (list 'IN c0 pk))
        (prop)))))

;; (IN e (UNION G (PAIR c0 c0))) from (IN e G) in context
(define (r5u-union-left! G c0 e)
  (let* ((pk (list 'PAIR c0 c0))
         (U  (list 'UNION G pk)))
    (have! (list 'IN e U)
      (lambda ()
        (fact 'union-membership G pk e)
        (dk-only! (iff-for (list 'IN e U)) (list 'IN e G))
        (prop)))))

;;; =====================================================================
;;; fibrewise-finite (AUX):  if every value of p_ on t_ lies in the finite
;;; set g_ and every fibre is finite, then t_ is finite.
;;;
;;; finite-set-induction on g_.  The point of the formulation is that the
;;; classifying map is NOT required to be a member of FUN(t_, g_): only the
;;; pointwise condition `forall y in t_. p_(y) in g_' is asked for, and THAT
;;; survives passing to a subset.  With a FUN typing the step is blocked --
;;; the tree has no RESTRICTION of a set-function to a subset.
;;; =====================================================================

(define (r5u-ff-base! pv)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (equal? (dk-goal) '(in empty-set set))
         (begin (fact 'empty-set-is-set) (ass))
         (let* ((landed (dk-peel!)))
           (dk-split-all! landed)
           (let* ((tv   (cadr (cadr (dk-goal))))
                  (univ (dk-pick (r5u-h1? tv 'EMPTY-SET) "the values-in-EMPTY-SET universal")))
             (have! (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ tv) (list 'IN 'z_ 'EMPTY-SET)))
               (lambda ()
                 (let* ((l2 (dk-peel!))
                        (zv (r5u-landed-in l2 tv))
                        (got (dk-apply! univ zv)))
                   (fact 'empty-set-has-no-members (list pv zv))
                   (dk-only! got (list 'NOT got))
                   (prop))))
             (fact 'subset-of-empty-is-empty tv)
             (subst (list '= tv 'EMPTY-SET))
             (fact 'card-empty)
             (subst '(= (CARD EMPTY-SET) 0))
             (fact 'nn-zero-in)
             (ass)))))
   (dk-opened (lambda () (comp-mi)))))

;; the property leaf of the step: t_ arbitrary, values in U = G u {c0}
(define (r5u-ff-inner! pv G c0 cls)
  (let* ((pk (list 'PAIR c0 c0))
         (U  (list 'UNION G pk)))
    (dk-split-all! (dk-peel!))
    (let* ((tv (cadr (cadr (dk-goal))))
           (T  (list 'SEP 'x tv (list 'NOT (list '= (list pv 'x) c0))))
           (K  (r5u-fib pv tv c0))
           (H1 (dk-pick (r5u-h1? tv U) "H1: values land in U"))
           (H2 (dk-pick (r5u-h2? U) "H2: fibres over U are finite")))
      (have! (list 'IN T 'SET) (lambda () (sep-set) (ass)))
      (have! (list 'IN K 'SET) (lambda () (sep-set) (ass)))
      ;; |K| in NN
      (r5u-union-right! G c0)
      (dk-apply! H2 c0)
      ;; |T| in NN, by the induction hypothesis at G
      (comp-me (list 'IN G cls))
      (let ((H1T (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ T) (list 'IN (list pv 'y_) G))))
            (H2T (list 'FORALL 'c_ (list 'IMPLIES (list 'IN 'c_ G)
                                         (list 'IN (list 'CARD (r5u-fib pv T 'c_)) 'NN)))))
        (have! H1T
          (lambda ()
            (let* ((l  (dk-peel!))
                   (yv (r5u-landed-in l T)))
              (sep-me (list 'IN yv T))
              (dk-apply! H1 yv)
              (fact 'union-membership G pk (list pv yv))
              (have! (list 'AND (list 'IN c0 'SET) (list 'IN c0 'SET)))
              (fact 'pairing-membership c0 c0)
              (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                                (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                                (equal? (caddr (cadr (caddr f))) pk)))
                               "the pairing universal")
                      (list pv yv))
              (dk-only! (iff-for (list 'IN (list pv yv) U))
                        (iff-for (list 'IN (list pv yv) pk))
                        (list 'IN (list pv yv) U)
                        (list 'NOT (list '= (list pv yv) c0)))
              (prop))))
        (have! H2T
          (lambda ()
            (let* ((l  (dk-peel!))
                   (cv (r5u-landed-in l G))
                   (S1 (r5u-fib pv T cv))
                   (S2 (r5u-fib pv tv cv)))
              (have! (list 'NOT (list '= cv c0))
                (lambda ()
                  (di)
                  (fact 'eq-sym cv c0)
                  (have! (list 'IN c0 G) (lambda () (subst (list '= c0 cv)) (ass)))
                  (ai (list 'NOT (list 'IN c0 G)))))
              (have! (list '= S1 S2)
                (lambda ()
                  (bc* 'class-extensionality)
                  (dk-peel!)
                  (let* ((wv (cadr (cadr (dk-goal))))
                         (i1 (list 'IMPLIES (list 'IN wv S1) (list 'IN wv S2)))
                         (i2 (list 'IMPLIES (list 'IN wv S2) (list 'IN wv S1))))
                    (have! i1
                      (lambda ()
                        (di)
                        (sep-me (list 'IN wv S1))
                        (sep-me (list 'IN wv T))
                        (r5u-close-all! (lambda () (sep-mi)))))
                    (have! i2
                      (lambda ()
                        (di)
                        (sep-me (list 'IN wv S2))
                        (have! (list 'NOT (list '= (list pv wv) c0))
                          (lambda ()
                            (di)
                            (fact 'eq-sym (list pv wv) cv)
                            (have! (list '= cv c0)
                                   (lambda () (subst (list '= cv (list pv wv))) (ass)))
                            (ai (list 'NOT (list '= cv c0)))))
                        (have! (list 'IN wv T)
                               (lambda () (r5u-close-all! (lambda () (sep-mi)))))
                        (r5u-close-all! (lambda () (sep-mi)))))
                    (dk-only! i1 i2)
                    (prop))))
              (subst (list '= S1 S2))
              (r5u-union-left! G c0 cv)
              (dk-apply! H2 cv)
              (ass))))
        (have! (list 'AND (list 'IN T 'SET) (list 'AND H1T H2T)))
        (dk-apply! (r5u-body pv G) T))
      ;; t_ = T u K
      (have! (list '= tv (list 'UNION T K))
        (lambda ()
          (bc* 'class-extensionality)
          (dk-peel!)
          (let* ((wv (cadr (cadr (dk-goal))))
                 (UTK (list 'UNION T K))
                 (i1 (list 'IMPLIES (list 'IN wv tv) (list 'IN wv UTK)))
                 (i2 (list 'IMPLIES (list 'IN wv UTK) (list 'IN wv tv))))
            (have! i1
              (lambda ()
                (di)
                (fact 'union-membership T K wv)
                (let ((iff (iff-for (list 'IN wv UTK)))
                      (a1  (list 'IMPLIES (list '= (list pv wv) c0) (list 'IN wv K)))
                      (a2  (list 'IMPLIES (list 'NOT (list '= (list pv wv) c0)) (list 'IN wv T))))
                  (have! a1 (lambda () (di) (r5u-close-all! (lambda () (sep-mi)))))
                  (have! a2 (lambda () (di) (r5u-close-all! (lambda () (sep-mi)))))
                  (dk-only! iff a1 a2 (list 'IN wv tv))
                  (prop))))
            (have! i2
              (lambda ()
                (di)
                (fact 'union-membership T K wv)
                (let ((iff (iff-for (list 'IN wv UTK)))
                      (a1  (list 'IMPLIES (list 'IN wv T) (list 'IN wv tv)))
                      (a2  (list 'IMPLIES (list 'IN wv K) (list 'IN wv tv))))
                  (have! a1 (lambda () (di) (sep-me (list 'IN wv T)) (ass)))
                  (have! a2 (lambda () (di) (sep-me (list 'IN wv K)) (ass)))
                  (dk-only! iff a1 a2 (list 'IN wv UTK))
                  (prop))))
            (dk-only! i1 i2)
            (prop))))
      (fact 'card-union-nn T K)
      (subst (list '= tv (list 'UNION T K)))
      (ass))))

(define (r5u-ff-step! pv cls)
  (dk-split-all! (dk-peel!))
  (let* ((g  (dk-goal))
         (U  (cadr g))
         (gs (cadr U))
         (c0 (cadr (caddr U))))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (equal? (dk-goal) (list 'in U 'set))
           (begin (have! (list 'AND (list 'IN c0 'SET) (list 'IN c0 'SET)))
                  (fact 'pairing c0 c0)
                  (have! (list 'AND (list 'IN gs 'SET) (list 'IN (list 'PAIR c0 c0) 'SET)))
                  (fact 'union-set-closure gs (list 'PAIR c0 c0))
                  (ass))
           (r5u-ff-inner! pv gs c0 cls)))
     (dk-opened (lambda () (comp-mi))))))

(sp (make-wff
  (list 'FORALL 'p_
    (list 'FORALL 'g_
      (list 'IMPLIES (list 'AND (list 'IN 'g_ 'SET) (list 'IN (list 'CARD 'g_) 'NN))
            (r5u-body 'p_ 'g_))))))
(dk-split-all! (dk-peel!))
(let* ((tv  (cadr (cadr (dk-goal))))
       (gt  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'NN)
                                      (pair? (cadr f)) (eq? (car (cadr f)) 'CARD)))
                     "the finiteness of g_"))
       (gv  (cadr (cadr gt)))
       (H1  (dk-pick (r5u-h1? tv gv) "H1 of the goal"))
       (pv  (car (cadr (caddr (caddr H1)))))
       (cls (r5u-cls pv))
       (stp (r5u-step-formula cls))
       (H2  (dk-pick (r5u-h2? gv) "H2 of the goal")))
  (have! (list 'IN 'EMPTY-SET cls) (lambda () (r5u-ff-base! pv)))
  (have! stp (lambda () (r5u-ff-step! pv cls)))
  (have! (list 'AND (list 'IN 'EMPTY-SET cls) stp))
  (let ((ind (dk-fact! 'finite-set-induction cls)))
    (have! (list 'AND (list 'IN gv 'SET) (list 'IN (list 'CARD gv) 'NN)))
    (let ((ing (dk-apply! ind gv)))
      (comp-me ing)
      (have! (list 'AND (list 'IN tv 'SET) (list 'AND H1 H2)))
      (dk-apply! (r5u-body pv gv) tv)
      (ass))))
(r5u-check! 'fibrewise-finite)
(qed 'fibrewise-finite)
(topic! 'fibrewise-finite 'combinatorial)

;;; =====================================================================
;;; pigeonhole-infinite -- theorem-library/pigeonhole.scm:24
;;; =====================================================================
(sp (make-wff
 '(FORALL S
     (IMPLIES (AND (IN S SET) (NOT (IN (CARD S) NN)))
       (FORALL F
         (IMPLIES (AND (IN F SET) (IN (CARD F) NN))
           (FORALL pmap_
             (IMPLIES (IN pmap_ (FUN S F))
               (FORSOME c
                 (AND (IN c F)
                      (NOT (IN (CARD (SEP x S (= (pmap_ x) c))) NN))))))))))))
(dk-split-all! (dk-peel!))
(let* ((fh (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)))
                    "the typing of pi"))
       (pv (cadr fh))
       (Sv (cadr (caddr fh)))
       (Fv (caddr (caddr fh)))
       (ex (dk-goal))
       (H1 (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ Sv) (list 'IN (list pv 'y_) Fv))))
       (H2 (list 'FORALL 'c_ (list 'IMPLIES (list 'IN 'c_ Fv)
                                   (list 'IN (list 'CARD (r5u-fib pv Sv 'c_)) 'NN)))))
  (pbc)
  (have! H1
    (lambda ()
      (let* ((l (dk-peel!)) (yv (r5u-landed-in l Sv)))
        (fact 'fun-apply-type-c pv Sv Fv yv)
        (ass))))
  (have! H2
    (lambda ()
      (let* ((l (dk-peel!)) (cv (r5u-landed-in l Fv)))
        (pbc)
        (have! ex
          (lambda ()
            (ew cv)
            (dk-only! (list 'IN cv Fv)
                      (list 'NOT (list 'IN (list 'CARD (r5u-fib pv Sv cv)) 'NN)))
            (prop)))
        (ai (list 'NOT ex)))))
  (have! (list 'AND (list 'IN Fv 'SET) (list 'IN (list 'CARD Fv) 'NN)))
  (have! (list 'AND (list 'IN Sv 'SET) (list 'AND H1 H2)))
  (fact 'fibrewise-finite pv Fv Sv)
  (ai (list 'NOT (list 'IN (list 'CARD Sv) 'NN))))
(r5u-check! 'pigeonhole-infinite)
(qed 'pigeonhole-infinite)
(topic! 'pigeonhole-infinite 'combinatorial)

;;; =====================================================================
;;; BATCH U -- the leaves NOT proven here, and why.  Routes, not excuses.
;;; =====================================================================
;;;
;;; nn-enum-spec (theorem-library/subsequence-capture.scm:46) -- FIFTEEN LINES,
;;;   but it CHAINS to an asserted leaf, so it is left.  NN-ENUM(S) is CHOICE
;;;   over the SEP of strictly monotone f in FUN(NN,S); `mac 'NN-ENUM' on the
;;;   goal, `sep-mi'/`sep-me' around `choice-axiom' (forsome x. x in a =>
;;;   CHOICE(a) in a), and the non-emptiness of that SEP is exactly
;;;   `subsequence-capture' (same file, still asserted).  Proving it would trade
;;;   one asserted leaf for another; the batch-5 rule says report instead.
;;;
;;; well-ordering-principle (theorem-library/well-ordering.scm:10) -- NOT a
;;;   restatement of nn-least-element (which well-orders NN; this asserts that
;;;   EVERY set bijects with ORD-SEGMENT of its cardinal).  It is a FOUNDATIONAL
;;;   decision, and its own warrant says so: CARD is AXIOMATISED in
;;;   cardinality.scm, never defined as the least ordinal in bijection, so this
;;;   statement is part of what GIVES CARD its meaning.  Proving it needs global
;;;   choice plus transfinite recursion, and would still only relate CARD to a
;;;   definition the tree has declined to make.  It belongs on the primitive
;;;   shelf beside the other card-* axioms, by an explicit decision, or CARD has
;;;   to be defined first (the L1/L2 route).  Not an agent's call.
;;;
;;; injection-extension-recurrence (structure-library/injection.scm:190), and
;;;   with it permutation-recurrence (:245) and injection-count-falling (:317),
;;;   which are its two corollaries and nothing else -- the recurrence is the
;;;   whole content.  Its proof is a BIJECTION
;;;       INJECTION(A u {b}, C)  ~  { <g, c> : g in INJECTION(A,C),
;;;                                           c in C \ IMAGE(g, A) }
;;;   and the tree cannot yet form the right-hand side: CARTESIAN is binary but
;;;   the SEP would have to separate a class of PAIRS by a property of both
;;;   coordinates, and there is no TUPLES-membership read-off for a literal
;;;   LIST and no tuple-extensionality (the same wall batch L hit on
;;;   dc-on-nn-pred).  Even granting it, the count needs "summing a CONSTANT m
;;;   over the fibres", i.e. a card-of-a-fibred-set lemma the tree has not got.
;;;   A separate arc, not a leaf.
;;;
;;; choose-succ (Pascal, structure-library/injection.scm:289) -- route, ~400
;;;   lines.  Split CHOOSE-SET(succ n, succ k) on membership of the new point n:
;;;     A = the members avoiding n.  A = CHOOSE-SET(n, succ k) by class-
;;;         extensionality, using ord-segment-insert (ORD-SEGMENT(succ n) =
;;;         ORD-SEGMENT(n) u {n}) and power-set-membership.
;;;     B = the members containing n.  B = IMAGE(VNB-LAMBDA S ... S u {n},
;;;         CHOOSE-SET(n,k)); the lambda is injective on CHOOSE-SET(n,k)
;;;         (n is in neither S nor S', so S u {n} = S' u {n} gives S = S' by
;;;         extensionality), so it is a member of INJECTION(CHOOSE-SET(n,k), _)
;;;         by lam-t + injection-membership-iff, and card-image-injection gives
;;;         CARD(B) = CHOOSE(n,k).  That each S u {n} has cardinal succ k is
;;;         card-insert + succ-nn-ord.
;;;   Then A n B = EMPTY-SET and card-union-disjoint.  The expensive parts are
;;;   the IMAGE membership round trips and the beta reductions, not the idea.
;;;   Batch P deferred it for the same reason; it is one assignment.
;;;
;;; choose-times-factorial (structure-library/injection.scm:336) -- the double
;;;   count.  It needs injection-count-falling (hence the recurrence, above) AND
;;;   the factorisation of an injection into (image, bijection onto the image),
;;;   which is a second fibred-count argument.  Two arcs away.
;;;
;;; prod-of-sums-expansion (theorem-library/prod-of-sums.scm:137) -- route only,
;;;   and every brick it names is now PROVEN: finite-set-induction on X, with
;;;   prod-ring-empty / prod-ring-insert / power-insert-cover / power-insert-
;;;   disjoint / power-of-empty (all theorem-library/rake-combinatorics.scm) and
;;;   ring-left-dist.  The base is POWER(EMPTY-SET) = {EMPTY-SET} contributing
;;;   ONE*ONE; the step factors (a(k0)+b(k0)) out with prod-ring-insert,
;;;   distributes, and reindexes the FINSUM over POWER(X u {k0}) along the
;;;   insert-split -- that reindex is `finsum-insert-ag' plus a
;;;   `finsum-reindex'-shaped transport along S |-> S u {k0}, and
;;;   finsum-reindex is itself still asserted (batch V).  So it waits on batch V.
