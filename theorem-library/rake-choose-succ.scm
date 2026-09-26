;;; rake-choose-succ.scm -- PASCAL'S RULE for the binomial coefficient, and the
;;; CHOOSE-SET lemmas it is assembled from.  Rake batch 5b, assignment 5b-G.
;;;
;;; THE TARGET (statement copied LITERALLY from structure-library/injection.scm,
;;; where it stands as the support `choose-succ'):
;;;
;;;   (FORALL n (IMPLIES (IN n NN)
;;;     (FORALL k (IMPLIES (IN k NN)
;;;       (= (CHOOSE (succ n) (succ k))
;;;          (+ (CHOOSE n k) (CHOOSE n (succ k))))))))
;;;
;;; CHOOSE(n,m) is CARD(CHOOSE-SET(n,m)) and CHOOSE-SET(n,m) is the SEP
;;;   { A in POWER(ORD-SEGMENT n) | CARD A = m }.
;;;
;;; THE ARGUMENT.  The (k+1)-subsets of ORD-SEGMENT(succ n) = {0,...,n} split on
;;; whether they contain the new point n:
;;;   * those that do NOT are exactly CHOOSE-SET(n, succ k);
;;;   * those that DO are exactly the image of CHOOSE-SET(n, k) under
;;;     L = (VNB-LAMBDA s_ (CHOOSE-SET n k) (UNION s_ (PAIR n n))),
;;;     and L is injective there (n is in no member, so the inserted point can
;;;     be removed again), so card-image-injection gives that half the cardinal
;;;     CHOOSE(n,k).
;;; The two halves are disjoint, so card-union-disjoint adds them, and
;;; nn-add-comm puts the sum in the order the support states it.
;;;
;;; Eleven lemmas are proved on the way, each installed as a theorem of its own so
;;; that the assembly is short and each piece is separately checkable:
;;;
;;;   choose-card-unfold           CARD(CHOOSE-SET(n,m)) == CHOOSE(n,m)
;;;   choose-set-mem-iff           the SEP membership as an IFF
;;;   choose-set-avoids-point      a member of CHOOSE-SET(n,m) omits n
;;;   choose-set-widen             CHOOSE-SET(n,m) subset CHOOSE-SET(succ n,m)
;;;   choose-set-insert-in         s |-> s u {n} maps CHOOSE-SET(n,k) into
;;;                                CHOOSE-SET(succ n, succ k)
;;;   choose-set-remove-restores   (a \ {n}) u {n} = a when n in a
;;;   choose-set-remove-in         a \ {n} is in CHOOSE-SET(n,k) when a is in
;;;                                CHOOSE-SET(succ n, succ k) and contains n
;;;   choose-set-avoid-in          a in CHOOSE-SET(succ n, succ k) without n is
;;;                                in CHOOSE-SET(n, succ k)
;;;   choose-set-insert-injective  s u {n} = t u {n} => s = t on CHOOSE-SET(n,m)
;;;   choose-set-split             the cover
;;;   choose-set-split-disjoint    the two halves meet nowhere
;;;
;;; LOAD WINDOW [258, end) -- the file may occupy any slot in it.
;;;   lo = 258: the latest citation is `choose-in-nn' (theorem-library/rake-
;;;       combinatorics2, position 257).  Next latest: `choose-set-unfold'
;;;       (rake-combinatorics, 256), `ord-segment-insert' (rake-finsum-core,
;;;       248), `card-subset-nn' (theorem-library/card-subset-nn, fourteen slots
;;;       below rake-combinatorics -- added 2026-09-18 with the card-insert
;;;       finiteness guard, see choose-set-remove-in),
;;;       `difference-membership' / `difference-set' (difference-laws,
;;;       191), `eq-sym' / `eq-trans' (equality-basics, 148), `ord-segment-self'
;;;       (110).  Everything else is primitive or definitional: library.scm
;;;       (extensionality, class-extensionality, power-set, power-set-membership,
;;;       union-membership, union-set-closure, intersection-membership, pairing,
;;;       pairing-membership, membership-implies-sethood,
;;;       empty-set-has-no-members), ordinals.scm (ord-segment-is-set,
;;;       ord-succ-nn, ord-succ-injective, nn-subset-ord), cardinality.scm
;;;       (card-insert, card-in-ord, card-union-disjoint), injection.scm
;;;       (CHOOSE / CHOOSE-SET, injection-membership-iff, image-membership-iff,
;;;       image-set, card-image-injection), number-systems (nn-add-comm,
;;;       nn-succ-closed).
;;;   hi = end: `choose-succ' is cited by NOTHING proven (it is an off-bill
;;;       support; theorem-library/binomial-probe names it in a comment list and
;;;       is not in load.scm).
;;;
;;; Helper prefix `r6g-'.  All helpers are file-local.

;;; ---------------------------------------------------------------------
;;; Helpers
;;; ---------------------------------------------------------------------

(define (r6g-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r6g: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r6g: proof not complete" name))))

;; `fact' of a membership IFF lands BOTH the instance and the universal, and
;; dk-deepest cannot separate them; name the instance by its left-hand side.
;; (iff-for retired 2026-09-25: the kit's `iff-for')

(define (r6g-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))

(define (r6g-pw X A) (list 'IN A (list 'POWER X)))
(define (r6g-sub X A) (list 'FORALL 'z (list 'IMPLIES (list 'IN 'z A) (list 'IN 'z X))))
(define (r6g-sing v)  (list 'PAIR v v))
(define (r6g-del A v) (list 'DIFFERENCE A (r6g-sing v)))
(define (r6g-cs n m)  (list 'CHOOSE-SET n m))

;; pairing-membership's guard sits BETWEEN its binders, so `fact' stops at the
;; detached (FORALL x ...) and the element has to come from `inst*!'.
(define (r6g-pairmem! kk v)
  (let ((g (list 'AND (list 'IN kk 'SET) (list 'IN kk 'SET))))
    (if (not (any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms))) (have! g)))
  (fact 'pairing-membership kk kk)
  (inst*! (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                    (pair? (caddr f)) (eq? (car (caddr f)) 'IFF)
                                    (equal? (caddr (cadr (caddr f))) (r6g-sing kk))))
                   "the pairing universal")
          v)
  (iff-for (list 'IN v (r6g-sing kk))))

;; From (IN a_ (CHOOSE-SET n m)) in context: land the two conjuncts of the SEP
;; membership, the sethood of a_, and the subset universal into ORD-SEGMENT(n).
;; Returns the subset universal.
(define (r6g-open-cs! nv mv av)
  (let* ((mem (list 'IN av (r6g-cs nv mv)))
         (seg (list 'ORD-SEGMENT nv))
         (csi (r6g-mem-iff! mem 'choose-set-mem-iff nv mv av)))
    (have! (list 'AND (r6g-pw seg av) (list '= (list 'CARD av) mv))
           (lambda () (dk-only! csi mem) (prop)))
    (dk-split-all!)
    (let ((pwi (r6g-mem-iff! (r6g-pw seg av) 'power-set-membership seg av)))
      (have! (list 'AND (list 'IN av 'SET) (r6g-sub seg av))
             (lambda () (dk-only! pwi (r6g-pw seg av)) (prop))))
    (dk-split-all!)
    (r6g-sub seg av)))

;; Goal (IN a_ (CHOOSE-SET n m)), given the subset universal and the cardinal
;; equation in context.
(define (r6g-close-cs! nv mv av)
  (let* ((seg (list 'ORD-SEGMENT nv))
         (pwi (r6g-mem-iff! (r6g-pw seg av) 'power-set-membership seg av)))
    (have! (r6g-pw seg av)
           (lambda () (dk-only! pwi (list 'IN av 'SET) (r6g-sub seg av)) (prop)))
    (let ((csi (r6g-mem-iff! (list 'IN av (r6g-cs nv mv)) 'choose-set-mem-iff nv mv av)))
      (dk-only! csi (r6g-pw seg av) (list '= (list 'CARD av) mv))
      (prop))))

;;; ===================================================================
;;; (1) choose-card-unfold -- CARD(CHOOSE-SET(n,m)) == CHOOSE(n,m).
;;;     CHOOSE is a def-functoid, so `mac-h' cannot open it in a HYPOTHESIS by
;;;     its own name (CLAUDE.md, the mac-h trap); the unfold as a THEOREM can.
;;; ===================================================================
(sp (make-wff '(FORALL n_ (FORALL m_ (== (CARD (CHOOSE-SET n_ m_)) (CHOOSE n_ m_))))))
(di)
(mac 'CHOOSE)
(qrfl)
(r6g-check! 'choose-card-unfold)
(qed 'choose-card-unfold)
(topic! 'choose-card-unfold 'plumbing)

;;; ===================================================================
;;; (2) choose-set-mem-iff -- the SEP membership, as an IFF theorem.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (FORALL m_ (FORALL a_
    (IFF (IN a_ (CHOOSE-SET n_ m_))
         (AND (IN a_ (POWER (ORD-SEGMENT n_))) (= (CARD a_) m_))))))))
(di)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (rhs (caddr g)))
  (have! (list 'IMPLIES lhs rhs)
    (lambda ()
      (di)
      (mac-h 'choose-set-unfold lhs)
      (sep-me (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                        (pair? (caddr f)) (eq? (car (caddr f)) 'SEP)))
                       "the SEP membership"))
      (prop)))
  (have! (list 'IMPLIES rhs lhs)
    (lambda ()
      (di)
      (dk-split-all!)
      (mac 'CHOOSE-SET)
      (for-each (lambda (leaf) (dk-focus! leaf) (ass))
                (dk-opened (lambda () (sep-mi))))))
  (prop))
(r6g-check! 'choose-set-mem-iff)
(qed 'choose-set-mem-iff)
(topic! 'choose-set-mem-iff 'plumbing)

;;; ===================================================================
;;; (3) choose-set-avoids-point -- a member of CHOOSE-SET(n,m) omits n.
;;;     It is a subset of ORD-SEGMENT(n), and n is not in ITS OWN segment.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL m_ (FORALL a_ (IMPLIES (IN a_ (CHOOSE-SET n_ m_)) (NOT (IN n_ a_)))))))))
(dk-peel!)
(let* ((g  (dk-goal))                      ; (NOT (IN n a))
       (nv (cadr (cadr g)))
       (av (caddr (cadr g)))
       (mem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'CHOOSE-SET)))
                     "the CHOOSE-SET membership"))
       (mv  (caddr (caddr mem)))
       (seg (list 'ORD-SEGMENT nv)))
  (let ((csi (r6g-mem-iff! mem 'choose-set-mem-iff nv mv av)))
    (have! (r6g-pw seg av) (lambda () (dk-only! csi mem) (prop))))
  (let ((pwi (r6g-mem-iff! (r6g-pw seg av) 'power-set-membership seg av)))
    (have! (r6g-sub seg av)
           (lambda () (dk-only! pwi (r6g-pw seg av)) (prop))))
  (di)                                     ; assume (IN n a); goal FALSITY
  (inst*! (r6g-sub seg av) nv)
  (fact 'ord-segment-self nv)
  (ai (list 'NOT (list 'IN nv seg))))
(r6g-check! 'choose-set-avoids-point)
(qed 'choose-set-avoids-point)
(topic! 'choose-set-avoids-point 'plumbing)

;;; ===================================================================
;;; (4) choose-set-widen -- CHOOSE-SET(n,m) subset CHOOSE-SET(succ n, m).
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL m_ (FORALL a_ (IMPLIES (IN a_ (CHOOSE-SET n_ m_))
                                   (IN a_ (CHOOSE-SET (succ n_) m_)))))))))
(dk-peel!)
(let* ((g  (dk-goal))                      ; (IN a (CHOOSE-SET (succ n) m))
       (av (cadr g))
       (cs (caddr g))
       (nv (cadr (cadr cs)))
       (mv (caddr cs))
       (seg  (list 'ORD-SEGMENT nv))
       (segs (list 'ORD-SEGMENT (list 'succ nv)))
       (pr   (r6g-sing nv))
       (un   (list 'UNION seg pr)))
  (r6g-open-cs! nv mv av)
  (fact 'ord-segment-insert nv)
  (have! (r6g-sub segs av)
    (lambda ()
      (let ((zv (dk-di-var! (lambda (gg) (cadr gg)))))
        (inst*! (r6g-sub seg av) zv)
        (let ((um (r6g-mem-iff! (list 'IN zv un) 'union-membership seg pr zv)))
          (subst (list '= segs un))
          (dk-only! um (list 'IN zv seg) (list 'IN zv av))
          (prop)))))
  (r6g-close-cs! (list 'succ nv) mv av))
(r6g-check! 'choose-set-widen)
(qed 'choose-set-widen)
(topic! 'choose-set-widen 'plumbing)

;;; ===================================================================
;;; (5) choose-set-insert-in -- inserting the new point n into a k-subset of
;;;     ORD-SEGMENT(n) gives a (succ k)-subset of ORD-SEGMENT(succ n).
;;;     card-insert does the counting; it applies because n is in no member
;;;     (lemma 3), and succ_ORD is succ on NN (ord-succ-nn).
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL k_ (IMPLIES (IN k_ NN)
      (FORALL s_ (IMPLIES (IN s_ (CHOOSE-SET n_ k_))
        (IN (UNION s_ (PAIR n_ n_)) (CHOOSE-SET (succ n_) (succ k_)))))))))))
(dk-peel!)
(let* ((g  (dk-goal))                      ; (IN (UNION s {n}) (CHOOSE-SET (succ n) (succ k)))
       (U  (cadr g))
       (sv (cadr U))
       (cs (caddr g))
       (nv (cadr (cadr cs)))
       (kv (cadr (caddr cs)))
       (seg  (list 'ORD-SEGMENT nv))
       (segs (list 'ORD-SEGMENT (list 'succ nv)))
       (pr   (r6g-sing nv))
       (un   (list 'UNION seg pr)))
  (r6g-open-cs! nv kv sv)
  (fact 'membership-implies-sethood nv 'NN)
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (fact 'pairing nv nv)
  (have! (list 'AND (list 'IN sv 'SET) (list 'IN pr 'SET)))
  (fact 'union-set-closure sv pr)
  (fact 'choose-set-avoids-point nv kv sv)
  (fact 'ord-segment-insert nv)
  ;; the cardinal.  card-insert asks that s be FINITE since 2026-09-18
  ;; (structure-library/cardinality.scm); CHOOSE-SET membership says CARD(s) = k.
  (have! (list 'AND (list 'IN nv 'SET) (list 'NOT (list 'IN nv sv))))
  (have! (list 'IN (list 'CARD sv) 'NN)
         (lambda () (subst (list '= (list 'CARD sv) kv)) (ass)))
  (fact 'card-insert sv nv)
  (fact 'ord-succ-nn kv)
  (have! (list '= (list 'CARD U) (list 'succ kv))
    (lambda ()
      (subst (list '= (list 'CARD U) (list 'succ_ORD (list 'CARD sv))))
      (subst (list '= (list 'CARD sv) kv))
      (ass)))
  ;; the inclusion
  (have! (r6g-sub segs U)
    (lambda ()
      (let* ((zv (dk-di-var! (lambda (gg) (cadr gg))))
             (umU (r6g-mem-iff! (list 'IN zv U) 'union-membership sv pr zv))
             (pmz (r6g-pairmem! nv zv))
             (umS (r6g-mem-iff! (list 'IN zv un) 'union-membership seg pr zv))
             (sz  (inst*! (r6g-sub seg sv) zv)))
        (subst (list '= segs un))
        (dk-only! umU pmz umS sz (list 'IN zv U))
        (prop))))
  (r6g-close-cs! (list 'succ nv) (list 'succ kv) U))
(r6g-check! 'choose-set-insert-in)
(qed 'choose-set-insert-in)
(topic! 'choose-set-insert-in 'combinatorial)

;;; ===================================================================
;;; (6) choose-set-remove-restores -- (a \ {n}) u {n} = a when n is in a.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ SET)
    (FORALL a_ (IMPLIES (AND (IN a_ SET) (IN n_ a_))
      (= (UNION (DIFFERENCE a_ (PAIR n_ n_)) (PAIR n_ n_)) a_)))))))
(dk-peel!)
(dk-split-all!)
(let* ((g  (dk-goal))                      ; (= (UNION (DIFFERENCE a {n}) {n}) a)
       (U  (cadr g))
       (av (caddr g))
       (D  (cadr U))
       (nv (cadr (caddr U)))
       (pr (r6g-sing nv)))
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (fact 'pairing nv nv)
  (fact 'difference-set av pr)
  (have! (list 'AND (list 'IN D 'SET) (list 'IN pr 'SET)))
  (fact 'union-set-closure D pr)
  (have! (list 'AND (list 'IN U 'SET) (list 'IN av 'SET)))
  (let ((ext (iff-for (begin (fact 'extensionality U av) (list '= U av)))))
    (have! (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ U) (list 'IN 'y_ av)))
      (lambda ()
        (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
               (umy (r6g-mem-iff! (list 'IN yv U) 'union-membership D pr yv))
               (dmy (r6g-mem-iff! (list 'IN yv D) 'difference-membership av pr yv))
               (pmy (r6g-pairmem! nv yv))
               (kay (list 'IMPLIES (list '= yv nv) (list 'IN yv av))))
          (have! kay (lambda () (di) (subst (list '= yv nv)) (ass)))
          (dk-only! umy dmy pmy kay)
          (prop))))
    (dk-only! ext (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ U) (list 'IN 'y_ av))))
    (prop)))
(r6g-check! 'choose-set-remove-restores)
(qed 'choose-set-remove-restores)
(topic! 'choose-set-remove-restores 'plumbing)

;;; ===================================================================
;;; (7) choose-set-remove-in -- a (succ k)-subset of ORD-SEGMENT(succ n) that
;;;     CONTAINS n loses n to become a k-subset of ORD-SEGMENT(n).
;;;     card-insert runs backwards here: it gives CARD(a) = succ_ORD(CARD(a\{n}))
;;;     and ord-succ-injective cancels the successor against succ k.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL k_ (IMPLIES (IN k_ NN)
      (FORALL a_ (IMPLIES (AND (IN a_ (CHOOSE-SET (succ n_) (succ k_))) (IN n_ a_))
        (IN (DIFFERENCE a_ (PAIR n_ n_)) (CHOOSE-SET n_ k_))))))))))
(dk-peel!)
(dk-split-all!)
(let* ((g  (dk-goal))                      ; (IN (DIFFERENCE a {n}) (CHOOSE-SET n k))
       (D  (cadr g))
       (av (cadr D))
       (cs (caddr g))
       (nv (cadr cs))
       (kv (caddr cs))
       (pr   (r6g-sing nv))
       (U    (list 'UNION D pr))
       (seg  (list 'ORD-SEGMENT nv))
       (segs (list 'ORD-SEGMENT (list 'succ nv)))
       (un   (list 'UNION seg pr)))
  (r6g-open-cs! (list 'succ nv) (list 'succ kv) av)
  (fact 'membership-implies-sethood nv 'NN)
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (fact 'pairing nv nv)
  (fact 'difference-set av pr)
  (fact 'ord-segment-insert nv)
  (fact 'eq-sym segs un)
  ;; D is a subset of ORD-SEGMENT(n): its members are in a, hence in
  ;; ORD-SEGMENT(n) u {n}, and they are not n.
  (have! (r6g-sub seg D)
    (lambda ()
      (let* ((zv  (dk-di-var! (lambda (gg) (cadr gg))))
             (dmz (r6g-mem-iff! (list 'IN zv D) 'difference-membership av pr zv))
             (pmz (r6g-pairmem! nv zv))
             (sz  (inst*! (r6g-sub segs av) zv)))
        (have! (list 'IN zv un) (lambda () (subst (list '= un segs)) (prop)))
        (let ((umz (r6g-mem-iff! (list 'IN zv un) 'union-membership seg pr zv)))
          (dk-only! dmz pmz umz (list 'IN zv un) (list 'IN zv D))
          (prop)))))
  ;; n is not in D
  (let ((dmn (r6g-mem-iff! (list 'IN nv D) 'difference-membership av pr nv))
        (pmn (r6g-pairmem! nv nv)))
    (have! (list '= nv nv) (lambda () (rfl)))
    (have! (list 'NOT (list 'IN nv D))
           (lambda () (dk-only! dmn pmn (list '= nv nv)) (prop))))
  ;; (D u {n}) = a, and card-insert counts it
  (have! (list 'AND (list 'IN av 'SET) (list 'IN nv av)))
  (fact 'choose-set-remove-restores nv av)         ; (= U a)
  (have! (list 'AND (list 'IN nv 'SET) (list 'NOT (list 'IN nv D))))
  ;; card-insert carries a FINITENESS guard since 2026-09-18
  ;; (structure-library/cardinality.scm), and here it is the one place in this
  ;; file where it is not already in hand: D is the set being extended, and its
  ;; cardinal is what the lemma computes.  D is a subset of ORD-SEGMENT(n) --
  ;; established three lines above -- which card-segment counts, so
  ;; card-subset-nn types CARD(D).
  (fact 'nn-subset-ord nv)                         ; (IN n ORD)
  (fact 'ord-segment-is-set nv)                    ; (IN ORD-SEGMENT(n) SET)
  (fact 'card-segment nv)                          ; (= (CARD ORD-SEGMENT(n)) n)
  (have! (list 'IN (list 'CARD seg) 'NN)
         (lambda () (subst (list '= (list 'CARD seg) nv)) (ass)))
  (have! (list 'AND (list 'IN seg 'SET) (list 'IN (list 'CARD seg) 'NN)))
  (have! (list 'AND (list 'IN D 'SET) (r6g-sub seg D)))
  (fact 'card-subset-nn seg D)                     ; (IN (CARD D) NN)
  (fact 'card-insert D nv)                         ; (= (CARD U) (succ_ORD (CARD D)))
  (have! (list '= (list 'CARD U) (list 'CARD av))
         (lambda () (subst (list '= U av)) (rfl)))
  (fact 'eq-sym (list 'CARD U) (list 'CARD av))
  (fact 'eq-trans (list 'CARD av) (list 'CARD U) (list 'succ_ORD (list 'CARD D)))
  ;; succ_ORD(CARD D) = CARD a = succ k = succ_ORD k, and succ_ORD is injective
  (fact 'eq-sym (list 'CARD av) (list 'succ_ORD (list 'CARD D)))
  (fact 'eq-trans (list 'succ_ORD (list 'CARD D)) (list 'CARD av) (list 'succ kv))
  (fact 'ord-succ-nn kv)                           ; (= (succ_ORD k) (succ k))
  (fact 'eq-sym (list 'succ_ORD kv) (list 'succ kv))
  (fact 'eq-trans (list 'succ_ORD (list 'CARD D)) (list 'succ kv) (list 'succ_ORD kv))
  (fact 'card-in-ord D)
  (fact 'nn-subset-ord kv)
  (have! (list 'AND (list 'IN (list 'CARD D) 'ORD)
               (list 'AND (list 'IN kv 'ORD)
                     (list '= (list 'succ_ORD (list 'CARD D)) (list 'succ_ORD kv)))))
  (fact 'ord-succ-injective (list 'CARD D) kv)     ; (= (CARD D) k)
  (r6g-close-cs! nv kv D))
(r6g-check! 'choose-set-remove-in)
(qed 'choose-set-remove-in)
(topic! 'choose-set-remove-in 'combinatorial)

;;; ===================================================================
;;; (8) choose-set-avoid-in -- a member of CHOOSE-SET(succ n, m) that does NOT
;;;     contain n is already a member of CHOOSE-SET(n, m).
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL m_ (FORALL a_ (IMPLIES (AND (IN a_ (CHOOSE-SET (succ n_) m_))
                                        (NOT (IN n_ a_)))
                                   (IN a_ (CHOOSE-SET n_ m_)))))))))
(dk-peel!)
(dk-split-all!)
(let* ((g  (dk-goal))                      ; (IN a (CHOOSE-SET n m))
       (av (cadr g))
       (cs (caddr g))
       (nv (cadr cs))
       (mv (caddr cs))
       (pr   (r6g-sing nv))
       (seg  (list 'ORD-SEGMENT nv))
       (segs (list 'ORD-SEGMENT (list 'succ nv)))
       (un   (list 'UNION seg pr)))
  (r6g-open-cs! (list 'succ nv) mv av)
  (fact 'membership-implies-sethood nv 'NN)
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (fact 'pairing nv nv)
  (fact 'ord-segment-insert nv)
  (fact 'eq-sym segs un)
  (have! (r6g-sub seg av)
    (lambda ()
      (let* ((zv  (dk-di-var! (lambda (gg) (cadr gg))))
             (pmz (r6g-pairmem! nv zv))
             (sz  (inst*! (r6g-sub segs av) zv))
             (kay (list 'IMPLIES (list '= zv nv) (list 'IN nv av))))
        (have! (list 'IN zv un) (lambda () (subst (list '= un segs)) (prop)))
        (have! kay (lambda () (di) (fact 'eq-sym zv nv) (subst (list '= nv zv)) (ass)))
        (let ((umz (r6g-mem-iff! (list 'IN zv un) 'union-membership seg pr zv)))
          (dk-only! pmz umz kay (list 'IN zv un) (list 'NOT (list 'IN nv av)))
          (prop)))))
  (r6g-close-cs! nv mv av))
(r6g-check! 'choose-set-avoid-in)
(qed 'choose-set-avoid-in)
(topic! 'choose-set-avoid-in 'combinatorial)

;;; ===================================================================
;;; (9) choose-set-insert-injective -- s |-> s u {n} is injective on
;;;     CHOOSE-SET(n,m): n belongs to no member, so the inserted point is the
;;;     only difference and set extensionality removes it again.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL m_ (FORALL s_ (IMPLIES (IN s_ (CHOOSE-SET n_ m_))
      (FORALL t_ (IMPLIES (IN t_ (CHOOSE-SET n_ m_))
        (IMPLIES (= (UNION s_ (PAIR n_ n_)) (UNION t_ (PAIR n_ n_)))
                 (= s_ t_)))))))))))
(dk-peel!)
(let* ((g  (dk-goal))                      ; (= s t)
       (sv (cadr g))
       (tv (caddr g))
       (mem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (cadr f) sv)
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'CHOOSE-SET)))
                     "the CHOOSE-SET membership of s"))
       (nv (cadr (caddr mem)))
       (mv (caddr (caddr mem)))
       (pr (r6g-sing nv))
       (Us (list 'UNION sv pr))
       (Ut (list 'UNION tv pr)))
  (fact 'membership-implies-sethood sv (r6g-cs nv mv))
  (fact 'membership-implies-sethood tv (r6g-cs nv mv))
  (fact 'membership-implies-sethood nv 'NN)
  (have! (list 'AND (list 'IN nv 'SET) (list 'IN nv 'SET)))
  (fact 'pairing nv nv)
  (fact 'choose-set-avoids-point nv mv sv)
  (fact 'choose-set-avoids-point nv mv tv)
  (have! (list 'AND (list 'IN sv 'SET) (list 'IN tv 'SET)))
  (let ((ext (iff-for (begin (fact 'extensionality sv tv) (list '= sv tv))))
        (body (list 'FORALL 'y_ (list 'IFF (list 'IN 'y_ sv) (list 'IN 'y_ tv)))))
    (have! body
      (lambda ()
        (let* ((yv  (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
               (umS (r6g-mem-iff! (list 'IN yv Us) 'union-membership sv pr yv))
               (umT (r6g-mem-iff! (list 'IN yv Ut) 'union-membership tv pr yv))
               (pmy (r6g-pairmem! nv yv))
               (link (list 'IFF (list 'IN yv Us) (list 'IN yv Ut)))
               (hs (list 'IMPLIES (list 'AND (list '= yv nv) (list 'IN yv sv))
                         (list 'IN nv sv)))
               (ht (list 'IMPLIES (list 'AND (list '= yv nv) (list 'IN yv tv))
                         (list 'IN nv tv))))
          (have! link (lambda () (subst (list '= Us Ut)) (prop)))
          (have! hs (lambda () (di) (dk-split-all!)
                            (fact 'eq-sym yv nv) (subst (list '= nv yv)) (ass)))
          (have! ht (lambda () (di) (dk-split-all!)
                            (fact 'eq-sym yv nv) (subst (list '= nv yv)) (ass)))
          (dk-only! umS umT pmy link hs ht
                    (list 'NOT (list 'IN nv sv)) (list 'NOT (list 'IN nv tv)))
          (prop))))
    (dk-only! ext body)
    (prop)))
(r6g-check! 'choose-set-insert-injective)
(qed 'choose-set-insert-injective)
(topic! 'choose-set-insert-injective 'combinatorial)

;;; ===================================================================
;;; (10) choose-set-split -- THE COVER.  The (succ k)-subsets of
;;;      ORD-SEGMENT(succ n) are the (succ k)-subsets of ORD-SEGMENT(n)
;;;      together with the image of the k-subsets under s |-> s u {n}.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL k_ (IMPLIES (IN k_ NN)
      (= (CHOOSE-SET (succ n_) (succ k_))
         (UNION (CHOOSE-SET n_ (succ k_))
                (IMAGE (VNB-LAMBDA s_ (CHOOSE-SET n_ k_) (UNION s_ (PAIR n_ n_)))
                       (CHOOSE-SET n_ k_))))))))))
(dk-peel!)
(let* ((g    (dk-goal))
       (CST  (cadr g))
       (RHS  (caddr g))
       (CSsk (cadr RHS))
       (B    (caddr RHS))
       (L    (cadr B))
       (CSk  (caddr B))
       (nv   (cadr CSk))
       (kv   (caddr CSk))
       (sn   (list 'succ nv))
       (sk   (list 'succ kv))
       (pr   (r6g-sing nv)))
  (fact 'nn-succ-closed nv)
  (fact 'nn-subset-ord nv)
  (fact 'nn-subset-ord sn)
  (fact 'ord-segment-is-set nv)
  (fact 'ord-segment-is-set sn)
  (fact 'power-set (list 'ORD-SEGMENT nv))
  (fact 'power-set (list 'ORD-SEGMENT sn))
  (have! (list 'IN CST 'SET)  (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
  (have! (list 'IN CSsk 'SET) (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
  (have! (list 'IN CSk 'SET)  (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
  (fact 'image-set L CSk)
  (have! (list 'AND (list 'IN CSsk 'SET) (list 'IN B 'SET)))
  (fact 'union-set-closure CSsk B)
  (have! (list 'AND (list 'IN CST 'SET) (list 'IN RHS 'SET)))
  (let ((ext  (iff-for (begin (fact 'extensionality CST RHS) (list '= CST RHS))))
        (body (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ CST) (list 'IN 'w_ RHS)))))
    (have! body
      (lambda ()
        (let* ((A   (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
               (um  (r6g-mem-iff! (list 'IN A RHS) 'union-membership CSsk B A))
               (im  (r6g-mem-iff! (list 'IN A B) 'image-membership-iff L CSk A))
               (D   (r6g-del A nv))
               ;; the existential is READ OFF the image IFF, never rebuilt: its
               ;; binder is renamed whenever the eigenvariable takes the name.
               (wit (caddr im)))
          ;; ---------------- forward
          (have! (list 'IMPLIES (list 'IN A CST) (list 'IN A RHS))
            (lambda ()
              (di)
              (fact 'membership-implies-sethood A CST)
              (fact 'membership-implies-sethood nv 'NN)
              (use-em (list 'IN nv A)
                ;; ---- A contains n: it is the image of A \ {n}
                (lambda ()
                  (have! (list 'AND (list 'IN A CST) (list 'IN nv A)))
                  (fact 'choose-set-remove-in nv kv A)     ; (IN D CSk)
                  (have! (list 'AND (list 'IN A 'SET) (list 'IN nv A)))
                  (fact 'choose-set-remove-restores nv A)  ; (= (UNION D {n}) A)
                  (have! (list '= (list L D) A)
                         (lambda () (lam-b) (ass)))
                  (have! wit (lambda () (ew D) (prop)))
                  (dk-only! im um wit)
                  (prop))
                ;; ---- A avoids n: it is already a (succ k)-subset of OS(n)
                (lambda ()
                  (have! (list 'AND (list 'IN A CST) (list 'NOT (list 'IN nv A))))
                  (fact 'choose-set-avoid-in nv sk A)      ; (IN A CSsk)
                  (dk-only! um (list 'IN A CSsk))
                  (prop)))))
          ;; ---------------- backward
          (have! (list 'IMPLIES (list 'IN A RHS) (list 'IN A CST))
            (lambda ()
              (di)
              (have! (list 'OR (list 'IN A CSsk) (list 'IN A B))
                     (lambda () (dk-only! um (list 'IN A RHS)) (prop)))
              (use-cases (list 'OR (list 'IN A CSsk) (list 'IN A B))
                (lambda ()
                  (fact 'choose-set-widen nv sk A)
                  (ass))
                (lambda ()
                  (have! wit (lambda () (dk-only! im (list 'IN A B)) (prop)))
                  (let* ((landed (dk-split! (dk-landed-1 (lambda () (ai wit)))))
                         (mem (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                                         (equal? (caddr f) CSk)))
                                        landed))
                         (S0  (cadr mem))
                         (eqn (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=))) landed)))
                    (lam-b-h eqn)
                    (let ((beta (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                          (pair? (cadr f))
                                                          (eq? (car (cadr f)) 'UNION)))
                                         "the beta-reduced equation")))
                      (fact 'choose-set-insert-in nv kv S0)   ; (IN (UNION S0 {n}) CST)
                      (fact 'eq-sym (cadr beta) A)
                      (subst (list '= A (cadr beta)))
                      (ass)))))))
          (dk-only! (list 'IMPLIES (list 'IN A CST) (list 'IN A RHS))
                    (list 'IMPLIES (list 'IN A RHS) (list 'IN A CST)))
          (prop))))
    (dk-only! ext body)
    (prop)))
(r6g-check! 'choose-set-split)
(qed 'choose-set-split)
(topic! 'choose-set-split 'combinatorial)

;;; ===================================================================
;;; (11) choose-set-split-disjoint -- the two halves meet nowhere: every
;;;      member of the left half omits n, every member of the image contains it.
;;; ===================================================================
(sp (make-wff
 '(FORALL n_ (IMPLIES (IN n_ NN)
    (FORALL k_ (IMPLIES (IN k_ NN)
      (= (INTERSECTION (CHOOSE-SET n_ (succ k_))
                       (IMAGE (VNB-LAMBDA s_ (CHOOSE-SET n_ k_) (UNION s_ (PAIR n_ n_)))
                              (CHOOSE-SET n_ k_)))
         EMPTY-SET)))))))
(dk-peel!)
(let* ((g    (dk-goal))
       (INT  (cadr g))
       (CSsk (cadr INT))
       (B    (caddr INT))
       (L    (cadr B))
       (CSk  (caddr B))
       (nv   (cadr CSk))
       (kv   (caddr CSk))
       (sk   (list 'succ kv))
       (pr   (r6g-sing nv)))
  (fact 'membership-implies-sethood nv 'NN)
  (bc* 'class-extensionality)
  (let* ((A   (dk-di-var! (lambda (gg) (cadr (cadr gg)))))
         (imm (r6g-mem-iff! (list 'IN A INT) 'intersection-membership CSsk B A))
         (im  (r6g-mem-iff! (list 'IN A B) 'image-membership-iff L CSk A))
         (wit (caddr im)))
    (fact 'empty-set-has-no-members A)
    (have! (list 'NOT (list 'IN A INT))
      (lambda ()
        (di)                                   ; assume it; goal FALSITY
        (have! (list 'AND (list 'IN A CSsk) (list 'IN A B))
               (lambda () (dk-only! imm (list 'IN A INT)) (prop)))
        (dk-split-all!)
        (fact 'choose-set-avoids-point nv sk A)          ; (NOT (IN n A))
        (have! wit (lambda () (dk-only! im (list 'IN A B)) (prop)))
        (let* ((landed (dk-split! (dk-landed-1 (lambda () (ai wit)))))
               (mem (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                               (equal? (caddr f) CSk)))
                              landed))
               (S0  (cadr mem))
               (eqn (any-pred (lambda (f) (and (pair? f) (eq? (car f) '=))) landed)))
          (lam-b-h eqn)
          (let* ((beta (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                 (pair? (cadr f))
                                                 (eq? (car (cadr f)) 'UNION)))
                                "the beta-reduced equation"))
                 (U   (cadr beta))
                 (pmn (r6g-pairmem! nv nv))
                 (umn (r6g-mem-iff! (list 'IN nv U) 'union-membership S0 pr nv)))
            (have! (list '= nv nv) (lambda () (rfl)))
            (have! (list 'IN nv U)
                   (lambda () (dk-only! pmn umn (list '= nv nv)) (prop)))
            (fact 'eq-sym U A)
            (have! (list 'IN nv A)
                   (lambda () (subst (list '= A U)) (ass)))
            (ai (list 'NOT (list 'IN nv A)))))))
    (prop)))
(r6g-check! 'choose-set-split-disjoint)
(qed 'choose-set-split-disjoint)
(topic! 'choose-set-split-disjoint 'combinatorial)

;;; ===================================================================
;;; (12) choose-succ -- PASCAL'S RULE.  structure-library/injection.scm:281,
;;;      the statement copied literally.
;;;
;;;      CHOOSE-SET(succ n, succ k) is the disjoint union of CHOOSE-SET(n,succ k)
;;;      and the image of CHOOSE-SET(n,k) under s |-> s u {n} (lemmas 10, 11);
;;;      the lambda is an INJECTION there (lemmas 5 and 9 give the FUN typing and
;;;      the injectivity), so card-image-injection gives the image the cardinal
;;;      CHOOSE(n,k), card-union-disjoint adds the two, and nn-add-comm puts the
;;;      sum in the order the statement uses.
;;; ===================================================================
(sp (make-wff
 '(FORALL n (IMPLIES (IN n NN)
     (FORALL k (IMPLIES (IN k NN)
       (= (CHOOSE (succ n) (succ k))
          (+ (CHOOSE n k) (CHOOSE n (succ k))))))))))
(dk-peel!)
(let* ((g   (dk-goal))
       (nv  (cadr (cadr (cadr g))))
       (kv  (cadr (caddr (cadr g))))
       (sn  (list 'succ nv))
       (sk  (list 'succ kv)))
  (fact 'nn-succ-closed nv)
  (fact 'nn-succ-closed kv)
  (fact 'nn-subset-ord nv)
  (fact 'nn-subset-ord sn)
  (fact 'ord-segment-is-set nv)
  (fact 'ord-segment-is-set sn)
  (fact 'power-set (list 'ORD-SEGMENT nv))
  (fact 'power-set (list 'ORD-SEGMENT sn))
  (fact 'choose-set-split nv kv)
  (let* ((spl  (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                         (pair? (cadr f)) (eq? (car (cadr f)) 'CHOOSE-SET)))
                        "the split equation"))
         (CST  (cadr spl))
         (RHS  (caddr spl))
         (CSsk (cadr RHS))
         (B    (caddr RHS))
         (L    (cadr B))
         (CSk  (caddr B)))
    ;; ---- sethood and finiteness of the three sets
    (have! (list 'IN CST 'SET)  (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
    (have! (list 'IN CSsk 'SET) (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
    (have! (list 'IN CSk 'SET)  (lambda () (mac 'CHOOSE-SET) (sep-set) (ass)))
    (fact 'image-set L CSk)
    (fact 'choose-in-nn nv kv)
    (fact 'choose-in-nn nv sk)
    (fact 'choose-card-unfold nv kv)
    (fact 'choose-card-unfold nv sk)
    (have! (list 'IN (list 'CARD CSk) 'NN)
           (lambda () (subst (list '== (list 'CARD CSk) (list 'CHOOSE nv kv))) (ass)))
    (have! (list 'IN (list 'CARD CSsk) 'NN)
           (lambda () (subst (list '== (list 'CARD CSsk) (list 'CHOOSE nv sk))) (ass)))
    ;; ---- the insertion map is an injection of CSk into CST
    (have! (list 'IN L (list 'FUN CSk CST))
      (lambda ()
        (for-each
         (lambda (leaf)
           (dk-focus! leaf)
           (if (eq? (car (dk-goal)) 'FORALL)
               (begin (dk-peel!)
                      (fact 'choose-set-insert-in nv kv (cadr (cadr (dk-goal))))
                      (ass))
               (ass)))
         (dk-opened (lambda () (lam-t))))))
    (let* ((inji (r6g-mem-iff! (list 'IN L (list 'INJECTION CSk CST))
                               'injection-membership-iff CSk CST L))
           (conj (caddr inji))                      ; (AND (IN L (FUN ..)) <injective>)
           (injective (caddr conj)))
      (have! injective
        (lambda ()
          (dk-peel!)
          (let* ((g2  (dk-goal))                    ; (= a b)
                 (av  (cadr g2))
                 (bv  (caddr g2))
                 (eqn (dk-pick (lambda (f) (and (pair? f) (eq? (car f) '=)
                                                (pair? (cadr f)) (pair? (car (cadr f)))
                                                (eq? (car (car (cadr f))) 'VNB-LAMBDA)))
                               "the equated images")))
            (lam-b-h eqn)
            (fact 'choose-set-insert-injective nv kv av bv)
            (ass))))
      (have! conj)
      (have! (list 'IN L (list 'INJECTION CSk CST))
             (lambda () (dk-only! inji conj) (prop))))
    (have! (list 'AND (list 'IN L (list 'INJECTION CSk CST))
                 (list 'AND (list 'IN CSk 'SET) (list 'IN (list 'CARD CSk) 'NN))))
    (fact 'card-image-injection CSk CST L)          ; (= (CARD B) (CARD CSk))
    (have! (list 'IN (list 'CARD B) 'NN)
           (lambda () (subst (list '= (list 'CARD B) (list 'CARD CSk))) (ass)))
    ;; ---- the two halves are disjoint, so their cardinals add
    (fact 'choose-set-split-disjoint nv kv)
    (have! (list 'AND (list 'IN CSsk 'SET) (list 'IN (list 'CARD CSsk) 'NN)))
    (have! (list 'AND (list 'IN B 'SET)
                 (list 'AND (list 'IN (list 'CARD B) 'NN)
                       (list '= (list 'INTERSECTION CSsk B) 'EMPTY-SET))))
    (fact 'card-union-disjoint CSsk B)
    (have! (list 'AND (list 'IN (list 'CARD CSsk) 'NN) (list 'IN (list 'CARD CSk) 'NN)))
    (fact 'nn-add-comm (list 'CARD CSsk) (list 'CARD CSk))
    ;; ---- and the goal is that sum
    (mac 'CHOOSE)
    (subst (list '= CST RHS))
    (subst (list '= (list 'CARD RHS) (list '+ (list 'CARD CSsk) (list 'CARD B))))
    (subst (list '= (list 'CARD B) (list 'CARD CSk)))
    (ass)))
(r6g-check! 'choose-succ)
(qed 'choose-succ)
(topic! 'choose-succ 'combinatorial)

