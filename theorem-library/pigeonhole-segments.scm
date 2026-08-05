;;; pigeonhole-segments.scm -- Track A of the CARD plan: finite pigeonhole for
;;; ordinal segments, the one piece of real mathematics the plan needs.
;;;
;;; WHY.  CARD is axiomatised rather than defined (cardinality.scm's own header
;;; says so).  Defining it -- CARD(A) = the least ordinal in bijection with A --
;;; makes `card-segment' (CARD(ORD-SEGMENT n) = n) a THEOREM, and its proof is:
;;; the identity bijection witnesses existence at alpha = n, and PIGEONHOLE
;;; kills every beta < n.  With `ord-well-ordered' (PROVEN modulo 0) supplying
;;; leastness, pigeonhole is the whole remaining content of the finite layer --
;;; and the library does not have it.  The only pigeonhole fact installed is
;;; `pigeonhole-infinite', which is the infinite statement and no use here.
;;;
;;; WHAT IS HERE.  The base case (nothing injects S(1) into S(0)), the
;;; induction step (on COLLAPSE-AT, theorem-library/finite-surgery.scm), and the
;;; induction that puts them together.  The step is the reason the surgery kit
;;; exists: given an injection g of S(succ succ n) into S(succ n), delete the
;;; point c = g(succ n) from the CODOMAIN with COLLAPSE-AT(c) and restrict to
;;; S(succ n) -- which is an injection into S(n), and the hypothesis forbids it.
;;; `delete-at' (bijection.scm) is the wrong surgery twice over: it removes a
;;; point of the DOMAIN of a function, and is stated only for a PERMUTATION of
;;; S(succ n) that sends the removed index to n.
;;;
;;; The general form -- no injection S(m) -> S(n) for n < m -- is at the end,
;;; and is a restriction of the theorem above rather than a second induction.

;;; --------------------------------------------------------------------
;;; ORD-SEGMENT(0) is empty.
;;;
;;; Was a warranted support (theorem-library/ord-segment-zero-no-members.scm,
;;; PSS-promoted 2026-05-27 with its machine proof archived).  It is the leaf
;;; both lemmas below would otherwise bill, and it is four citations deep:
;;; k in S(0) gives <_ORD k 0 -- ord-segment-membership, once 0 is typed in ORD
;;; -- which is <=_ORD k 0 plus k /= 0 (ord-lt-iff); ord-zero-least supplies
;;; <=_ORD 0 k; ord-le-antisymm closes it to k = 0, against k /= 0.
;;;
;;; It is proven HERE rather than in its own file because that file loads inside
;;; the block of pure `support' declarations, eighty entries before the tactic
;;; layer exists.
(sp (make-wff '(FORALL k (NOT (IN k (ORD-SEGMENT 0))))))
(di)                          ; the FORALL
(di)                          ; the NOT: assume k in S(0), prove FALSITY
(fact 'nn-zero-in)
(fact 'nn-subset-ord 0)       ; 0 in ORD, which ord-segment-membership wants
(mac-h 'ord-segment-membership '(IN k (ORD-SEGMENT 0)))
(mac-h 'ord-lt-iff '(<_ORD k 0))
(dk-split! '(AND (<=_ORD k 0) (NOT (= k 0))))
(fact 'ord-le-closure 'k 0)
(dk-split! '(AND (IN k ORD) (IN 0 ORD)))
(fact 'ord-zero-least 'k)
(have! '(AND (<=_ORD k 0) (<=_ORD 0 k)))
(fact 'ord-le-antisymm 'k 0)
(ai '(NOT (= k 0)))
(qed 'ord-segment-zero-no-members)
(category! 'ord-segment-zero-no-members 'set-theory)

;;; --------------------------------------------------------------------
;;; Nothing maps into the empty segment.
;;;
;;; ORD-SEGMENT(0) has no members, so a function into it cannot be applied at
;;; any point of an inhabited domain.  Stated as an absurdity rather than as
;;; "the domain is empty" because that is the shape every consumer wants: land
;;; the two typings, get FALSITY.
(sp (make-wff '(FORALL a (FORALL f (FORALL x
     (IMPLIES (IN f (FUN a (ORD-SEGMENT 0)))
       (IMPLIES (IN x a) FALSITY)))))))
(di) (di) (di)
(fact 'fun-apply-type-c 'f 'a '(ORD-SEGMENT 0) 'x)
(fact 'ord-segment-zero-no-members '(f x))
(ai '(NOT (IN (f x) (ORD-SEGMENT 0))))
(qed 'fun-into-seg-zero-absurd)
(category! 'fun-into-seg-zero-absurd 'set-theory)

;;; --------------------------------------------------------------------
;;; PIGEONHOLE, base case: no injection from S(1) into S(0).
;;;
;;; S(succ 0) contains 0 (the segment-successor iff, right disjunct), and an
;;; injection is in particular a function, so the lemma above applies.  The
;;; injectivity clause is never used -- at this rung a plain function already
;;; contradicts -- and that is worth noticing: the base case of pigeonhole is
;;; not about injectivity at all.
(sp (make-wff '(FORALL f
     (NOT (IN f (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))))))
(di)                       ; the FORALL
(di)                       ; a NOT goal: assume the positive, prove FALSITY
(mac-h 'injection-membership-iff
       '(IN f (INJECTION (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0))))
(dk-split! '(AND (IN f (FUN (ORD-SEGMENT (succ 0)) (ORD-SEGMENT 0)))
                 (FORALL a (IMPLIES (IN a (ORD-SEGMENT (succ 0)))
                   (FORALL b (IMPLIES (IN b (ORD-SEGMENT (succ 0)))
                     (IMPLIES (= (f a) (f b)) (= a b))))))))
(fact 'nn-zero-in)
(have! '(IN 0 (ORD-SEGMENT (succ 0)))
       (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
(fact 'fun-into-seg-zero-absurd '(ORD-SEGMENT (succ 0)) 'f 0)
(ass)
(qed 'no-injection-seg-1-into-seg-0)
(category! 'no-injection-seg-1-into-seg-0 'set-theory)

;;; --------------------------------------------------------------------
;;; PIGEONHOLE, the induction step.
;;;
;;;   nothing injects S(succ n) -> S(n)
;;;     =>  nothing injects S(succ succ n) -> S(succ n)
;;;
;;; Given g : S(succ succ n) >-> S(succ n), put c = g(succ n) and compose g with
;;; the collapse of NN at c:
;;;
;;;     h  =  lam i in S(succ n).  COLLAPSE-AT(c)(g i)
;;;
;;; h lands in S(n) because g i lies in S(succ n) and differs from c (i differs
;;; from succ n, and g is injective), which is exactly collapse-at-in-seg; and h
;;; is injective because the collapse is injective away from c
;;; (collapse-at-inj) and g is injective.  The hypothesis then forbids h.
;;;
;;; A NOTE ON THE DRIVER, and it is the CLAUDE.md lesson again: `lam-t' renames
;;; the lambda's binder, so the peeled index is `i__1022', not `i_'.  Naming it
;;; `i_' made every later citation cite a formula that was not in the context,
;;; and the first symptom was a mac-h that "does not occur".  `ph-eigen' reads
;;; the eigenvariable off the context instead.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
     (IMPLIES (FORALL f_ (NOT (IN f_ (INJECTION (ORD-SEGMENT (succ n_))
                                                (ORD-SEGMENT n_)))))
       (FORALL g_ (NOT (IN g_ (INJECTION (ORD-SEGMENT (succ (succ n_)))
                                         (ORD-SEGMENT (succ n_)))))))))))

(define ph-S2 '(ORD-SEGMENT (succ (succ n_))))
(define ph-S1 '(ORD-SEGMENT (succ n_)))
(define ph-S0 '(ORD-SEGMENT n_))
(define ph-c  '(g_ (succ n_)))
(define ph-h  (list 'VNB-LAMBDA 'i_ ph-S1 (list (list 'COLLAPSE-AT ph-c) '(g_ i_))))

(define (ph-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop))))))
(define (ph-eigen)          ; the index just peeled: (IN v S1) with v a symbol
  (let ((fs (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (symbol? (cadr f)) (equal? (caddr f) ph-S1)))
                    (dk-asms))))
    (if (null? fs) (error "ph-eigen: no peeled index in context") (cadr (car fs)))))
(define (ph-first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "ph-first: nothing with head" h) (car fs))))

(ph-peel!)                               ; n_, its guard, the IH, g_, the NOT
(define ph-IH (ph-first 'FORALL))        ; the only universal in context yet

(fact 'nn-succ-closed 'n_)
(fact 'nn-succ-closed '(succ n_))
(fact 'nn-subset-ord '(succ n_))
(mac-h 'injection-membership-iff (list 'IN 'g_ (list 'INJECTION ph-S2 ph-S1)))
(define ph-gcs (dk-split! (ph-first 'AND)))
(define ph-ginj (car (filter (dk-head? 'FORALL) ph-gcs)))

;;; succ n is a point of S(succ succ n), so c = g(succ n) is a point of S(succ n)
(have! (list 'IN '(succ n_) ph-S2)
       (lambda () (mac 'seg-mem-succ-le) (fact 'nn-le-refl '(succ n_)) (ass)))
(fact 'fun-apply-type-c 'g_ ph-S2 ph-S1 '(succ n_))
(fact 'ord-segment-nn-subset '(succ n_) ph-c)

;;; everything the collapse needs to know about an index v of S(succ n)
(define (ph-index! v)
  (fact 'ord-segment-nn-subset '(succ n_) v)
  (have! (list '<= v 'n_)
         (lambda () (mac-h 'seg-mem-succ-le (list 'IN v ph-S1)) (ass)))
  (have! (list 'IN v ph-S2)
         (lambda () (mac 'seg-mem-succ-le)
                    (fact 'nn-le-succ 'n_)
                    (fact 'co-le-trans v 'n_ '(succ n_))
                    (ass)))
  (fact 'nn-le-imp-neq-succ 'n_ v)                        ; v /= succ n
  (fact 'fun-apply-type-c 'g_ ph-S2 ph-S1 v)              ; g v in S(succ n)
  (fact 'ord-segment-nn-subset '(succ n_) (list 'g_ v))   ; g v in NN
  (have! (list 'NOT (list '= (list 'g_ v) ph-c))          ; g v /= c, since g is 1-1
         (lambda ()
           (di)
           (let* ((t1 (dk-deepest (lambda () (inst+ ph-ginj v)))))
             (dk-deepest (lambda () (inst+ t1 '(succ n_))))
             (ai (list 'NOT (list '= v '(succ n_))))))))

(define (ph-beta!)
  (let loop ()
    (let ((eq (ph-first '=)))
      (if (dk-contains? eq 'VNB-LAMBDA) (begin (lam-b-h eq) (loop))))))

;;; the collapsed composite is an injection S(succ n) -> S(n)
(have! (list 'IN ph-h (list 'INJECTION ph-S1 ph-S0))
       (lambda ()
         (mac 'injection-membership-iff)
         (for-each
          (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) 'IN)
                ;; (IN h (FUN S1 S0)) -- lambda typing
                (for-each
                 (lambda (m)
                   (dk-focus! m)
                   (if (eq? (car (dk-goal)) 'FORALL)
                       (begin
                         (ph-peel!)
                         (let ((v (ph-eigen)))     ; NOT `i_': the binder is renamed
                           (ph-index! v)
                           (fact 'collapse-at-in-seg 'n_ ph-c (list 'g_ v))
                           (ass)))
                       (begin (fact 'ord-segment-is-set '(succ n_)) (ass))))
                 (dk-opened (lambda () (lam-t))))
                ;; injectivity of h
                (begin
                  (ph-peel!)
                  (let* ((g (dk-goal)) (va (cadr g)) (vb (caddr g)))
                    (ph-index! va)
                    (ph-index! vb)
                    (ph-beta!)
                    (fact 'collapse-at-inj ph-c (list 'g_ va) (list 'g_ vb))
                    (let ((t1 (dk-deepest (lambda () (inst+ ph-ginj va)))))
                      (dk-deepest (lambda () (inst+ t1 vb)))
                      (ass))))))
          (dk-opened (lambda () (di))))))

;;; ... which the induction hypothesis forbids
(dk-deepest (lambda () (inst+ ph-IH ph-h)))
(ai (list 'NOT (list 'IN ph-h (list 'INJECTION ph-S1 ph-S0))))
(qed 'pigeonhole-step)
(category! 'pigeonhole-step 'combinatorial)

;;; --------------------------------------------------------------------
;;; PIGEONHOLE for segments: nothing injects S(succ n) into S(n), for any n.
;;;
;;; The two rungs above, joined by NN-induction.  This is the statement
;;; `card-segment' consumes: with the identity witnessing CARD(S(n)) <= n, it is
;;; what rules out every smaller ordinal.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN)
     (FORALL f_ (NOT (IN f_ (INJECTION (ORD-SEGMENT (succ n_))
                                       (ORD-SEGMENT n_)))))))))
(let* ((br   (use-induction))
       (base (cdr (assq 'base br)))
       (step (cdr (assq 'step br))))
  (dk-focus! base)
  (fact 'no-injection-seg-1-into-seg-0)
  (ass)
  (dk-focus! step)
  (fact 'pigeonhole-step 'n_)
  (ass))
(qed 'pigeonhole-segments)
(category! 'pigeonhole-segments 'combinatorial)

;;; --------------------------------------------------------------------
;;; PIGEONHOLE, general form:  n < m  =>  nothing injects S(m) into S(n).
;;;
;;; NOT a second induction -- a RESTRICTION.  n < m gives succ n <= m
;;; (nn-lt-succ-le, finite-surgery.scm), so every index of S(succ n) is an index
;;; of S(m); restricting a would-be injection f to S(succ n) -- the composite
;;; lambda again -- gives an injection S(succ n) -> S(n), which the theorem above
;;; forbids.  This is the form `card-segment' consumes: for A = S(n) and a
;;; candidate cardinal beta < n, a bijection A -> S(beta) is in particular an
;;; injection S(n) -> S(beta), and this kills it.  (Which is why the CARD
;;; description is written A -> SEGMENT and not the other way round: segment-first
;;; would need the bijection INVERTED, and INVERSE-BIJ is defined via CHOICE.)
(sp (make-wff (forall-guarded '(m_ n_) (list '(IN m_ NN) '(IN n_ NN))
                '(IMPLIES (< n_ m_)
                   (FORALL f_ (NOT (IN f_ (INJECTION (ORD-SEGMENT m_)
                                                     (ORD-SEGMENT n_)))))))))

(define pg-Sm '(ORD-SEGMENT m_))
(define pg-S1 '(ORD-SEGMENT (succ n_)))
(define pg-S0 '(ORD-SEGMENT n_))
(define pg-h  (list 'VNB-LAMBDA 'i_ pg-S1 '(f_ i_)))

(define (pg-peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop))))))
(define (pg-first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "pg-first: nothing with head" h) (car fs))))
(define (pg-eigen)
  (let ((fs (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (symbol? (cadr f)) (equal? (caddr f) pg-S1)))
                    (dk-asms))))
    (if (null? fs) (error "pg-eigen: no peeled index in context") (cadr (car fs)))))
(define (pg-beta!)
  (let loop ()
    (let ((eq (pg-first '=)))
      (if (dk-contains? eq 'VNB-LAMBDA) (begin (lam-b-h eq) (loop))))))

(pg-peel!)
(fact 'nn-succ-closed 'n_)
(fact 'nn-subset-ord '(succ n_))
(mac-h 'injection-membership-iff (list 'IN 'f_ (list 'INJECTION pg-Sm pg-S0)))
(define pg-cs (dk-split! (pg-first 'AND)))
(define pg-finj (car (filter (dk-head? 'FORALL) pg-cs)))

;;; an index of S(succ n) is an index of S(m), and f sends it into S(n)
(define (pg-index! v)
  (fact 'ord-segment-nn-subset '(succ n_) v)
  (have! (list '<= v 'n_)
         (lambda () (mac-h 'seg-mem-succ-le (list 'IN v pg-S1)) (ass)))
  (have! (list 'IN v pg-Sm)
         (lambda () (mac 'seg-mem-lt) (fact 'co-le-lt-trans v 'n_ 'm_) (ass)))
  (fact 'fun-apply-type-c 'f_ pg-Sm pg-S0 v))

(have! (list 'IN pg-h (list 'INJECTION pg-S1 pg-S0))
       (lambda ()
         (mac 'injection-membership-iff)
         (for-each
          (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) 'IN)
                (for-each
                 (lambda (mm)
                   (dk-focus! mm)
                   (if (eq? (car (dk-goal)) 'FORALL)
                       (begin (pg-peel!) (pg-index! (pg-eigen)) (ass))
                       (begin (fact 'ord-segment-is-set '(succ n_)) (ass))))
                 (dk-opened (lambda () (lam-t))))
                (begin
                  (pg-peel!)
                  (let* ((g (dk-goal)) (va (cadr g)) (vb (caddr g)))
                    (pg-index! va)
                    (pg-index! vb)
                    (pg-beta!)
                    (let ((t1 (dk-deepest (lambda () (inst+ pg-finj va)))))
                      (dk-deepest (lambda () (inst+ t1 vb)))
                      (ass))))))
          (dk-opened (lambda () (di))))))

(dk-fact! 'pigeonhole-segments 'n_ pg-h)
(ai (list 'NOT (list 'IN pg-h (list 'INJECTION pg-S1 pg-S0))))
(qed 'pigeonhole-segments-gen)
(category! 'pigeonhole-segments-gen 'combinatorial)
