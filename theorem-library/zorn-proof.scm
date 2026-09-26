;;; zorn-proof.scm -- proving ZORN'S LEMMA from the well-ordering principle, via
;;; the GREEDY-KEPT-CHAIN construction (avoids the cardinality/Hartogs comparison
;;; lemma the base lacks).  Multi-session build; this file grows as lemmas land.
;;; Started 2026-07-22.
;;;
;;; CONSTRUCTION.  Given a well-ordering phi : ORD-SEGMENT(CARD grd) -> grd of the
;;; ground set, walk the elements in phi-order and KEEP each one that dominates
;;; every element kept so far.  The kept set is a chain; its upper bound (hypo)
;;; is maximal.  Cumulative kept set by transfinite recursion:
;;;   ZKEPT(0)       = {}
;;;   ZKEPT(succ a)  = ZKEPT(a)  U  {phi(a)  if phi(a) dominates all of ZKEPT(a)}
;;;   ZKEPT(lim)     = U_{b<lim} ZKEPT(b)
;;; GREEDY-CHAIN = ZKEPT(CARD grd).
;;; ====================================================================

;;; KEEP-SET(phi, grd, porel, kset, alpha): the conditionally-added element --
;;; {phi(alpha)} if phi(alpha) is in grd and dominates every z in kset, else {}.
;;; (A SEP over grd, so no singleton constructor is needed.)
(def-functoid 'KEEP-SET '(phi grd porel kset alpha)
  '(SEP y grd
     (AND (= y (phi alpha))
          (FORALL z (IMPLIES (IN z kset) (IN (LIST z y) porel))))))

;;; KEEP-SET's members get read out of the CONTEXT (every chain argument below
;;; starts from "x is in the kept piece"), and `mac-h' cannot unfold a functoid
;;; in an assumption -- def-functoid installs a macete, not a theorem.  So state
;;; the membership IFF once, as a DEFINITIONAL axiom: it is exactly the functoid
;;; unfold composed with the SEP separation schema (pi-sep-mem-intro!/-elim!,
;;; primitive-inferences.scm:1093,1107), both trusted base.  No debt.
(fluid-let ((*current-provenance* 'definitional))
  (theory-add-axiom! *current-theory* 'keep-set-membership
    (nest-quantifiers 'FORALL '(phi grd porel kset alpha y_)
      '(IFF (IN y_ (KEEP-SET phi grd porel kset alpha))
            (AND (IN y_ grd)
                 (AND (= y_ (phi alpha))
                      (FORALL z (IMPLIES (IN z kset)
                                         (IN (LIST z y_) porel)))))))))

;;; ZKEPT(phi, grd, porel, alpha): the cumulative kept set at stage alpha.
(def-by-ord-recursion 'ZKEPT '(phi grd porel)
  'EMPTY-SET                                        ; ZKEPT(...,0) = {}
  '(alpha val)                                      ; val = ZKEPT(...,alpha)
  '(UNION val (KEEP-SET phi grd porel val alpha))   ; successor step
  '(lam)
  '(BIG-UNION beta (ORD-SEGMENT lam) (ZKEPT phi grd porel beta)))   ; limit step

;;; GREEDY-CHAIN(phi, grd, porel): the full kept chain, ZKEPT at CARD(grd).
(def-functoid 'GREEDY-CHAIN '(phi grd porel)
  '(ZKEPT phi grd porel (CARD grd)))

;;; ====================================================================
;;; RUNG 3 -- the chain invariant: ZKEPT(...,alpha) is a chain for every ordinal
;;; alpha, by transfinite induction (tfi3).  Its three cases were STATED here as
;;; PSS seeds on 2026-07-27 and are now PROVEN, in order, below -- base,
;;; successor, a monotonicity helper, limit -- followed by the tfi3 that puts
;;; them together and the GREEDY-CHAIN corollary.  No step of rung 3 is asserted:
;;; the base and successor cases are unconditional (`modulo 0'), and what the
;;; other four bills carry is the ORD ORDER AXIOM LAYER (ord-le-refl,
;;; ord-le-total, ord-le-antisymm, ord-le-closure, ord-zero-least,
;;; ord-succ-immediate, ord-segment-membership -- structure-library/ordinals.scm),
;;; which is installed by `theory-add-axiom!' and carries no `warrant!' at all;
;;; that, and nothing in this file, is why the bills read trust: none.
;;; ====================================================================

;; zp-focus!: the open leaf whose goal has head HD.  Shape-based, but every use
;; below is on a two-leaf AND split whose halves have DIFFERENT heads, so the
;; discrimination is exact; it errors rather than returning #f (CLAUDE.md).
(define (zp-focus! hd)
  (let loop ((ls (proof-leaves)))
    (cond ((null? ls) (error "zp-focus!: no open leaf with goal head" hd))
          ((and (pair? (dk-goal-of (car ls))) (eq? (car (dk-goal-of (car ls))) hd))
           (dk-focus! (car ls)))
          (else (loop (cdr ls))))))

;; zp-vacuous!: the goal is under an `IN v EMPTY-SET' hypothesis, so anything
;; follows -- empty-set-has-no-members contradicts it.
(define (zp-vacuous! v)
  (fact 'empty-set-has-no-members v)
  (pbc)
  (ai `(NOT (IN ,v EMPTY-SET))))

;; (1) BASE: the empty set is a chain (vacuously).
(sp (make-wff (forall-guarded '(grd porel) '((IN grd SET))
                '(IS-CHAIN grd porel EMPTY-SET))))
(di) (di)
(mac 'is-chain)
(di)
(zp-focus! 'SUBSET)                     ; EMPTY-SET subset grd
(mac 'subset-def)
(di)                                    ; a GUARDED forall peels binder + guard
(zp-vacuous! 'x)
(zp-focus! 'FORALL)                     ; the comparability clause, vacuously
(di)
(zp-vacuous! 'x)
(qed 'zorn-empty-is-chain)

;; (2) SUCCESSOR: adjoining KEEP-SET keeps a chain a chain.  KEEP-SET is {phi(a)}
;; when phi(a) dominates all of kset, else {}, so every element it adds dominates
;; the whole chain -- one uniform argument, no empty/singleton split.
(define zp-keep '(KEEP-SET phi grd porel kset alpha))

;; the LIVE (IN v (UNION ...)) hypothesis for v -- read out of the context, never
;; reconstructed, so `ue' is fed the exact term the engine built.
(define (zp-union-mem v)
  (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'IN) (eq? (cadr a) v)
                                 (pair? (caddr a)) (eq? (car (caddr a)) 'UNION)))
                (dk-asms))
      (error "zp-union-mem: no union membership for" v)))

;; focus the branch of a just-opened case split that assumes MARKER
(define (zp-branch! leaves marker)
  (dk-focus!
    (or (any-pred (lambda (l) (any-pred (lambda (a) (equal? a marker)) (dk-asms-of l)))
                  leaves)
        (error "zp-branch!: no branch assuming" marker))))

;; instantiate a doubly-guarded context universal at two terms
(define (zp-inst2! f t1 t2)
  (dk-deepest (lambda () (inst+ (dk-deepest (lambda () (inst+ f t1))) t2))))

;; unfold (IN v KEEP-SET) in the context; return its domination clause
;; (FORALL z. IN z kset => [z,v] in porel).
(define (zp-dominates! v)
  (let ((parts (dk-split!
                 (dk-landed-1 (lambda () (mac-h 'keep-set-membership `(IN ,v ,zp-keep)))))))
    (or (any-pred (dk-head? 'FORALL) parts)
        (error "zp-dominates!: no domination clause" parts))))

(sp (make-wff (forall-guarded '(phi grd porel kset alpha)
  '((IS-PARTIAL-ORDER grd porel) (IS-CHAIN grd porel kset))
  `(IS-CHAIN grd porel (UNION kset ,zp-keep)))))
(di) (di) (di)

;; project the two hypotheses.  mac-h REPLACES, which is fine: neither
;; IS-CHAIN(kset) nor IS-PARTIAL-ORDER is cited again below.
(define zp-cparts
  (dk-split! (dk-landed-1 (lambda () (mac-h 'is-chain '(IS-CHAIN grd porel kset))))))
(define zp-kcomp (car  zp-cparts))       ; forall x,y in kset. comparable
(define zp-ksub  (cadr zp-cparts))       ; SUBSET kset grd
(define zp-refl
  (caddr (dk-split!
           (dk-landed-1 (lambda () (mac-h 'is-partial-order
                                          '(IS-PARTIAL-ORDER grd porel)))))))

(mac 'is-chain)
(di)

;;; (A) UNION kset KEEP-SET subset grd: kset by hypothesis, KEEP-SET because it
;;; separates grd.
(zp-focus! 'SUBSET)
(mac 'subset-def)
(di)
(let ((br (dk-opened (lambda () (ue (zp-union-mem 'x))))))
  (zp-branch! br '(IN x kset))
  (inst+ (dk-landed-1 (lambda () (mac-h 'subset-def zp-ksub))) 'x)
  (ass)
  (zp-branch! br `(IN x ,zp-keep))
  (dk-split! (dk-landed-1 (lambda () (mac-h 'keep-set-membership `(IN x ,zp-keep)))))
  (ass))

;;; (B) comparability: four cases on where x and y come from.
(zp-focus! 'FORALL)
(di)
(let ((brx (dk-opened (lambda () (ue (zp-union-mem 'x))))))

  (zp-branch! brx '(IN x kset))
  (let ((bry (dk-opened (lambda () (ue (zp-union-mem 'y))))))
    ;; both old: the chain hypothesis decides
    (zp-branch! bry '(IN y kset))
    (zp-inst2! zp-kcomp 'x 'y)
    (ass)
    ;; y just kept: y dominates every member of kset, x among them
    (zp-branch! bry `(IN y ,zp-keep))
    (inst+ (zp-dominates! 'y) 'x)
    (oi-l)
    (ass))

  (zp-branch! brx `(IN x ,zp-keep))
  (let ((bry (dk-opened (lambda () (ue (zp-union-mem 'y))))))
    ;; mirror image
    (zp-branch! bry '(IN y kset))
    (inst+ (zp-dominates! 'x) 'y)
    (oi-r)
    (ass)
    ;; both just kept: both equal phi(alpha), so the goal collapses to
    ;; reflexivity at x.  Rewrite y -> phi(alpha) -> x in the goal (`subst'
    ;; accepts the context equality in either orientation).
    (zp-branch! bry `(IN y ,zp-keep))
    (zp-dominates! 'x)
    (zp-dominates! 'y)
    (oi-l)
    (subst '(= y (phi alpha)))
    (subst '(= (phi alpha) x))
    (inst+ zp-refl 'x)
    (ass)))
(qed 'zorn-chain-plus-keepset)

;; (2a) MONOTONICITY (helper for the limit case): the ZKEPT tower is increasing.
;; The INDUCTION VARIABLE b is outermost and its typing guard is adjacent to its
;; binder, because that is exactly the shape `tfi3' demands (pi-tfi3!,
;; primitive-inferences.scm:962: goal (FORALL v (IMPLIES (IN v ORD) P))).  The
;; construction parameters phi/grd/porel therefore sit INSIDE, quantified within
;; P.  Same theorem as the binder order this support was first stated with; the
;; order is dictated by the rule, not by taste.
(define (zp-refl!) (mac 'subset-def) (di) (ass))   ; close a goal (SUBSET A A)

;; instantiate a context universal at successive terms, detaching in-context
;; guards as they appear; returns the final landed formula
(define (zp-inst*! f . terms)
  (let loop ((f f) (ts terms))
    (if (null? ts) f
        (loop (dk-deepest (lambda () (inst+ f (car ts)))) (cdr ts)))))

;; from a context (SUBSET A B) and (IN x A), land (IN x B)
(define (zp-mem! sub x)
  (inst+ (dk-landed-1 (lambda () (mac-h 'subset-def sub))) x))

(sp (make-wff
      (forall-guarded '(b) '((IN b ORD))
        (nest-quantifiers 'FORALL '(phi grd porel)
          (forall-guarded '(a) '((IN a ORD) (ORD-LE a b))
            '(SUBSET (ZKEPT phi grd porel a) (ZKEPT phi grd porel b)))))))
(define zp-mono-cases (dk-opened (lambda () (tfi3))))

;;; BASE b = 0: a <= 0 and 0 <= a force a = 0, and inclusion is reflexive.
(dk-focus! (car zp-mono-cases))
(di) (di)
(fact 'ord-zero-least 'a)
(have! '(AND (ORD-LE a 0) (ORD-LE 0 a)))
(fact 'ord-le-antisymm 'a 0)
(subst '(= a 0))
(zp-refl!)

;;; SUCCESSOR: either a <= b -- and the induction hypothesis puts ZKEPT(a) inside
;;; ZKEPT(b), the LEFT half of ZKEPT(succ b) = ZKEPT(b) U KEEP-SET -- or a is
;;; succ b itself and there is nothing to prove.  Everything is elementwise, so
;;; no subset-transitivity lemma is needed: `ui' does the work.
(dk-focus! (cadr zp-mono-cases))
(di)
(define zp-mono-ih
  (car (filter (dk-head? 'FORALL)
               (dk-split! (dk-landed-1 (lambda () (di)))))))
(di) (di)
(mac 'subset-def)
(di)
(have! '(AND (IN a ORD) (IN b ORD)))
(fact 'ord-le-total 'a 'b)

(define (zp-succ-below!)                ; the a <= b argument, used twice
  (zp-mem! (zp-inst*! zp-mono-ih 'phi 'grd 'porel 'a) 'x)
  (mac 'zkept-succ)
  (ui 1)
  (ass))

(use-cases (list '(ORD-LE a b) '(ORD-LE b a))
  zp-succ-below!
  (lambda ()
    (use-em '(= b a)
      (lambda ()                        ; b = a: then a <= b by reflexivity
        (have! '(ORD-LE a b)
               (lambda () (subst '(= b a)) (fact 'ord-le-refl 'a) (ass)))
        (zp-succ-below!))
      (lambda ()                        ; b < a with a <= succ b: a IS succ b
        (have! '(ORD-LT b a) (lambda () (mac 'ord-lt-iff) (from-context!)))
        (have! '(AND (IN b ORD) (AND (IN a ORD) (ORD-LT b a))))
        (fact 'ord-succ-immediate 'b 'a)
        (have! '(AND (ORD-LE a (succ_ORD b)) (ORD-LE (succ_ORD b) a)))
        (fact 'ord-le-antisymm 'a '(succ_ORD b))
        (subst '(= (succ_ORD b) a))
        (ass)))))

;;; LIMIT: a = b is trivial; a < b puts ZKEPT(a) into the big union at index a.
;;; The tfi3 limit hypothesis is never needed -- the union IS the value at b.
(dk-focus! (caddr zp-mono-cases))
(di)
(dk-split! (dk-landed-1 (lambda () (di))))
(di) (di)
(mac 'subset-def)
(di)
(dk-split! (dk-fact! 'ord-le-closure 'a 'b))       ; recovers (IN b ORD)
(use-em '(= a b)
  (lambda () (subst '(= b a)) (ass))
  (lambda ()
    (have! '(ORD-LT a b) (lambda () (mac 'ord-lt-iff) (from-context!)))
    (mac 'zkept-limit)
    (let ((ls (dk-opened (lambda () (bu-mi 'a)))))   ; witness index a
      (for-each (lambda (l)
                  (dk-focus! l)
                  (if (eq? (car (caddr (dk-goal))) 'ORD-SEGMENT)
                      (begin (mac 'ord-segment-membership) (ass))
                      (ass)))
                ls))))
(qed 'zorn-zkept-monotone)

;; (3) LIMIT: the union of the tower over a limit ordinal is a chain.  Two members
;; of the union lie in ZKEPT(b1), ZKEPT(b2); by monotonicity both lie in the larger
;; ZKEPT(max b1 b2), which is a chain, so they are comparable.
;; NOTE.  Until 2026-07-27 this statement could be INSTALLED but never PROVED:
;; `LIMIT-ORD' sat in *wff-term-form-heads* (wff.scm) among succ_ORD /
;; ORD-SEGMENT / SUP-ORD, which are terms, so `make-wff' rejected every goal
;; mentioning it -- and `support' does not validate, so nothing complained.
;; See the comment at that list.

;; the (IN v <HEAD>...) hypothesis for v, read out of the LIVE context
(define (zp-asm-with v head)
  (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (cadr a) v)
                                 (pair? (caddr a)) (eq? (car (caddr a)) head)))
                (dk-asms))
      (error "zp-asm-with: no membership" v head)))

;; open (IN v BIG-UNION); return the fresh index eigenvariable bu-me created
(define (zp-open-bu! v)
  (let* ((new (dk-landed (lambda () (bu-me (zp-asm-with v 'BIG-UNION)))))
         (seg (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                             (pair? (caddr a))
                                             (eq? (car (caddr a)) 'ORD-SEGMENT)))
                            new)
                  (error "zp-open-bu!: no segment membership landed" new))))
    (cadr seg)))

;; from (IN e (ORD-SEGMENT lam)) and (IN lam ORD), land (IN e ORD).  The segment
;; hypothesis is consumed only INSIDE the side branch (mac-h replaces), so the
;; main branch keeps it for the family hypothesis.
(define (zp-in-ord! e)
  (have! `(ORD-LE ,e lam)
         (lambda ()
           (mac-h 'ord-segment-membership `(IN ,e (ORD-SEGMENT lam)))
           (dk-split! (dk-landed-1 (lambda () (mac-h 'ord-lt-iff `(ORD-LT ,e lam)))))
           (ass)))
  (dk-split! (dk-fact! 'ord-le-closure e 'lam)))

(sp (make-wff
  (forall-guarded '(phi grd porel lam)
    '((IS-PARTIAL-ORDER grd porel) (LIMIT-ORD lam)
      (FORALL beta (IMPLIES (IN beta (ORD-SEGMENT lam))
                            (IS-CHAIN grd porel (ZKEPT phi grd porel beta)))))
    '(IS-CHAIN grd porel (BIG-UNION beta2 (ORD-SEGMENT lam)
                                    (ZKEPT phi grd porel beta2))))))
(di) (di) (di) (di)
(define zp-fam (car (filter (dk-head? 'FORALL) (dk-asms))))
;; LIMIT-ORD is wanted only for (IN lam ORD); unfolding it away costs nothing here.
(dk-split! (dk-landed-1 (lambda () (mac-h 'limit-ord-iff '(LIMIT-ORD lam)))))
(mac 'is-chain)
(di)

;;; (A) the union is inside grd: each member came from some stage, and every
;;; stage is a chain, hence a subset of grd.
(zp-focus! 'SUBSET)
(mac 'subset-def)
(di)
(let ((e (zp-open-bu! 'x)))
  (let* ((ch    (dk-deepest (lambda () (inst+ zp-fam e))))
         (parts (dk-split! (dk-landed-1 (lambda () (mac-h 'is-chain ch))))))
    (zp-mem! (car (filter (dk-head? 'SUBSET) parts)) 'x))
  (ass))

;;; (B) comparability: x and y come from stages e1 and e2; the ordinals are
;;; comparable, so BOTH lie in the larger stage, which is a chain.
(define (zp-decide! hi)                  ; x and y both at stage hi
  (let* ((ch    (dk-deepest (lambda () (inst+ zp-fam hi))))
         (parts (dk-split! (dk-landed-1 (lambda () (mac-h 'is-chain ch)))))
         (comp  (car (filter (dk-head? 'FORALL) parts))))
    (dk-deepest (lambda () (inst+ (dk-deepest (lambda () (inst+ comp 'x))) 'y)))
    (ass)))

(define (zp-lift! lo hi v)               ; v sits at lo <= hi; monotonicity lifts it
  (zp-mem! (zp-inst*! (dk-landed-1 (lambda () (ta 'zorn-zkept-monotone)))
                      hi 'phi 'grd 'porel lo)
           v)
  (zp-decide! hi))

(zp-focus! 'FORALL)
(di)
(let* ((e1 (zp-open-bu! 'x))
       (e2 (zp-open-bu! 'y)))
  (zp-in-ord! e1)
  (zp-in-ord! e2)
  (have! `(AND (IN ,e1 ORD) (IN ,e2 ORD)))
  (fact 'ord-le-total e1 e2)
  (use-cases (list `(ORD-LE ,e1 ,e2) `(ORD-LE ,e2 ,e1))
    (lambda () (zp-lift! e1 e2 'x))
    (lambda () (zp-lift! e2 e1 'y))))
(qed 'zorn-zkept-limit-is-chain)

;;; ====================================================================
;;; RUNG 3, ASSEMBLED.  The three cases above ARE the cases of a `tfi3', so the
;;; invariant is now four lines of plumbing per case: unfold ZKEPT at 0 / succ /
;;; limit with its own defining equation, then cite the case lemma.
;;; ====================================================================

(sp (make-wff
      (forall-guarded '(alpha) '((IN alpha ORD))
        (nest-quantifiers 'FORALL '(phi grd porel)
          '(IMPLIES (IS-PARTIAL-ORDER grd porel)
                    (IS-CHAIN grd porel (ZKEPT phi grd porel alpha)))))))
(define zp-inv-cases (dk-opened (lambda () (tfi3))))

;;; BASE: ZKEPT(...,0) is the empty set.
(dk-focus! (car zp-inv-cases))
(di) (di)
(mac 'zkept-zero)
(dk-split! (dk-landed-1 (lambda () (mac-h 'is-partial-order '(IS-PARTIAL-ORDER grd porel)))))
(fact 'zorn-empty-is-chain 'grd 'porel)
(ass)

;;; SUCCESSOR: ZKEPT(...,succ alpha) is the previous stage adjoined with KEEP-SET.
(dk-focus! (cadr zp-inv-cases))
(di)
(define zp-inv-ih
  (car (filter (dk-head? 'FORALL) (dk-split! (dk-landed-1 (lambda () (di)))))))
(di) (di)
(mac 'zkept-succ)
(zp-inst*! zp-inv-ih 'phi 'grd 'porel)
;; 2026-09-18 (LUTINS instantiation): zorn-chain-plus-keepset is cited at the
;; stage ZKEPT(phi,grd,porel,alpha), and IS-CHAIN is not one of the strict
;; relations, so the invariant in context does not certify it.  The recursion
;; equation does: zkept-succ is a strict `=' whose right side is
;; UNION(ZKEPT(...,alpha), KEEP-SET(...)), where the stage sits OUTSIDE every
;; binder in an argument position.
(fact 'zkept-succ 'phi 'grd 'porel 'alpha)
(fact 'zorn-chain-plus-keepset 'phi 'grd 'porel '(ZKEPT phi grd porel alpha) 'alpha)
(ass)

;;; LIMIT: ZKEPT(...,lambda) is the union of the tower below lambda.  The tfi3
;;; hypothesis is indexed by (ORD-LT beta alpha) and the limit lemma wants it
;;; indexed by (IN beta (ORD-SEGMENT alpha)); ord-segment-membership converts.
(dk-focus! (caddr zp-inv-cases))
(di)
(define zp-inv-ihl
  (car (filter (dk-head? 'FORALL) (dk-split! (dk-landed-1 (lambda () (di)))))))
(di) (di)
(mac 'zkept-limit)
(have! '(IN alpha ORD)
       (lambda ()
         (dk-split! (dk-landed-1 (lambda () (mac-h 'limit-ord-iff '(LIMIT-ORD alpha)))))
         (ass)))
(have! '(FORALL beta (IMPLIES (IN beta (ORD-SEGMENT alpha))
                              (IS-CHAIN grd porel (ZKEPT phi grd porel beta))))
       (lambda ()
         (di)
         (mac-h 'ord-segment-membership '(IN beta (ORD-SEGMENT alpha)))
         (zp-inst*! zp-inv-ihl 'beta 'phi 'grd 'porel)
         (ass)))
(fact 'zorn-zkept-limit-is-chain 'phi 'grd 'porel 'alpha)
(ass)
(qed 'zorn-zkept-is-chain)

;;; The construction's payoff: GREEDY-CHAIN = ZKEPT at CARD(grd) is a chain.
;;; (CARD of a set is an ordinal -- card-in-ord, cardinality.scm.)
(sp (make-wff
      (forall-guarded '(phi grd porel) '((IS-PARTIAL-ORDER grd porel))
        '(IS-CHAIN grd porel (GREEDY-CHAIN phi grd porel)))))
(di) (di)
(mac 'greedy-chain)
;; (IN grd SET) is wanted for card-in-ord, but IS-PARTIAL-ORDER must SURVIVE --
;; it is the last hypothesis of zorn-zkept-is-chain.  So unfold it only inside
;; the side branch of a have!, exactly as rung 1 did for well-ordering-principle.
(have! '(IN grd SET)
       (lambda ()
         (dk-split! (dk-landed-1
                      (lambda () (mac-h 'is-partial-order '(IS-PARTIAL-ORDER grd porel)))))
         (ass)))
(fact 'card-in-ord 'grd)
(zp-inst*! (dk-landed-1 (lambda () (ta 'zorn-zkept-is-chain)))
           '(CARD grd) 'phi 'grd 'porel)
(ass)
(qed 'greedy-chain-is-chain)
