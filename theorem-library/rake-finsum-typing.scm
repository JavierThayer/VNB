;;; rake-finsum-typing.scm -- the finsum / monoid-power typing leaves of the
;;; rake (batch G), PROVEN, together with the guarded form of the one statement
;;; in the batch that is NOT provable as stated.
;;;
;;;   comm-monoid-carrier-closed-opr  (NEW)  (OPR m)(a,b) in CARR(m)
;;;   comm-monoid-identity-in-carr    (NEW)  IDEN(m) in CARR(m)
;;;   sum-ag-comm-monoid-type-ind     (NEW)  sum-ag typing, fold length OUTERMOST
;;;   enum-fam-comm-monoid-in-fun     (NEW)  the enumeration family is total
;;;   finsum-comm-monoid-type                formerly an `informal' support
;;;                                          (theorem-library/finsum-comm-monoid.scm:36)
;;;   crmcm-carr                      (NEW)  the multiplicative view's carrier
;;;   prod-ring-type                         formerly an `informal' support
;;;                                          (theorem-library/prod-of-sums.scm:175)
;;;   mpow-comm-monoid-type-ind       (NEW)  monoid-power typing, n OUTERMOST
;;;   ring-power-type                        formerly an `informal' support
;;;                                          (structure-library/ring-power.scm:41)
;;;   sum-ag-in-subset-ind            (NEW)  a fold stays inside a sub-monoid
;;;   finsum-in-subset                (NEW)  the FINSUM form of it
;;;   submodule-finsum-closed                formerly a `well-known' support
;;;                                          (structure-library/mod-seq.scm:325)
;;;   funcomp-succ-type       funcomp-succ-type WITH (IN q NN) -- installed under the ORIGINAL name; the support was retired GUARDED (integrator, 2026-09-17)
;;;
;;; Every retired statement is copied LITERALLY from its support site.
;;;
;;; ONE MECHANISM, FOUR LEAVES.  finsum-comm-monoid-type's warrant said "same
;;; induction as finsum-type", and that is exactly right: theorem-library/
;;; finsum-type-proof.scm's chain (fold-length induction for SUM-AG, then
;;; ENUM-FAM's totality, then FINSUM as the SUM-AG over FIN-ENUM) is reproduced
;;; here over IS-COMM-MONOID instead of IS-ABELIAN-GROUP.  What the abelian-group
;;; chain took from `group-identity-in' and `group-carrier-closed-opr' this one
;;; takes from the two projections proved at the head of this file, by op-typing's
;;; driver: unfold IS-COMM-MONOID, take the (op OPR (CARTESIAN CARR CARR) CARR)
;;; conjunct, bridge the TUPLING with apply-tupling-2 (a `==', which `subst'
;;; takes), then pair-in-cartesian + fun-apply-type-c.  Inverses and
;;; commutativity are never used, which is the whole content of the warrant.
;;;
;;; The MONOID-level projections are NOT cited.  `monoid-identity-in' and
;;; `monoid-carrier-closed-opr' (structure-library/monoid.scm:40,45) are
;;; `theory-add-axiom!' with no warrant -- `trust: none' -- so a chain through
;;; them would bill worse than the supports it replaces.  Both are proved here
;;; under COMM-MONOID's own unfold instead; the two monoid axioms are a separate
;;; candidate and are NOT touched (their auto-generated view companions --
;;; monoid-identity-in-abelian-group-as-monoid-module-vector-ag and friends --
;;; would disappear if they were retired; see CLAUDE.md, "Proving a fact that
;;; used to be an axiom moves it past the view specializer").
;;;
;;; prod-ring-type and ring-power-type are the same fact seen through the
;;; MULTIPLICATIVE view: PROD-RING(R,f,X) is FINPROD, i.e. FINSUM, over
;;; COMMUTATIVE-RING-MULTIPLICATIVE-CM(R), and RING-POWER(R,x,n) is MPOW over the
;;; same view.  `def-functor' installs no per-slot read-off (CLAUDE.md, "`slot' on
;;; a VIEW built by def-functor has no per-slot projection"), so `crmcm-carr' is
;;; proved here by theorem-library/ag-view-read-offs.scm's recipe -- slot, functoid
;;; unfold, nth-r -- and it is the SAME-SYMBOL case (CARR read off CARR), so the
;;; opening `slot' rewrites the goal's right-hand side too and it has to be put
;;; back with a `have!' plus one `subst'.  `mpow-type' (structure-library/
;;; monoid-power.scm) is an asserted axiom and is NOT cited; the induction is
;;; redone here over a commutative monoid, which is what the view supplies.
;;;
;;; submodule-finsum-closed goes the same way and NOT the way its warrant
;;; proposed.  That warrant says "induction on |S| via finsum-insert" -- an
;;; induction over finite SETS, for which the tree has no principle, and
;;; finsum-insert needs f restricted to a smaller domain, which the tree cannot
;;; express (the argument is spelled out in theorem-library/
;;; finsum-single-support.scm).  FINSUM is DEFINED as a SUM-AG over an
;;; enumeration, so the available induction -- `ni' on the fold length -- does the
;;; whole job.  The lemma is stated for an ARBITRARY subset of an abelian group
;;; closed under OPR and containing IDEN (`finsum-in-subset'); the submodule
;;; statement is that at ag := MODULE-VECTOR-AG(md), with mvag-id / mvag-op
;;; turning IDEN and OPR into VZERO and VADD, where submodule-vzero-in and
;;; submodule-vadd-closed (both `definitional') apply.
;;;
;;; funcomp-succ-type IS NOT PROVABLE AS STATED -- a GUARD finding, not a defect
;;; of the driver.  It says
;;;
;;;   forall X, q, f.  f in FUN(INTERVAL(1, succ q), X)
;;;                    =>  (z |-> f(succ z)) in FUN(INTERVAL(1,q), X)
;;;
;;; with `q' UNTYPED.  The pointwise obligation is `succ z in INTERVAL(1, succ q)'
;;; for z in INTERVAL(1,q), whose third clause is `succ z <= succ q'.  From
;;; `z <= q' that step needs `succ q = q + 1' (nn-succ-plus-one) or
;;; `nn-add-le-mono', and every route through the tree's NN order demands
;;; `q in NN'.  It is not merely unreachable: for a q outside NN the statement is
;;; FALSE in a model.  Take q = 3/2.  `succ' is the ordinal successor, so succ(3/2)
;;; is not a real and nothing in the theory decides `i <= succ(3/2)'; a model may
;;; make it false for every i, and then INTERVAL(1, succ q) = EMPTY-SET while
;;; INTERVAL(1,q) = {1}.  The empty function lies in FUN(EMPTY-SET, X), so the
;;; hypothesis holds, and the conclusion would require f(succ 1) = f(2) to lie in
;;; X for an f whose domain is empty.  So `funcomp-succ-type' below
;;; carries `(IN q NN)', in the shape `matact-summand-type-le-guarded' set
;;; (CLAUDE.md, mod-seq.scm:329); the guard is free at the only citation site,
;;; theorem-library/border-mult-proof.scm:157, whose own theorem already assumes
;;; `q in NN'.  The INTEGRATOR decides whether to retire the unguarded support;
;;; this file does not, and does not touch it.
;;;
;;; NOT PROVEN HERE: choose-in-nn (structure-library/injection.scm:277).  Its only
;;; route is CARD(POWER(ORD-SEGMENT n)) in NN -- `card-power-nn'
;;; (theorem-library/prod-of-sums.scm:78), which is ASSERTED `well-known'.  The
;;; driver is written and closes `proven modulo {card-power-nn} [trust:
;;; well-known]' (scratchpad/rkf/p18.scm); by the batch brief an asserted card
;;; fact means the leaf is reported and left.
;;;
;;; NOT IN THIS FILE: nn-minus-in-nn and falling-in-nn.  Both need `nn-le-gap'
;;; (theorem-library/series-block-abs), which loads BELOW this file's upper bound.
;;; They are theorem-library/rake-finsum-typing-nn.scm.
;;;
;;; BILL (probe on the band, worker-01): ALL THIRTEEN `proven modulo 0'.
;;;
;;; CITATIONS, with the file that installs each (load position as of 2026-09-17,
;;; while the integrator was still wiring the other rake batches -- use the FILE
;;; NAMES):
;;;   theorem-library/axioms (primitive):        apply-tupling-2, equality-symmetry  15
;;;   structure-library/monoid (definitional):   is-comm-monoid  (the IS-X iff)      20
;;;   structure-library/finite-dimensional (definitional):
;;;                                              submodule-vzero-in,
;;;                                              submodule-vadd-closed              55
;;;   structure-library/views (definitional):    commutative-ring-multiplicative-cm-
;;;                                              is-comm-monoid,
;;;                                              module-vector-ag-is-abelian-group  60
;;;   structure-library/monoid-power (definitional):  mpow-zero, mpow-succ           78
;;;   structure-library/ring-power (functoid):   RING-POWER                          80
;;;   structure-library/sequences (definitional):sum-ag-zero, sum-ag-succ            92
;;;   structure-library/finsum (functoid):       FINSUM, ENUM-FAM, FIN-ENUM          93
;;;   structure-library/finprod (functoid):      PROD-RING, FINPROD                  94
;;;   structure-library/ring (definitional):     is-ring
;;;   structure-library/commutative-ring (definitional): is-commutative-ring-def
;;;   structure-library/bijection (definitional):bijection-membership-iff
;;;   number-systems (primitive):                nn-is-set, nn-succ-closed
;;;   theorem-library/interval-basics:           interval-in-set, interval-elt-in-nn,
;;;                                              interval-lo, interval-hi           151
;;;   theorem-library/interval-mem-intro:        interval-mem-intro                 152
;;;   theorem-library/ord-segment-nn-succ-proof: ord-segment-nn-succ                153
;;;   theorem-library/ord-segment-nn-subset-proof: ord-segment-nn-subset            154
;;;   theorem-library/finsum-insert:             fin-enum-is-bijection              155
;;;   theorem-library/ag-view-read-offs:         mvag-id, mvag-op                   161
;;;   theorem-library/binary-minus-laws:         rr-sub-in-rr                       162
;;;   theorem-library/fun-apply-type-proof:      fun-apply-type-c                   163
;;;   theorem-library/pair-tuple-sethood:        pair-in-cartesian                  165
;;;   theorem-library/nn-order-ord:              nn-one-in, nn-le-succ              167
;;;   theorem-library/nn-order-basics:           nn-in-rr, nn-le-trans-guarded      169
;;;   theorem-library/nn-parity-proof:           nn-succ-plus-one                   212
;;;   theorem-library/nn-order-proof:            nn-add-le-mono                     224
;;;
;;; LOAD WINDOW, by FILE NAME:
;;;   lo -- AFTER theorem-library/nn-order-proof, the LATEST citation
;;;         (nn-add-le-mono, used only by funcomp-succ-type).  Everything
;;;         else loads earlier; nn-parity-proof (nn-succ-plus-one) is next.
;;;   hi -- BEFORE theorem-library/spans-transport-proof, the earliest PROVEN
;;;         citer of submodule-finsum-closed (its only one; smith-staircase-proof
;;;         merely re-`topic!'s the name).  finsum-comm-monoid-type, prod-ring-type
;;;         and ring-power-type have NO proven citer at all, and none of the four
;;;         has a view companion, so nothing else constrains the position.
;;;   i.e. between nn-order-proof and spans-transport-proof (positions (224, 364)
;;;   in the 2026-09-17 numbering).
;;;
;;; Helper prefix: rkf-.

;;; ---------------------------------------------------------------------------
;;; helpers

(define (rkf-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; rkf: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "rkf: proof not complete" name))))

;; Among LEAVES (as dk-opened returns them), the unique one whose GOAL satisfies PRED.
(define (rkf-leaf leaves pred what)
  (let ((hits (filter (lambda (l) (pred (dk-goal-of l))) leaves)))
    (cond ((null? hits) (error "rkf-leaf: no leaf for" what))
          ((pair? (cdr hits)) (error "rkf-leaf: ambiguous leaf for" what))
          (#t (car hits)))))

(define (rkf-pick-head head what) (dk-pick (dk-head? head) what))

;; the NN-typed eigenvariable in context: (IN v NN) with v a symbol.
(define (rkf-nn-var)
  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                  (eq? (caddr f) 'NN)))
                 "n in NN")))

;; (rkf-guarded-forall? F DOM) -- F is (FORALL v (IMPLIES (IN v DOM) _)), with DOM
;; a term or a predicate on terms.  EVERY accessor is length-guarded: the
;; predicate runs over the WHOLE context, where a two-element antecedent like
;; (IS-MODULE md) makes a bare `caddr' die with "() passed to safe-car".
(define (rkf-guarded-forall? f dom)
  (and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3)
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                     (if (procedure? dom) (dom (caddr a)) (equal? (caddr a) dom))))))))

;; the eigenvariable of the ORD-SEGMENT typing among LANDED (what dk-peel! returned).
(define (rkf-seg-var landed)
  (let ((f (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f))
                                      (pair? (caddr f)) (eq? (car (caddr f)) 'ORD-SEGMENT)))
                     landed)))
    (if f (cadr f)
        (error "rkf-seg-var: no ORD-SEGMENT typing landed"
               (map expression->string landed)))))

;;; ===========================================================================
;;; (1) The two COMM-MONOID projections -- op-typing.scm's driver, for OPR/IDEN.
;;;
;;; The gap between the IS-COMM-MONOID op-clause -- (IN (OPR s) (FUN (CARTESIAN
;;; (CARR s) (CARR s)) (CARR s))) -- and the applied form is the TUPLING: a
;;; structure operation eats one pair, the parser emits the curried (f a b).
;;; `apply-tupling-2' is stated with `==', and `subst' takes a `==' as happily as
;;; a `=' (pi-eq-subst!), so the bridge is one rewrite of the goal.

(sp (make-wff
     '(FORALL s (IMPLIES (IS-COMM-MONOID s)
        (FORALL a (IMPLIES (IN a (CARR s))
        (FORALL b (IMPLIES (IN b (CARR s))
          (IN ((OPR s) a b) (CARR s))))))))))
(dk-peel!)
(mac-h 'is-comm-monoid '(IS-COMM-MONOID s))
(dk-split-all!)
(fact 'apply-tupling-2 '(OPR s) 'a 'b)
(subst '(== ((OPR s) a b) ((OPR s) (LIST a b))))
(fact 'pair-in-cartesian '(CARR s) '(CARR s) 'a 'b)
(fact 'fun-apply-type-c '(OPR s) '(CARTESIAN (CARR s) (CARR s)) '(CARR s) '(LIST a b))
(ass)
(rkf-check! 'comm-monoid-carrier-closed-opr)
(qed 'comm-monoid-carrier-closed-opr)
(topic! 'comm-monoid-carrier-closed-opr 'algebra)

(sp (make-wff '(FORALL s (IMPLIES (IS-COMM-MONOID s) (IN (IDEN s) (CARR s))))))
(dk-peel!)
(mac-h 'is-comm-monoid '(IS-COMM-MONOID s))
(dk-split-all!)
(ass)
(rkf-check! 'comm-monoid-identity-in-carr)
(qed 'comm-monoid-identity-in-carr)
(topic! 'comm-monoid-identity-in-carr 'algebra)

;;; ===========================================================================
;;; (2) finsum-comm-monoid-type, by finsum-type-proof.scm's chain.

;;; sum-ag-comm-monoid-type-ind: the fold length OUTERMOST, because `ni' tests
;;; the goal's SHAPE and `di' is greedy (CLAUDE.md), so there is no peeling down
;;; to an inner n-universal.
;;;   base: SUM-AG(m,f,0) = IDEN(m)                      (sum-ag-zero)
;;;   step: SUM-AG(m,f,succ n) = (OPR m)(SUM-AG(m,f,n), f n)   (sum-ag-succ)

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL m (IMPLIES (IS-COMM-MONOID m)
        (FORALL f (IMPLIES (IN f (FUN NN (CARR m)))
          (IN (SUM-AG m f n) (CARR m))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkf-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkf-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (let ((mv (cadr (rkf-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m"))))
    (mac 'sum-ag-zero)
    (dk-fact! 'comm-monoid-identity-in-carr mv)
    (ass))
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (rkf-nn-var))
         (gl (dk-goal))                          ; (IN (SUM-AG m f (succ n)) (CARR m))
         (mv (cadr (cadr gl)))
         (fv (caddr (cadr gl)))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH")))
    (mac 'sum-ag-succ)
    (dk-apply! ih mv fv)
    (dk-fact! 'fun-apply-type-c fv 'NN (list 'CARR mv) nv)
    (dk-fact! 'comm-monoid-carrier-closed-opr mv (list 'SUM-AG mv fv nv) (list fv nv))
    (ass)))
(rkf-check! 'sum-ag-comm-monoid-type-ind)
(qed 'sum-ag-comm-monoid-type-ind)
(topic! 'sum-ag-comm-monoid-type-ind 'algebra)

;;; enum-fam-comm-monoid-in-fun: ENUM-FAM(m,f,phi,n) is a TOTAL function
;;; NN -> CARR(m).  Its IF guard fills the indices OUTSIDE ORD-SEGMENT(n) with
;;; IDEN(m), which is what makes the family total even though phi is only defined
;;; on the segment.  `lam-t' opens TWO leaves -- the pointwise typing AND the
;;; sethood of the lambda's domain NN (CLAUDE.md).

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL m (IMPLIES (IS-COMM-MONOID m)
        (FORALL S (FORALL phi (IMPLIES (IN phi (FUN (ORD-SEGMENT n) S))
        (FORALL f (IMPLIES (IN f (FUN S (CARR m)))
          (IN (ENUM-FAM m f phi n) (FUN NN (CARR m))))))))))))))
(dk-peel!)
(let* ((nv    (rkf-nn-var))
       (mv    (cadr (rkf-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m")))
       (phi-h (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                        (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                        (pair? (cadr (caddr a)))
                                        (eq? (car (cadr (caddr a))) 'ORD-SEGMENT)))
                       "phi in FUN(ORD-SEGMENT n, S)"))
       (phiv  (cadr phi-h))
       (sv    (caddr (caddr phi-h)))
       (fv    (cadr (dk-pick (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                              (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                              (equal? (cadr (caddr a)) sv)))
                             "f in FUN(S, CARR m)"))))
  (mac 'ENUM-FAM)
  (let* ((ls   (dk-opened (lambda () (lam-t))))
         (setl (rkf-leaf ls (lambda (g) (equal? g '(IN NN SET))) "NN in SET"))
         (ptw  (rkf-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'FORALL))) "pointwise typing")))
    (dk-focus! setl)
    (fact 'nn-is-set)
    (ass)
    (dk-focus! ptw)
    (let* ((iv  (dk-di-var!))
           (pp  (list 'IN iv (list 'ORD-SEGMENT nv)))
           (ift (list 'IF pp (list fv (list phiv iv)) (list 'IDEN mv))))
      (use-em pp
        (lambda ()                                   ; inside the segment
          (let* ((l (dk-opened (lambda () (if-true ift))))
                 (c (rkf-leaf l (lambda (g) (equal? g pp)) "if-true condition"))
                 (m (rkf-leaf l (lambda (g) (not (equal? g pp))) "if-true main")))
            (dk-focus! c) (ass)
            (dk-focus! m)
            (subst (list '= ift (list fv (list phiv iv))))
            (dk-fact! 'fun-apply-type-c phiv (list 'ORD-SEGMENT nv) sv iv)
            (dk-fact! 'fun-apply-type-c fv sv (list 'CARR mv) (list phiv iv))
            (ass)))
        (lambda ()                                   ; outside: the value IS the identity
          (let* ((l (dk-opened (lambda () (if-false ift))))
                 (c (rkf-leaf l (dk-head? 'NOT) "if-false condition"))
                 (m (rkf-leaf l (lambda (g) (not ((dk-head? 'NOT) g))) "if-false main")))
            (dk-focus! c) (ass)
            (dk-focus! m)
            (subst (list '= ift (list 'IDEN mv)))
            (dk-fact! 'comm-monoid-identity-in-carr mv)
            (ass)))))))
(rkf-check! 'enum-fam-comm-monoid-in-fun)
(qed 'enum-fam-comm-monoid-in-fun)
(topic! 'enum-fam-comm-monoid-in-fun 'plumbing)

;;; finsum-comm-monoid-type -- the statement as theorem-library/finsum-comm-monoid.scm
;;; spells it, copied literally.  FINSUM(m,f,S) is DEFINED as
;;; SUM-AG(m, ENUM-FAM(m,f,FIN-ENUM S,|S|), |S|).  The FUN typing of FIN-ENUM(S)
;;; is taken INLINE, by unfolding the definitional `bijection-membership-iff' on
;;; the hypothesis rather than citing `bijection-in-fun' (which is proved in
;;; structure-library/bijection-derived, far below this file).

(sp (make-wff
     '(FORALL m (IMPLIES (IS-COMM-MONOID m)
        (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
        (FORALL f (IMPLIES (IN f (FUN S (CARR m)))
          (IN (FINSUM m f S) (CARR m)))))))))))
(dk-peel!)
(let* ((mv (cadr (rkf-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m")))
       (sv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                          "S in SET")))
       (fv (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                           (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                           (equal? (cadr (caddr f)) sv)))
                          "f in FUN(S, CARR m)")))
       (fam (list 'ENUM-FAM mv fv (list 'FIN-ENUM sv) (list 'CARD sv))))
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (dk-fact! 'enum-fam-comm-monoid-in-fun (list 'CARD sv) mv sv (list 'FIN-ENUM sv) fv)
  (dk-fact! 'sum-ag-comm-monoid-type-ind (list 'CARD sv) mv fam)
  (ass))
(rkf-check! 'finsum-comm-monoid-type)
(qed 'finsum-comm-monoid-type)
(topic! 'finsum-comm-monoid-type 'algebra)

;;; ===========================================================================
;;; (3) The multiplicative view, and the two ring-side typings that ride on it.

;;; crmcm-carr: CARR(COMMUTATIVE-RING-MULTIPLICATIVE-CM R) = CARR(R).
;;; ag-view-read-offs.scm's recipe, and its SAME-SYMBOL case: the target accessor
;;; and the source accessor are both CARR, so the opening `(slot 'CARR)' rewrites
;;; the goal's right-hand side as well and it has to be put back before `rfl'.
;;; The guard is what makes the terms denote, and `=' asserts definedness, so the
;;; guard is not decoration (the six ag-view read-offs carry theirs for the same
;;; reason).

(sp (make-wff '(FORALL r (IMPLIES (IS-COMMUTATIVE-RING r)
                 (= (CARR (COMMUTATIVE-RING-MULTIPLICATIVE-CM r)) (CARR r))))))
(di)                                    ; the binder
(di)                                    ; the guard -- not a typing, so one `di'
                                        ; does not take both
(mac-h 'is-commutative-ring-def '(IS-COMMUTATIVE-RING r))
(dk-split-all!)
(mac-h 'is-ring '(IS-RING r))
(dk-split-all!)
(slot 'CARR)
(mac 'COMMUTATIVE-RING-MULTIPLICATIVE-CM)
(nth-r)
(let ((proj (caddr (dk-goal))))         ; (NTH 1 r), left by the opening slot
  (have! (list '== proj '(CARR r)) (lambda () (slot 'CARR) (qrfl)))
  (subst (list '== proj '(CARR r))))
(rfl)
(rkf-check! 'crmcm-carr)
(qed 'crmcm-carr)
(topic! 'crmcm-carr 'algebra)

;;; prod-ring-type -- the statement as theorem-library/prod-of-sums.scm spells it,
;;; copied literally.  PROD-RING is FINPROD is FINSUM at the multiplicative view.

(sp (make-wff
     '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
        (FORALL X (IMPLIES (AND (IN X SET) (IN (CARD X) NN))
        (FORALL f (IMPLIES (IN f (FUN X (CARR R)))
          (IN (PROD-RING R f X) (CARR R))))))))))
(dk-peel!)
(dk-split-all!)                          ; the finiteness premise is a conjunction
(let* ((view '(COMMUTATIVE-RING-MULTIPLICATIVE-CM R))
       (vcarr (list 'CARR view)))
  (mac 'PROD-RING)
  (mac 'FINPROD)
  (dk-fact! 'crmcm-carr 'R)
  (dk-fact! 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
  (have! (list 'IN 'f (list 'FUN 'X vcarr))
         (lambda () (subst (list '= vcarr '(CARR R))) (ass)))
  (dk-fact! 'finsum-comm-monoid-type view 'X 'f)
  (dk-fact! 'equality-symmetry vcarr '(CARR R))
  (subst (list '= '(CARR R) vcarr))
  (ass))
(rkf-check! 'prod-ring-type)
(qed 'prod-ring-type)
(topic! 'prod-ring-type 'algebra)

;;; mpow-comm-monoid-type-ind: MPOW's typing over a commutative monoid, the
;;; exponent OUTERMOST.  `mpow-type' (structure-library/monoid-power.scm) states
;;; this over IS-MONOID and is an ASSERTED axiom, so it is not cited; the
;;; induction its warrant describes is run here.
;;;   base: MPOW(m,x,0) = IDEN(m)                     (mpow-zero)
;;;   step: MPOW(m,x,succ n) = (OPR m)(x, MPOW(m,x,n))  (mpow-succ)

(sp (make-wff
     '(FORALL n (IMPLIES (IN n NN)
        (FORALL m (IMPLIES (IS-COMM-MONOID m)
        (FORALL x (IMPLIES (IN x (CARR m))
          (IN (MPOW m x n) (CARR m))))))))))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkf-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkf-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (let ((mv (cadr (rkf-pick-head 'IS-COMM-MONOID "IS-COMM-MONOID m"))))
    (mac 'mpow-zero)
    (dk-fact! 'comm-monoid-identity-in-carr mv)
    (ass))
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv (rkf-nn-var))
         (gl (dk-goal))                          ; (IN (MPOW m x (succ n)) (CARR m))
         (mv (cadr (cadr gl)))
         (xv (caddr (cadr gl)))
         (ih (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL))) "the IH")))
    (mac 'mpow-succ)
    (dk-apply! ih mv xv)
    (dk-fact! 'comm-monoid-carrier-closed-opr mv xv (list 'MPOW mv xv nv))
    (ass)))
(rkf-check! 'mpow-comm-monoid-type-ind)
(qed 'mpow-comm-monoid-type-ind)
(topic! 'mpow-comm-monoid-type-ind 'algebra)

;;; ring-power-type -- the statement as structure-library/ring-power.scm spells
;;; it, copied literally.  RING-POWER(R,x,n) = MPOW(view, x, n); crmcm-carr moves
;;; the typing between CARR(R) and the view's carrier in both directions, which is
;;; what the `equality-symmetry' citation is for (the goal names CARR(R) and the
;;; lemma concludes about the view's).

(sp (make-wff
     '(FORALL R (IMPLIES (IS-COMMUTATIVE-RING R)
        (FORALL x (IMPLIES (IN x (CARR R))
          (FORALL n (IMPLIES (IN n NN)
            (IN (RING-POWER R x n) (CARR R))))))))))
(dk-peel!)
(let* ((nv (rkf-nn-var))
       (view '(COMMUTATIVE-RING-MULTIPLICATIVE-CM R))
       (vcarr (list 'CARR view)))
  (mac 'RING-POWER)
  (dk-fact! 'crmcm-carr 'R)
  (dk-fact! 'commutative-ring-multiplicative-cm-is-comm-monoid 'R)
  (have! (list 'IN 'x vcarr)
         (lambda () (subst (list '= vcarr '(CARR R))) (ass)))
  (dk-fact! 'mpow-comm-monoid-type-ind nv view 'x)
  (dk-fact! 'equality-symmetry vcarr '(CARR R))
  (subst (list '= '(CARR R) vcarr))
  (ass))
(rkf-check! 'ring-power-type)
(qed 'ring-power-type)
(topic! 'ring-power-type 'algebra)

;;; ===========================================================================
;;; (4) A finite sum stays inside a sub-monoid -- and submodule-finsum-closed.

;;; sum-ag-in-subset-ind: n in NN => for an abelian group ag and ANY subset sm
;;; that contains IDEN(ag) and is closed under (OPR ag), a fold all of whose
;;; summands lie in sm lies in sm.  Nothing here is about modules; the submodule
;;; statement is this at ag := MODULE-VECTOR-AG(md).
;;;   base: the empty fold IS the seed          (sum-ag-zero)
;;;   step: sum-ag-succ, the top summand from the agreement hypothesis at n
;;;         (n is in ORD-SEGMENT(succ n) but not in ORD-SEGMENT(n)), the rest from
;;;         the IH on the agreement cut down to ORD-SEGMENT(n).

(define rkf-sub-ind-stmt
  '(FORALL n (IMPLIES (IN n NN)
     (FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL sm (IMPLIES (IN (IDEN ag) sm)
       (IMPLIES (FORALL x_ (IMPLIES (IN x_ sm)
                  (FORALL y_ (IMPLIES (IN y_ sm) (IN ((OPR ag) x_ y_) sm)))))
     (FORALL g_ (IMPLIES (FORALL i_ (IMPLIES (IN i_ (ORD-SEGMENT n)) (IN (g_ i_) sm)))
       (IN (SUM-AG ag g_ n) sm)))))))))))

(sp (make-wff rkf-sub-ind-stmt))
(let* ((leaves (dk-opened (lambda () (ni))))
       (base (rkf-leaf leaves (lambda (g) (not (dk-contains? g 'succ))) "induction base"))
       (step (rkf-leaf leaves (lambda (g) (dk-contains? g 'succ))       "induction step")))
  (dk-focus! base)
  (dk-peel!)
  (mac 'sum-ag-zero)                        ; goal (IN (IDEN ag) sm) -- a hypothesis
  (ass)
  (dk-focus! step)
  (dk-peel!)
  (let* ((nv  (rkf-nn-var))
         (gl  (dk-goal))                    ; (IN (SUM-AG ag g_ (succ n)) sm)
         (agv (cadr (cadr gl)))
         (gv  (caddr (cadr gl)))
         (smv (caddr gl))
         ;; the three universals in context are told apart by their ANTECEDENT,
         ;; never by their head (CLAUDE.md, "never name an ASSUMPTION by shape").
         (agree (dk-pick (lambda (f) (rkf-guarded-forall?
                                      f (lambda (d) (and (pair? d) (eq? (car d) 'ORD-SEGMENT)))))
                         "the agreement hypothesis on OS(succ n)"))
         (clos  (dk-pick (lambda (f) (rkf-guarded-forall? f smv)) "the closure hypothesis"))
         (ih    (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                          (not (equal? f agree)) (not (equal? f clos))))
                         "the IH")))
    (mac 'sum-ag-succ)
    ;; the top summand
    (have! (list 'IN nv (list 'ORD-SEGMENT (list 'succ nv)))
           (lambda () (mac 'ord-segment-nn-succ) (oi-r) (rfl)))
    (dk-apply! agree nv)
    ;; the rest: the IH, whose own guard is this hypothesis restricted to OS(n)
    (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'ORD-SEGMENT nv))
                                   (list 'IN (list gv 'i_) smv)))
           (lambda ()
             (let* ((landed (dk-peel!))
                    (iv     (rkf-seg-var landed)))
               (have! (list 'IN iv (list 'ORD-SEGMENT (list 'succ nv)))
                      (lambda () (mac 'ord-segment-nn-succ) (oi-l) (ass)))
               (dk-apply! agree iv)
               (ass))))
    (dk-apply! ih agv smv gv)
    (dk-apply! (dk-apply! clos (list 'SUM-AG agv gv nv)) (list gv nv))
    (ass)))
(rkf-check! 'sum-ag-in-subset-ind)
(qed 'sum-ag-in-subset-ind)
(topic! 'sum-ag-in-subset-ind 'algebra)

;;; finsum-in-subset -- the FINSUM form.  The whole content is that the ENUM-FAM
;;; of the chosen enumeration lands in sm on ORD-SEGMENT(|S|): at an index i_
;;; there it beta-reduces through its IF to f(FIN-ENUM(S)(i_)), and FIN-ENUM(S)(i_)
;;; lies in S, where f lands in sm by hypothesis.  `lam-b' needs its argument
;;; TYPED FIRST (CLAUDE.md), which is what the ord-segment-nn-subset citation is
;;; for: an index in the segment is in NN, the lambda's own domain.

(define rkf-fis-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL sm (IMPLIES (IN (IDEN ag) sm)
       (IMPLIES (FORALL x_ (IMPLIES (IN x_ sm)
                  (FORALL y_ (IMPLIES (IN y_ sm) (IN ((OPR ag) x_ y_) sm)))))
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR ag)))
       (IMPLIES (FORALL z (IMPLIES (IN z S) (IN (f z) sm)))
         (IN (FINSUM ag f S) sm)))))))))))))

(sp (make-wff rkf-fis-stmt))
(dk-peel!)
(let* ((agv (cadr (rkf-pick-head 'IS-ABELIAN-GROUP "IS-ABELIAN-GROUP ag")))
       (sv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (eq? (caddr f) 'SET)))
                           "S in SET")))
       (fv  (cadr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                            (pair? (caddr f)) (eq? (car (caddr f)) 'FUN)
                                            (equal? (cadr (caddr f)) sv)))
                           "f in FUN(S, CARR ag)")))
       (smv (caddr (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                             (equal? (cadr f) (list 'IDEN agv))))
                            "IDEN(ag) in sm")))
       (agree (dk-pick (lambda (f) (rkf-guarded-forall? f sv)) "forall z in S. f z in sm"))
       (phi (list 'FIN-ENUM sv))
       (seg (list 'ORD-SEGMENT (list 'CARD sv)))
       (fam (list 'ENUM-FAM agv fv phi (list 'CARD sv))))
  (mac 'FINSUM)
  (let ((bij (dk-fact! 'fin-enum-is-bijection sv)))
    (mac-h 'bijection-membership-iff bij)
    (dk-split-all!))
  (have! (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ seg)
                                 (list 'IN (list fam 'i_) smv)))
         (lambda ()
           (let* ((landed (dk-peel!))
                  (iv     (rkf-seg-var landed))
                  (ift (list 'IF (list 'IN iv seg) (list fv (list phi iv)) (list 'IDEN agv))))
             (dk-fact! 'ord-segment-nn-subset (list 'CARD sv) iv)   ; type BEFORE the beta
             (mac 'ENUM-FAM)
             (lam-b)
             (let* ((ls  (dk-opened (lambda () (if-true ift))))
                    (cnd (rkf-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'IN)
                                                       (equal? (cadr g) iv)))
                                   "if-true condition"))
                    (mn  (rkf-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'IN)
                                                       (not (equal? (cadr g) iv))))
                                   "if-true main")))
               (dk-focus! cnd) (ass)
               (dk-focus! mn)
               (subst (list '= ift (list fv (list phi iv))))
               (dk-fact! 'fun-apply-type-c phi seg sv iv)
               (dk-apply! agree (list phi iv))
               (ass)))))
  (dk-fact! 'sum-ag-in-subset-ind (list 'CARD sv) agv smv fam)
  (ass))
(rkf-check! 'finsum-in-subset)
(qed 'finsum-in-subset)
(topic! 'finsum-in-subset 'algebra)

;;; submodule-finsum-closed -- the statement as structure-library/mod-seq.scm
;;; spells it, copied literally.  mvag-id and mvag-op are applied to the GOAL of
;;; a `have!' lane, so the IS-SUBMODULE hypothesis is never unfolded and never
;;; deleted (`mac-h' replaces the assumption it unfolds -- CLAUDE.md).

(define rkf-sfc-stmt
  '(FORALL md (IMPLIES (IS-MODULE md)
     (FORALL sm (IMPLIES (IS-SUBMODULE md sm)
     (FORALL S (IMPLIES (IN S SET) (IMPLIES (IN (CARD S) NN)
     (FORALL f (IMPLIES (IN f (FUN S (CARR (MODULE-VECTOR-AG md))))
       (IMPLIES (FORALL z (IMPLIES (IN z S) (IN (f z) sm)))
         (IN (FINSUM (MODULE-VECTOR-AG md) f S) sm))))))))))))

(sp (make-wff rkf-sfc-stmt))
(dk-peel!)
(let ((vag '(MODULE-VECTOR-AG md)))
  (dk-fact! 'module-vector-ag-is-abelian-group 'md)
  (have! (list 'IN (list 'IDEN vag) 'sm)
         (lambda () (mac 'mvag-id)                    ; goal (IN (VZERO md) sm)
                    (dk-fact! 'submodule-vzero-in 'md 'sm)
                    (ass)))
  (have! (list 'FORALL 'x_ (list 'IMPLIES (list 'IN 'x_ 'sm)
           (list 'FORALL 'y_ (list 'IMPLIES (list 'IN 'y_ 'sm)
             (list 'IN (list (list 'OPR vag) 'x_ 'y_) 'sm)))))
         (lambda ()
           (dk-peel!)
           (mac 'mvag-op)                             ; goal (IN ((VADD md) x_ y_) sm)
           (dk-apply! (dk-apply! (dk-fact! 'submodule-vadd-closed 'md 'sm) 'x_) 'y_)
           (ass)))
  (dk-fact! 'finsum-in-subset vag 'sm 'S 'f)
  (ass))
(rkf-check! 'submodule-finsum-closed)
(qed 'submodule-finsum-closed)
(topic! 'submodule-finsum-closed 'algebra)

;;; ===========================================================================
;;; (5) funcomp-succ-type, WITH the guard its proof needs.  See the header: the
;;; unguarded statement (theorem-library/finsum-additive.scm:429) is not merely
;;; unreachable but false in a model where q lies outside NN.  This file does NOT
;;; retire it; the integrator decides.

(sp (make-wff
     '(FORALL X (FORALL q (IMPLIES (IN q NN)
        (FORALL f (IMPLIES (IN f (FUN (INTERVAL 1 (succ q)) X))
          (IN (VNB-LAMBDA z (INTERVAL 1 q) (f (succ z))) (FUN (INTERVAL 1 q) X)))))))))
(dk-peel!)
(let ((ls (dk-opened (lambda () (lam-t)))))        ; TWO leaves: sethood and pointwise
  (let ((setl (rkf-leaf ls (lambda (g) (equal? g '(IN (INTERVAL 1 q) SET))) "domain sethood"))
        (ptw  (rkf-leaf ls (lambda (g) (and (pair? g) (eq? (car g) 'FORALL))) "pointwise typing")))
    (dk-focus! setl)
    (fact 'interval-in-set 1 'q)
    (ass)
    (dk-focus! ptw)
    (let ((zv (dk-di-var!)))
      (fact 'interval-elt-in-nn 1 'q zv)
      (fact 'interval-lo 1 'q zv)
      (fact 'interval-hi 1 'q zv)
      (fact 'nn-succ-closed zv)
      (fact 'nn-one-in)
      (fact 'nn-le-succ zv)
      (fact 'nn-le-trans-guarded 1 zv (list 'succ zv))    ; 1 <= z <= succ z
      (fact 'nn-in-rr zv) (fact 'nn-in-rr 'q) (fact 'rr-one-in)
      (fact 'nn-succ-plus-one zv)
      (fact 'nn-succ-plus-one 'q)
      ;; succ z <= succ q.  THIS is the step that needs (IN q NN): without it
      ;; succ q is not q + 1 and nothing relates the two sides.
      (have! (list '<= (list 'succ zv) '(succ q))
        (lambda ()
          (subst (list '= (list 'succ zv) (list '+ zv 1)))
          (subst '(= (succ q) (+ q 1)))
          (have! (list '= (list '+ zv 1) (list '+ 1 zv)) (lambda () (crs)))
          (subst (list '= (list '+ zv 1) (list '+ 1 zv)))
          (have! '(= (+ q 1) (+ 1 q)) (lambda () (crs)))
          (subst '(= (+ q 1) (+ 1 q)))
          (fact 'nn-add-le-mono 'q 1 zv)
          (ass)))
      (fact 'interval-mem-intro 1 '(succ q) (list 'succ zv))
      (fact 'fun-apply-type-c 'f '(INTERVAL 1 (succ q)) 'X (list 'succ zv))
      (ass))))
(rkf-check! 'funcomp-succ-type)
(qed 'funcomp-succ-type)
(topic! 'funcomp-succ-type 'combinatorial)
