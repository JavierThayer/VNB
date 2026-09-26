;;; theorem-library/rake-sum-set-defined.scm -- SUM-SET DEFINED, and its four
;;; characterising laws PROVEN from the definition.  Rake batch 5c, assignment
;;; 5c-S (the user's decision (B) of 2026-09-18).  Helper prefix `r7s-'.
;;;
;;; THE DEFINING FORM, which belongs in the library and which this file assumes
;;; has already been evaluated:
;;;
;;;     (def-functoid 'SUM-SET '(r S f) '(FINSUM (RING-ADDITIVE-AG r) f S))
;;;
;;; Note the ARGUMENT ORDER: SUM-SET takes (ring, index set, summand) and FINSUM
;;; takes (group, summand, index set), so the last two swap.
;;;
;;; WHAT THIS FILE PROVES, and what had to change in each statement:
;;;
;;;   sum-set-empty              UNCHANGED (statement copied literally).
;;;   finsum-singleton-ptwise    NEW brick: finsum-singleton with the summand
;;;                                typed POINTWISE at the one point instead of
;;;                                by a FUN membership over the singleton.
;;;   sum-set-singleton-defined  sum-set-singleton plus (IN x SET) and the
;;;                                POINTWISE typing (IN (f x) (CARR r)).
;;;   sum-set-type-defined       sum-set-type plus (IN (CARD S) NN).
;;;   sum-set-disjoint-union-defined
;;;                              sum-set-disjoint-union plus (IN (CARD S1) NN)
;;;                                and (IN (CARD S2) NN).
;;;
;;; WHY EACH GUARD IS NECESSARY -- none of the four is decoration:
;;;
;;;   * FINITENESS.  FINSUM(ag,f,S) is SUM-AG(ag, ENUM-FAM(...), CARD S), a fold
;;;     over the NN-segment [0, CARD S).  For an infinite S, CARD S is not in NN
;;;     and the fold is an uninterpreted term: every FINSUM law in the tree
;;;     (finsum-type-ptwise, finsum-union-disjoint, finsum-congruence-q,
;;;     finsum-insert-ptwise) carries (IN (CARD S) NN), and nothing weaker is
;;;     available.  The axioms sum-set-type and sum-set-disjoint-union asserted
;;;     their conclusions for an ARBITRARY index set; that is exactly the
;;;     over-reach this file cannot and should not reproduce.  (The axiom
;;;     sum-set-disjoint-union needs the guard on BOTH halves: each side of the
;;;     conclusion is a sum in its own right.)
;;;   * (IN x SET) in the singleton law.  {x} is PAIR(x,x), and `pairing' makes
;;;     it a SET only for a set x; without that CARD({x}) is not known to be 1
;;;     and the enumeration behind FINSUM does not exist.
;;;   * the POINTWISE typing (IN (f x) (CARR r)) in the singleton law.  The
;;;     axiom's conclusion is a strict `=', which asserts that both sides denote;
;;;     with f entirely unquantified-over, f(x) is `IOTA y. [x,y] in f'
;;;     (app-graph) and need not denote at all, so the axiom as written is
;;;     underdetermined.  The pointwise form is the WEAKEST hypothesis that
;;;     makes it true -- weaker than the FUN typing over {x} that
;;;     finsum-singleton asks for, and, unlike it, available at the two citation
;;;     sites (where f is typed on a superset X and no restriction exists).
;;;
;;; sum-set-empty needs NO guard at all, and that is worth recording: its
;;; conclusion is a quasi-equality `==', finsum-empty is likewise unguarded, and
;;; the RING-ADDITIVE-AG read-off it needs is not the guarded theorem `ras-id'
;;; but the definitional functoid unfold composed with an NTH projection, which
;;; owes nothing.  So the law holds for an arbitrary r, ring or not.
;;;
;;; CITATIONS (0-based over the file names in load.scm, at the time of writing):
;;;   theory.scm (11, primitive): pairing, pairing-membership, union-membership,
;;;     intersection-membership, empty-set-is-set, empty-set-has-no-members,
;;;     class-extensionality, subset-def
;;;   structure-library/views.scm (60, definitional): RING-ADDITIVE-AG (the
;;;     functoid unfold), ring-additive-ag-is-abelian-group
;;;   structure-library/cardinality.scm (82, primitive): card-empty
;;;   number-systems (primitive): nn-zero-in
;;;   theorem-library/equality-basics (146): eq-sym
;;;   theorem-library/ag-view-read-offs (158): ras-carr, ras-op
;;;   theorem-library/fun-apply-type-proof (160): fun-apply-type-c
;;;   theorem-library/subset-lemmas (190): subset-mem-fwd, subclass-of-set-is-set
;;;   theorem-library/subtype-laws (199): abelian-group-is-group, group-left-id
;;;   theorem-library/finsum-insert (233): finsum-empty
;;;   theorem-library/rake-finsum-laws (249): finsum-type-ptwise
;;;   theorem-library/rake-finsum-union (NEW, batch 5c-M): finsum-insert-ptwise,
;;;     finsum-union-disjoint
;;;
;;; LOAD WINDOW: lo = one past theorem-library/rake-finsum-union (the latest
;;; citation; every other citation is at or below 249).  Nothing forces hi -- but
;;; theorem-library/rake-sum-set-scalar, the only citer of the four laws, sits at
;;; 212 today and MUST BE MOVED below this file.
;;;
;;; WHAT THE INTEGRATOR MUST DO, beyond wiring this file:
;;;
;;;   1. structure-library/sequences.scm: delete the four SUM-SET axioms
;;;      (:207-250) and drop their four names from the `warrant!' sweep at
;;;      :305-314 (the PROD-SET four stay).  Put the DEFINING FORM at the end of
;;;      structure-library/finsum.scm, NOT where the axioms were: sequences.scm
;;;      loads at 92 and finsum.scm at 93, so at the axioms' site the head
;;;      FINSUM is not yet a registered constant.  Leave SUM-SET in
;;;      *wff-term-form-heads* (wff.scm:488) -- it is what keeps the head out of
;;;      wff position, and test-suite.scm:2617 checks exactly that.
;;;   2. theorem-library/rake-sum-set-scalar.scm must MOVE below this file, and
;;;      takes five small edits; both of its theorems then bill `modulo 0'
;;;      instead of `trust: none'.  The edits are verified (see the report).
;;;
;;; PROD-SET is the same job and needs NO view at all: a comm monoid's slots are
;;; (CARR OPR IDEN) and FINSUM reads only those, so the defining form is
;;; (def-functoid 'PROD-SET '(cm S f) '(FINSUM cm f S)) -- see the report.

;;; ---------------------------------------------------------------------
;;; Helpers (all file-local, prefix `r7s-')
;;; ---------------------------------------------------------------------

(define (r7s-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; r7s: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "r7s: proof not complete" name))))

(define (r7s-sing v) (list 'PAIR v v))

;; `fact' of a membership IFF lands BOTH the instance and the universal; name
;; the instance by its left-hand side (rake-finsum-union's r7m-iff-for).
;; (iff-for retired 2026-09-25: the kit's `iff-for')

(define (r7s-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))

;; (IN v SET) for a singleton {v}, and (IN v {v}).
(define (r7s-pair! xv)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
  (fact 'pairing xv xv))

(define (r7s-ensure! form thunk)
  (if (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms))
      form
      (begin (have! form thunk) form)))

;; the pointwise typing universal, spelled with the binder `z_'
(define (r7s-ptw ca fsym dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom)
                          (list 'IN (list fsym 'z_) ca))))

;; forall z in DOM. NOT (z in SV)
(define (r7s-disj sv dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom) (list 'NOT (list 'IN 'z_ sv)))))

;;; ===================================================================
;;; (1) sum-set-empty -- STATEMENT UNCHANGED, and unguarded.
;;;
;;;     forall r, f.  SUM-SET(r, {}, f) == ZERO(r)
;;;
;;; Unfold SUM-SET, then finsum-empty (itself unguarded) leaves
;;; IDEN(RING-ADDITIVE-AG r) == ZERO r, and the view's own functoid unfold plus
;;; one NTH reduction closes it.  `ras-id' is NOT used: it is guarded on
;;; IS-RING and stated with `=', and neither is needed for a quasi-equality.
;;; ===================================================================

(sp (make-wff '(FORALL r (FORALL f (== (SUM-SET r EMPTY-SET f) (ZERO r))))))
(dk-peel!)
(mac 'SUM-SET)
(mac 'finsum-empty)
(slot 'IDEN)
(mac 'RING-ADDITIVE-AG)
(nth-r)
(qrfl)
(r7s-check! 'sum-set-empty)
(qed 'sum-set-empty)
(topic! 'sum-set-empty 'algebra)

;;; ===================================================================
;;; (2) finsum-singleton-ptwise -- a one-point FINSUM, with the summand typed
;;;     POINTWISE.
;;;
;;;     ag abelian, x a set, f(x) in CARR(ag)
;;;        =>  FINSUM(ag, f, {x}) = f(x)
;;;
;;; The proven `finsum-singleton' asks for (IN f (FUN {x} (CARR ag))), which no
;;; caller with f typed on a larger set can supply -- the tree has no
;;; RESTRICTION.  This is the same move finsum-insert-ptwise makes one storey
;;; up, and it is proved FROM it: {x} is EMPTY-SET u {x}, the empty sum is
;;; IDEN(ag) and the unit law finishes.
;;; ===================================================================

(define r7s-fsp-stmt
  '(FORALL ag (IMPLIES (IS-ABELIAN-GROUP ag)
     (FORALL x_ (IMPLIES (IN x_ SET)
       (FORALL f_ (IMPLIES (IN (f_ x_) (CARR ag))
         (= (FINSUM ag f_ (PAIR x_ x_)) (f_ x_)))))))))

(sp (make-wff r7s-fsp-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (agv (cadr lhs)) (fv (caddr lhs)) (pr (cadddr lhs))
       (xv  (cadr pr))
       (un  (list 'UNION 'EMPTY-SET pr))
       (ca  (list 'CARR agv)))
  (r7s-pair! xv)
  (fact 'empty-set-is-set)
  (fact 'empty-set-has-no-members xv)         ; (NOT (IN x EMPTY-SET))
  (fact 'card-empty)
  (fact 'nn-zero-in)
  (have! '(IN (CARD EMPTY-SET) NN)
         (lambda () (subst '(= (CARD EMPTY-SET) 0)) (ass)))
  ;; {} u {x} = {x}, and its converse orientation for the rewrites below
  (have! (list '= un pr)
         (lambda ()
           (bc* 'class-extensionality)
           (let ((v (dk-di-var! (lambda (gg) (cadr (cadr gg))))))
             (let ((nem (dk-fact! 'empty-set-has-no-members v)))
               (mac 'union-membership)
               (dk-only! nem)
               (prop)))))
  (fact 'eq-sym un pr)
  ;; the pointwise typing the insert law wants, over the union
  (have! (r7s-ptw ca fv un)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (have! (list 'IN zv pr)
                    (lambda () (subst (list '= pr un)) (ass)))
             (let ((pm (dk-fact! 'pairing-membership xv xv zv)))
               (have! (list '= zv xv)
                      (lambda () (dk-only! pm (list 'IN zv pr)) (prop)))
               (subst (list '= zv xv))
               (ass)))))
  (dk-fact! 'finsum-insert-ptwise agv 'EMPTY-SET xv fv)
  (fact 'finsum-empty agv fv)
  (fact 'abelian-group-is-group agv)
  (fact 'group-left-id agv (list fv xv))
  (subst (list '= pr un))
  (subst (list '= (list 'FINSUM agv fv un)
               (list (list 'OPR agv) (list 'FINSUM agv fv 'EMPTY-SET) (list fv xv))))
  (subst (list '== (list 'FINSUM agv fv 'EMPTY-SET) (list 'IDEN agv)))
  (ass))
(r7s-check! 'finsum-singleton-ptwise)
(qed 'finsum-singleton-ptwise)
(topic! 'finsum-singleton-ptwise 'algebra)

;;; ===================================================================
;;; (3) sum-set-singleton-defined -- sum-set-singleton with the two guards its
;;;     terms need.
;;;
;;;     IS-RING r, x a set, f(x) in CARR(r)  =>  SUM-SET(r, {x}, f) = f(x)
;;;
;;; The axiom quantified x and f with no hypothesis whatsoever and concluded a
;;; strict `='; see the header for why that is underdetermined.
;;; ===================================================================

(define r7s-ssd-stmt
  '(FORALL r
     (IMPLIES (IS-RING r)
       (FORALL x (IMPLIES (IN x SET)
         (FORALL f (IMPLIES (IN (f x) (CARR r))
           (= (SUM-SET r (PAIR x x) f) (f x)))))))))

(sp (make-wff r7s-ssd-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))                          ; (SUM-SET r {x} f)
       (rv  (cadr lhs)) (pr (caddr lhs)) (fv (cadddr lhs))
       (xv  (cadr pr))
       (agv (list 'RING-ADDITIVE-AG rv))
       (ca  (list 'CARR agv)))
  (fact 'ras-carr rv)                          ; (= (CARR ag) (CARR r))
  (fact 'ring-additive-ag-is-abelian-group rv)
  (have! (list 'IN (list fv xv) ca)
         (lambda () (subst (list '= ca (list 'CARR rv))) (ass)))
  (mac 'SUM-SET)
  (dk-fact! 'finsum-singleton-ptwise agv xv fv)
  (ass))
(r7s-check! 'sum-set-singleton-defined)
(qed 'sum-set-singleton-defined)
(topic! 'sum-set-singleton-defined 'algebra)

;;; ===================================================================
;;; (4) sum-set-type-defined -- sum-set-type with the finiteness guard.
;;;
;;;     IS-RING r, X a set, S subset X, f in FUN(X, CARR r), CARD S in NN
;;;        =>  SUM-SET(r, S, f) in CARR r
;;;
;;; The guard is appended as one more conjunct of the axiom's own AND chain, so
;;; a citer's `have!' of the antecedent grows by one line and nothing else.
;;; ===================================================================

(define r7s-std-stmt
  '(FORALL r (FORALL X (FORALL S (FORALL f
      (IMPLIES (AND (IS-RING r)
               (AND (IN X SET)
               (AND (SUBSET S X)
               (AND (IN f (FUN X (CARR r)))
                    (IN (CARD S) NN)))))
               (IN (SUM-SET r S f) (CARR r))))))))

(sp (make-wff r7s-std-stmt))
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))
       (tm  (cadr g))                          ; (SUM-SET r S f)
       (rv  (cadr tm)) (sv (caddr tm)) (fv (cadddr tm))
       (bigv (caddr (dk-pick (dk-head? 'SUBSET) "the subset hypothesis")))
       (agv (list 'RING-ADDITIVE-AG rv))
       (ca  (list 'CARR agv)))
  (display ";; r7s std vars: ") (display (list rv sv fv bigv)) (newline)
  (fact 'ras-carr rv)
  (fact 'ring-additive-ag-is-abelian-group rv)
  (fact 'subclass-of-set-is-set sv bigv)       ; (IN S SET)
  (have! (r7s-ptw ca fv sv)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (subst (list '= ca (list 'CARR rv)))
             (fact 'subset-mem-fwd sv bigv zv)
             (fact 'fun-apply-type-c fv bigv (list 'CARR rv) zv)
             (ass))))
  (mac 'SUM-SET)
  (fact 'eq-sym ca (list 'CARR rv))
  (subst (list '= (list 'CARR rv) ca))
  (dk-fact! 'finsum-type-ptwise agv sv fv)
  (ass))
(r7s-check! 'sum-set-type-defined)
(qed 'sum-set-type-defined)
(topic! 'sum-set-type-defined 'algebra)

;;; ===================================================================
;;; (5) sum-set-disjoint-union-defined -- sum-set-disjoint-union with the
;;;     finiteness guard on BOTH halves.
;;;
;;;     IS-RING r; X a set; S1, S2 sets with S1 n S2 = {}; S1 u S2 subset X;
;;;     f in FUN(X, CARR r); CARD S1 in NN; CARD S2 in NN
;;;        =>  SUM-SET(r, S1 u S2, f) = ADD(r)(SUM-SET(r,S1,f), SUM-SET(r,S2,f))
;;;
;;; `finsum-union-disjoint' (rake-finsum-union.scm) states disjointness as the
;;; universal "every member of S2 is outside S1" and the summand typing
;;; POINTWISE; both are derived here from the axiom's own vocabulary, exactly as
;;; `finsum-union-disjoint-fun' does.
;;; ===================================================================

(define r7s-sdu-stmt
  '(FORALL r
     (IMPLIES (IS-RING r)
       (FORALL X (FORALL S1 (FORALL S2 (FORALL f
         (IMPLIES (AND (IN X SET)
                  (AND (IN S1 SET)
                  (AND (IN S2 SET)
                  (AND (= (INTERSECTION S1 S2) EMPTY-SET)
                  (AND (SUBSET (UNION S1 S2) X)
                  (AND (IN f (FUN X (CARR r)))
                  (AND (IN (CARD S1) NN)
                       (IN (CARD S2) NN))))))))
                  (= (SUM-SET r (UNION S1 S2) f)
                     ((ADD r) (SUM-SET r S1 f) (SUM-SET r S2 f)))))))))))

(sp (make-wff r7s-sdu-stmt))
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))
       (lhs (cadr g))                          ; (SUM-SET r (UNION S1 S2) f)
       (rv  (cadr lhs)) (un (caddr lhs)) (fv (cadddr lhs))
       (s1v (cadr un)) (s2v (caddr un))
       (bigv (caddr (dk-pick (dk-head? 'SUBSET) "the subset hypothesis")))
       (agv (list 'RING-ADDITIVE-AG rv))
       (ca  (list 'CARR agv)))
  (display ";; r7s sdu vars: ") (display (list rv s1v s2v fv bigv)) (newline)
  (fact 'ras-carr rv)
  (fact 'ras-op rv)                            ; (= (OPR ag) (ADD r))
  (fact 'ring-additive-ag-is-abelian-group rv)
  ;; the summand, typed pointwise on the union
  (have! (r7s-ptw ca fv un)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (subst (list '= ca (list 'CARR rv)))
             (fact 'subset-mem-fwd un bigv zv)
             (fact 'fun-apply-type-c fv bigv (list 'CARR rv) zv)
             (ass))))
  ;; disjointness as a universal, from the intersection equation
  (have! (r7s-disj s1v s2v)
         (lambda ()
           (let* ((zv (dk-di-var!))
                  (im (r7s-mem-iff! (list 'IN zv (list 'INTERSECTION s1v s2v))
                                    'intersection-membership s1v s2v zv)))
             (di)                              ; assume (IN z S1)
             (have! (list 'IN zv (list 'INTERSECTION s1v s2v))
                    (lambda () (dk-only! im (list 'IN zv s1v) (list 'IN zv s2v)) (prop)))
             (fact 'eq-sym (list 'INTERSECTION s1v s2v) 'EMPTY-SET)
             (have! (list 'IN zv 'EMPTY-SET)
                    (lambda () (subst (list '= 'EMPTY-SET (list 'INTERSECTION s1v s2v))) (ass)))
             (ai (dk-fact! 'empty-set-has-no-members zv)))))
  (mac 'SUM-SET)
  (fact 'eq-sym (list 'OPR agv) (list 'ADD rv))
  (subst (list '= (list 'ADD rv) (list 'OPR agv)))
  (dk-fact! 'finsum-union-disjoint agv s1v s2v fv)
  (ass))
(r7s-check! 'sum-set-disjoint-union-defined)
(qed 'sum-set-disjoint-union-defined)
(topic! 'sum-set-disjoint-union-defined 'algebra)

(display ";; r7s: rake-sum-set-defined complete\n")
