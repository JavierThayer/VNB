;;; theorem-library/rake-prod-set-defined.scm -- PROD-SET DEFINED, and its four
;;; characterising laws PROVEN from the definition.  Rake batch 5c, assignment
;;; 5c-P (the user's decision of 2026-09-19).  Helper prefix `psd-'.
;;;
;;; The twin of theorem-library/rake-sum-set-defined.scm (5c-S), one storey
;;; lower: SUM-SET sums over a RING through the view RING-ADDITIVE-AG, PROD-SET
;;; multiplies over a COMMUTATIVE MONOID and needs NO view at all -- a comm
;;; monoid's slots are (CARR OPR IDEN) and that is exactly what FINSUM reads.
;;; So every `ras-carr' / `ras-op' rewrite of the SUM-SET file disappears here,
;;; and the abelian-group bricks are replaced by their comm-monoid twins.
;;;
;;; THE DEFINING FORM, which belongs in the library and which this file assumes
;;; has already been evaluated:
;;;
;;;     (def-functoid 'PROD-SET '(cm S f) '(FINSUM cm f S))
;;;
;;; Note the ARGUMENT ORDER: PROD-SET takes (monoid, index set, factor) and
;;; FINSUM takes (monoid, factor, index set), so the last two swap.
;;;
;;; WHAT THIS FILE PROVES, and what had to change in each statement:
;;;
;;;   prod-set-empty              UNCHANGED (statement copied literally).
;;;   finsum-cm-singleton-ptwise  NEW brick: the comm-monoid twin of
;;;                                 finsum-singleton-ptwise (rake-sum-set-
;;;                                 defined.scm) -- a one-point FINSUM with the
;;;                                 factor typed POINTWISE at the one point
;;;                                 instead of by a FUN membership over {x}.
;;;   prod-set-singleton-defined  prod-set-singleton plus (IN x SET) and the
;;;                                 POINTWISE typing (IN (f x) (CARR cm)).
;;;   prod-set-type-defined       prod-set-type plus (IN (CARD S) NN).
;;;   prod-set-disjoint-union-defined
;;;                               prod-set-disjoint-union plus (IN (CARD S1) NN)
;;;                                 and (IN (CARD S2) NN).
;;;
;;; WHY EACH GUARD IS NECESSARY -- none of the four is decoration.  The reasons
;;; are those of the SUM-SET file, verbatim, because the defect is in FINSUM's
;;; index set and not in the algebra:
;;;
;;;   * FINITENESS.  FINSUM(m,f,S) is SUM-AG(m, ENUM-FAM(...), CARD S), a fold
;;;     over the NN-segment [0, CARD S).  For an infinite S, CARD S is not in NN
;;;     and the fold is an uninterpreted term: every comm-monoid FINSUM law in
;;;     the tree (finsum-comm-monoid-type-ptwise, finsum-cm-union-disjoint,
;;;     finsum-cm-insert-ptwise, finsum-cm-congruence-q) carries (IN (CARD S)
;;;     NN), and nothing weaker is available.  The axioms prod-set-type and
;;;     prod-set-disjoint-union asserted their conclusions for an ARBITRARY
;;;     index set; that is exactly the over-reach this file cannot and should
;;;     not reproduce.  (prod-set-disjoint-union needs the guard on BOTH halves:
;;;     each side of the conclusion is a product in its own right.)
;;;   * (IN x SET) in the singleton law.  {x} is PAIR(x,x), and `pairing' makes
;;;     it a SET only for a set x; without that CARD({x}) is not known to be 1
;;;     and the enumeration behind FINSUM does not exist.
;;;   * the POINTWISE typing (IN (f x) (CARR cm)) in the singleton law.  The
;;;     axiom's conclusion is a strict `=', which asserts that both sides denote;
;;;     with f entirely unquantified-over, f(x) is `IOTA y. [x,y] in f'
;;;     (app-graph) and need not denote at all, so the axiom as written is
;;;     underdetermined.  The pointwise form is the WEAKEST hypothesis that
;;;     makes it true -- weaker than the FUN typing over {x} that
;;;     finsum-singleton asks for, and, unlike it, available at a citation site
;;;     where f is typed on a superset X and no restriction exists.
;;;
;;; prod-set-empty needs NO guard at all: its conclusion is a quasi-equality
;;; `==', finsum-empty is likewise unguarded, and with PROD-SET unfolding
;;; straight to FINSUM at cm there is not even a view read-off to pay for.  So
;;; the law holds for an arbitrary cm, comm monoid or not.
;;;
;;; NOTE on prod-set-disjoint-union: unlike its SUM-SET twin it types f on the
;;; UNION itself (no ambient X, no SUBSET), so the pointwise typing comes from
;;; one `fun-apply-type-c' and `subset-mem-fwd' is not needed.
;;;
;;; CITATIONS (0-based over the file names in load.scm, at the time of writing):
;;;   theory.scm (11, primitive): pairing, pairing-membership, union-membership,
;;;     intersection-membership, empty-set-is-set, empty-set-has-no-members,
;;;     class-extensionality
;;;   structure-library/cardinality.scm (82, primitive): card-empty
;;;   number-systems (primitive): nn-zero-in
;;;   theorem-library/equality-basics (146): eq-sym
;;;   theorem-library/fun-apply-type-proof (160): fun-apply-type-c
;;;   theorem-library/subset-lemmas (190): subset-mem-fwd, subclass-of-set-is-set
;;;   theorem-library/finsum-insert (236): finsum-empty
;;;   theorem-library/rake-finsum-core (254): comm-monoid-left-id
;;;   theorem-library/rake-finsum-cm-ptwise (255): finsum-comm-monoid-type-ptwise
;;;   theorem-library/rake-finsum-cm-union (270): finsum-cm-insert-ptwise,
;;;     finsum-cm-union-disjoint
;;;
;;; LOAD WINDOW: [271, end).  lo = one past theorem-library/rake-finsum-cm-union
;;; (270), the latest citation; every other citation is at or below 255.
;;; Nothing forces hi: NO file in the tree cites any of the four PROD-SET
;;; axioms (checked 2026-09-19; the only occurrences outside sequences.scm are
;;; the four `lookup-theorem' checks in test-suite.scm).
;;;
;;; WHAT THE INTEGRATOR MUST DO, beyond wiring this file:
;;;
;;;   1. Put the DEFINING FORM at the end of structure-library/finprod.scm
;;;      (position 94), beside FINPROD and PROD-RING, NOT where the axioms are:
;;;      sequences.scm loads at 92 and finsum.scm at 93, so at the axioms' site
;;;      the head FINSUM is not yet a registered constant.  (End of finsum.scm,
;;;      beside SUM-SET, works equally; finprod.scm is where a reader looks.)
;;;      Leave PROD-SET in *wff-term-form-heads* (wff.scm:488) -- it is what
;;;      keeps the head out of wff position, and test-suite.scm:2656-2660 checks
;;;      exactly that.
;;;   2. structure-library/sequences.scm: delete the four PROD-SET axioms
;;;      (:246-273) and the whole `warrant!' sweep at :276-292, whose name list
;;;      is now empty (the four sum-set names left it the evening before); the
;;;      section separator at :275 goes with it.
;;;   3. test-suite.scm:2644-2654: the four "<name> axiom installed" checks.
;;;      `prod-set-empty' keeps its name and its check passes unchanged; the
;;;      other three must be renamed to prod-set-singleton-defined,
;;;      prod-set-disjoint-union-defined, prod-set-type-defined, or the suite
;;;      stops with `lookup-theorem: unknown theorem'.

;;; ---------------------------------------------------------------------
;;; Helpers (all file-local, prefix `psd-')
;;; ---------------------------------------------------------------------

(define (psd-check! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; psd: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   ") (display (expression->string (dk-goal-of l))) (newline))
                  (proof-leaves))
        (error "psd: proof not complete" name))))

(define (psd-sing v) (list 'PAIR v v))

;; `fact' of a membership IFF lands both the instance and the universal; name
;; the instance by its left-hand side.
;; (iff-for retired 2026-09-25: the kit's `iff-for')

(define (psd-mem-iff! lhs . args)
  (apply fact args)
  (iff-for lhs))

;; (IN {v} SET) for a singleton, from (IN v SET) in context.
(define (psd-pair! xv)
  (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
  (fact 'pairing xv xv))

(define (psd-ensure! form thunk)
  (if (any-pred (lambda (f) (alpha-equiv? f form)) (dk-asms))
      form
      (begin (have! form thunk) form)))

;; the pointwise typing universal, spelled with the binder `z_'
(define (psd-ptw ca fsym dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom)
                          (list 'IN (list fsym 'z_) ca))))

;; forall z in DOM. NOT (z in SV)
(define (psd-disj sv dom)
  (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ dom) (list 'NOT (list 'IN 'z_ sv)))))

;;; ===================================================================
;;; (1) prod-set-empty -- STATEMENT UNCHANGED, and unguarded.
;;;
;;;     forall cm, f.  PROD-SET(cm, {}, f) == IDEN(cm)
;;;
;;; Unfold PROD-SET and finsum-empty (itself unguarded) is the whole proof.
;;; ===================================================================

(sp (make-wff '(FORALL cm (FORALL f (== (PROD-SET cm EMPTY-SET f) (IDEN cm))))))
(dk-peel!)
(mac 'PROD-SET)
(mac 'finsum-empty)
(qrfl)
(psd-check! 'prod-set-empty)
(qed 'prod-set-empty)
(topic! 'prod-set-empty 'algebra)

;;; ===================================================================
;;; (2) finsum-cm-singleton-ptwise -- a one-point FINSUM in a COMMUTATIVE
;;;     MONOID, with the factor typed POINTWISE.
;;;
;;;     cm a comm monoid, x a set, f(x) in CARR(cm)
;;;        =>  FINSUM(cm, f, {x}) = f(x)
;;;
;;; The comm-monoid twin of finsum-singleton-ptwise, and the same proof:
;;; {x} is EMPTY-SET u {x}, finsum-cm-insert-ptwise peels the point off, the
;;; empty product is IDEN(cm) and comm-monoid-left-id finishes.
;;; ===================================================================

(define psd-fsp-stmt
  '(FORALL m (IMPLIES (IS-COMM-MONOID m)
     (FORALL x_ (IMPLIES (IN x_ SET)
       (FORALL f_ (IMPLIES (IN (f_ x_) (CARR m))
         (= (FINSUM m f_ (PAIR x_ x_)) (f_ x_)))))))))

(sp (make-wff psd-fsp-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))
       (mv  (cadr lhs)) (fv (caddr lhs)) (pr (cadddr lhs))
       (xv  (cadr pr))
       (un  (list 'UNION 'EMPTY-SET pr))
       (ca  (list 'CARR mv)))
  (display ";; psd fsp vars: ") (display (list mv fv xv)) (newline)
  (psd-pair! xv)
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
  (have! (psd-ptw ca fv un)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (have! (list 'IN zv pr)
                    (lambda () (subst (list '= pr un)) (ass)))
             (let ((pm (dk-fact! 'pairing-membership xv xv zv)))
               (have! (list '= zv xv)
                      (lambda () (dk-only! pm (list 'IN zv pr)) (prop)))
               (subst (list '= zv xv))
               (ass)))))
  (dk-fact! 'finsum-cm-insert-ptwise mv 'EMPTY-SET xv fv)
  (fact 'finsum-empty mv fv)
  (fact 'comm-monoid-left-id mv (list fv xv))
  (subst (list '= pr un))
  (subst (list '= (list 'FINSUM mv fv un)
               (list (list 'OPR mv) (list 'FINSUM mv fv 'EMPTY-SET) (list fv xv))))
  (subst (list '== (list 'FINSUM mv fv 'EMPTY-SET) (list 'IDEN mv)))
  (ass))
(psd-check! 'finsum-cm-singleton-ptwise)
(qed 'finsum-cm-singleton-ptwise)
(topic! 'finsum-cm-singleton-ptwise 'algebra)

;;; ===================================================================
;;; (3) prod-set-singleton-defined -- prod-set-singleton with the two guards
;;;     its terms need.
;;;
;;;     IS-COMM-MONOID cm, x a set, f(x) in CARR(cm)
;;;        =>  PROD-SET(cm, {x}, f) = f(x)
;;;
;;; The axiom quantified x and f with no hypothesis whatsoever and concluded a
;;; strict `='; see the header for why that is underdetermined.
;;; ===================================================================

(define psd-psd-stmt
  '(FORALL cm
     (IMPLIES (IS-COMM-MONOID cm)
       (FORALL x (IMPLIES (IN x SET)
         (FORALL f (IMPLIES (IN (f x) (CARR cm))
           (= (PROD-SET cm (PAIR x x) f) (f x)))))))))

(sp (make-wff psd-psd-stmt))
(dk-peel!)
(let* ((g   (dk-goal))
       (lhs (cadr g))                          ; (PROD-SET cm {x} f)
       (cv  (cadr lhs)) (pr (caddr lhs)) (fv (cadddr lhs))
       (xv  (cadr pr)))
  (display ";; psd sing vars: ") (display (list cv xv fv)) (newline)
  (mac 'PROD-SET)
  (dk-fact! 'finsum-cm-singleton-ptwise cv xv fv)
  (ass))
(psd-check! 'prod-set-singleton-defined)
(qed 'prod-set-singleton-defined)
(topic! 'prod-set-singleton-defined 'algebra)

;;; ===================================================================
;;; (4) prod-set-type-defined -- prod-set-type with the finiteness guard.
;;;
;;;     IS-COMM-MONOID cm, X a set, S subset X, f in FUN(X, CARR cm),
;;;     CARD S in NN   =>   PROD-SET(cm, S, f) in CARR cm
;;;
;;; The guard is appended as one more conjunct of the axiom's own AND chain, so
;;; a citer's `have!' of the antecedent grows by one line and nothing else.
;;; ===================================================================

(define psd-ptd-stmt
  '(FORALL cm (FORALL X (FORALL S (FORALL f
      (IMPLIES (AND (IS-COMM-MONOID cm)
               (AND (IN X SET)
               (AND (SUBSET S X)
               (AND (IN f (FUN X (CARR cm)))
                    (IN (CARD S) NN)))))
               (IN (PROD-SET cm S f) (CARR cm))))))))

(sp (make-wff psd-ptd-stmt))
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))
       (tm  (cadr g))                          ; (PROD-SET cm S f)
       (cv  (cadr tm)) (sv (caddr tm)) (fv (cadddr tm))
       (bigv (caddr (dk-pick (dk-head? 'SUBSET) "the subset hypothesis")))
       (ca  (list 'CARR cv)))
  (display ";; psd type vars: ") (display (list cv sv fv bigv)) (newline)
  (fact 'subclass-of-set-is-set sv bigv)       ; (IN S SET)
  (have! (psd-ptw ca fv sv)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (fact 'subset-mem-fwd sv bigv zv)
             (fact 'fun-apply-type-c fv bigv ca zv)
             (ass))))
  (mac 'PROD-SET)
  (dk-fact! 'finsum-comm-monoid-type-ptwise cv sv fv)
  (ass))
(psd-check! 'prod-set-type-defined)
(qed 'prod-set-type-defined)
(topic! 'prod-set-type-defined 'algebra)

;;; ===================================================================
;;; (5) prod-set-disjoint-union-defined -- prod-set-disjoint-union with the
;;;     finiteness guard on BOTH halves.
;;;
;;;     IS-COMM-MONOID cm; S1, S2 sets with S1 n S2 = {};
;;;     f in FUN(S1 u S2, CARR cm); CARD S1 in NN; CARD S2 in NN
;;;        =>  PROD-SET(cm, S1 u S2, f)
;;;              = (OPR cm)(PROD-SET(cm,S1,f), PROD-SET(cm,S2,f))
;;;
;;; `finsum-cm-union-disjoint' (rake-finsum-cm-union.scm) states disjointness
;;; as the universal "every member of S2 is outside S1" and the factor typing
;;; POINTWISE; both are derived here from the axiom's own vocabulary.
;;; ===================================================================

(define psd-pdu-stmt
  '(FORALL cm
     (IMPLIES (IS-COMM-MONOID cm)
       (FORALL S1 (FORALL S2 (FORALL f
         (IMPLIES (AND (IN S1 SET)
                  (AND (IN S2 SET)
                  (AND (= (INTERSECTION S1 S2) EMPTY-SET)
                  (AND (IN f (FUN (UNION S1 S2) (CARR cm)))
                  (AND (IN (CARD S1) NN)
                       (IN (CARD S2) NN))))))
                  (= (PROD-SET cm (UNION S1 S2) f)
                     ((OPR cm) (PROD-SET cm S1 f) (PROD-SET cm S2 f))))))))))

(sp (make-wff psd-pdu-stmt))
(let ((landed (dk-peel!)))
  (dk-split-all! landed))
(let* ((g   (dk-goal))
       (lhs (cadr g))                          ; (PROD-SET cm (UNION S1 S2) f)
       (cv  (cadr lhs)) (un (caddr lhs)) (fv (cadddr lhs))
       (s1v (cadr un)) (s2v (caddr un))
       (ca  (list 'CARR cv)))
  (display ";; psd pdu vars: ") (display (list cv s1v s2v fv)) (newline)
  ;; the factor, typed pointwise on the union
  (have! (psd-ptw ca fv un)
         (lambda ()
           (let ((zv (dk-di-var!)))
             (fact 'fun-apply-type-c fv un ca zv)
             (ass))))
  ;; disjointness as a universal, from the intersection equation
  (have! (psd-disj s1v s2v)
         (lambda ()
           (let* ((zv (dk-di-var!))
                  (im (psd-mem-iff! (list 'IN zv (list 'INTERSECTION s1v s2v))
                                    'intersection-membership s1v s2v zv)))
             (di)                              ; assume (IN z S1)
             (have! (list 'IN zv (list 'INTERSECTION s1v s2v))
                    (lambda () (dk-only! im (list 'IN zv s1v) (list 'IN zv s2v)) (prop)))
             (fact 'eq-sym (list 'INTERSECTION s1v s2v) 'EMPTY-SET)
             (have! (list 'IN zv 'EMPTY-SET)
                    (lambda () (subst (list '= 'EMPTY-SET (list 'INTERSECTION s1v s2v))) (ass)))
             (ai (dk-fact! 'empty-set-has-no-members zv)))))
  (mac 'PROD-SET)
  (dk-fact! 'finsum-cm-union-disjoint cv s1v s2v fv)
  (ass))
(psd-check! 'prod-set-disjoint-union-defined)
(qed 'prod-set-disjoint-union-defined)
(topic! 'prod-set-disjoint-union-defined 'algebra)

(display ";; psd: rake-prod-set-defined complete\n")
