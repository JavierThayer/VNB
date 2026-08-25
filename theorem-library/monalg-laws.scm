;;; monalg-laws.scm -- the monoid-algebra laws that go through without
;;; reindexing, PROVEN.
;;;
;;; structure-library/polynomial.scm seeds all seven ring laws of A[M] as
;;; supports with a Bourbaki citation.  This file discharges the first of them,
;;; `monalg-add-fun', and supplies two general bricks it needed on the way.  The
;;; other six are reported on at the foot of this file: what each one is missing
;;; and, where the gap is one lemma, what that lemma says.
;;;
;;; THE TWO BRICKS
;;;
;;; `monoid-carrier-is-set' -- CARR(m) is a set when m is a monoid.  Nothing in
;;; the tree derived this, and EVERY structure-level function-typing argument
;;; needs it: `lam-t' opens the sethood of the lambda's domain as a second leaf
;;; (CLAUDE.md's "lam-t opens TWO leaves"), and for a lambda over CARR(m) that
;;; leaf is exactly this.  The proof is three lines -- the declare-structure IFF
;;; has `(IN (CARR s) SET)' as a conjunct, so `mac-h' the unfold and split.
;;;
;;; `monalg-add-apply' -- the POINTWISE VALUE of the pointwise sum,
;;; ((f+g)(x) == f(x) + g(x)) for x in CARR(m).  Guarded, so it is a macete that
;;; `mac' declines on an untyped goal and `mac-h' applies to a hypothesis with
;;; the typing spawned as a side condition -- which is exactly how the support
;;; argument below uses it.  `==', not `=': `rfl' carries a definedness
;;; side-condition, and `(ADD a)(f x, g x)' is not syntactically defined, so the
;;; `=' form would owe a witness it does not need.  (Measured: with `=' and
;;; `rfl' the proof does not close.)

(define (mal-both! g1 b1 b2)                ; the two leaves an AND-goal `di' opens
  (let ((ls (dk-opened (lambda () (di)))))
    (dk-focus! (any-pred (lambda (n) (equal? (dk-goal-of n) g1)) ls)) (b1)
    (dk-focus! (any-pred (lambda (n) (not (equal? (dk-goal-of n) g1))) ls)) (b2)))

(define (mal-peel!)                         ; peel the whole FORALL/IMPLIES prefix
  (let loop ((k 0))                         ; -- never a fixed count of `di's
    (if (> k 12) (error "mal-peel!: runaway"))
    (if (memq (car (dk-goal)) '(forall implies))
        (begin (di) (loop (+ k 1))))))

;;; =====================================================================
;;; brick: a monoid's carrier is a set
;;; =====================================================================

(sp (make-wff '(FORALL m_ (IMPLIES (IS-MONOID m_) (IN (CARR m_) SET)))))
(di) (di)
(mac-h 'is-monoid '(IS-MONOID m_))
(dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
(ass)
(qed 'monoid-carrier-is-set)
(gloss! 'monoid-carrier-is-set
  "The carrier of a monoid is a set -- a conjunct of the IS-MONOID definition,
   surfaced as a citable theorem.  Needed wherever `lam-t' asks for the sethood
   of a lambda's domain.")
(topic! 'monoid-carrier-is-set 'plumbing)

;;; =====================================================================
;;; brick: the pointwise value of the pointwise sum
;;; =====================================================================

(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_ (FORALL x_
   (IMPLIES (IN x_ (CARR m_))
     (== ((MONALG-ADD a_ m_ f_ g_) x_) ((ADD a_) (f_ x_) (g_ x_)))))))))))
(di) (di) (mac 'MONALG-ADD) (lam-b) (qrfl)
(qed 'monalg-add-apply)
(gloss! 'monalg-add-apply
  "(f+g)(x) = f(x) + g(x) in A, for x in CARR(M): the defining value of the
   pointwise sum of two elements of the monoid algebra.")
(topic! 'monalg-add-apply 'algebra)

;;; =====================================================================
;;; monalg-add-fun -- the pointwise sum stays in FINSUPP
;;; =====================================================================
;;;
;;; Two obligations, from `finsupp-membership':
;;;   (i)  f+g is a function CARR(M) -> CARR(A)  -- `lam-t', then the pointwise
;;;        typing off `ring-add-closed';
;;;   (ii) its support is finite -- supp(f+g) is contained in
;;;        supp(f) u supp(g), and a subset of a finite set is finite.
;;;
;;; The inclusion is the only mathematics: if f(z) and g(z) are BOTH zero then
;;; so is f(z)+g(z), by ring-add-left-id at ZERO.  It is written as an
;;; excluded-middle split on `f(z) = ZERO(A)' rather than left to `prop', which
;;; declines here -- the context carries 19 distinct atoms against a cap of 12
;;; (*prop-atom-cap*) -- so both branches close by `oi-l'/`oi-r' and assumption.
;;;
;;; WAS: an asserted support in structure-library/polynomial.scm with a Bourbaki
;;; reference warrant (retired there, 2026-08-20; nothing cited it).
;;; BILL: modulo {ring-add-closed, card-subset-nn}.  Both are asserted
;;; `well-known' and neither shadows the other -- `ring-add-closed' is a SHAPE
;;; PROJECTION of the IS-RING definition and could be proven exactly as
;;; `monoid-carrier-is-set' is above (the op-signature conjunct plus
;;; fun-apply-type and the tupling convention); `card-subset-nn' is the genuine
;;; combinatorial leaf.

(define mal-sf '(SUPP a_ m_ f_))
(define mal-sg '(SUPP a_ m_ g_))
(define mal-s3 '(SUPP a_ m_ (MONALG-ADD a_ m_ f_ g_)))
(define mal-u (list 'UNION mal-sf mal-sg))

(sp (make-wff '(FORALL a_ (FORALL m_ (FORALL f_ (FORALL g_
   (IMPLIES (IS-RING a_) (IMPLIES (IS-MONOID m_)
   (IMPLIES (IN f_ (FINSUPP a_ m_)) (IMPLIES (IN g_ (FINSUPP a_ m_))
     (IN (MONALG-ADD a_ m_ f_ g_) (FINSUPP a_ m_))))))))))))
(mal-peel!)
(fact 'monoid-carrier-is-set 'm_)
(mac-h 'finsupp-membership '(IN f_ (FINSUPP a_ m_)))
(dk-split! (list 'AND '(IN f_ (FUN (CARR m_) (CARR a_))) (list 'IN (list 'CARD mal-sf) 'NN)))
(mac-h 'finsupp-membership '(IN g_ (FINSUPP a_ m_)))
(dk-split! (list 'AND '(IN g_ (FUN (CARR m_) (CARR a_))) (list 'IN (list 'CARD mal-sg) 'NN)))
(mac 'finsupp-membership)
(mal-both! '(in (monalg-add a_ m_ f_ g_) (fun (carr m_) (carr a_)))
  ;; ---- (i) f+g is a function -------------------------------------------
  (lambda ()
    (mac 'MONALG-ADD)
    (for-each
      (lambda (l)
        (dk-focus! l)
        (if (equal? (dk-goal-of l) '(in (carr m_) set))
            (ass)
            ;; lam-t's pointwise leaf binds a FRESH variable -- read it off the
            ;; landed typing, never off the lambda's printed binder name.
            (let ((xv (cadr (dk-landed-1 (lambda () (di))))))
              (fact 'fun-apply-type-c 'f_ '(CARR m_) '(CARR a_) xv)
              (fact 'fun-apply-type-c 'g_ '(CARR m_) '(CARR a_) xv)
              (fact 'ring-add-closed 'a_ (list 'f_ xv) (list 'g_ xv))
              (ass))))
      (dk-opened (lambda () (lam-t)))))
  ;; ---- (ii) the support is finite ---------------------------------------
  (lambda ()
    (have! (list 'IN mal-sf 'SET) (lambda () (fact 'supp-in-set 'a_ 'm_ 'f_) (ass)))
    (have! (list 'IN mal-sg 'SET) (lambda () (fact 'supp-in-set 'a_ 'm_ 'g_) (ass)))
    (have! (list 'IN mal-s3 'SET)
           (lambda () (fact 'supp-in-set 'a_ 'm_ '(MONALG-ADD a_ m_ f_ g_)) (ass)))
    (fact 'card-union-nn mal-sf mal-sg)
    ;; card-subset-nn and union-set-closure both take AND antecedents, which
    ;; `fact' will not split -- land each conjunction first.
    (have! (list 'AND (list 'IN mal-u 'SET) (list 'IN (list 'CARD mal-u) 'NN))
      (lambda ()
        (mal-both! (list 'in mal-u 'set)
          (lambda () (have! (list 'AND (list 'IN mal-sf 'SET) (list 'IN mal-sg 'SET))
                            (lambda () (mal-both! (list 'in mal-sf 'set)
                                                  (lambda () (ass)) (lambda () (ass)))))
                     (fact 'union-set-closure mal-sf mal-sg) (ass))
          (lambda () (ass)))))
    (have! (list 'AND (list 'IN mal-s3 'SET)
             (list 'FORALL 'z_ (list 'IMPLIES (list 'IN 'z_ mal-s3) (list 'IN 'z_ mal-u))))
      (lambda ()
        (mal-both! (list 'in mal-s3 'set)
          (lambda () (ass))
          (lambda ()
            (di)
            (mac-h 'supp-membership (list 'IN 'z_ mal-s3))
            (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
            ;; a GUARDED macete on a hypothesis: mac-h applies it and spawns the
            ;; typing (IN z_ (CARR m_)) as a side condition, which the context
            ;; already carries.
            (mac-h 'monalg-add-apply
                   (list 'NOT (list '= (list '(MONALG-ADD a_ m_ f_ g_) 'z_) '(ZERO a_))))
            (mac 'union-membership)
            (mac 'supp-membership)
            (use-em '(= (f_ z_) (ZERO a_))
              (lambda ()                       ; f(z) = 0, so g(z) cannot be
                (have! '(NOT (= (g_ z_) (ZERO a_)))
                  (lambda ()
                    (di)
                    (have! '(= ((ADD a_) (f_ z_) (g_ z_)) (ZERO a_))
                      (lambda ()
                        (subst '(= (f_ z_) (ZERO a_)))
                        (subst '(= (g_ z_) (ZERO a_)))
                        (fact 'ring-zero-in 'a_)
                        (fact 'ring-add-left-id 'a_ '(ZERO a_))
                        (ass)))
                    (ai '(NOT (= ((ADD a_) (f_ z_) (g_ z_)) (ZERO a_))))))
                (oi-r)
                (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (di)))))
              (lambda ()                       ; f(z) /= 0
                (oi-l)
                (for-each (lambda (n) (dk-focus! n) (ass))
                          (dk-opened (lambda () (di))))))))))
    (fact 'card-subset-nn mal-u mal-s3)
    (ass)))
(qed 'monalg-add-fun)
(gloss! 'monalg-add-fun
  "The pointwise sum of two finitely-supported functions is finitely supported:
   supp(f+g) is contained in supp(f) u supp(g).  The typing that makes ADD an
   operation on the carrier of the monoid algebra A[M].")
(topic! 'monalg-add-fun 'algebra)

;;; =====================================================================
;;; WHAT THE OTHER SIX NEED  (survey, 2026-08-20 -- no proof attempted)
;;; =====================================================================
;;;
;;; monalg-mul-fun -- BLOCKED, and by a set-theoretic fact, not by algebra.
;;;   supp(f*g) is contained in the product set supp(f).supp(g) = the IMAGE of
;;;   the finite set supp(f) x supp(g) under (OPR M).  To conclude that the
;;;   image is FINITE the tree needs "the image of a finite set is finite", and
;;;   it has only `card-image-injection' (structure-library/injection.scm:160),
;;;   which is |IMAGE(phi,S)| = |S| for an INJECTION.  (OPR M) is not injective.
;;;   The missing statement:
;;;       phi in FUN(S, C), S in SET, CARD(S) in NN  =>  CARD(IMAGE(phi,S)) in NN
;;;   It is the one lemma, it is worth having for its own sake, and it also
;;;   unblocks the finiteness half of monalg-mul-assoc.
;;;
;;; monalg-one-left -- reachable, with ONE wrinkle that has to be handled and is
;;;   easy to miss.  The convolution index set is
;;;   { (p,q) in supp(ONE) x supp(f) : p.q = x }, and the proof wants
;;;   supp(MONALG-ONE A M) = { IDEN(M) }, which is TRUE ONLY IF
;;;   ONE(A) /= ZERO(A).  In the trivial ring supp(ONE) is EMPTY and that
;;;   description is false -- the conclusion still holds (both sides are zero,
;;;   by finsum-empty), but by a different argument.  So the proof is a case
;;;   split on ONE(A) = ZERO(A), and `integral-domain-nontrivial' is NOT
;;;   available: A is only a ring here.  Given the split, the non-trivial branch
;;;   is `finsum-single-support' (structure-library/matrix.scm:495) at the index
;;;   (IDEN M, x), after showing the index set is the singleton -- which is set
;;;   extensionality over the SEP plus monoid-left-id/right-id.
;;;
;;; monalg-distrib-left -- reachable, and `finsum-embed'
;;;   (theorem-library/finsum-additive.scm:384) is the lemma that makes it so.
;;;   The three sums run over three DIFFERENT index sets -- filtered by
;;;   supp(g+h), supp(g), supp(h) -- so nothing pointwise applies until all
;;;   three are extended to the common set
;;;       { (p,q) in supp(f) x (supp(g) u supp(h)) : p.q = x }.
;;;   `finsum-embed' does exactly that (the summand vanishes at every added
;;;   index), and `finsum-add-ag' then adds the two extended sums pointwise.
;;;   No reindexing bijection is needed.  This is the most promising of the six.
;;;
;;; monalg-comm -- MOVES NOTHING even if proved.  Its conclusion is
;;;   IS-COMMUTATIVE-RING(MONALG A M), which by is-commutative-ring's definition
;;;   contains IS-RING(MONALG A M) -- i.e. `monalg-is-ring', the umbrella that
;;;   is the very thing still asserted.  The commutativity CONJUNCT alone is the
;;;   swap reindex (p,q) |-> (q,p), which `finsum-reindex-ag' covers once the
;;;   bijection between the two SEP index sets is constructed and typed.  Worth
;;;   doing only after the umbrella, or restated as the conjunct alone.
;;;
;;; monalg-mul-assoc -- see the analysis in the session report.  The single
;;;   missing lemma is a FIBERED / dependent-index Fubini, of which the existing
;;;   `finsum-fubini' is the constant-fiber special case:
;;;
;;;       ag abelian group; K a finite set; I a finite set; phi in FUN(K,I);
;;;       F in FUN(K, CARR ag)
;;;       =>  FINSUM(ag, F, K)
;;;           = FINSUM(ag, LAMBDA i. FINSUM(ag, F, { k in K : phi(k) = i }), I)
;;;
;;;   ("group the terms of a finite sum by the fibers of any map").  With it,
;;;   both ((f*g)*h)(x) and (f*(g*h))(x) collapse to the SAME single sum over
;;;   { (p,q,r) in supp f x supp g x supp h : p.q.r = x } -- the first by
;;;   phi(p,q,r) = (p.q, r), the second by phi(p,q,r) = (p, q.r) -- and the two
;;;   agree by the associativity of (OPR M).  `finsum-fubini' cannot do this:
;;;   it interchanges two sums over a CARTESIAN PRODUCT, and here the inner
;;;   index set { (p,q) : p.q = r } DEPENDS on the outer index.  The scalar
;;;   pull-in that precedes the flattening is `finsum-ring-distrib-right-gen'
;;;   (finsum-additive.scm:244), which the tree already has.
