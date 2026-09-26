;;; poly-degree-laws.scm -- DEG / LEADCOEF / MONOMIAL, PROVEN.
;;;
;;; The companion of structure-library/poly-degree.scm, which carries the
;;; definitions and the argument for the convention (DEG = the LARGEST exponent
;;; with a nonzero coefficient, 0 on the zero polynomial).  Read that header
;;; first; this one is about the proofs.
;;;
;;; NOTHING HERE IS ASSERTED.  All fifteen statements reach `qed', and six of
;;; them (deg-bound-apply, deg-unfold, leadcoef-unfold, monomial-at,
;;; monomial-off, monomial-support) bill `modulo 0'.  The debt the rest carry is
;;; entirely INHERITED and entirely of one kind:
;;;
;;;   nn-finite-subset-bounded   (subsequence-principle.scm) -- via
;;;       poly-tail-zero-fwd; the fact that a polynomial's support is bounded
;;;       at all, and so the existence half of every degree here.
;;;   the NN order supports of structure-library/order-lemmas -- nn-le-succ,
;;;       nn-le-imp-neq-succ, nn-le-succ-cases, nn-one-le-succ, nn-pos-is-succ,
;;;       nn-not-le-succ-le, co-le-trans, co-le-lt-trans -- the discreteness and
;;;       transitivity of the natural order.
;;;   card-subset-nn, ring-add-closed, binplus-in-fun-nn -- via
;;;       monalg-add-fun and poly-tail-zero-bwd.
;;;
;;; Every one is `well-known', so every bill here reads [trust: well-known].
;;; Nothing in this file adds a leaf of its own.  The observation worth keeping:
;;; the polynomial degree layer costs NO new mathematics, only the NN order
;;; facts the tree has been asserting since the Smith normal form work.
;;;
;;; ==================================================================
;;; THE MECHANISM: the definite description and its two obligations
;;; ==================================================================
;;;
;;; DEG is an IOTA, so every claim about it starts by `mac DEG' -- putting the
;;; description into the goal -- and then `iota-d', which opens exactly two
;;; leaves: the existence-and-uniqueness of the described object, and the
;;; original goal with the defining property assumed.  The second is `ass'.
;;; The first is where all the work is, and it is the pattern the user asked
;;; for:
;;;
;;;   EXISTENCE   `minimize!' over the guard "n in NN and n bounds the support
;;;               of p", with n itself as the measure.  minimize! then owes its
;;;               two standing obligations and nothing else: the measure lands
;;;               in NN (here it IS the guard's first conjunct, so `prop'), and
;;;               the guard is satisfiable -- which is poly-tail-zero-fwd, the
;;;               eventually-zero reading of membership in POLY.  Landing that
;;;               existential in the shape minimize! would have asked for makes
;;;               minimize! skip the cut entirely and return #f for it.
;;;   UNIQUENESS  two minimal elements bound each other, and nn-le-antisym
;;;               (theorem-library/nn-order-proof.scm, proven) closes it.
;;;
;;; So DEG's well-definedness is a `minimize!' obligation discharge, not an
;;; axiom, and the file asserts no "the degree exists" support.
;;;
;;; ONE STEP OF ARITHMETIC BRIDGING is needed to get from poly-tail-zero-fwd's
;;; hypothesis to DEG-BOUND's: the former says p(k) = 0 for n <= k, the latter
;;; for n < k, and the second is weaker.  `mac-h <' unfolds `<' into
;;; `<= and /=' in the assumption and the `<=' half is what the tail wants.
;;;
;;; ==================================================================
;;; `leadcoef-nonzero' COMES IN TWO FORMS, and why
;;; ==================================================================
;;;
;;; The mathematician's statement is "p /= 0 implies LEADCOEF(p) /= 0".  The
;;; minimality argument, however, consumes a POINTWISE hypothesis -- "p has SOME
;;; nonzero coefficient",
;;;
;;;     FORSOME k in NN.  p(k) /= ZERO(A)
;;;
;;; -- because that is what it walks up to the degree.  Both are here.
;;; `leadcoef-nonzero-ptwise' is the argument; `leadcoef-nonzero' is the
;;; statement, and is the one to cite.
;;;
;;; UNTIL 2026-08-21 ONLY THE POINTWISE FORM EXISTED, and this header said the
;;; equivalence between the two "is FUNCTION EXTENSIONALITY composed with the
;;; pointwise value of MONALG-ZERO, and neither of those is in the tree in
;;; citable form".  Half of that was wrong: `fun-domain-extensionality'
;;; (theory.scm) has been in the tree, and PRIMITIVE, since 2026-07-28.  The
;;; other half was right, and it was one `lam-b'.  Both live in
;;; theorem-library/poly-zero.scm now, together with the bridge
;;;
;;;     p in CARR(POLY A) =>
;;;         ( p = ZERO(POLY A)  <=>  forall k in NN. p(k) = ZERO(A) )
;;;
;;; which is `poly-zero-iff', bills `modulo 0', and is what carries the
;;; hypothesis across.  See the section below `leadcoef-nonzero-ptwise'.
;;;
;;; The proof itself is the standard minimality argument and it needs the
;;; discreteness of NN in three places:
;;;
;;;   * the support member k0 satisfies k0 <= DEG (nn-not-lt-le, from
;;;     DEG-BOUND at k0);
;;;   * assuming p(DEG) = 0 makes k0 /= DEG, hence k0 < DEG, hence 1 <= DEG
;;;     (nn-lt-succ-le + nn-one-le-succ + co-le-trans), so DEG is a SUCCESSOR
;;;     (nn-pos-is-succ).  This is what removes the DEG = 0 case, which is the
;;;     only case where "take one less" is not available;
;;;   * writing DEG = succ e, e is then also a bound (every k > e is >= DEG, so
;;;     either k = DEG, where the coefficient is zero by assumption, or
;;;     k > DEG, where it is zero by DEG-BOUND), and minimality gives
;;;     DEG <= e, i.e. succ e <= e -- absurd by nn-succ-not-le, proved just
;;;     below.
;;;
;;; ==================================================================
;;; ADDITION: no NN `max', and none is invented
;;; ==================================================================
;;;
;;; `deg(f+g) <= max(deg f, deg g)' cannot be stated: the tree has no NN
;;; maximum (ineq-supply.scm's `*ineq-supply-wanted*' records the same gap for
;;; the real min/max).  It is stated instead in the equivalent BOUND form
;;;
;;;     forall n in NN.  deg f <= n  and  deg g <= n  =>  deg (f+g) <= n
;;;
;;; which is what a max-free ordered set can say and is exactly as strong: the
;;; max form follows by instantiating at n = max(deg f, deg g), and conversely
;;; the bound form follows from the max form by transitivity.  Every consumer
;;; the tree could have wants the bound form anyway, since it is the form that
;;; composes.  See the foot of the file for what adding a NN max would take.
;;;
;;; Needs: structure-library/poly-degree (the definitions), poly-tail-zero
;;; (poly-tail-zero-fwd), poly-membership (poly-membership), minimize +
;;; nn-least-element (minimize!), nn-order-proof (nn-le-antisym),
;;; finite-surgery (nn-not-lt-le, nn-lt-succ-le), order-lemmas (nn-le-succ,
;;; nn-one-le-succ, nn-pos-is-succ, nn-le-imp-neq-succ, nn-le-refl,
;;; co-le-trans), equality-basics (neq-sym), monalg-laws (monalg-add-apply),
;;; poly-zero (poly-zero-iff), push-not (push-not-h).
;;;
;;; Driver helpers are `pd-' prefixed throughout: a top-level define named like
;;; a tactic silently rebinds it (CLAUDE.md, "Case folding").

;;; ---------------------------------------------------------------------
;;; Shapes, built once.
;;; ---------------------------------------------------------------------

(define (pd-bound a p n) (list 'DEG-BOUND a p n))

;; The minimality clause of the definition, with t in the minimised position.
(define (pd-minclause a p t)
  (list 'FORALL 'j_ (list 'IMPLIES '(IN j_ NN)
     (list 'IMPLIES (pd-bound a p 'j_) (list '<= t 'j_)))))

;; The whole described property, at t.
(define (pd-prop a p t)
  (list 'AND (list 'IN t 'NN)
    (list 'AND (pd-bound a p t) (pd-minclause a p t))))

;; DEG's own description, at the binders a_ / p_.
(define pd-iota
  (list 'IOTA 'n_ (pd-prop 'a_ 'p_ 'n_)))

;; minimize!'s guard and the existential it would otherwise cut.
(define pd-guard (list 'AND '(IN n_ NN) (pd-bound 'a_ 'p_ 'n_)))
(define pd-ne    (list 'FORSOME 'n_ pd-guard))

;; Focus each leaf a branching tactic opened, by a PREDICATE on its goal --
;; never by the order dk-opened happens to return.  Errors on a miss.
(define (pd-branch! opened . clauses)
  (for-each
   (lambda (c)
     (let ((n (any-pred (lambda (s) ((car c) (dk-goal-of s))) opened)))
       (if (not n) (error "pd-branch!: no opened leaf matches"))
       (dk-focus! n)
       ((cdr c))))
   clauses))

(define (pd-head h) (lambda (g) (and (pair? g) (eq? (car g) h))))

;; Peel the whole FORALL/IMPLIES prefix.  ONE `di' does NOT do it: it takes a
;; GUARDED universal whole but an UNGUARDED one only down to the quantifier,
;; leaving the implication for the next call (CLAUDE.md).  Counting `di's is
;; therefore not a way to reach a chosen goal; loop until the head changes, and
;; guard on progress so a no-op cannot spin.

;; Prove a strict inequality whose two halves (`<=' and `/=') are already in
;; context.  NOT `(mac '<) (prop)': `prop' is capped at 12 distinct atoms
;; (*prop-atom-cap*) and the contexts below carry 14, so it declines with a
;; cap message rather than a countermodel.  Splitting the unfolded conjunction
;; by hand needs no search at all.
(define (pd-lt!)
  (mac '<)
  (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (di)))))

(define (pd-peel!)
  (let lp ((n 0))
    (let ((g (dk-goal)))
      (cond ((> n 12) (error "pd-peel!: no progress" g))
            ((memq (car g) '(FORALL IMPLIES)) (di)
             (if (equal? g (dk-goal)) (error "pd-peel!: di did not fire" g))
             (lp (+ n 1)))
            (else 'done)))))

;;; =====================================================================
;;; deg-well-defined -- the degree exists, is a bound, and is the least one
;;; =====================================================================
;;;
;;; The three conjuncts are proved TOGETHER rather than separately, and they
;;; have to be: `di' on an AND goal splits it into two leaves, and each leaf
;;; would then owe its own copy of the existence-and-uniqueness obligation.
;;; One `di' peels the whole FORALL/IMPLIES prefix and stops at the AND -- so
;;; exactly one, never two.

(sp (make-wff
  (list 'FORALL 'a_ (list 'FORALL 'p_
    (list 'IMPLIES '(IN p_ (CARR (POLY a_)))
      (pd-prop 'a_ 'p_ '(DEG a_ p_)))))))
(di)
(mac 'DEG)

(define pd-iota-leaves (dk-opened (lambda () (iota-d pd-iota))))

;; (2) the goal, with the defining property in context: it IS the goal.
(dk-focus! (any-pred (lambda (s) ((pd-head 'and) (dk-goal-of s))) pd-iota-leaves))
(ass)

;; (1) existence and uniqueness.
(dk-focus! (any-pred (lambda (s) ((pd-head 'forsome) (dk-goal-of s))) pd-iota-leaves))

;; -- some index bounds the tail of p (poly-tail-zero-fwd), and it is a
;;    DEG-BOUND, `<' being weaker than `<='.
(define pd-tail-parts
  (dk-split! (any-pred (dk-head? 'AND)
               (dk-landed (lambda () (ai (dk-fact! 'poly-tail-zero-fwd 'a_ 'p_)))))))
(define pd-w   (cadr (any-pred (dk-head? 'IN) pd-tail-parts)))
(define pd-uni (any-pred (dk-head? 'FORALL) pd-tail-parts))

(have! (pd-bound 'a_ 'p_ pd-w)
  (lambda ()
    (mac 'DEG-BOUND) (di) (di)
    (mac-h '< (list '< pd-w 'k_))
    (dk-split! (list 'AND (list '<= pd-w 'k_) (list 'NOT (list '= pd-w 'k_))))
    (dk-deepest (lambda () (inst+ pd-uni 'k_)))
    (ass)))

;; -- minimize!'s NONEMPTY obligation, landed in the shape it asks for, so it
;;    is never cut (minimize! returns #f for it).
(have! pd-ne (lambda () (ew pd-w) (prop)))

(define pd-r    (minimize! '(n_) pd-guard 'n_))
(define pd-d    (car (car pd-r)))
(define pd-exun (proof-state-focus *ps*))

;; -- TYPE: the measure is a natural number.  It is the guard's first conjunct.
(dk-focus! (or (cadr pd-r) (error "deg-well-defined: minimize! opened no TYPE goal")))
(di) (di) (prop)

;; -- the chosen bound witnesses the description.
(dk-focus! pd-exun)
(define pd-minim
  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                 (dk-contains? f (list '<= pd-d (cadr f)))))
                (dk-asms))
      (error "deg-well-defined: minimize!'s minimality assumption not found")))
(dk-split! (list 'AND (list 'IN pd-d 'NN) (pd-bound 'a_ 'p_ pd-d)))
(ew pd-d)

(pd-branch! (dk-opened (lambda () (di)))
  ;; (a) the witness has the property
  (cons (pd-head 'and)
    (lambda ()
      (pd-branch! (dk-opened (lambda () (di)))
        (cons (pd-head 'in) ass)
        (cons (pd-head 'and)
          (lambda ()
            (pd-branch! (dk-opened (lambda () (di)))
              (cons (pd-head 'deg-bound) ass)
              (cons (pd-head 'forall)
                (lambda ()
                  (di) (di)
                  (have! (list 'AND '(IN j_ NN) (pd-bound 'a_ 'p_ 'j_)))
                  (dk-deepest (lambda () (inst+ pd-minim 'j_)))
                  (ass)))))))))
  ;; (b) uniqueness: two least bounds bound each other.
  (cons (pd-head 'forall)
    (lambda ()
      (di)
      (let* ((pd-y    (cadr (cadr (cadr (dk-goal)))))
             (three   (dk-split! (dk-landed-1 (lambda () (di)))))
             (pd-ymin (any-pred (dk-head? 'FORALL) three)))
        (have! (list 'AND (list 'IN pd-y 'NN) (pd-bound 'a_ 'p_ pd-y)))
        (dk-deepest (lambda () (inst+ pd-minim pd-y)))     ; DEG <= y
        (dk-deepest (lambda () (inst+ pd-ymin pd-d)))      ; y <= DEG
        (fact 'nn-le-antisym pd-d pd-y)
        (ass)))))

(qed 'deg-well-defined)
(gloss! 'deg-well-defined
  "For a polynomial p over A, DEG(A,p) is a natural number, it bounds the
   support of p (p(k) = ZERO(A) for every k > DEG(A,p)), and it is the LEAST
   natural number that does.  The three facts together are exactly the defining
   description of DEG, so this is the theorem that makes DEG defined at all.
   Proved by `minimize!' over the bounds of p's support -- existence of one
   bound is poly-tail-zero-fwd -- with uniqueness from nn-le-antisym.")
(topic! 'deg-well-defined 'algebra)

;;; =====================================================================
;;; deg-bound-apply -- DEG-BOUND, read forward
;;; =====================================================================
;;;
;;; `DEG-BOUND' is a `def-predicate', so its defining IFF is a THEOREM and
;;; `mac-h' CAN unfold it in a hypothesis -- but `mac-h' REPLACES what it
;;; unfolds, and every proof below needs the DEG-BOUND hypothesis again
;;; afterwards.  One citable forward rule costs four lines and is
;;; non-destructive at every later site.

(sp (make-wff '(FORALL a_ (FORALL p_ (FORALL n_ (FORALL k_
   (IMPLIES (DEG-BOUND a_ p_ n_)
     (IMPLIES (IN k_ NN)
       (IMPLIES (< n_ k_) (= (p_ k_) (ZERO a_)))))))))))
(pd-peel!)
(mac-h 'DEG-BOUND '(DEG-BOUND a_ p_ n_))
(dk-deepest (lambda () (inst+ (any-pred (dk-head? 'FORALL) (dk-asms)) 'k_)))
(ass)
(qed 'deg-bound-apply)
(gloss! 'deg-bound-apply
  "If n bounds the support of p then p(k) = ZERO(A) for every k in NN with
   n < k.  The forward reading of DEG-BOUND; use it instead of `mac-h
   DEG-BOUND', which consumes the hypothesis.")
(topic! 'deg-bound-apply 'algebra)

;;; ---- the two functoid unfolds, as citable equations -------------------
;;; `def-functoid' installs a rewrite macete and no theorem, so `mac' unfolds
;;; DEG / LEADCOEF in a GOAL and `mac-h' cannot unfold either in a HYPOTHESIS.
;;; The unfolding equation is provable in one line and IS a theorem, so
;;; `mac-h' rebuilds its rule from the theorem table (CLAUDE.md; the seven
;;; siblings in poly-membership.scm).  `==' rather than `=': `rfl' carries a
;;; definedness side-condition and DEG(A,p) is a description, so `=' would owe
;;; a witness that quasi-equality does not ask for.

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'p_
   (list '== '(DEG a_ p_) pd-iota)))))
(pd-peel!) (mac 'DEG) (qrfl)
(qed 'deg-unfold)
(gloss! 'deg-unfold
  "DEG(A,p) is the definite description of the least natural number bounding
   the support of p, as a citable equation.  Cite it with mac-h to open a DEG
   inside a hypothesis.")
(topic! 'deg-unfold 'plumbing)

(sp (make-wff '(FORALL a_ (FORALL p_ (== (LEADCOEF a_ p_) (p_ (DEG a_ p_)))))))
(pd-peel!) (mac 'LEADCOEF) (qrfl)
(qed 'leadcoef-unfold)
(gloss! 'leadcoef-unfold
  "LEADCOEF(A,p) = p(DEG(A,p)), as a citable equation.")
(topic! 'leadcoef-unfold 'plumbing)

;;; =====================================================================
;;; nn-succ-not-le -- succ n is never <= n
;;; =====================================================================
;;;
;;; The discreteness brick every "n is not minimal, take one less" argument
;;; below ends on, and the tree did not have it: order-lemmas has nn-le-succ
;;; (n <= succ n) and nn-le-imp-neq-succ (j <= k => j /= succ k) but nothing
;;; that puts them together.  Four citations, and it turns each of the three
;;; sites that need it from five lines into one.

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (NOT (<= (succ n_) n_))))))
(pd-peel!)
(di)                                    ; assume succ n_ <= n_; goal FALSITY
(fact 'nn-succ-closed 'n_)
(fact 'nn-le-succ 'n_)
(fact 'nn-le-antisym 'n_ '(succ n_))    ; n_ = succ n_
(fact 'nn-le-refl 'n_)
(fact 'nn-le-imp-neq-succ 'n_ 'n_)      ; n_ /= succ n_
(ai '(NOT (= n_ (succ n_))))
(qed 'nn-succ-not-le)
(gloss! 'nn-succ-not-le
  "succ n is never <= n, for n in NN.  Antisymmetry against nn-le-succ gives
   n = succ n, which nn-le-imp-neq-succ forbids.")
(topic! 'nn-succ-not-le 'inequalities)

;;; =====================================================================
;;; leadcoef-nonzero -- a polynomial with a nonzero coefficient has a
;;; nonzero LEADING coefficient
;;; =====================================================================
;;;
;;; The whole content is that DEG is the LEAST bound.  If p(DEG) were zero then
;;; DEG - 1 would bound the support too, and DEG would not be least.  "DEG - 1"
;;; is the step that needs care in NN: it exists only because the hypothesis
;;; forces DEG >= 1, and that is why the proof first walks a support member k0
;;; up to k0 < DEG.  Nothing here uses monus; DEG is exhibited as a SUCCESSOR
;;; (nn-pos-is-succ) and the predecessor is the eigenvariable that comes with
;;; it.

;;; "every coefficient of p vanishes" -- the right-hand side of poly-zero-iff,
;;; and (negated, then pushed) the hypothesis of the pointwise form below.
(define pd-allzero '(FORALL k_ (IMPLIES (IN k_ NN) (= (p_ k_) (ZERO a_)))))

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'p_
   (list 'IMPLIES '(IN p_ (CARR (POLY a_)))
     (list 'IMPLIES '(FORSOME k_ (AND (IN k_ NN) (NOT (= (p_ k_) (ZERO a_)))))
       (list 'NOT '(= (LEADCOEF a_ p_) (ZERO a_)))))))))
(pd-peel!)
(mac 'LEADCOEF)
(di)                                    ; assume p(DEG) = 0; goal FALSITY

(define pd-dd '(DEG a_ p_))

;; a nonzero coefficient, named.
(define pd-k0parts
  (dk-split! (any-pred (dk-head? 'AND)
    (dk-landed (lambda () (ai (any-pred (dk-head? 'FORSOME) (dk-asms))))))))
(define pd-k0 (cadr (any-pred (dk-head? 'IN) pd-k0parts)))

;; the degree, its bound property and its minimality.
(define pd-dparts (dk-split! (dk-fact! 'deg-well-defined 'a_ 'p_)))
(define pd-dmin
  (or (any-pred (dk-head? 'FORALL) pd-dparts)
      (error "leadcoef-nonzero-ptwise: deg-well-defined's minimality clause not found")))

;; (1) k0 <= DEG: a coefficient past DEG vanishes and this one does not.
(have! (list 'NOT (list '< pd-dd pd-k0))
  (lambda ()
    (di)
    (fact 'deg-bound-apply 'a_ 'p_ pd-dd pd-k0)
    (ai (list 'NOT (list '= (list 'p_ pd-k0) '(ZERO a_))))))
(fact 'nn-not-lt-le pd-dd pd-k0)

;; (2) k0 /= DEG (their coefficients differ), hence k0 < DEG, hence 1 <= DEG.
(have! (list 'NOT (list '= pd-k0 pd-dd))
  (lambda ()
    (di)
    (have! (list '= (list 'p_ pd-k0) '(ZERO a_))
      (lambda () (subst (list '= pd-k0 pd-dd)) (ass)))
    (ai (list 'NOT (list '= (list 'p_ pd-k0) '(ZERO a_))))))
(have! (list '< pd-k0 pd-dd) pd-lt!)
(fact 'nn-lt-succ-le pd-k0 pd-dd)
(fact 'nn-one-le-succ pd-k0)
(fact 'rr-one-in) (fact 'nn-succ-closed pd-k0) (fact 'nn-in-rr (list 'succ pd-k0)) (fact 'nn-in-rr pd-dd)
(fact 'rr-le-trans-c 1 (list 'succ pd-k0) pd-dd)

;; (3) so DEG is a successor -- and this is the step that would fail, and
;;     SHOULD fail, without the nonzero-coefficient hypothesis.
(define pd-eparts
  (dk-split! (any-pred (dk-head? 'AND)
    (dk-landed (lambda () (ai (dk-fact! 'nn-pos-is-succ pd-dd)))))))
(define pd-e (cadr (any-pred (dk-head? 'IN) pd-eparts)))

;; (4) the predecessor bounds the support too: past it, an index either IS DEG
;;     (coefficient zero by the assumption under refutation) or exceeds DEG
;;     (coefficient zero by DEG's own bound property).
(have! (list 'DEG-BOUND 'a_ 'p_ pd-e)
  (lambda ()
    (mac 'DEG-BOUND)
    (pd-peel!)
    (let ((pd-kk (cadr (cadr (dk-goal)))))     ; goal (= (p_ kk) (ZERO a_))
      (fact 'nn-lt-succ-le pd-e pd-kk)
      (have! (list '<= pd-dd pd-kk)
        (lambda () (subst (list '= pd-dd (list 'succ pd-e))) (ass)))
      (use-em (list '= pd-kk pd-dd)
        (lambda () (subst (list '= pd-kk pd-dd)) (ass))
        (lambda ()
          (fact 'neq-sym pd-kk pd-dd)
          (have! (list '< pd-dd pd-kk) pd-lt!)
          (fact 'deg-bound-apply 'a_ 'p_ pd-dd pd-kk)
          (ass))))))

;; (5) minimality then says DEG <= its own predecessor.  Absurd.
(dk-deepest (lambda () (inst+ pd-dmin pd-e)))
(fact 'eq-sym pd-dd (list 'succ pd-e))
(have! (list '<= (list 'succ pd-e) pd-e)
  (lambda () (subst (list '= (list 'succ pd-e) pd-dd)) (ass)))
(fact 'nn-succ-not-le pd-e)
(ai (list 'NOT (list '<= (list 'succ pd-e) pd-e)))
(qed 'leadcoef-nonzero-ptwise)
(gloss! 'leadcoef-nonzero-ptwise
  "A polynomial over A with at least one nonzero coefficient has a nonzero
   leading coefficient: LEADCOEF(A,p) = p(DEG(A,p)) /= ZERO(A).  The POINTWISE
   form of the hypothesis, which is what the minimality argument below consumes;
   `leadcoef-nonzero' states the same thing on `p /= ZERO(POLY(A))' and is the
   one to cite.")
(topic! 'leadcoef-nonzero-ptwise 'algebra)

;;; ---- the same thing, on the hypothesis a mathematician writes ---------
;;;
;;; "p /= 0 implies LEADCOEF(p) /= 0".  Until 2026-08-21 this file could only
;;; state the pointwise form above, and its header recorded the reason: the two
;;; hypotheses are equivalent through FUNCTION EXTENSIONALITY composed with the
;;; pointwise value of MONALG-ZERO, and neither was available.  Both are now
;;; (theorem-library/poly-zero.scm), and the equivalence is `poly-zero-iff'.
;;;
;;; THE MOVE, and there is no mathematics in it -- three lines, twice generic:
;;;
;;;   `prop' contraposes the bridge.  Both sides of the IFF are opaque atoms to
;;;   it -- one an equation, one a universal -- so "A <=> B, NOT A, therefore
;;;   NOT B" is pure propositional logic and needs no instantiation.
;;;
;;;   `push-not-h' (push-not.scm) turns NOT of the guarded universal into the
;;;   guarded existential, in ONE call and with the guard never negated: the
;;;   guarded surface is a fixed point of the push, so what lands is literally
;;;   the shape `leadcoef-nonzero-ptwise' quantifies.  By hand that step is a
;;;   `pbc', a `have!' with an `ew' lane and an `ai'.
;;;
;;; The IS-RING hypothesis is new and is the bridge's, not this argument's:
;;; `poly-zero-apply' needs ZERO(A) to be DEFINED before it can say a
;;; coefficient of the zero polynomial equals it, and `ring-zero-in' is what
;;; says so.  BILL: unchanged from the pointwise form -- the bridge is
;;; `modulo 0', so the whole debt is still the inherited NN-order one.

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'p_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN p_ (CARR (POLY a_)))
       (list 'IMPLIES '(NOT (= p_ (ZERO (POLY a_))))
         (list 'NOT '(= (LEADCOEF a_ p_) (ZERO a_))))))))))
(pd-peel!)
(fact 'poly-zero-iff 'a_ 'p_)
(have! (list 'NOT pd-allzero) (lambda () (prop)))
(push-not-h (list 'NOT pd-allzero))
(fact 'leadcoef-nonzero-ptwise 'a_ 'p_)
(ass)
(qed 'leadcoef-nonzero)
(gloss! 'leadcoef-nonzero
  "A polynomial that is not the zero polynomial has a nonzero leading
   coefficient: p /= ZERO(POLY(A)) implies LEADCOEF(A,p) /= ZERO(A).  The form
   to cite.  Proved from `leadcoef-nonzero-ptwise' by contraposing the
   extensionality bridge `poly-zero-iff' and pushing the negation through the
   universal; it adds no debt of its own.")
(topic! 'leadcoef-nonzero 'algebra)

;;; =====================================================================
;;; MONOMIALS -- c.x^n
;;; =====================================================================
;;;
;;; MONOMIAL(A,c,n) is a VNB-LAMBDA on NN, so its value at an index is `lam-b'
;;; and its typing is `lam-t'.  Both want the argument TYPED FIRST: `lam-b'
;;; fired on an untyped argument still reduces but OWES (IN k NN) at a node
;;; whose context may not be able to close it (CLAUDE.md).  Every statement
;;; below therefore carries the index typing in its own hypotheses, and
;;; `pd-peel!' lands it before the reduction.
;;;
;;; `=' and not `==' throughout: `if-true' / `if-false' hand back the
;;; reduction as a genuine equation (`(= (IF p a b) a)'), so the definedness
;;; that `=' asserts is discharged by the rule that produced it.

;;; ---- the value at the exponent ---------------------------------------
(sp (make-wff '(FORALL a_ (FORALL c_ (FORALL n_
   (IMPLIES (IN n_ NN) (= ((MONOMIAL a_ c_ n_) n_) c_)))))))
(pd-peel!)
(mac 'MONOMIAL)
(lam-b)
(for-each (lambda (n) (dk-focus! n)
            (if (equal? (dk-goal) '(= n_ n_)) (rfl) (ass)))
          (dk-opened (lambda () (if-true (list 'IF '(= n_ n_) 'c_ '(ZERO a_))))))
(qed 'monomial-at)
(gloss! 'monomial-at
  "The monomial c.x^n has coefficient c at the exponent n.")
(topic! 'monomial-at 'algebra)

;;; ---- the value anywhere else -----------------------------------------
(sp (make-wff '(FORALL a_ (FORALL c_ (FORALL n_ (FORALL k_
   (IMPLIES (IN k_ NN)
     (IMPLIES (NOT (= k_ n_)) (= ((MONOMIAL a_ c_ n_) k_) (ZERO a_))))))))))
(pd-peel!)
(mac 'MONOMIAL)
(lam-b)
(for-each (lambda (n) (dk-focus! n) (ass))
          (dk-opened (lambda () (if-false (list 'IF '(= k_ n_) 'c_ '(ZERO a_))))))
(qed 'monomial-off)
(gloss! 'monomial-off
  "The monomial c.x^n has coefficient ZERO(A) at every exponent other than n.")
(topic! 'monomial-off 'algebra)

;;; ---- a monomial IS a polynomial --------------------------------------
;;; Reached through poly-tail-zero-bwd rather than through the support: the
;;; eventually-zero criterion needs only the ONE index succ n as a witness,
;;; where the support route would need CARD({n}) -- i.e. `card-singleton',
;;; which is still an asserted well-known fact (CLAUDE.md, the split cardinality
;;; shelf).  Same theorem, one fewer piece of debt.
(define pd-mono '(MONOMIAL a_ c_ n_))

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'c_ (list 'FORALL 'n_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN c_ (CARR a_))
       (list 'IMPLIES '(IN n_ NN)
         (list 'IN pd-mono '(CARR (POLY a_)))))))))))
(pd-peel!)
(fact 'ring-zero-in 'a_)

;; (i) it is a sequence in CARR(A): a lambda on NN with values in the carrier.
(have! (list 'IN pd-mono '(SQN (CARR a_)))
  (lambda ()
    (mac 'sqn-membership)
    (mac 'MONOMIAL)
    (for-each
     (lambda (n)
       (dk-focus! n)
       (if (equal? (dk-goal) '(IN NN SET))
           (begin (ta 'nn-is-set) (ass))
           (begin
             (pd-peel!)
             (let ((pd-if (cadr (dk-goal))))          ; goal (IN (IF ...) (CARR a_))
               (use-em (cadr pd-if)
                 (lambda ()
                   (for-each (lambda (m) (dk-focus! m)
                               (if (eq? (car (dk-goal)) 'IN)
                                   (begin (subst (list '= pd-if (caddr pd-if))) (ass))
                                   (ass)))
                             (dk-opened (lambda () (if-true pd-if)))))
                 (lambda ()
                   (for-each (lambda (m) (dk-focus! m)
                               (if (eq? (car (dk-goal)) 'IN)
                                   (begin (subst (list '= pd-if (cadddr pd-if))) (ass))
                                   (ass)))
                             (dk-opened (lambda () (if-false pd-if))))))))))
     (dk-opened (lambda () (lam-t))))))

;; (ii) it vanishes from succ n on: past n every index differs from n.
(have! (list 'FORSOME 'm_ (list 'AND '(IN m_ NN)
         (list 'FORALL 'k_ (list 'IMPLIES '(IN k_ NN)
           (list 'IMPLIES '(<= m_ k_) (list '= (list pd-mono 'k_) '(ZERO a_)))))))
  (lambda ()
    (ew '(succ n_))
    (for-each
     (lambda (n)
       (dk-focus! n)
       (if (eq? (car (dk-goal)) 'IN)
           (begin (fact 'nn-succ-closed 'n_) (ass))
           (begin
             (pd-peel!)
             (have! '(NOT (= k_ n_))
               (lambda ()
                 (di)
                 ;; `subst' rewrites EVERY occurrence, so substituting into
                 ;; the goal (<= (succ n_) n_) moves both ends at once and
                 ;; lands nothing.  Move the SHORT hypothesis instead: k_ <= k_
                 ;; becomes k_ <= n_, and transitivity does the rest.
                 (fact 'eq-sym 'k_ 'n_)
                 (fact 'nn-le-refl 'k_)
                 (have! '(<= k_ n_) (lambda () (subst '(= n_ k_)) (ass)))
(fact 'nn-in-rr 'k_) (fact 'nn-in-rr 'n_) (fact 'nn-succ-closed 'n_) (fact 'nn-in-rr '(succ n_))
                 (fact 'rr-le-trans-c '(succ n_) 'k_ 'n_)
                 (fact 'nn-succ-not-le 'n_)
                 (ai '(NOT (<= (succ n_) n_)))))
             (fact 'monomial-off 'a_ 'c_ 'n_ 'k_)
             (ass))))
     (dk-opened (lambda () (di))))))

(fact 'poly-tail-zero-bwd 'a_ pd-mono)
(ass)
(qed 'monomial-in-poly)
(gloss! 'monomial-in-poly
  "The monomial c.x^n is a polynomial over A whenever A is a ring, c is in its
   carrier and n is a natural number.")
(topic! 'monomial-in-poly 'algebra)

;;; ---- the support of a monomial ---------------------------------------
;;; Stated POINTWISE -- "k is in the support iff k is n" -- rather than as the
;;; set equation SUPP(...) = {n}.  The set form would need extensionality plus
;;; a singleton constructor, and every consumer reads a support MEMBER out of a
;;; context anyway, which is the pointwise form.
(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'c_ (list 'FORALL 'n_ (list 'FORALL 'k_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN c_ (CARR a_))
       (list 'IMPLIES '(NOT (= c_ (ZERO a_)))
         (list 'IMPLIES '(IN n_ NN)
           (list 'IFF (list 'IN 'k_ (list 'SUPP 'a_ 'NN-ADD-MONOID pd-mono))
                      '(AND (IN k_ NN) (= k_ n_)))))))))))))
(pd-peel!)
(pd-branch! (dk-opened (lambda () (di)))
  ;; => : a nonvanishing coefficient can only sit at n.
  (cons (pd-head 'and)
    (lambda ()
      (mac-h 'supp-membership (list 'IN 'k_ (list 'SUPP 'a_ 'NN-ADD-MONOID pd-mono)))
      (dk-split! (any-pred (dk-head? 'AND) (dk-asms)))
      (slot-h 'CARR '(IN k_ (CARR NN-ADD-MONOID)))
      (have! '(= k_ n_)
        (lambda ()
          (use-em '(= k_ n_)
            ass
            (lambda ()
              (fact 'monomial-off 'a_ 'c_ 'n_ 'k_)
              (ai (list 'NOT (list '= (list pd-mono 'k_) '(ZERO a_))))))))
      (for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened (lambda () (di))))))
  ;; <= : at n the coefficient is c, which is not zero.  `di' on an IFF goal
  ;; opens the two implications with their antecedents ALREADY assumed, so this
  ;; leaf's goal is the membership and the conjunction is a hypothesis.
  (cons (lambda (g) (not (and (pair? g) (eq? (car g) 'and))))
    (lambda ()
      (dk-split! '(AND (IN k_ NN) (= k_ n_)))
      (fact 'monomial-at 'a_ 'c_ 'n_)
      ;; `subst' rewrites EVERY occurrence, so it has to be run on a goal whose
      ;; only occurrence of k_ is the index -- (mono k_) = c, not (mono n_) = 0,
      ;; whose n_ also sits INSIDE the monomial and would move with it.
      (have! (list '= (list pd-mono 'k_) 'c_)
        (lambda () (subst '(= k_ n_)) (ass)))
      (fact 'eq-sym (list pd-mono 'k_) 'c_)
      (mac 'supp-membership)
      (slot 'CARR)
      (for-each
       (lambda (n)
         (dk-focus! n)
         (if (eq? (car (dk-goal)) 'IN)
             (ass)
             (begin
               (di)
               (fact 'eq-trans 'c_ (list pd-mono 'k_) '(ZERO a_))
               (ai '(NOT (= c_ (ZERO a_)))))))
       (dk-opened (lambda () (di)))))))
(qed 'monomial-support)
(gloss! 'monomial-support
  "The support of the monomial c.x^n with c /= 0 is exactly {n}: an index lies
   in it iff it is a natural number equal to n.  Stated pointwise.")
(topic! 'monomial-support 'algebra)

;;; =====================================================================
;;; deg-is -- how to COMPUTE a degree
;;; =====================================================================
;;;
;;; The recognition principle for DEG, and the only thing any later degree
;;; computation needs: exhibit a bound and show it is least, and the IOTA is
;;; that value.  Without it every such computation would have to re-run
;;; `mac DEG' + `iota-d' and re-discharge existence.  With it they run against
;;; deg-well-defined and one antisymmetry.

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'p_ (list 'FORALL 'm_
   (list 'IMPLIES '(IN p_ (CARR (POLY a_)))
     (list 'IMPLIES '(IN m_ NN)
       (list 'IMPLIES (pd-bound 'a_ 'p_ 'm_)
         (list 'IMPLIES (pd-minclause 'a_ 'p_ 'm_)
           '(= (DEG a_ p_) m_))))))))))
(pd-peel!)
(let* ((parts (dk-split! (dk-fact! 'deg-well-defined 'a_ 'p_)))
       (dmin  (or (any-pred (dk-head? 'FORALL) parts)
                  (error "deg-is: deg-well-defined's minimality clause not found")))
       (mmin  (or (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)
                                             (dk-contains? f '(<= m_ j_))))
                            (dk-asms))
                  (error "deg-is: the hypothesis minimality clause not found"))))
  (dk-deepest (lambda () (inst+ dmin 'm_)))            ; DEG <= m
  (dk-deepest (lambda () (inst+ mmin '(DEG a_ p_))))   ; m <= DEG
  (fact 'nn-le-antisym '(DEG a_ p_) 'm_)
  (ass))
(qed 'deg-is)
(gloss! 'deg-is
  "If m in NN bounds the support of the polynomial p and every bound is at
   least m, then DEG(A,p) = m.  The recognition principle for DEG: exhibit the
   bound and its minimality and the description is pinned.")
(topic! 'deg-is 'algebra)

;;; ---- the degree and leading coefficient of a monomial ------------------
;;; c /= 0 is needed and is exactly where it is needed: for c = 0 the monomial
;;; IS the zero polynomial, whose degree is 0 by the convention, not n.

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'c_ (list 'FORALL 'n_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN c_ (CARR a_))
       (list 'IMPLIES '(NOT (= c_ (ZERO a_)))
         (list 'IMPLIES '(IN n_ NN)
           (list '= (list 'DEG 'a_ pd-mono) 'n_))))))))))
(pd-peel!)
(fact 'monomial-in-poly 'a_ 'c_ 'n_)
(fact 'monomial-at 'a_ 'c_ 'n_)

;; n bounds the support: past n every index differs from n.
(have! (pd-bound 'a_ pd-mono 'n_)
  (lambda ()
    (mac 'DEG-BOUND)
    (pd-peel!)
    (mac-h '< '(< n_ k_))
    (dk-split! '(AND (<= n_ k_) (NOT (= n_ k_))))
    (fact 'neq-sym 'n_ 'k_)
    (fact 'monomial-off 'a_ 'c_ 'n_ 'k_)
    (ass)))

;; and no smaller index does: at n the coefficient is c, which is not zero.
(have! (pd-minclause 'a_ pd-mono 'n_)
  (lambda ()
    (pd-peel!)
    (have! '(NOT (< j_ n_))
      (lambda ()
        (di)
        (fact 'deg-bound-apply 'a_ pd-mono 'j_ 'n_)     ; monomial(n) = ZERO
        (fact 'eq-sym (list pd-mono 'n_) 'c_)           ; c = monomial(n)
        (fact 'eq-trans 'c_ (list pd-mono 'n_) '(ZERO a_))
        (ai '(NOT (= c_ (ZERO a_))))))
    (fact 'nn-not-lt-le 'j_ 'n_)
    (ass)))

(fact 'deg-is 'a_ pd-mono 'n_)
(ass)
(qed 'monomial-deg)
(gloss! 'monomial-deg
  "The monomial c.x^n with c /= 0 has degree n.  (For c = 0 the monomial is the
   zero polynomial and its degree is 0, by the DEG(0) = 0 convention.)")
(topic! 'monomial-deg 'algebra)

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'c_ (list 'FORALL 'n_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN c_ (CARR a_))
       (list 'IMPLIES '(NOT (= c_ (ZERO a_)))
         (list 'IMPLIES '(IN n_ NN)
           (list '= (list 'LEADCOEF 'a_ pd-mono) 'c_))))))))))
(pd-peel!)
(fact 'monomial-deg 'a_ 'c_ 'n_)
(fact 'monomial-at 'a_ 'c_ 'n_)
(mac 'LEADCOEF)
(subst (list '= (list 'DEG 'a_ pd-mono) 'n_))
(ass)
(qed 'monomial-leadcoef)
(gloss! 'monomial-leadcoef
  "The monomial c.x^n with c /= 0 has leading coefficient c.")
(topic! 'monomial-leadcoef 'algebra)

;;; =====================================================================
;;; deg-add-le -- the degree of a sum
;;; =====================================================================
;;;
;;; STATED IN BOUND FORM.  `deg(f+g) <= max(deg f, deg g)' is not writable: the
;;; tree has no NN maximum.  See the file header; the bound form below is
;;; equivalent and is the form that composes.
;;;
;;; The mathematics is one line -- past a common bound both coefficients
;;; vanish, so their sum does -- and every other line here is bookkeeping
;;; between the two spellings of the carrier (CARR(POLY A) and
;;; FINSUPP(A, NN-ADD-MONOID)) and between NN and CARR(NN-ADD-MONOID).

(define pd-sum '(MONALG-ADD a_ NN-ADD-MONOID f_ g_))

(sp (make-wff (list 'FORALL 'a_ (list 'FORALL 'f_ (list 'FORALL 'g_ (list 'FORALL 'n_
   (list 'IMPLIES '(IS-RING a_)
     (list 'IMPLIES '(IN f_ (CARR (POLY a_)))
       (list 'IMPLIES '(IN g_ (CARR (POLY a_)))
         (list 'IMPLIES '(IN n_ NN)
           (list 'IMPLIES '(<= (DEG a_ f_) n_)
             (list 'IMPLIES '(<= (DEG a_ g_) n_)
               (list '<= (list 'DEG 'a_ pd-sum) 'n_)))))))))))))
(pd-peel!)

;; -- the sum is a polynomial.  `mac-h poly-carrier' is destructive, so each
;;    conversion happens inside its own `have!' lane and the main branch keeps
;;    the CARR(POLY A) spelling for the DEG facts below.
(ta 'nn-add-monoid-is-comm-monoid)
(fact 'comm-monoid-is-monoid 'NN-ADD-MONOID)
(have! '(IN f_ (FINSUPP a_ NN-ADD-MONOID))
  (lambda () (mac-h 'poly-carrier '(IN f_ (CARR (POLY a_)))) (ass)))
(have! '(IN g_ (FINSUPP a_ NN-ADD-MONOID))
  (lambda () (mac-h 'poly-carrier '(IN g_ (CARR (POLY a_)))) (ass)))
(fact 'monalg-add-fun 'a_ 'NN-ADD-MONOID 'f_ 'g_)
(have! (list 'IN pd-sum '(CARR (POLY a_)))
  (lambda () (mac 'poly-carrier) (ass)))

;; -- n bounds the support of the sum.
(have! (pd-bound 'a_ pd-sum 'n_)
  (lambda ()
    (mac 'DEG-BOUND)
    (pd-peel!)
    (dk-split! (dk-fact! 'deg-well-defined 'a_ 'f_))
    (dk-split! (dk-fact! 'deg-well-defined 'a_ 'g_))
(fact 'nn-in-rr '(DEG a_ f_)) (fact 'nn-in-rr '(DEG a_ g_)) (fact 'nn-in-rr 'n_) (fact 'nn-in-rr 'k_)
    (fact 'co-le-lt-trans '(DEG a_ f_) 'n_ 'k_)
    (fact 'co-le-lt-trans '(DEG a_ g_) 'n_ 'k_)
    (fact 'deg-bound-apply 'a_ 'f_ '(DEG a_ f_) 'k_)
    (fact 'deg-bound-apply 'a_ 'g_ '(DEG a_ g_) 'k_)
    (have! '(IN k_ (CARR NN-ADD-MONOID)) (lambda () (slot 'CARR) (ass)))
    (mac 'monalg-add-apply)
    (subst '(= (f_ k_) (ZERO a_)))
    (subst '(= (g_ k_) (ZERO a_)))
    (fact 'ring-zero-in 'a_)
    (fact 'ring-add-left-id 'a_ '(ZERO a_))
    (ass)))

;; -- so the LEAST bound is at most n.
(let ((parts (dk-split! (dk-fact! 'deg-well-defined 'a_ pd-sum))))
  (dk-deepest
   (lambda () (inst+ (or (any-pred (dk-head? 'FORALL) parts)
                         (error "deg-add-le: minimality clause not found"))
                     'n_)))
  (ass))
(qed 'deg-add-le)
(gloss! 'deg-add-le
  "If n bounds both DEG(A,f) and DEG(A,g) then it bounds DEG(A,f+g).  The
   max-free form of `deg(f+g) <= max(deg f, deg g)': VNB has no NN maximum, and
   this statement is equivalent to the max form (instantiate at the max) while
   being the one that composes.")
(topic! 'deg-add-le 'algebra)

;;; =====================================================================
;;; WHAT IS NOT HERE, AND WHAT IT WOULD TAKE
;;; =====================================================================
;;;
;;; deg(fg) = deg f + deg g.  DELIBERATELY NOT ATTEMPTED, and it is not a
;;; question of driver effort: the statement is FALSE over a general ring (take
;;; A = ZZ/4, f = g = 2x: the product is 0, of degree 0, not 2).  It needs A to
;;; be an INTEGRAL DOMAIN, and then the proof needs three things this layer does
;;; not have:
;;;
;;;   (1) the pointwise value of the CONVOLUTION, i.e. the analogue of
;;;       monalg-add-apply for MONALG-MUL.  That is a FINSUM over the SEP of
;;;       factorisation pairs, so opening it means opening a finite sum with a
;;;       dependent index set -- which is exactly what theorem-library/
;;;       finsum-fiber.scm was built for and what monalg-mul-assoc is waiting
;;;       on.  Same blocker, one storey down.
;;;   (2) the collapse of that sum at the top index: for m = deg f + deg g the
;;;       only surviving pair is (deg f, deg g), every other factorisation
;;;       putting one factor past its polynomial's degree.  `finsum-single-
;;;       support' (matrix.scm) is the shape, but the index set here is a SEP of
;;;       a CARTESIAN, not an INTERVAL.
;;;   (3) LEADCOEF(fg) = LEADCOEF(f).LEADCOEF(g) /= 0, which is where the
;;;       no-zero-divisor hypothesis is spent (integral-domain-cancel-zero,
;;;       structure-library/integral-domain-laws.scm, is the citable form).
;;;
;;; The right shape for the eventual statement is the pair
;;;     deg-mul-le    deg(fg) <= deg f + deg g          (ANY ring, needs (1)+(2))
;;;     deg-mul       deg(fg)  = deg f + deg g          (integral domain, +(3))
;;; -- the inequality being the half that survives zero divisors and the half
;;; every filtration argument actually uses.
;;;
;;; DIVISION WITH REMAINDER.  Needs, beyond all of the above: a MONIC (or
;;; unit-leading) divisor, so that the leading coefficient can be inverted; a
;;; recursion on the degree, which is strong induction on NN and NOT `ni'
;;; (`pi-nn-induction!' is ordinary successor induction -- the tree has
;;; nn-least-element and hence minimal-counterexample descent, which is the
;;; usable form, but no packaged strong-induction tactic); and the whole
;;; subtraction layer for polynomials (MONALG-NEG composed with MONALG-ADD,
;;; whose pointwise value has no lemma yet).  It is the gate to
;;; `poly-is-euclidean-ring', hence to POLY being a PID, and it is a separate
;;; arc.
;;;
;;; A NN MAXIMUM.  `deg-add-le' is stated in bound form because there is none.
;;; Adding one is small and self-contained: NN-MAX(a,b) = IF (<= a b) b a, with
;;; nn-max-left / nn-max-right (each argument is <=) and nn-max-least (any
;;; common bound is >=), all three closable by `use-em' on (<= a b) plus
;;; if-true / if-false and the order supports already cited here.  It was not
;;; done because nothing in the tree asks for it yet and inventing vocabulary
;;; ahead of a consumer is how the tree acquires unused constructors.
;;; ineq-supply.scm's `*ineq-supply-wanted*' records the same gap on the RR side
;;; (`min' / `rr-min-*'), so the two want deciding together.
;;;
;;; FUNCTION EXTENSIONALITY -- CLOSED, 2026-08-21, in
;;; theorem-library/poly-zero.scm.  This entry used to read "the second is the
;;; real gap: nothing in the tree states that two functions agreeing pointwise
;;; on their common domain are equal".  That was false, and the correction is
;;; worth more than the theorem it unblocked: `fun-domain-extensionality'
;;; (theory.scm:451) is a base axiom, PRIMITIVE, in exactly that form and with
;;; no finiteness or sethood side condition.  The standing rule the entry was
;;; recalling (`drop_fn_ext_consequences') forbids adding per-operator
;;; congruence lemmas AROUND it; it never forbade citing it.  What was genuinely
;;; missing was the small half -- `monalg-zero-apply', one `lam-b' -- plus the
;;; definitional projection saying which term the zero of POLY(A) is.  Both are
;;; one file, all six statements `modulo 0', and `leadcoef-nonzero' now carries
;;; the hypothesis a mathematician writes.
;;;
;;; The lesson for the rest of the tree: a "the tree cannot state this"
;;; obstacle in a file header is a claim about the theorem table, and the
;;; theorem table can be asked.
