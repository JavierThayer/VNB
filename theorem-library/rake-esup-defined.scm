;;; theorem-library/rake-esup-defined.scm -- ESUP DEFINED as a definite
;;; description, and its four characterising axioms PROVEN from the definition.
;;; Assignment "ESUP and ESUM defined" (the user's decision of 2026-09-19).
;;; Helper prefix `esd-'.
;;;
;;; THE DEFINING FORM.  For the probe this file installs it on a FRESH head
;;; `ESUP2', because `ESUP' is already registered in the band and pinned by the
;;; four axioms this file replaces.  What belongs in
;;; structure-library/extended-reals-pos.scm, in place of esup-in / esup-upper /
;;; esup-least / esup-empty, is the same form on the real name:
;;;
;;;   (def-functoid 'ESUP '(s_)
;;;     '(IOTA bb_ (AND (IN bb_ RR-POS-STAR)
;;;                  (AND (FORALL x (IMPLIES (IN x s_) (<= x bb_)))
;;;                       (FORALL b (IMPLIES (AND (IN b RR-POS-STAR)
;;;                                               (FORALL x (IMPLIES (IN x s_) (<= x b))))
;;;                                    (<= bb_ b)))))))
;;;
;;; "the least upper bound of s_ in [0,+inf]".  The inner binders are spelled
;;; `x' and `b' ON PURPOSE: they are the binders esup-upper and esup-least use,
;;; so the two laws come out of the description's conjuncts LITERALLY, with no
;;; alpha-renaming step (a `have!' of an alpha-variant of a context formula is a
;;; silent self-loop -- CLAUDE.md).
;;;
;;; WHY DEFINE RATHER THAN STAMP.  The four ESUP axioms are bare
;;; `theory-add-axiom!' forms with no `warrant!' at all, and nothing in the tree
;;; showed the characterisation was SATISFIABLE -- the point
;;; rake-etimes-defined.scm's closing audit makes about ESUM, in the same words.
;;; The description below is satisfiable by construction: `esup2-exists' EXHIBITS
;;; the least upper bound.
;;;
;;; WHAT THE DEFINITION COSTS: nothing.  All four statements are proven
;;; UNCHANGED, character for character, modulo the head rename.
;;;
;;; CONTENTS
;;;   esup2-exists   every subset of [0,+inf] HAS a least upper bound there
;;;   esup2-unique   it is unique (antisymmetry)
;;;   esup2-prop     the defining property, through `iota-d'
;;;   esup2-in       esup-in,    statement UNCHANGED
;;;   esup2-upper    esup-upper, statement UNCHANGED
;;;   esup2-least    esup-least, statement UNCHANGED
;;;   esup2-empty    esup-empty, statement UNCHANGED
;;; All seven `modulo 0' against a CURRENT tree.  A probe on a band built before
;;; 2026-09-18 evening reports `modulo {pos-inf-upper-bound}': that axiom is
;;; stamped `primitive' in structure-library/extended-reals.scm:71 today, and the
;;; only reason it shows is that the band predates the stamp.
;;;
;;; THE MATHEMATICS -- three cases, and `rr-sup' does the work of one of them.
;;; For S subset [0,+inf]:
;;;   (a) S has NO real upper bound.  Then POS-INF is the lub: it bounds S
;;;       (rr-pos-star-below-pos-inf), and any competing bound c in [0,+inf] must
;;;       be POS-INF, since a REAL c would be an RR-UPPER-BOUND of S.
;;;   (b) S has a real upper bound and is INHABITED.  Then every member of S is
;;;       real (rr-pos-star-le-real-in-rr: an element of [0,+inf] below a real is
;;;       real), so S is an inhabited bounded set of reals and SUP(S) exists by
;;;       order completeness of RR (rr-sup-in/-upper/-least, number-systems.scm,
;;;       PRIMITIVE -- the file is in load.scm's *primitive-files*, so those three
;;;       contribute {} to every bill).  SUP(S) >= 0 because S has a member.
;;;   (c) S has a real upper bound and is EMPTY.  Then 0 is the lub, by
;;;       rr-pos-star-nonneg.
;;; Uniqueness is antisymmetry, `rr-pos-star-le-antisymm' (rake-extended-order).
;;;
;;; `iota-e' EXISTS (primitive-inferences.scm:1758, `pi-iota-in-elim!', added
;;; 2026-09-15 on the user's decision).  CLAUDE.md's "IOTA definedness has no
;;; elimination rule (iota-in-elim)" is STALE.  This file does not need it:
;;; `iota-d' posts existence-and-uniqueness and grants the defining property,
;;; which is the direction a definition wants.
;;;
;;; CITATIONS, with their 0-based load.scm positions:
;;;   theory.scm (11, primitive): subset-def, empty-set-has-no-members
;;;   number-systems (34, PRIMITIVE): rr-zero-in, rr-leq-transitive,
;;;     rr-sup-in, rr-sup-upper, rr-sup-least, RR-UPPER-BOUND, RR-BOUNDED-ABOVE
;;;   structure-library/extended-reals-pos (76, definitional):
;;;     rr-pos-star-membership
;;;   theorem-library/subset-lemmas (190): subset-mem-fwd
;;;   theorem-library/rake-rr-pos-star (192): zero-in-rr-pos-star,
;;;     pos-inf-in-rr-pos-star, rr-pos-star-nonneg, rr-pos-star-below-pos-inf
;;;   theorem-library/rake-extended-order (238): rr-pos-star-le-refl,
;;;     rr-pos-star-le-real-in-rr, rr-pos-star-le-antisymm
;;; Tactics: interactive (134), driver-kit (138), prop (141).  Nothing here uses
;;; `contra', `prep' or `ineq-supply'.
;;;
;;; TWO MECHANICAL FINDINGS, both worked around below and both worth the kit:
;;;   * `dk-only!' can GROUND the leaf it is weakening (the known defect).  In
;;;     the copied `star-cases!' lane it did, and the `prop' that followed then
;;;     ran on an unrelated open leaf and printed a countermodel for a goal
;;;     nobody asked about.  The guard here is one line: fire `prop' only while
;;;     the goal is still the disjunction.
;;;   * `fact' of a GROUND theorem (no universal to peel, no antecedent to
;;;     detach -- `zero-in-rr-pos-star') CLOSES a goal that IS it but lands
;;;     NOTHING in the context otherwise, so it cannot be used to make a ground
;;;     fact citable.  Cite it AT the conjunct that needs it (esd-empty-close!).
;;;
;;; LOAD WINDOW [239, end).  lo = 239 is forced by rake-extended-order (238),
;;; whose three order laws this file cites.  No PROVEN theorem cites esup-in /
;;; esup-upper / esup-least / esup-empty today (grep: only reference/*.md and
;;; comments), so no citer forces hi -- but once the head is renamed to ESUP the
;;; file must precede anything that consumes those four laws, i.e. the ESUM work.

;;; =====================================================================
;;; (0)  THE DEFINITION, on the probe head ESUP2.
;;; =====================================================================

(define esd-ub-of
  (lambda (tm st) (list 'FORALL 'x (list 'IMPLIES (list 'IN 'x st) (list '<= 'x tm)))))

(define esd-least-of
  (lambda (tm st)
    (list 'FORALL 'b
          (list 'IMPLIES (list 'AND (list 'IN 'b 'RR-POS-STAR) (esd-ub-of 'b st))
                (list '<= tm 'b)))))

;;; the description's body: "tm is the least upper bound of st in [0,+inf]"
(define esd-lub-of
  (lambda (tm st)
    (list 'AND (list 'IN tm 'RR-POS-STAR)
          (list 'AND (esd-ub-of tm st) (esd-least-of tm st)))))

;;; INTEGRATED 2026-09-19: the def-functoid (probed here on the head ESUP2) now lives in
;;; structure-library/extended-reals-pos.scm on the head ESUP, and the theorems below
;;; carry the names esup-*.  Comments above that say ESUP2 / esup2-* describe the probe.

;;; =====================================================================
;;; (1)  FILE-LOCAL DRIVER HELPERS
;;; =====================================================================

;;; The case split off `rr-pos-star-membership' (definitional), the lane
;;; rake-rr-pos-star.scm and rake-extended-order.scm both use.  `dk-only!' first:
;;; `prop' has an atom cap and these contexts are deep.
(define (esd-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (esd-inf-case  tm) (list '= tm 'POS-INF))

(define (esd-star-cases! tm real-body inf-body)
  (have! (list 'OR (esd-real-case tm) (esd-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (dk-only! inst (list 'IN tm 'RR-POS-STAR))
             ;; `dk-only!' can GROUND the side leaf (the known defect listed in
             ;; CLAUDE.md): once the context is weakened to the membership iff
             ;; and the typing, the node hash-conses onto one already proved, and
             ;; focus falls back to an unrelated open leaf.  Running `prop' there
             ;; is a no-op that prints a countermodel for a goal nobody asked
             ;; about.  Fire it only while the goal is still the disjunction;
             ;; `have!' errors below if the side goal is in fact still open.
             (if ((dk-head? 'OR) (dk-goal)) (prop)))))
  (use-cases (list (esd-real-case tm) (esd-inf-case tm)) real-body inf-body))

;;; The index set, read STRUCTURALLY off a formula that contains the upper-bound
;;; conjunct: the first (IN x <term>) in a depth-first walk.  Never guess an
;;; eigenvariable from the binder -- `di' renames when the name is taken.
(define (esd-set-of f)
  (cond ((not (pair? f)) #f)
        ((and (eq? (car f) 'IN) (eq? (cadr f) 'x)) (caddr f))
        (#t (let loop ((l (cdr f)))
              (if (null? l) #f (or (esd-set-of (car l)) (loop (cdr l))))))))

;;; A closer for `dk-conj-close!' on a goal that IS the lub conjunction: the
;;; three conjuncts are told apart by HEAD and BINDER, never by position.
(define (esd-lub-closer in-thunk ub-thunk least-thunk)
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((eq? (car g) 'IN) (in-thunk))
            ((and (eq? (car g) 'FORALL) (eq? (cadr g) 'x)) (ub-thunk))
            ((and (eq? (car g) 'FORALL) (eq? (cadr g) 'b)) (least-thunk))
            (#t (error "esd-lub-closer: unexpected conjunct"
                       (expression->string g)))))))

;;; `fact' of a GROUND theorem CLOSES a goal that IS it, but lands nothing in the
;;; context when the goal is something else, so `(IN 0 RR-POS-STAR)' is not
;;; citable from a bare `(fact 'zero-in-rr-pos-star)'.  This closer cites it AT
;;; the conjunct that needs it.
(define (esd-empty-close!)
  (if (equal? (dk-goal) '(IN 0 RR-POS-STAR))
      (begin (fact 'zero-in-rr-pos-star) (ass))
      (ass)))

;;; Peel the `least' conjunct goal (FORALL b (IMPLIES (AND ...) (<= t b))):
;;; `di' is greedy and lands the guard as ONE conjunction.  Returns the
;;; eigenvariable, read off the GOAL (<= t v), not off the context order.
(define (esd-peel-least!)
  (let ((landed (dk-peel!)))
    (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f))) landed)
    (caddr (dk-goal))))

;;; =====================================================================
;;; (2)  EXISTENCE.  Every subset of [0,+inf] HAS a least upper bound there.
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 's_
           (list 'IMPLIES '(SUBSET s_ RR-POS-STAR)
                 (list 'FORSOME 'bb_ (esd-lub-of 'bb_ 's_))))))
(dk-peel!)
(define esd-S (esd-set-of (dk-goal)))
(define esd-subset (list 'SUBSET esd-S 'RR-POS-STAR))

(use-em (list 'RR-BOUNDED-ABOVE esd-S)

  ;; -------------------------------------------------------------------
  ;; (b)/(c)  S HAS a real upper bound.  Split again on inhabitedness.
  (lambda ()
    (use-em (list 'FORSOME 'x (list 'IN 'x esd-S))

      ;; ---- (b) inhabited: the lub is SUP(S), the REAL supremum ----
      (lambda ()
        (let ((esd-x0 (dk-skolem! (list 'FORSOME 'x (list 'IN 'x esd-S)))))
          ;; `ai' CONSUMED the existential; rr-sup-* wants it back as a guard.
          (have! (list 'FORSOME 'x (list 'IN 'x esd-S))
                 (lambda () (ew esd-x0) (ass)))
          ;; S is a set of REALS.  The real bound is skolemized INSIDE this
          ;; lane, so the main branch keeps (RR-BOUNDED-ABOVE S) for rr-sup-in.
          (have! (list 'SUBSET esd-S 'RR)
            (lambda ()
              (let* ((ex (dk-landed-1
                          (lambda () (mac-h 'RR-BOUNDED-ABOVE
                                            (list 'RR-BOUNDED-ABOVE esd-S)))))
                     (mm (dk-skolem! ex))
                     (ub (dk-landed-1
                          (lambda () (mac-h 'RR-UPPER-BOUND
                                            (list 'RR-UPPER-BOUND esd-S mm))))))
                (dk-split! ub)
                (mac 'subset-def)
                (let ((v (dk-di-var!)))
                  (fact 'subset-mem-fwd esd-S 'RR-POS-STAR v)
                  (dk-apply! (esd-ub-of mm esd-S) v)
                  (have! (list 'AND (list 'IN v 'RR-POS-STAR) (list 'IN mm 'RR)))
                  (fact 'rr-pos-star-le-real-in-rr v mm)
                  (ass)))))
          (fact 'rr-sup-in esd-S)                       ; (IN (SUP S) RR)
          (fact 'rr-sup-upper esd-S)                    ; RR-UPPER-BOUND(S, SUP S)
          (let ((esd-sup (list 'SUP esd-S)))
            (dk-split! (dk-landed-1
                        (lambda () (mac-h 'RR-UPPER-BOUND
                                          (list 'RR-UPPER-BOUND esd-S esd-sup)))))
            ;; 0 <= SUP(S): S has a member, and that member is >= 0.
            (have! (list 'IN esd-sup 'RR-POS-STAR)
              (lambda ()
                (fact 'subset-mem-fwd esd-S 'RR-POS-STAR esd-x0)
                (fact 'rr-pos-star-nonneg esd-x0)
                (fact 'subset-mem-fwd esd-S 'RR esd-x0)
                (dk-apply! (esd-ub-of esd-sup esd-S) esd-x0)
                (fact 'rr-zero-in)
                (have! (list 'AND '(IN 0 RR)
                             (list 'AND (list 'IN esd-x0 'RR) (list 'IN esd-sup 'RR))))
                (have! (list 'AND (list '<= 0 esd-x0) (list '<= esd-x0 esd-sup)))
                (fact 'rr-leq-transitive 0 esd-x0 esd-sup)
                (let ((inst (dk-fact! 'rr-pos-star-membership esd-sup)))
                  (dk-only! inst (list 'IN esd-sup 'RR) (list '<= 0 esd-sup))
                  (prop))))
            (ew esd-sup)
            (dk-conj-close!
             (esd-lub-closer
              (lambda () (ass))
              (lambda ()
                (let ((v (dk-di-var!)))
                  (dk-apply! (esd-ub-of esd-sup esd-S) v)
                  (ass)))
              (lambda ()
                (let ((cv (esd-peel-least!)))
                  (esd-star-cases! cv
                    (lambda ()
                      (dk-split! (esd-real-case cv))
                      (have! (list 'RR-UPPER-BOUND esd-S cv)
                             (lambda () (mac 'RR-UPPER-BOUND) (dk-conj-close! (lambda () (ass)))))
                      (fact 'rr-sup-least esd-S cv)
                      (ass))
                    (lambda ()
                      (subst (list '= cv 'POS-INF))
                      (fact 'rr-pos-star-below-pos-inf esd-sup)
                      (ass))))))))))

      ;; ---- (c) empty: the lub is 0 ----
      (lambda ()
        (ew 0)
        (dk-conj-close!
         (esd-lub-closer
          (lambda () (fact 'zero-in-rr-pos-star) (ass))
          (lambda ()
            (let ((v (dk-di-var!)))
              (have! (list 'FORSOME 'x (list 'IN 'x esd-S))
                     (lambda () (ew v) (ass)))
              (ai (list 'NOT (list 'FORSOME 'x (list 'IN 'x esd-S))))))
          (lambda ()
            (let ((cv (esd-peel-least!)))
              (fact 'rr-pos-star-nonneg cv)
              (ass))))))))

  ;; -------------------------------------------------------------------
  ;; (a)  S has NO real upper bound: the lub is POS-INF.
  (lambda ()
    (ew 'POS-INF)
    (dk-conj-close!
     (esd-lub-closer
      (lambda () (fact 'pos-inf-in-rr-pos-star) (ass))
      (lambda ()
        (let ((v (dk-di-var!)))
          (fact 'subset-mem-fwd esd-S 'RR-POS-STAR v)
          (fact 'rr-pos-star-below-pos-inf v)
          (ass)))
      (lambda ()
        (let ((cv (esd-peel-least!)))
          (esd-star-cases! cv
            (lambda ()
              (dk-split! (esd-real-case cv))
              (have! (list 'RR-UPPER-BOUND esd-S cv)
                     (lambda () (mac 'RR-UPPER-BOUND) (dk-conj-close! (lambda () (ass)))))
              (have! (list 'RR-BOUNDED-ABOVE esd-S)
                     (lambda () (mac 'RR-BOUNDED-ABOVE) (ew cv) (ass)))
              (ai (list 'NOT (list 'RR-BOUNDED-ABOVE esd-S))))
            (lambda ()
              (subst (list '= cv 'POS-INF))
              (fact 'pos-inf-in-rr-pos-star)
              (fact 'rr-pos-star-le-refl 'POS-INF)
              (ass)))))))))

(qed 'esup-exists)
(topic! 'esup-exists 'analysis)
(alias! 'esup-exists "every subset of [0,+inf] has a least upper bound")

;;; =====================================================================
;;; (3)  UNIQUENESS.  Antisymmetry of <= on [0,+inf].
;;; =====================================================================

(sp (make-wff
     (list 'FORALL 's_ (list 'FORALL 'b1_ (list 'FORALL 'b2_
       (list 'IMPLIES (list 'AND (esd-lub-of 'b1_ 's_) (esd-lub-of 'b2_ 's_))
             '(= b1_ b2_)))))))
(dk-peel!)
(dk-split-all!)
(let* ((g   (dk-goal))
       (u1  (cadr g))
       (u2  (caddr g))
       (st  (esd-set-of (car (filter (lambda (f) (esd-set-of f)) (dk-asms))))))
  (have! (list 'AND (list 'IN u2 'RR-POS-STAR) (esd-ub-of u2 st)))
  (dk-apply! (esd-least-of u1 st) u2)
  (have! (list 'AND (list 'IN u1 'RR-POS-STAR) (esd-ub-of u1 st)))
  (dk-apply! (esd-least-of u2 st) u1)
  (have! (list 'AND (list 'IN u1 'RR-POS-STAR) (list 'IN u2 'RR-POS-STAR)))
  (have! (list 'AND (list '<= u1 u2) (list '<= u2 u1)))
  (fact 'rr-pos-star-le-antisymm u1 u2)
  (ass))
(qed 'esup-unique)
(topic! 'esup-unique 'analysis)
(alias! 'esup-unique "the least upper bound in [0,+inf] is unique")

;;; =====================================================================
;;; (4)  THE DEFINING PROPERTY.  This is the `iota-d' step, and the only one.
;;; =====================================================================

(define (esd-exuniq! st)
  (let* ((ex (dk-fact! 'esup-exists st))
         (w  (dk-skolem! ex)))
    (dk-split-all!)
    (ew w)
    (for-each
     (lambda (k)
       (dk-focus! k)
       (if (eq? (car (dk-goal)) 'FORALL)
           (begin
             (dk-peel!)
             (dk-split-all!)
             (let ((y (caddr (dk-goal))))
               (have! (list 'AND (esd-lub-of w st) (esd-lub-of y st)))
               (fact 'esup-unique st w y)
               (ass)))
           (dk-conj-close! (lambda () (ass)))))
     (dk-opened (lambda () (di))))))

(sp (make-wff
     (list 'FORALL 's_
           (list 'IMPLIES '(SUBSET s_ RR-POS-STAR)
                 (esd-lub-of '(ESUP s_) 's_)))))
(dk-peel!)
(define esd-P-S (esd-set-of (dk-goal)))
(mac 'ESUP)
(define esd-io (cadr (cadr (dk-goal))))        ; the IOTA term, as the engine built it
(for-each
 (lambda (k)
   (dk-focus! k)
   (if (eq? (car (dk-goal)) 'FORSOME)
       (esd-exuniq! esd-P-S)
       (ass)))
 (dk-opened (lambda () (iota-d esd-io))))
(qed 'esup-prop)
(topic! 'esup-prop 'analysis)
(alias! 'esup-prop "the defining property of the supremum in [0,+inf]")

;;; =====================================================================
;;; (5)  THE FOUR RETIRED AXIOMS, statements unchanged (head rename apart).
;;; =====================================================================

;;; esup-in -- extended-reals-pos.scm:82.
(sp (make-wff '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
                  (IN (ESUP S) RR-POS-STAR)))))
(dk-peel!)
(let ((st (cadr (dk-pick (dk-head? 'SUBSET) "the subset hypothesis"))))
  (fact 'esup-prop st)
  (dk-split-all!)
  (ass))
(qed 'esup-in)
(topic! 'esup-in 'analysis)

;;; esup-upper -- extended-reals-pos.scm:87.
(sp (make-wff '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
                  (FORALL x (IMPLIES (IN x S) (<= x (ESUP S))))))))
(let ((landed (dk-peel!)))
  (let* ((sub (dk-pick (dk-head? 'SUBSET) "the subset hypothesis"))
         (st  (cadr sub))
         (mem (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (caddr f) st)))
                       "the membership hypothesis"))
         (v   (cadr mem)))
    (fact 'esup-prop st)
    (dk-split-all!)
    (dk-apply! (esd-ub-of (list 'ESUP st) st) v)
    (ass)))
(qed 'esup-upper)
(topic! 'esup-upper 'analysis)

;;; esup-least -- extended-reals-pos.scm:94.
(sp (make-wff '(FORALL S (IMPLIES (SUBSET S RR-POS-STAR)
                  (FORALL b (IMPLIES (AND (IN b RR-POS-STAR)
                                          (FORALL x (IMPLIES (IN x S) (<= x b))))
                    (<= (ESUP S) b)))))))
(dk-peel!)
(let* ((sub (dk-pick (dk-head? 'SUBSET) "the subset hypothesis"))
       (st  (cadr sub))
       (bv  (caddr (dk-goal))))
  (fact 'esup-prop st)
  (dk-split-all!)
  (have! (list 'AND (list 'IN bv 'RR-POS-STAR) (esd-ub-of bv st)))
  (dk-apply! (esd-least-of (list 'ESUP st) st) bv)
  (ass))
(qed 'esup-least)
(topic! 'esup-least 'analysis)

;;; esup-empty -- extended-reals-pos.scm:102.  The empty sup is 0.
;;; A strict `=' is honest here: ESUP2(EMPTY-SET) is in RR-POS-STAR by
;;; esup2-in, so it denotes, and uniqueness pins it at 0.
(sp (make-wff '(= (ESUP EMPTY-SET) 0)))
(have! '(SUBSET EMPTY-SET RR-POS-STAR)
  (lambda ()
    (mac 'subset-def)
    (let ((v (dk-di-var!)))
      (fact 'empty-set-has-no-members v)
      (ai (list 'NOT (list 'IN v 'EMPTY-SET))))))
;;; Not through esup2-unique: the two laws just proved say it in four citations,
;;; and no conjunction of two descriptions has to be reassembled for `fact'.
(fact 'esup-in 'EMPTY-SET)                  ; (IN (ESUP2 EMPTY-SET) RR-POS-STAR)
(have! (esd-ub-of 0 'EMPTY-SET)              ; vacuously, 0 bounds the empty set
  (lambda ()
    (let ((v (dk-di-var!)))
      (fact 'empty-set-has-no-members v)
      (ai (list 'NOT (list 'IN v 'EMPTY-SET))))))
(have! (list 'AND '(IN 0 RR-POS-STAR) (esd-ub-of 0 'EMPTY-SET))
       (lambda () (dk-conj-close! esd-empty-close!)))
(fact 'esup-least 'EMPTY-SET 0)             ; (<= (ESUP2 EMPTY-SET) 0)
(fact 'rr-pos-star-nonneg '(ESUP EMPTY-SET)); (<= 0 (ESUP2 EMPTY-SET))
(have! '(AND (IN (ESUP EMPTY-SET) RR-POS-STAR) (IN 0 RR-POS-STAR))
       (lambda () (dk-conj-close! esd-empty-close!)))
(have! '(AND (<= (ESUP EMPTY-SET) 0) (<= 0 (ESUP EMPTY-SET))))
(fact 'rr-pos-star-le-antisymm '(ESUP EMPTY-SET) 0)
(ass)
(qed 'esup-empty)
(topic! 'esup-empty 'analysis)

;;; =====================================================================
;;; WHAT THE INTEGRATOR DOES
;;; =====================================================================
;;;
;;; 1. structure-library/extended-reals-pos.scm -- DELETE the four axioms at
;;;    :82 (esup-in), :87 (esup-upper), :94 (esup-least), :102 (esup-empty) and
;;;    put the `def-functoid' quoted at the head of this file in their place,
;;;    plus its `notation!'.  Nothing in the tree cites any of the four (grep
;;;    over *.scm: only comments and reference/*.md), so no proof moves.
;;;
;;; 2. structure-library/extended-reals-pos.scm :164 -- replace
;;;
;;;      (theory-add-axiom! *current-theory* 'rr-pos-star-add-monoid-def
;;;        '(= RR-POS-STAR-ADD-MONOID (LIST RR-POS-STAR eplus 0)))
;;;      ... (register-definitional-structure! 'RR-POS-STAR-ADD-MONOID 'COMM-MONOID)
;;;      ... (warrant! 'rr-pos-star-add-monoid-def 'well-known "...")
;;;
;;;    by the ONE form (the shape numeric-instances.scm:404 uses for
;;;    NN-ADD-MONOID; it calls register-definitional-structure! itself, so the
;;;    separate call at :178 and the warrant! at :185 both go):
;;;
;;;      (declare-instance! 'RR-POS-STAR-ADD-MONOID 'COMM-MONOID
;;;                         'rr-pos-star-add-monoid-def
;;;        '(RR-POS-STAR eplus 0))
;;;
;;;    PROBED (scratchpad/esd/step0.scm, against the band): the theorem comes
;;;    back under the SAME name with the SAME statement -- install-theorem!
;;;    says "re-installing the same statement" -- its provenance goes
;;;    `asserted' -> `definitional' (so it leaves every bill), and the three
;;;    slot macetes RR-POS-STAR-ADD-MONOID@CARR / @OPR / @IDEN appear, which do
;;;    not exist today.  Those are what `slot' needs for the ESUM work.
;;;
;;; 3. This file: rename ESUP2 -> ESUP and esup2-* -> esup-* with
;;;    scratchpad/rename-sym.py (token-aware), delete section (0) -- the
;;;    def-functoid now lives in the structure file -- and wire it into
;;;    load.scm right after theorem-library/rake-extended-order (238).
