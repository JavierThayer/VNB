;;; rake-baire.scm -- towards the BAIRE CATEGORY theorem (batch 12-F, 2026-09-20).
;;;
;;; `baire-category' (theorem-library/baire-category.scm:70, warranted `reference')
;;; is built from nested closed balls.  The construction breaks into stages, each a
;;; theorem of its own; this file holds the ones that are DONE.  The statement of
;;; `baire-category' itself is NOT attempted here and nothing below cites it.
;;;
;;; THE ROUTE, and where it stands (see the report at the end of the header):
;;;
;;;   (1) the STEP                    theorem-library/metric-closure-laws.scm,
;;;       `nowhere-dense-closed-ball' -- PROVEN.  Inside any ball, below any
;;;       prescribed positive bound on the radius, a nowhere-dense A leaves room for
;;;       a closed ball missing its closure.  This is the choice made at each stage.
;;;   (2) NESTING IS TRANSITIVE       `nested-family-monotone', below -- PROVEN.
;;;       A family gg : NN -> w with gg(succ n) subset gg(n) has gg(m) subset gg(n)
;;;       for every n <= m.  Stated for an arbitrary family, not for balls: the
;;;       content is the NN induction and nothing else.
;;;   (3) the RECURSION               NOT done.  dc-on-nn-pred over the state space
;;;       CARTESIAN(PTS s, RR-POS-STAR) -- a PAIR (centre, radius), which the tree
;;;       can form; a triple could not be (CLAUDE.md, "Open foundational items").
;;;   (4) the CENTRES ARE CAUCHY, (5) completeness gives the limit, (6) the limit is
;;;       in every closed ball (closed-set-limit-in, PROVEN in metric-closure-laws)
;;;       and hence in no ee(n).
;;;
;;; Helper prefix: rbr-.

(define (rbr-head? f h) (and (pair? f) (eq? (car f) h)))

;;; The leaf of a branching tactic whose printed GOAL contains STR.  `ni' opens
;;; base and step; here they are told apart by `gg(0)' -- NOT by `succ', which the
;;; nesting hypothesis puts in BOTH goals (one lost probe, 2026-09-20).
(define (rbr-leaf-with str ls)
  (or (any-pred (lambda (n) (substring? str (expression->string (dk-goal-of n)))) ls)
      (error "rbr-leaf-with: no leaf whose goal contains" str)))

;;; =====================================================================
;;; nested-family-monotone
;;; =====================================================================
;;; The family is TYPED (gg in FUN(NN, w)).  Without that typing neither `gg(n)'
;;; nor `gg(succ n)' is certified DEFINED, and every instantiation at one of them
;;; owes `t = t' (the LUTINS rule).  The typing is free at the use site: the closed
;;; balls of the Baire construction are members of POWER(PTS s).
;;;
;;; The induction variable m is OUTERMOST, because `ni' tests the literal shape
;;; (FORALL n (IMPLIES (IN n NN) body)).

(sp (make-wff '(FORALL m (IMPLIES (IN m NN)
   (FORALL w (FORALL gg (IMPLIES (IN gg (FUN NN w))
     (IMPLIES (FORALL n (IMPLIES (IN n NN) (SUBSET (gg (succ n)) (gg n))))
       (FORALL n (IMPLIES (IN n NN)
         (IMPLIES (<= n m) (SUBSET (gg m) (gg n)))))))))))))

(let ((ls (dk-opened (lambda () (ni)))))
  ;; ---- BASE: m = 0.  n <= 0 makes n zero, and the inclusion is reflexivity.
  ;; The two leaves are told apart by `gg(0)', NOT by `succ': the NESTING
  ;; hypothesis carries a succ in BOTH goals.
  (dk-focus! (rbr-leaf-with "gg(0)" ls))
  (dk-peel!)
  (dk-fact! 'nn-le-zero-is-zero 'n)
  (subst '(= 0 n))
  (subset-by-element!)
  (ass)
  ;; ---- STEP.  n <= succ k splits into n <= k (the induction hypothesis, then one
  ;; transitivity through gg(k)) and n = succ k (reflexivity again).
  (dk-focus! (car (filter (lambda (nd) (not (eq? nd (rbr-leaf-with "gg(0)" ls)))) ls)))
  (let* ((landed (dk-peel!))
         (ih (dk-pick (lambda (f)
                        (and (rbr-head? f 'FORALL) (rbr-head? (caddr f) 'FORALL)))
                      "the induction hypothesis"))
         (hyp (dk-pick (lambda (f)
                         (and (rbr-head? f 'FORALL) (rbr-head? (caddr f) 'IMPLIES)
                              (rbr-head? (caddr (caddr f)) 'SUBSET)))
                       "the one-step nesting hypothesis"))
         (kv  (cadr (cadr (cadr (dk-goal))))))   ; goal (SUBSET (gg (succ k)) (gg n))
    (fact 'nn-succ-closed kv)
    (fact 'fun-apply-type-c 'gg 'NN 'w 'n)
    (fact 'fun-apply-type-c 'gg 'NN 'w kv)
    (fact 'fun-apply-type-c 'gg 'NN 'w (list 'succ kv))
    (dk-fact! 'nn-le-succ-cases kv 'n)
    (use-cases (list (list '<= 'n kv) (list '= 'n (list 'succ kv)))
      (lambda ()
        (dk-apply! (dk-apply! ih 'w 'gg) 'n)     ; (SUBSET (gg k) (gg n))
        (dk-apply! hyp kv)                       ; (SUBSET (gg (succ k)) (gg k))
        (fact 'subset-trans (list 'gg (list 'succ kv)) (list 'gg kv) '(gg n))
        (ass))
      (lambda ()
        (subst (list '= (list 'succ kv) 'n))
        (subset-by-element!)
        (ass)))))
(qed 'nested-family-monotone)
(gloss! 'nested-family-monotone
  "A decreasing NN-indexed family is decreasing at every gap: if gg(succ n) is
   contained in gg(n) for all n, then gg(m) is contained in gg(n) whenever n <= m.
   Stated for a typed family gg in FUN(NN, w) -- the typing is what certifies
   gg(n) as DEFINED, and it is free wherever the family is a family of sets.")
(topic! 'nested-family-monotone 'plumbing)
