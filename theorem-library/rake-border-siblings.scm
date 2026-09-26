;;; rake-border-siblings.scm -- the three remaining BORDER entry read-offs,
;;; PROVEN: border-entry-11, border-entry-1j, border-entry-i1.
;;;
;;; These are the siblings of border-entry-block / border-entry-block2, proven
;;; in theorem-library/rake-border-entry.scm on 2026-09-18.  BORDER(A,b,M,p,q)
;;; is installed DIRECTLY (structure-library/mat-equiv.scm:66) as
;;;   MATOF(succ p, succ q,
;;;     vnb-lambda([i,j], [1,succ p] x [1,succ q],
;;;       IF i = 1 THEN (IF j = 1 THEN b ELSE ZERO A)
;;;                ELSE (IF j = 1 THEN ZERO A ELSE ENTRY(M, i-1, j-1))))
;;; and each read-off is the same lane: `mac' the constructor, cite
;;; entry-of-matof (with border-entries-defined discharging its definedness
;;; hypothesis), `lam-b' the pair-lambda, then resolve the IF tower with
;;; if-true / if-false against the context.  This file is the fourth copy of
;;; that resolver (`rbs-tower!'); it belongs in driver-kit.scm.
;;;
;;; WHAT IS NEW here, relative to the block read-offs: both index branches are
;;; taken at the LITERAL index 1, so
;;;   * the interval membership of the literal is `one-in-interval'
;;;     (1 in [1, succ n], theorem-library/rake-intervals.scm), not
;;;     succ-in-interval;
;;;   * the tower's condition at that index is the ground `(= 1 1)', which is in
;;;     no context, so it is put there by a one-line `have!' closed by `rfl'
;;;     before the resolver runs -- `use-em' on a DECIDED proposition ERRORS
;;;     (CLAUDE.md, "The tactics' real behaviour").
;;;
;;; STATEMENT AUDIT (CLAUDE.md, "the species of FALSE or underdetermined
;;; support").  All three carry, since the 2026-09-16 guarding, the full
;;; border-type premise set -- (IS-RING A), (IN p NN), (IN q NN),
;;; (IN b (CARR A)), (IN M (MAT p q (CARR A))) -- ahead of the index premises.
;;; That is what makes the strict `=' legitimate: p, q in NN types the box,
;;; M in MAT(p,q,CARR A) makes every tabulated value a SET (border-entries-
;;; defined), and IS-RING A makes ZERO(A) denote; nothing is left untyped.  The
;;; right-hand sides are b and ZERO(A), both typed in the context.  Statements
;;; copied LITERALLY from structure-library/mat-equiv.scm:96, :102, :110.
;;;
;;; LOAD WINDOW [247, 380).
;;;   lo = 247: the latest citation is `border-entries-defined'
;;;             (theorem-library/rake-border-entry, 246).  Then entry-of-matof
;;;             (theorem-library/tuple-tabulation, 245), one-in-interval
;;;             (theorem-library/rake-intervals, 224), ring-zero-in
;;;             (structure-library/ring, 23), nn-succ-closed
;;;             (structure-library/number-systems), and the BORDER macete
;;;             (structure-library/mat-equiv, 99).
;;;   hi = 380: theorem-library/border-mult-proof is the earliest citer of all
;;;             three (border-assembly-proof 381, bordered-eq-border-proof 382,
;;;             smith-staircase-proof 385 follow).
;;;   (Positions are 0-based indices over load.scm's file entries as of
;;;    2026-09-19; rake-border-entry's own header, written 2026-09-18, counted
;;;    five lower because five files have been wired since.)
;;;
;;; Helper prefix: rbs-.

(define (rbs-qed! name . opt-topic)
  (if (proof-done? *ps*)
      (begin (qed name)
             (topic! name (if (pair? opt-topic) (car opt-topic) 'algebra)))
      (begin
        (display "\n*** rake-border-siblings: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-border-siblings: unfinished" name))))

;;; if-true / if-false open exactly two leaves: the CONDITION (or its negation)
;;; and the MAIN goal, which gains (= <IF> <branch>).  Discriminate on the GOAL,
;;; never on where focus landed; close the condition leaf from the context and
;;; stay on the main one.  (rake-border-entry.scm's `r6b-if!'.)
(define (rbs-if! true? ift)
  (let* ((want   (if true? (cadr ift) (list 'NOT (cadr ift))))
         (opened (dk-opened (lambda () (if true? (if-true ift) (if-false ift)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "rbs-if!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))))

;;; Resolve the IF tower sitting at position `get' of the goal: decide each
;;; condition against the context and hand the leaf to `close!' when the tower
;;; is gone.  Unlike rake-border-entry's copy there is no `use-em' arm: every
;;; condition of these three read-offs is decided by the context (the caller
;;; puts the ground `(= 1 1)' there first), and a `use-em' on a decided
;;; proposition would ERROR rather than split.
(define (rbs-tower! get close! depth)
  (if (> depth 6) (error "rbs-tower!: tower deeper than 6"))
  (let ((t (get)))
    (if (and (pair? t) (eq? (car t) 'IF))
        (let ((c (cadr t)))
          (cond ((member c (dk-asms))
                 (rbs-if! #t t) (subst (list '= t (caddr t)))
                 (rbs-tower! get close! (+ depth 1)))
                ((member (list 'NOT c) (dk-asms))
                 (rbs-if! #f t) (subst (list '= t (cadddr t)))
                 (rbs-tower! get close! (+ depth 1)))
                (#t (error "rbs-tower!: context decides neither the condition nor its negation"
                           (expression->string c)))))
        (close!))))

;;; The ground condition `(= 1 1)', landed as an assumption so the resolver can
;;; take the true branch.  (`rfl' certifies the literal 1 as DEFINED.)
(define (rbs-have-one-eq-one!)
  (if (not (member '(= 1 1) (dk-asms)))
      (begin
        (have! '(= 1 1) (lambda () (rfl)))
        (dk-focus-having! '(= 1 1)))))

;;; The shared opening: peel, type the box dimensions, unfold BORDER, and
;;; replace ENTRY(MATOF(...), iv, jv) by the tabulator applied to iv, jv.
;;; Leaves focus on the main branch with the beta-reduced IF tower as goal.
(define (rbs-open! iv jv)
  (fact 'nn-succ-closed 'p)
  (fact 'nn-succ-closed 'q)
  (mac 'BORDER)
  (let* ((lhs (cadr (dk-goal)))            ; (ENTRY (MATOF (succ p) (succ q) LAM) iv jv)
         (mf  (cadr lhs))
         (lam (cadddr mf))
         (eqn (list '= lhs (list lam iv jv))))
    (have! eqn
      (lambda ()
        (fact 'border-entries-defined 'A 'b 'M 'p 'q)
        (fact 'entry-of-matof '(succ p) '(succ q) lam iv jv)
        (ass)))
    (dk-focus-having! eqn)
    (subst eqn))
  (lam-b))

;;; ---- border-entry-11 ---------------------------------------------------
;;; Statement copied from structure-library/mat-equiv.scm:96, unchanged.
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q
     (IMPLIES (IS-RING A) (IMPLIES (IN p NN) (IMPLIES (IN q NN) (IMPLIES (IN b (CARR A)) (IMPLIES (IN M (MAT p q (CARR A)))
     (= (ENTRY (BORDER A b M p q) 1 1) b)))))))))))))
(dk-peel!)
(fact 'one-in-interval 'p)
(fact 'one-in-interval 'q)
(rbs-open! 1 1)
(rbs-have-one-eq-one!)
(rbs-tower! (lambda () (cadr (dk-goal)))
            (lambda () (if (member (dk-goal) (dk-asms)) (ass) (rfl)))
            0)
(rbs-qed! 'border-entry-11)

;;; ---- border-entry-1j ---------------------------------------------------
;;; Statement copied from structure-library/mat-equiv.scm:102, unchanged.
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL j
     (IMPLIES (IS-RING A) (IMPLIES (IN p NN) (IMPLIES (IN q NN) (IMPLIES (IN b (CARR A)) (IMPLIES (IN M (MAT p q (CARR A)))
     (IMPLIES (IN j (INTERVAL 1 (succ q))) (IMPLIES (NOT (= j 1))
       (= (ENTRY (BORDER A b M p q) 1 j) (ZERO A)))))))))))))))))
(dk-peel!)
(fact 'one-in-interval 'p)
(fact 'ring-zero-in 'A)
(rbs-open! 1 'j)
(rbs-have-one-eq-one!)
(rbs-tower! (lambda () (cadr (dk-goal)))
            (lambda () (if (member (dk-goal) (dk-asms)) (ass) (rfl)))
            0)
(rbs-qed! 'border-entry-1j)

;;; ---- border-entry-i1 ---------------------------------------------------
;;; Statement copied from structure-library/mat-equiv.scm:110, unchanged.
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i
     (IMPLIES (IS-RING A) (IMPLIES (IN p NN) (IMPLIES (IN q NN) (IMPLIES (IN b (CARR A)) (IMPLIES (IN M (MAT p q (CARR A)))
     (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
       (= (ENTRY (BORDER A b M p q) i 1) (ZERO A)))))))))))))))))
(dk-peel!)
(fact 'one-in-interval 'q)
(fact 'ring-zero-in 'A)
(rbs-open! 'i 1)
(rbs-have-one-eq-one!)
(rbs-tower! (lambda () (cadr (dk-goal)))
            (lambda () (if (member (dk-goal) (dk-asms)) (ass) (rfl)))
            0)
(rbs-qed! 'border-entry-i1)

;;; ---- succ-nn-minus-1 ---------------------------------------------------
;;; succ(i - 1) = i for i in NN with 1 <= i -- the inverse of monus-by-1 on
;;; positive indices, and the other half of the pair whose first half
;;; (nn-minus-succ-1: NN-MINUS(succ z, 1) = z) rake-intervals.scm proved.
;;;
;;; AUDIT: `succ' is applied to NN-MINUS(i, 1), and NN-MINUS is total on NN, so
;;; with (IN i NN) the succ argument is typed -- the "succ off NN is
;;; uninterpreted" species does not apply.  The `<= 1 i' guard is what makes the
;;; equation true (at i = 0 it fails: NN-MINUS(0,1) = 0 and succ 0 = 1 /= 0).
;;; Statement copied from structure-library/order-lemmas.scm:266, unchanged.
;;;
;;; ROUTE: 1 <= i makes i a successor (nn-pos-is-succ), and on a successor the
;;; monus is stripped by nn-minus-succ-1.  Two rewrites and an rfl.
(sp (make-wff
  '(FORALL i (IMPLIES (IN i NN) (IMPLIES (<= 1 i) (= (succ (NN-MINUS i 1)) i))))))
(dk-peel!)
(let* ((rbs-ex (dk-fact! 'nn-pos-is-succ 'i))     ; forsome q. q in NN and i = succ q
       (rbs-w  (dk-skolem! rbs-ex)))              ; splits the AND, returns the witness
  (fact 'nn-minus-succ-1 rbs-w)                   ; NN-MINUS(succ w, 1) = w
  (subst (list '= 'i (list 'succ rbs-w)))
  (subst (list '= (list 'NN-MINUS (list 'succ rbs-w) 1) rbs-w))
  (rfl))
(rbs-qed! 'succ-nn-minus-1 'inequalities)
