;;; rake-border-entry.scm -- the BORDER block entry read-offs, PROVEN.
;;;
;;; WHAT BORDER IS (structure-library/mat-equiv.scm).  BORDER(A,b,M,p,q) is the
;;; (succ p)-by-(succ q) matrix with b in the corner, zeros in the rest of row 1
;;; and column 1, and M in the lower-right block -- installed DIRECTLY as
;;; MATOF(succ p, succ q, vnb-lambda([i,j], ..., <IF tower over i = 1, j = 1>)).
;;; Three of its five entry read-offs are supports; the two BLOCK ones are here.
;;;
;;; THE LANE is elem-entry-readoffs.scm's: `mac' the constructor, cite
;;; entry-of-matof, `lam-b' the pair-lambda, resolve the IF tower with
;;; if-true/if-false against the context.  What it needs and did not have is
;;; BORDER's own DEFINEDNESS lemma -- entry-of-matof has asked, since the
;;; SIZE/MAT surgery of 2026-09-16, for "every tabulated value is a SET".  Two of
;;; BORDER's three branches are b and ZERO(A) (membership-implies-sethood off
;;; IS-RING); the third is ENTRY(M, i-1, j-1), which needs `entry-in-carrier' at
;;; an index supplied by `pred-in-interval'.  rake-algebra3.scm's closing block
;;; named pred-in-interval as the blocker; it is PROVEN since rake batch K
;;; (theorem-library/rake-intervals.scm, guarded on the bound in NN), so the
;;; lemma is reachable and is the first theorem below.
;;;
;;; TWO theorems, not one.  `border-entry-block' (mat-equiv.scm:118) was the
;;; assignment; `border-entry-block2' (:130) is the SAME driver with general
;;; indices i, j /= 1 instead of succ i, succ j, and it is the one the tree
;;; actually cites (border-mult-proof, border-assembly-proof,
;;; smith-staircase-proof, bordered-eq-border-proof -- six sites; `border-entry-
;;; block' has NO citer at all).  block2 is proven first and `border-entry-block'
;;; is four citations off it: succ-in-interval puts succ i in [1, succ p],
;;; succ-not-one gives succ i /= 1, and nn-minus-succ-1 strips the monus.
;;;
;;; DEFINEDNESS.  The tower resolution ends at ENTRY(M, i-1, j-1) = ENTRY(M,
;;; i-1, j-1), and `rfl' refuses an ENTRY with no range typing, so
;;; entry-in-carrier is cited BEFORE the resolver runs rather than after.
;;;
;;; LOAD WINDOW [241, 363).
;;;   lo = 241: the latest citation is `entry-of-matof'
;;;             (theorem-library/tuple-tabulation, 240).  Then pred-in-interval /
;;;             succ-in-interval / succ-not-one / nn-minus-succ-1
;;;             (theorem-library/rake-intervals, 222), entry-in-carrier
;;;             (theorem-library/entry-in-carrier, 173), interval-elt-in-nn
;;;             (theorem-library/interval-basics, 151), ring-zero-in
;;;             (structure-library/ring, 23), the BORDER macete
;;;             (structure-library/mat-equiv, 101).
;;;   hi = 363: theorem-library/border-mult-proof is the earliest citer of
;;;             border-entry-block2.
;;;
;;; Helper prefix: r6b-.

(define (r6b-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'algebra))
      (begin
        (display "\n*** rake-border-entry: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "rake-border-entry: unfinished" name))))

;;; if-true / if-false open exactly two leaves: the CONDITION (or its negation)
;;; and the MAIN goal, which gains (= <IF> <branch>).  Discriminate on the GOAL,
;;; never on where focus landed; close the condition leaf from the context and
;;; stay on the main one.  (elem-entry-readoffs.scm's `eer-if!', which its own
;;; header says belongs in driver-kit.scm; this is the third copy.)
(define (r6b-if! true? ift)
  (let* ((want   (if true? (cadr ift) (list 'NOT (cadr ift))))
         (opened (dk-opened (lambda () (if true? (if-true ift) (if-false ift)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "r6b-if!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (ass)
    (dk-focus! (car mains))))

;;; Resolve the IF tower sitting at position `get' of the goal: decide each
;;; condition against the context, `use-em' on one it does not decide, and hand
;;; the leaf to `close!' when the tower is gone.
(define (r6b-tower! get close! depth)
  (if (> depth 6) (error "r6b-tower!: tower deeper than 6"))
  (let ((t (get)))
    (if (and (pair? t) (eq? (car t) 'IF))
        (let ((c (cadr t)))
          (cond ((member c (dk-asms))
                 (r6b-if! #t t) (subst (list '= t (caddr t)))
                 (r6b-tower! get close! (+ depth 1)))
                ((member (list 'NOT c) (dk-asms))
                 (r6b-if! #f t) (subst (list '= t (cadddr t)))
                 (r6b-tower! get close! (+ depth 1)))
                (#t (use-em c
                      (lambda () (r6b-tower! get close! (+ depth 1)))
                      (lambda () (r6b-tower! get close! (+ depth 1)))))))
        (close!))))

;;; BORDER's tabulator, verbatim from structure-library/mat-equiv.scm.
(define r6b-blam
  '(VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 (succ p)) (INTERVAL 1 (succ q)))
     (IF (= i 1)
         (IF (= j 1) b (ZERO A))
         (IF (= j 1) (ZERO A) (ENTRY M (NN-MINUS i 1) (NN-MINUS j 1))))))

;;; ---- border-entries-defined -------------------------------------------
;;; entry-of-matof's definedness hypothesis for BORDER: the tabulator's value at
;;; every index pair of the box is a SET.
(sp (make-wff
  (forall-guarded '(A b M p q)
      '((IS-RING A) (IN p NN) (IN q NN) (IN b (CARR A)) (IN M (MAT p q (CARR A))))
    (list 'FORALL 'i_
      (list 'IMPLIES '(IN i_ (INTERVAL 1 (succ p)))
        (list 'FORALL 'j_
          (list 'IMPLIES '(IN j_ (INTERVAL 1 (succ q)))
            (list 'IN (list r6b-blam 'i_ 'j_) 'SET))))))))
(dk-peel!)
(fact 'ring-zero-in 'A)
(fact 'membership-implies-sethood 'b '(CARR A))
(fact 'membership-implies-sethood '(ZERO A) '(CARR A))
(lam-b)
(r6b-tower!
  (lambda () (cadr (dk-goal)))
  (lambda ()
    (let ((v (cadr (dk-goal))))
      (if (and (pair? v) (eq? (car v) 'ENTRY))
          (begin                                  ; the i,j /= 1 branch
            (fact 'pred-in-interval 'p 'i_)
            (fact 'pred-in-interval 'q 'j_)
            (fact 'entry-in-carrier 'p 'q '(CARR A) 'M '(NN-MINUS i_ 1) '(NN-MINUS j_ 1))
            (fact 'membership-implies-sethood v '(CARR A))
            (ass))
          (ass))))                                ; b, or ZERO(A)
  0)
(r6b-qed! 'border-entries-defined)

;;; ---- border-entry-block2 ----------------------------------------------
;;; Statement copied from structure-library/mat-equiv.scm:130, unchanged.
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IS-RING A) (IMPLIES (IN p NN) (IMPLIES (IN q NN) (IMPLIES (IN b (CARR A)) (IMPLIES (IN M (MAT p q (CARR A)))
     (IMPLIES (IN i (INTERVAL 1 (succ p))) (IMPLIES (NOT (= i 1))
     (IMPLIES (IN j (INTERVAL 1 (succ q))) (IMPLIES (NOT (= j 1))
       (= (ENTRY (BORDER A b M p q) i j) (ENTRY M (NN-MINUS i 1) (NN-MINUS j 1)))))))))))))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'p)
(fact 'nn-succ-closed 'q)
(mac 'BORDER)
(let* ((lhs (cadr (dk-goal)))                 ; (ENTRY (MATOF (succ p) (succ q) LAM) i j)
       (mf  (cadr lhs))
       (lam (cadddr mf))
       (eqn (list '= lhs (list lam 'i 'j))))
  (have! eqn
    (lambda ()
      (fact 'border-entries-defined 'A 'b 'M 'p 'q)
      (fact 'entry-of-matof '(succ p) '(succ q) lam 'i 'j)
      (ass)))
  (dk-focus-having! eqn)
  (subst eqn))
(lam-b)
(fact 'pred-in-interval 'p 'i)
(fact 'pred-in-interval 'q 'j)
(fact 'entry-in-carrier 'p 'q '(CARR A) 'M '(NN-MINUS i 1) '(NN-MINUS j 1))
(r6b-tower! (lambda () (cadr (dk-goal)))
            (lambda () (if (member (dk-goal) (dk-asms)) (ass) (rfl)))
            0)
(r6b-qed! 'border-entry-block2)

;;; ---- border-entry-block ------------------------------------------------
;;; Statement copied from structure-library/mat-equiv.scm:118, unchanged.
(sp (make-wff
  '(FORALL A (FORALL b (FORALL M (FORALL p (FORALL q (FORALL i (FORALL j
     (IMPLIES (IS-RING A) (IMPLIES (IN p NN) (IMPLIES (IN q NN) (IMPLIES (IN b (CARR A)) (IMPLIES (IN M (MAT p q (CARR A)))
     (IMPLIES (IN i (INTERVAL 1 p)) (IMPLIES (IN j (INTERVAL 1 q))
       (= (ENTRY (BORDER A b M p q) (succ i) (succ j)) (ENTRY M i j))))))))))))))))))
(dk-peel!)
(fact 'interval-elt-in-nn 1 'p 'i)
(fact 'interval-elt-in-nn 1 'q 'j)
(fact 'succ-in-interval 'p 'i)
(fact 'succ-in-interval 'q 'j)
(fact 'succ-not-one 'p 'i)
(fact 'succ-not-one 'q 'j)
(fact 'entry-in-carrier 'p 'q '(CARR A) 'M 'i 'j)
(fact 'border-entry-block2 'A 'b 'M 'p 'q '(succ i) '(succ j))
(have! '(= (ENTRY M (NN-MINUS (succ i) 1) (NN-MINUS (succ j) 1)) (ENTRY M i j))
  (lambda ()
    (fact 'nn-minus-succ-1 'i)
    (subst '(= (NN-MINUS (succ i) 1) i))
    (fact 'nn-minus-succ-1 'j)
    (subst '(= (NN-MINUS (succ j) 1) j))
    (rfl)))
(dk-focus-having! '(= (ENTRY M (NN-MINUS (succ i) 1) (NN-MINUS (succ j) 1)) (ENTRY M i j)))
(subst '(= (ENTRY (BORDER A b M p q) (succ i) (succ j))
           (ENTRY M (NN-MINUS (succ i) 1) (NN-MINUS (succ j) 1))))
(ass)
(r6b-qed! 'border-entry-block)
