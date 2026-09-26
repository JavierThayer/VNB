;;; makeset-basics.scm -- reading membership out of a literal brace set.
;;;
;;; `{a, b}' is surface sugar for (MAKE-SET (LIST a b)) (parser.scm), so it is
;;; the form a user types -- and until now the only way to reason about it was
;;; `make-set-membership' itself, whose right-hand side is an EXISTENTIAL OVER
;;; INDICES:
;;;
;;;   x in MAKE-SET(L)  iff  x in SET and
;;;                          exists i in NN. 1 <= i <= LENGTH(L) and NTH(i,L) = x
;;;
;;; Every concrete question about `{a,b}' therefore began with an index witness,
;;; a LENGTH reduction and an NTH reduction.  This file does that once and
;;; exposes the answer as a disjunction:
;;;
;;;   ms-index-2            i in NN, 1 <= i <= 2  =>  i = 1 or i = 2
;;;   ms-nth-2              ... =>  NTH(i,[a,b]) = a  or  NTH(i,[a,b]) = b
;;;   makeset2-membership   x in {a,b}  iff  x in SET and (x = a or x = b)
;;;   ms-eq-symm            x = y  iff  y = x
;;;
;;; ms-eq-symm IS NOT `eq-symm'.  There is no `eq-symm' in the library -- it is
;;; installed only inside test-suite.scm, as a fixture -- yet four proof files
;;; (mvt-bounds, rolle, deriv-monotone, deriv-constant) contain lines of the form
;;; `(quietly (lambda () (fact 'eq-symm ...)))' commented "flip EQ1".  `fact' on
;;; an unknown name WARNS and continues, and `quietly' swallows the warning, so
;;; those lines are silent no-ops and those proofs close by some other route.
;;; A separate name is used here deliberately: installing `eq-symm' under its own
;;; name would make four dormant citations start firing, which is a change to
;;; four proofs that has nothing to do with this file.
;;;
;;; The 2-element case is written out rather than derived from a general
;;; cons-recursion on MAKE-SET, because the whole point is the literal `{a,b}'
;;; a user types.  The second half of that reason -- "a general law wants a LIST
;;; recursion the theory does not have" -- was true until 2026-08-13 and is now
;;; FALSE: structure-library/list-recursion.scm supplies CONS and `makeset-cons',
;;; and theorem-library/tuples-induction.scm proves the induction principle.  The
;;; general law is therefore reachable, and these hand-written 2-element lemmas
;;; are the thing it would retire; they are kept because the library still cites
;;; them (card-pair, makeset2-split), not because the machinery is missing.

;;; --- file-local helpers (ms-- prefix) ------------------------------------

(define (ms--peel!)
  (let loop ()
    (let ((g (dk-goal)))
      (if (and (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop))))))

(define (ms--first h)
  (let ((fs (filter (dk-head? h) (dk-asms))))
    (if (null? fs) (error "ms--first: nothing with head" h) (car fs))))

;;; split every conjunction in the context, to exhaustion
(define (ms--split-all!)
  (let loop ()
    (let ((ands (filter (dk-head? 'AND) (dk-asms))))
      (if (pair? ands) (begin (ai (car ands)) (loop))))))

;;; close an AND-tree of context facts and ground arithmetic
(define (ms--close!)
  (let ((g (dk-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (l) (dk-focus! l) (ms--close!))
                 (dk-opened (lambda () (di)))))
      ((any-pred (lambda (f) (alpha-equiv? f g)) (dk-asms)) (ass))
      (else (arith)))))

;;; A case split on `p or p'.  pairing-membership at (a,a) lands `x = a or x = a',
;;; whose two disjuncts are the SAME formula, so OR-elim posts two case nodes
;;; that hash-cons to ONE (same assertion, same context).  `use-cases' with two
;;; lanes then runs the second lane on a node the first lane has already
;;; justified, re-focusing it through `dk-focus!' -- which, on a node that is no
;;; longer a leaf, moves the focus and records NOTHING (driver-kit.scm:164).  The
;;; printed page lacked that move and replayed lane 2 against the engine-chosen
;;; leaf; the page-audit gate reported makeset2-split with two leaves open
;;; (2026-09-15).  One case, one lane: the goal here is the AND from
;;; makeset2-membership, so split it and close each conjunct by name.
(define (ms--same-case! or-form intro)
  (let ((cases (dk-opened (lambda () (ai or-form)))))
    (if (not (= (length cases) 1))
        (error "ms--same-case!: expected ONE case leaf, got" (length cases)))
    (dk-focus! (car cases))
    (for-each (lambda (l)
                (dk-focus! l)
                (if (equal? (dk-goal) '(IN x_ SET)) (ass) (begin (intro) (ass))))
              (dk-opened (lambda () (di))))))

;;; --------------------------------------------------------------------
;;; ms-eq-symm:  equality is symmetric.
;;;
;;; Not vacuous under PARTIAL equality: `(= x y)' asserts both sides defined,
;;; so in each direction the hypothesis is exactly the definedness witness
;;; `rfl' needs (asm-establishes-defined?, primitive-inferences.scm).
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL x_ (FORALL y_ (IFF (= x_ y_) (= y_ x_))))))
(ms--peel!)
(for-each
 (lambda (l)
   (dk-focus! l)
   (let* ((g (dk-goal))
          (lhs (cadr g)) (rhs (caddr g)))
     ;; goal (= u v) with (= v u) in context: rewrite u to v and reflect
     (subst (list '= rhs lhs))
     (rfl)))
 (dk-opened (lambda () (di))))
(qed 'ms-eq-symm)
(topic! 'ms-eq-symm 'plumbing)

;;; --------------------------------------------------------------------
;;; ms-index-2:  an index into a 2-tuple is 1 or 2.
;;;
;;; `nn-le-succ-cases' is keyed on (succ k), and the auto-detach in `fact'
;;; compares assumptions by ALPHA-EQUIVALENCE -- it does not collapse numerals
;;; the way a macete's `condition-holds?' does.  So (<= i_ 2) in the context does
;;; NOT discharge the antecedent (<= i_ (succ 1)); the bridge is landed by hand.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL i_ (IMPLIES (IN i_ NN)
     (IMPLIES (<= 1 i_) (IMPLIES (<= i_ 2) (OR (= i_ 1) (= i_ 2))))))))
(ms--peel!)
(fact 'nn-one-in)
(have! '(= (succ 1) 2) (lambda () (arith)))
(have! '(<= i_ (succ 1)) (lambda () (subst '(= (succ 1) 2)) (ass)))
(dk-fact! 'nn-le-succ-cases 1 'i_)
(use-cases (list '(<= i_ 1) '(= i_ (succ 1)))
  (lambda ()
    (have! '(= i_ 1) (lambda () (fact 'nn-le-antisym 'i_ 1) (ass)))
    (oi-l) (ass))
  (lambda ()
    (oi-r)
    (have! '(= 2 (succ 1)) (lambda () (arith)))
    (subst '(= 2 (succ 1)))
    (ass)))
(qed 'ms-index-2)
(topic! 'ms-index-2 'combinatorial)

;;; --------------------------------------------------------------------
;;; ms-nth-2:  an entry of [a,b] is a or b.
;;;
;;; The index equation is `subst'ed into the GOAL -- which is where the NTH
;;; sits -- and `nth-r' then reduces the literal spine.  Doing it the other way
;;; round (rewriting the hypothesis) is not available: `subst' is goal-only.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL a_ (FORALL b_ (FORALL i_
     (IMPLIES (IN i_ NN)
       (IMPLIES (<= 1 i_) (IMPLIES (<= i_ 2)
         (OR (= (NTH i_ (LIST a_ b_)) a_)
             (= (NTH i_ (LIST a_ b_)) b_))))))))))
(ms--peel!)
(dk-fact! 'ms-index-2 'i_)
(use-cases (list '(= i_ 1) '(= i_ 2))
  (lambda () (subst '(= i_ 1)) (nth-r) (oi-l) (rfl))
  (lambda () (subst '(= i_ 2)) (nth-r) (oi-r) (rfl)))
(qed 'ms-nth-2)
(topic! 'ms-nth-2 'combinatorial)

;;; --------------------------------------------------------------------
;;; makeset2-membership:  x in {a,b}  iff  x in SET and (x = a or x = b).
;;;
;;; The (IN x SET) conjunct is not decoration: it is the sethood guard the
;;; 2026-08-13 soundness repair put on make-set-membership, and without it a
;;; proper class would be a member of {a,b} (see test-suite-negative.scm 2b).
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL x_ (FORALL a_ (FORALL b_
     (IFF (IN x_ (MAKE-SET (LIST a_ b_)))
          (AND (IN x_ SET) (OR (= x_ a_) (= x_ b_)))))))))
(ms--peel!)

(for-each
 (lambda (l)
   (dk-focus! l)
   (cond
     ;; (<=)  x in SET and (x = a or x = b)  =>  x in {a,b}
     ((and (pair? (dk-goal)) (eq? (car (dk-goal)) 'IN))
      (ms--split-all!)
      (mac 'make-set-membership)
      (for-each
       (lambda (m)
         (dk-focus! m)
         (if (equal? (dk-goal) '(IN x_ SET))
             (ass)
             (use-cases (list '(= x_ a_) '(= x_ b_))
               (lambda ()
                 (mac-h 'ms-eq-symm '(= x_ a_))
                 (ew 1) (len-r) (nth-r) (ms--close!))
               (lambda ()
                 (mac-h 'ms-eq-symm '(= x_ b_))
                 (ew 2) (len-r) (nth-r) (ms--close!)))))
       (dk-opened (lambda () (di)))))
     ;; (=>)  x in {a,b}  =>  x in SET and (x = a or x = b)
     (else
      (mac-h 'make-set-membership '(IN x_ (MAKE-SET (LIST a_ b_))))
      (ms--split-all!)
      (ai (ms--first 'FORSOME))
      (ms--split-all!)
      ;; the witness index is READ OFF the landed equation, never guessed:
      ;; `ai' names the eigenvariable and the name is not predictable.
      (let* ((eq  (car (filter (lambda (f)
                                 (and (pair? f) (eq? (car f) '=)
                                      (pair? (cadr f)) (eq? (car (cadr f)) 'NTH)))
                               (dk-asms))))
             (idx (cadr (cadr eq)))
             (nth (cadr eq)))
        (have! '(= 2 (LENGTH (LIST a_ b_))) (lambda () (len-r) (rfl)))
        (have! (list '<= idx 2)
               (lambda () (subst '(= 2 (LENGTH (LIST a_ b_)))) (ass)))
        (dk-fact! 'ms-nth-2 'a_ 'b_ idx)
        (mac-h 'ms-eq-symm eq)                    ; (= nth x) -> (= x nth)
        (for-each
         (lambda (m)
           (dk-focus! m)
           (if (equal? (dk-goal) '(IN x_ SET))
               (ass)
               (use-cases (list (list '= nth 'a_) (list '= nth 'b_))
                 (lambda () (oi-l) (subst (list '= 'x_ nth)) (ass))
                 (lambda () (oi-r) (subst (list '= 'x_ nth)) (ass)))))
         (dk-opened (lambda () (di))))))))
 (dk-opened (lambda () (di))))
(qed 'makeset2-membership)
(topic! 'makeset2-membership 'combinatorial)

;;; --------------------------------------------------------------------
;;; makeset2-split:  {a,b} = {a} u {b}, in the PAIR form card-insert speaks.
;;;
;;; card-insert (cardinality.scm) is stated over UNION(A, PAIR(x,x)) while the
;;; surface writes MAKE-SET; cardinality.scm:48 flags that mismatch itself
;;; (REVIEW.md G-10).  This is the bridge, by class-extensionality over
;;; makeset2-membership and pairing-membership.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET) (FORALL b_ (IMPLIES (IN b_ SET)
     (= (MAKE-SET (LIST a_ b_)) (UNION (PAIR a_ a_) (PAIR b_ b_)))))))))
(ms--peel!)
(have! '(AND (IN a_ SET) (IN a_ SET)))
(have! '(AND (IN b_ SET) (IN b_ SET)))
(dk-fact! 'pairing-membership 'a_ 'a_)
(dk-fact! 'pairing-membership 'b_ 'b_)

(have! '(FORALL x_ (IFF (IN x_ (MAKE-SET (LIST a_ b_)))
                        (IN x_ (UNION (PAIR a_ a_) (PAIR b_ b_)))))
  (lambda ()
    (di)
    (for-each
     (lambda (l)
       (dk-focus! l)
       (cond
         ;; x in {a,b}  =>  x in {a} u {b}
         ((equal? (dk-goal) '(IN x_ (UNION (PAIR a_ a_) (PAIR b_ b_))))
          (mac-h 'makeset2-membership '(IN x_ (MAKE-SET (LIST a_ b_))))
          (ms--split-all!)
          (mac 'union-membership)
          (use-cases (list '(= x_ a_) '(= x_ b_))
            (lambda () (oi-l) (mac 'pairing-membership) (oi-l) (ass))
            (lambda () (oi-r) (mac 'pairing-membership) (oi-l) (ass))))
         ;; x in {a} u {b}  =>  x in {a,b}
         (else
          (mac-h 'union-membership '(IN x_ (UNION (PAIR a_ a_) (PAIR b_ b_))))
          (mac 'makeset2-membership)
          (use-cases (list '(IN x_ (PAIR a_ a_)) '(IN x_ (PAIR b_ b_)))
            (lambda ()
              (fact 'membership-implies-sethood 'x_ '(PAIR a_ a_))
              (mac-h 'pairing-membership '(IN x_ (PAIR a_ a_)))
              (ms--split-all!)
              (ms--same-case! '(OR (= x_ a_) (= x_ a_)) oi-l))
            (lambda ()
              (fact 'membership-implies-sethood 'x_ '(PAIR b_ b_))
              (mac-h 'pairing-membership '(IN x_ (PAIR b_ b_)))
              (ms--split-all!)
              (ms--same-case! '(OR (= x_ b_) (= x_ b_)) oi-r))))))
     (dk-opened (lambda () (di))))))

(fact 'class-extensionality '(MAKE-SET (LIST a_ b_)) '(UNION (PAIR a_ a_) (PAIR b_ b_)))
(ass)
(qed 'makeset2-split)
(topic! 'makeset2-split 'combinatorial)

;;; --------------------------------------------------------------------
;;; card-pair:  a, b sets and distinct  =>  CARD({a,b}) = 2.
;;;
;;; BOTH guards are load-bearing, and neither is decoration: at b := a the set
;;; is a singleton and the cardinal is 1, and at a := ORD a proper class is a
;;; member of nothing, so {a,b} loses an element.  Four rewrites: the split
;;; above, card-insert, card-singleton, and succ_ORD -> succ on NN.
;;; --------------------------------------------------------------------

(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ SET) (FORALL b_ (IMPLIES (IN b_ SET)
     (IMPLIES (NOT (= a_ b_)) (= (CARD (MAKE-SET (LIST a_ b_))) 2))))))))
(ms--peel!)
(have! '(AND (IN a_ SET) (IN a_ SET)))
(dk-fact! 'pairing 'a_ 'a_)
(dk-fact! 'pairing-membership 'a_ 'a_)

;; b is not in {a}: pairing-membership would make it equal to a
(have! '(NOT (IN b_ (PAIR a_ a_)))
  (lambda ()
    (di)
    (mac-h 'pairing-membership '(IN b_ (PAIR a_ a_)))
    ;; `b = a or b = a': one case node (see ms--same-case!), one lane.
    (let ((cases (dk-opened (lambda () (ai '(OR (= b_ a_) (= b_ a_)))))))
      (if (not (= (length cases) 1))
          (error "card-pair: expected ONE case leaf, got" (length cases)))
      (dk-focus! (car cases))
      (mac-h 'ms-eq-symm '(= b_ a_)) (ai '(NOT (= a_ b_))))))

;; card-insert carries a FINITENESS guard since 2026-09-18
;; (structure-library/cardinality.scm): unguarded it is false of an infinite A.
;; Here the set being extended is the singleton {a}, whose cardinal card-singleton
;; gives as succ 0.
(fact 'card-singleton 'a_)
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(have! '(IN (CARD (PAIR a_ a_)) NN)
       (lambda () (subst '(= (CARD (PAIR a_ a_)) (succ 0))) (ass)))
(have! '(AND (IN b_ SET) (NOT (IN b_ (PAIR a_ a_)))))
(dk-fact! 'card-insert '(PAIR a_ a_) 'b_)
(fact 'makeset2-split 'a_ 'b_)
(fact 'nn-one-in)
(fact 'ord-succ-nn 1)

(subst '(= (MAKE-SET (LIST a_ b_)) (UNION (PAIR a_ a_) (PAIR b_ b_))))
(subst '(= (CARD (UNION (PAIR a_ a_) (PAIR b_ b_))) (succ_ORD (CARD (PAIR a_ a_)))))
(subst '(= (CARD (PAIR a_ a_)) (succ 0)))
(have! '(= (succ 0) 1) (lambda () (arith)))
(subst '(= (succ 0) 1))
(subst '(= (succ_ORD 1) (succ 1)))
(arith)
(qed 'card-pair)
(topic! 'card-pair 'combinatorial)
