;;; makeset-card-bound.scm -- a tuple of length n has at most n distinct entries.
;;;
;;;     makeset-card-bound:
;;;       forall n in NN, a, l in TUPLES(a).
;;;           LENGTH(l) = n  =>  CARD(MAKE-SET(l)) <= n
;;;
;;; MAKE-SET(l) is the set of ENTRIES of the tuple l (theory.scm:617), so this
;;; is the counting half of "a finite sequence has finitely many values": the
;;; entries may repeat, and every repetition only makes the entry set smaller.
;;;
;;; THE PROOF is list induction, run as induction on the LENGTH -- the shape
;;; theorem-library/tuples-induction.scm established: `ni' on the length, with
;;; `tuple-length-zero' in the base and `tuple-cons-decompose' in the step
;;; (structure-library/list-recursion.scm, the two GENERATION axioms).  In the
;;; step `makeset-cons' turns MAKE-SET(CONS(x,m)) into {x} u MAKE-SET(m), and
;;; the whole content of the argument is then the bound on ONE insertion.
;;;
;;; WHY THE INDUCTION IS STRENGTHENED.  The bound alone does not carry itself
;;; across the step: to insert x into S = MAKE-SET(m) one needs S to be a SET
;;; (card-insert is guarded on it) and CARD(S) to be a NATURAL NUMBER (both
;;; nn-succ-mono and nn-le-trans-guarded are guarded on it).  Neither is
;;; available from outside:
;;;
;;;   * `make-set-sethood' (theory.scm) needs `a in SET', and the statement
;;;     quantifies `a' with NO guard -- a is an arbitrary class.  Sethood of
;;;     MAKE-SET(l) is therefore something this induction must PROVE, which it
;;;     can, because each entry of l is a member of a and hence a set
;;;     (membership-implies-sethood), and a union of two sets is a set.
;;;   * CARD(S) in NN is the finiteness of S, which is exactly what the
;;;     induction is establishing.
;;;
;;; So `makeset-card-bound-strong' carries all three conjuncts and
;;; `makeset-card-bound' is its third projection.  One induction, not three.
;;;
;;; THE FOUR LEMMAS, and why each is here.
;;;
;;;   union-comm                 UNION(A,B) = UNION(B,A).  `card-insert'
;;;     (cardinality.scm) is stated as CARD(UNION(A, {x})) = succ_ORD(CARD A)
;;;     and `makeset-cons' produces UNION({x}, MAKE-SET(m)) -- the arguments in
;;;     the other order.  The macete rewriter does no commutativity
;;;     normalisation, so the two do not meet without this.  PROVEN from
;;;     class-extensionality + union-membership; the propositional residue is
;;;     closed by (prop).
;;;
;;;   union-singleton-absorb     x in S  =>  UNION({x}, S) = S.  The other half
;;;     of the insertion case analysis: when x is ALREADY an entry of the tail,
;;;     the entry set does not grow.  PROVEN the same way; the one step (prop)
;;;     cannot take is x = y => x in S, which is an equality fact, so it is
;;;     landed as an explicit implication by `subst' first.
;;;
;;;   card-union-singleton-bound   S in SET, x in SET, CARD(S) in NN =>
;;;       CARD(UNION({x}, S)) in NN  and  CARD(UNION({x}, S)) <= succ(CARD S).
;;;     The insertion bound, and the only place the case split lives: `use-em'
;;;     on `x in S'.  On the NO branch `card-insert' gives the exact value
;;;     succ_ORD(CARD S), which `ord-succ-nn' (ordinals.scm) converts to the NN
;;;     successor; on the YES branch union-singleton-absorb gives CARD S, which
;;;     is <= succ(CARD S) by `nn-le-succ'.  Nothing in the library proved this
;;;     bound before; every cardinality fact about UNION was either the exact
;;;     value for a DISJOINT union (card-union-disjoint) or the exact value for
;;;     a FRESH element (card-insert), and an entry set has neither property.
;;;
;;;   makeset-card-bound-strong  the strengthened induction described above.
;;;
;;; NAMED-ONLY.  union-comm and union-singleton-absorb are `declare-named-only!'
;;; (macetes.scm): as live macetes their left-hand sides match every UNION and
;;; every set in the library, and union-comm as an unconditional symmetric
;;; equation would rewrite each union back and forth forever.  They are cited by
;;; name (`fact') here, which named-only does not restrict.
;;;
;;; THE BILL.  {tuple-length-zero, tuple-cons-decompose, nn-le-succ,
;;; nn-succ-mono}, trust: well-known.  The first two are the generation axioms
;;; -- what "a tuple is a finite sequence" means -- and are on
;;; list-recursion.scm's own list of candidates for the primitive shelf; the
;;; other two are the NN order supports (structure-library/order-lemmas.scm),
;;; asserted well-known there and cited by a dozen files.  Everything else the
;;; proof uses -- card-empty, card-insert, class-extensionality,
;;; union-membership, pairing, pairing-membership, membership-implies-sethood,
;;; make-set-empty, makeset-cons, ord-succ-nn, nn-succ-closed -- is primitive or
;;; definitional and contributes nothing.
;;;
;;; Needs: structure-library/list-recursion (CONS, makeset-cons, the two
;;; generation axioms), structure-library/cardinality (card-empty, card-insert),
;;; structure-library/order-lemmas (nn-le-succ, nn-succ-mono),
;;; theorem-library/nn-order-basics (nn-le-refl, nn-le-trans-guarded),
;;; theorem-library/empty-cardinality and theorem-library/tuples-induction
;;; (neither is cited, but this file belongs beside them).

;;; --- file-local helpers (mcb- prefix) -----------------------------------

;; The peel / only / conj-close / pick / split-all / apply helpers this file was
;; written with are in driver-kit.scm since 2026-09-14 (dk-peel!, dk-only!,
;; dk-conj-close!, dk-pick, dk-split-all!, dk-apply!).  `(dk-conj-close! ass)'
;; is the old mcb-conj-close!: split the conjunctive goal, `ass' each leaf.

(define (mcb-final f)
  (if (and (pair? f) (memq (car f) '(forall implies))) (mcb-final (caddr f)) f))

;; The induction hypothesis, selected by its CONCLUSION.  Selecting it by binder
;; name (a `(forall a ...)' in the context) picks `tuple-cons-decompose'
;; instead -- `dk-fact!' leaves the whole citation chain behind, and the axiom
;; itself is a (forall a ...) too.  This is the brief's "never name an
;; assumption by shape", and it cost a run.
(define (mcb-ih? f)
  (let ((c (mcb-final f)))
    (and (pair? c) (eq? (car c) 'and)
         (pair? (cadr c)) (eq? (car (cadr c)) 'in)
         (pair? (cadr (cadr c))) (eq? (car (cadr (cadr c))) 'make-set))))

;;; -----------------------------------------------------------------------
;;; union-comm:  UNION(A,B) = UNION(B,A)
;;;
;;; Unguarded: UNION is total over classes (theory.scm), and so is
;;; class-extensionality.

(quietly (lambda ()
  (sp (make-wff '(FORALL a_ (FORALL b_ (= (UNION a_ b_) (UNION b_ a_))))))
  (di)
  (bc* 'class-extensionality)
  (di)
  (mac 'union-membership)
  (prop)))
(qed 'union-comm)
(declare-named-only! 'union-comm
  "An unconditional symmetric equation whose left side matches every UNION in
   the library: as a live macete it would rewrite every union into its mirror
   image, and then back.  Cite it by name.")
(topic! 'union-comm 'plumbing)

;;; -----------------------------------------------------------------------
;;; union-singleton-absorb:  y in S  =>  UNION({y}, S) = S
;;;
;;; `y in S' already gives `y in SET' (membership-implies-sethood), which is
;;; what pairing-membership wants, so no sethood guard is stated.
;;;
;;; The (prop) at the end decides
;;;     ({y}-membership iff x=y),  (x=y => x in S),  y in S
;;;         |-   (x in {y} or x in S)  iff  x in S
;;; whose only non-propositional step is the middle hypothesis -- prop treats
;;; `x = y' as an opaque atom, so the equality reasoning is done BEFORE it, by
;;; the `subst' inside the have!.

(quietly (lambda ()
  (sp (make-wff '(FORALL s_ (FORALL y_ (IMPLIES (IN y_ s_)
                   (= (UNION (PAIR y_ y_) s_) s_))))))
  (di)
  (fact 'membership-implies-sethood 'y_ 's_)
  (bc* 'class-extensionality)
  (di)
  (mac 'union-membership)
  (have! '(AND (IN y_ SET) (IN y_ SET)))
  (fact 'pairing-membership 'y_ 'y_ 'x)
  (have! '(IMPLIES (= x y_) (IN x s_))
         (lambda () (di) (subst '(= x y_)) (ass)))
  (dk-only! '(iff (in x (pair y_ y_)) (or (= x y_) (= x y_)))
             '(implies (= x y_) (in x s_))
             '(in y_ s_))
  (prop)))
(qed 'union-singleton-absorb)
(declare-named-only! 'union-singleton-absorb
  "Its RIGHT side is a bare variable, so the `-rev' companion would match every
   term in every goal and rewrite it into a union.  Cite it by name.")
(topic! 'union-singleton-absorb 'plumbing)

;;; -----------------------------------------------------------------------
;;; card-union-singleton-bound:
;;;   S in SET, y in SET, CARD(S) in NN
;;;     =>  CARD(UNION({y}, S)) in NN  and  CARD(UNION({y}, S)) <= succ(CARD S)
;;;
;;; The insertion bound.  `card-insert' gives the exact cardinal only when y is
;;; FRESH, so the case split is unavoidable; `use-em' is the right door for it
;;; (cutting (OR P (NOT P)) by hand leaves an obligation nothing proves).
;;;
;;; On the fresh branch the three substitutions are, in order: the argument
;;; order (union-comm), the value (card-insert), and the successor flavour
;;; (ord-succ-nn: succ_ORD and succ agree on NN).  Each is a `subst' rather than
;;; a `mac' because the equations are in the CONTEXT, landed by `fact'.

(quietly (lambda ()
  (sp (make-wff '(FORALL s_ (IMPLIES (IN s_ SET)
     (FORALL y_ (IMPLIES (IN y_ SET)
       (IMPLIES (IN (CARD s_) NN)
         (AND (IN (CARD (UNION (PAIR y_ y_) s_)) NN)
              (<= (CARD (UNION (PAIR y_ y_) s_)) (succ (CARD s_)))))))))))
  (dk-peel!)
  (use-em '(IN y_ s_)
    ;; y_ is already in S: the union is S itself.
    (lambda ()
      (fact 'union-singleton-absorb 's_ 'y_)
      (subst '(= (UNION (PAIR y_ y_) s_) s_))
      (fact 'nn-le-succ '(CARD s_))
      (dk-conj-close! ass))
    ;; y_ is fresh: the cardinal is exactly succ(CARD S).
    (lambda ()
      (have! '(AND (IN y_ SET) (NOT (IN y_ s_))))
      (fact 'card-insert 's_ 'y_)
      (fact 'union-comm '(PAIR y_ y_) 's_)
      (fact 'ord-succ-nn '(CARD s_))
      (subst '(= (UNION (PAIR y_ y_) s_) (UNION s_ (PAIR y_ y_))))
      (subst '(= (CARD (UNION s_ (PAIR y_ y_))) (succ_ORD (CARD s_))))
      (subst '(= (succ_ORD (CARD s_)) (succ (CARD s_))))
      (fact 'nn-succ-closed '(CARD s_))
      (fact 'nn-le-refl '(succ (CARD s_)))
      (dk-conj-close! ass)))))
(qed 'card-union-singleton-bound)
(topic! 'card-union-singleton-bound 'combinatorial)

;;; -----------------------------------------------------------------------
;;; makeset-card-bound-strong: the induction, with sethood and finiteness of
;;; the entry set carried alongside the bound.

;; The base leaf is identified by its GOAL, built by hand: it is the body with
;; n := 0, and both leaves of `ni' are FORALL/FORALL/IMPLIES/IMPLIES otherwise.
(define mcb-base-goal
  '(forall a (forall l (implies (in l (tuples a))
      (implies (= (length l) 0)
        (and (in (make-set l) set)
             (and (in (card (make-set l)) nn)
                  (<= (card (make-set l)) 0))))))))

(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (FORALL a (FORALL l (IMPLIES (IN l (TUPLES a))
     (IMPLIES (= (LENGTH l) n)
       (AND (IN (MAKE-SET l) SET)
            (AND (IN (CARD (MAKE-SET l)) NN)
                 (<= (CARD (MAKE-SET l)) n)))))))))))
(quietly (lambda ()
 (for-each
  (lambda (lf)
    (dk-focus! lf)
    (cond
      ;; BASE.  Length 0, so the tuple IS [] and its entry set is empty.
      ((equal? (dk-goal) mcb-base-goal)
       (dk-peel!)
       (have! '(AND (IN l (TUPLES a)) (= (LENGTH l) 0)))
       (fact 'tuple-length-zero 'a 'l)
       (subst '(= l (LIST)))
       (mac 'make-set-empty)
       (mac 'card-empty)
       (ta 'empty-set-is-set)
       (ta 'nn-zero-in)
       (fact 'nn-le-refl 0)
       (dk-conj-close! ass))
      ;; STEP.  l = CONS(x,m) with LENGTH(m) = n; the induction hypothesis
      ;; applies to m, and card-union-singleton-bound puts the head back.
      (else
       (dk-peel!)
       (dk-split-all!)
       (let ((ih (dk-pick mcb-ih? "the induction hypothesis")))
         (have! '(AND (IN n NN) (AND (IN l (TUPLES a)) (= (LENGTH l) (succ n)))))
         (ai (dk-fact! 'tuple-cons-decompose 'a 'n 'l))
         (dk-split-all!)
         (ai (dk-pick (dk-head? 'forsome) "the tail existential"))
         (dk-split-all!)
         (let* ((leq (dk-pick (lambda (f) (and (eq? (car f) '=) (symbol? (cadr f))
                                                (pair? (caddr f))
                                                (eq? (car (caddr f)) 'cons)))
                               "l = cons(x0, m0)"))
                (x0 (cadr (caddr leq)))
                (m0 (caddr (caddr leq))))
           ;; the three conjuncts at the tail
           (dk-apply! ih 'a m0)
           (dk-split-all!)
           ;; MAKE-SET(l) = {x0} u MAKE-SET(m0)
           (subst leq)
           (mac 'makeset-cons)
           ;; sethood of the head, the singleton, and the union
           (fact 'membership-implies-sethood x0 'a)
           (have! (list 'AND (list 'IN x0 'SET) (list 'IN x0 'SET)))
           (fact 'pairing x0 x0)
           (have! (list 'AND (list 'IN (list 'PAIR x0 x0) 'SET)
                        (list 'IN (list 'MAKE-SET m0) 'SET)))
           (fact 'union-set-closure (list 'PAIR x0 x0) (list 'MAKE-SET m0))
           ;; the insertion bound, then succ-monotonicity and transitivity:
           ;;   CARD(u) <= succ(CARD(MAKE-SET m0)) <= succ(n)
           (fact 'card-union-singleton-bound (list 'MAKE-SET m0) x0)
           (dk-split-all!)
           (fact 'nn-succ-closed (list 'CARD (list 'MAKE-SET m0)))
           (fact 'nn-succ-closed 'n)
           (fact 'nn-succ-mono (list 'CARD (list 'MAKE-SET m0)) 'n)
           (fact 'nn-le-trans-guarded
                 (list 'CARD (list 'UNION (list 'PAIR x0 x0) (list 'MAKE-SET m0)))
                 (list 'succ (list 'CARD (list 'MAKE-SET m0)))
                 (list 'succ 'n))
           (dk-conj-close! ass))))))
  (dk-opened (lambda () (ni))))))
(qed 'makeset-card-bound-strong)
(topic! 'makeset-card-bound-strong 'combinatorial)

;;; -----------------------------------------------------------------------
;;; makeset-card-bound: the third conjunct of the strengthened form.

(quietly (lambda ()
  (sp "forall([n in nn, a, l in tuples(a)], length(l) = n implies card(make-set(l)) <= n)")
  (dk-peel!)
  (fact 'makeset-card-bound-strong 'n 'a 'l)
  (dk-split-all!)
  (ass)))
(qed 'makeset-card-bound)
(topic! 'makeset-card-bound 'combinatorial)
