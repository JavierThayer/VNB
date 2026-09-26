;;; elem-entry-readoffs.scm -- the elementary-matrix ENTRY read-offs, PROVEN.
;;;
;;; WHAT THE FAMILY IS.  MATUNIT, ELEM-F, ELEM-G and ELEM-H are each installed
;;; (structure-library/elementary-matrix.scm) DIRECTLY as
;;;
;;;     MATOF(n, n, vnb-lambda([i,j], [1,n] x [1,n], <IF tower over i,j,k,l>))
;;;
;;; and 38 of the 41 supports in that file say what that tower evaluates to at
;;; one index pair, under hypotheses that decide some of the tower's equality
;;; tests.  There is therefore ONE proof, not 38; 23 of them are below.
;;;
;;;   1. `mac' the constructor -- the goal's left side becomes ENTRY of a MATOF;
;;;   2. `mac entry-of-matof' -- it applies because the two index typings the
;;;      statement's own guards landed ARE its side conditions;
;;;   3. `lam-b' -- the pair-lambda reduces (licensed by the same two typings),
;;;      so the goal is <IF tower> = <value>;
;;;   4. push the statement's own index equations (c = k, i = l, ...) into the
;;;      goal, so every equality test is over variables the context decides;
;;;   5. resolve the IF tower: decide each condition against the context by a
;;;      three-valued evaluation over its equality ATOMS, `if-true' / `if-false'
;;;      on a decided one, `use-em' on an undecided one.  `if-false' hands the
;;;      main branch the equation (= <IF> <else-branch>), which for these
;;;      statements IS the goal, so the branch closes by `ass' and DEFINEDNESS
;;;      is never owed.  The condition branch is propositional: `prop' after the
;;;      reflexive tests (= k k) are landed by `rfl'.
;;;
;;; `eer-close!' (below) is that resolver.  It is written to go in
;;; `driver-kit.scm' -- see the report; it is here only because this agent edits
;;; no shared file.
;;;
;;; TWO ROUTES, and the difference is DEFINEDNESS.  For the four `entry-of-*'
;;; statements the right-hand side IS the tower, so steps 2-3 leave `t = t',
;;; which `rfl' REFUSES: `=' is the definedness predicate and a tower over
;;; ONE(A)/ZERO(A)/r is not defined for an arbitrary A (`term-self-defined?',
;;; primitive-inferences.scm, certifies neither).  Those four take the FORWARD
;;; route instead -- cite entry-of-matof, `lam-b-h' its equation in the
;;; HYPOTHESIS, and the reduced equation IS the goal -- which owes no
;;; definedness because entry-of-matof already grants it.
;;;
;;; MEASURED, not predicted: the guarded forms of `elem-f-col-k' and
;;; `elem-g-rk-at-l' -- the two listed below, with the missing index typings and
;;; NOTHING else added -- close through `eer-run!' unchanged, `modulo
;;; {entry-of-matof}' (scratchpad/ee-probe5.scm).  So the residue below is a
;;; question about the STATEMENTS, not about the lane.
;;;
;;; NOT HERE, and it is a finding rather than an omission: the 15 supports whose
;;; ENTRY index is NOT typed by any guard (elem-f-col-k/-col-l/-col-other,
;;; elem-g-col-k/-col-l/-col-other, elem-f-ck-at, elem-f-cl-at, elem-f-rk-at,
;;; elem-f-rl-at, elem-f-ro-at (removed 2026-09-20), elem-g-entry-l-at-k, elem-g-rk-at-k,
;;; elem-g-rk-at-l, elem-g-ro-at).  entry-of-matof requires both indices in
;;; [1,n]; those statements quantify an index with no typing at all, so they
;;; also assert that ENTRY -- i.e. NTH of NTH -- DENOTES outside the index box,
;;; `=' being the definedness predicate.  The theory's only statement about NTH
;;; is `nth-in-range' (theory.scm:665), guarded on 1 <= i <= length(L); nothing
;;; says NTH denotes past the end.  They want the guard added, at the cost of
;;; one index typing per citation.  The other three supports of the file were a
;;; different shape: elem-f-type / elem-h-type are MATOF typings, and
;;; elem-f-symmetric is a matrix equality (matrix-entry-extensionality on
;;; entry-of-elem-f).  All three are PROVEN since 2026-09-16: elem-h-type in
;;; `mat-typing-bundle.scm' (the elem-g-type driver, verbatim), elem-f-type and
;;; elem-f-symmetric in the spliced block at the end of this file.
;;;
;;; Bills: entry-of-matof (asserted, well-known) and, for the four forward ones,
;;; nothing else; equality-symmetry is primitive.
;;;
;;; Helper prefix: eer-.

;;; ---- the lane ---------------------------------------------------------

;; the (= a b) atoms of a propositional combination, in order
(define (eer-atoms f acc)
  (cond ((not (pair? f)) acc)
        ((eq? (car f) '=) (if (member f acc) acc (cons f acc)))
        ((memq (car f) '(AND OR NOT IMPLIES IFF))
         (let loop ((xs (cdr f)) (a acc))
           (if (null? xs) a (loop (cdr xs) (eer-atoms (car xs) a)))))
        (#t acc)))

(define (eer-atom-list f) (reverse (eer-atoms f '())))

;; T / F / U for one atom against the context.  `=' is symmetric, so both
;; spellings of a context equation count.
(define (eer-lookup atom asms)
  (let ((a (cadr atom)) (b (caddr atom)))
    (cond ((equal? a b) 'T)
          ((or (member (list '= a b) asms) (member (list '= b a) asms)) 'T)
          ((or (member (list 'NOT (list '= a b)) asms)
               (member (list 'NOT (list '= b a)) asms)) 'F)
          (#t 'U))))

(define (eer-not3 v) (cond ((eq? v 'T) 'F) ((eq? v 'F) 'T) (#t 'U)))

(define (eer-eval f asg)
  (cond ((and (pair? f) (eq? (car f) 'NOT)) (eer-not3 (eer-eval (cadr f) asg)))
        ((and (pair? f) (eq? (car f) 'AND))
         (let ((x (eer-eval (cadr f) asg)) (y (eer-eval (caddr f) asg)))
           (cond ((or (eq? x 'F) (eq? y 'F)) 'F)
                 ((and (eq? x 'T) (eq? y 'T)) 'T)
                 (#t 'U))))
        ((and (pair? f) (eq? (car f) 'OR))
         (let ((x (eer-eval (cadr f) asg)) (y (eer-eval (caddr f) asg)))
           (cond ((or (eq? x 'T) (eq? y 'T)) 'T)
                 ((and (eq? x 'F) (eq? y 'F)) 'F)
                 (#t 'U))))
        (#t (let ((p (assoc f asg))) (if p (cdr p) 'U)))))

(define (eer-combos atoms)
  (if (null? atoms)
      (list '())
      (let ((rest (eer-combos (cdr atoms))))
        (append (map (lambda (r) (cons (cons (car atoms) 'T) r)) rest)
                (map (lambda (r) (cons (cons (car atoms) 'F) r)) rest)))))

;; Decide a condition against the context: T / F if EVERY assignment to its
;; undecided atoms agrees, U otherwise.  This is what sees that
;; (j = k) and not(j = k) and not(j = l) is false with (j = k) unknown.
(define (eer-decide cond0 asms)
  (let* ((atoms (eer-atom-list cond0))
         (known (map (lambda (a) (cons a (eer-lookup a asms))) atoms))
         (unk   (map car (filter (lambda (p) (eq? (cdr p) 'U)) known)))
         (base  (filter (lambda (p) (not (eq? (cdr p) 'U))) known)))
    (if (> (length unk) 6)
        'U
        (let loop ((cs (eer-combos unk)) (val #f))
          (cond ((null? cs) (if val val 'U))
                (#t (let ((v (eer-eval cond0 (append base (car cs)))))
                      (cond ((eq? v 'U) 'U)
                            ((and val (not (eq? v val))) 'U)
                            (#t (loop (cdr cs) v))))))))))

(define (eer-first-unknown cond0 asms)
  (let loop ((as (eer-atom-list cond0)))
    (cond ((null? as) #f)
          ((eq? (eer-lookup (car as) asms) 'U) (car as))
          (#t (loop (cdr as))))))

;; Close a leaf whose goal is a propositional combination of equality atoms:
;; land the reflexive ones by `rfl', then `prop' decides the rest from context.
(define (eer-cond!)
  (let ((g (dk-goal)))
    (cond ((member g (dk-asms)) (ass))
          ((and (pair? g) (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
          ;; goal (= x y) with the other spelling in context
          ((and (pair? g) (eq? (car g) '=)
                (member (list '= (caddr g) (cadr g)) (dk-asms)))
           (fact 'equality-symmetry (caddr g) (cadr g)) (ass))
          ;; goal (NOT (= x y)) with (NOT (= y x)) in context.  NOT via `have!':
          ;; the claim would BE the goal, and that cut is a silent self-loop.
          ((and (pair? g) (eq? (car g) 'NOT)
                (pair? (cadr g)) (eq? (car (cadr g)) '=)
                (member (list 'NOT (list '= (caddr (cadr g)) (cadr (cadr g)))) (dk-asms)))
           (let* ((a (cadr g)) (x (cadr a)) (y (caddr a)))
             (di) (fact 'equality-symmetry x y) (ai (list 'NOT (list '= y x)))))
          (#t (begin (eer-supply! g) (prop))))))

;; `prop' reads atoms LITERALLY, so (= l k) and (= k l) are two atoms to it
;; while they are one fact.  The decision procedure above knows `=' is
;; symmetric; supply the spelling the goal uses before handing it over, and
;; land the reflexive tests (= k k) that no hypothesis states.
(define (eer-supply! g)
  (for-each
   (lambda (a)
     (let* ((x (cadr a)) (y (caddr a)) (rev (list '= y x)))
       (cond ((or (alpha-equiv? a (dk-goal))
                  (alpha-equiv? (list 'NOT a) (dk-goal))) #f)
             ((equal? x y)
              (if (not (member a (dk-asms))) (have! a (lambda () (rfl)))))
             ((and (member rev (dk-asms)) (not (member a (dk-asms))))
              (have! a (lambda () (fact 'equality-symmetry y x) (ass))))
             ((and (member (list 'NOT rev) (dk-asms))
                   (not (member (list 'NOT a) (dk-asms))))
              (have! (list 'NOT a)
                     (lambda () (di) (fact 'equality-symmetry x y) (ai (list 'NOT rev)))))
             (#t #f))))
   (eer-atom-list g)))

;; if-true / if-false open exactly two leaves: the CONDITION (or its negation)
;; and the MAIN goal, which gains (= <IF> <branch>).  Discriminate on the GOAL,
;; never on where focus landed; close the condition leaf and stay on the main.
(define (eer-if! true? ifterm)
  (let* ((want   (if true? (cadr ifterm) (list 'NOT (cadr ifterm))))
         (opened (dk-opened (lambda () (if true? (if-true ifterm) (if-false ifterm)))))
         (conds  (filter (lambda (l) (alpha-equiv? (dk-goal-of l) want)) opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (= 1 (length conds)) (= 1 (length mains))))
        (error "eer-if!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (dk-focus! (car conds)) (eer-cond!)
    (dk-focus! (car mains))))

;; How many of the context's NEGATED equations mention V?
(define (eer-neg-mentions v asms)
  (length (filter (lambda (f)
                    (and (pair? f) (eq? (car f) 'NOT)
                         (pair? (cadr f)) (eq? (car (cadr f)) '=)
                         (or (equal? (cadr (cadr f)) v) (equal? (caddr (cadr f)) v))))
                  asms)))

;; In the POSITIVE branch of a case split on (= p q), push that equation into the
;; goal -- as `eer-push-eqs!' pushes the statement's own index equations.  Without
;; it the goal and the hypotheses talk about different variables and the resolver,
;; whose atoms are opaque, cannot see that (i = c) with not(c = k) forces
;; not(i = k): elem-f-col-other ends in a branch whose context is contradictory
;; only by equality reasoning.
;;
;; WHICH SIDE TO ELIMINATE is not free, and elem-g-col-l is the case that shows it:
;; substituting i := k there DISCARDS the one variable the context constrains
;; (not(i = l)) and lands the same wall one level down.  Eliminate the side the
;; context's negated equations do NOT mention; the equation is turned round by
;; equality-symmetry when that is the right-hand side.
(define (eer-push-split! atom)
  (let ((p (cadr atom)) (q (caddr atom)))
    (if (and (symbol? p) (symbol? q) (not (equal? p q)))
        (let* ((flip (> (eer-neg-mentions p (dk-asms)) (eer-neg-mentions q (dk-asms))))
               (e    (if flip (list '= q p) atom)))
          (if (and flip (not (member e (dk-asms))))
              (have! e (lambda () (fact 'equality-symmetry p q) (ass))))
          (if (dc-ment? (cadr e) (dk-goal)) (subst e))))))

;; THE RESOLVER.  Focus goal is (= <term> <term>); reduce the RIGHT side's IF
;; tower first (substituting each resolution), then the LEFT side's, at which
;; point the equation if-true/if-false handed the branch IS the goal.
(define (eer-close! depth)
  (if (> depth 14) (error "eer-close!: tower deeper than 14"))
  (let ((g (dk-goal)))
    (if (member g (dk-asms))
        (ass)
        (let* ((lhs (cadr g)) (rhs (caddr g))
               (ift (cond ((and (pair? rhs) (eq? (car rhs) 'IF)) rhs)
                          ((and (pair? lhs) (eq? (car lhs) 'IF)) lhs)
                          (#t #f))))
          (cond
            ((not ift) (rfl))
            (#t
             (let ((d (eer-decide (cadr ift) (dk-asms))))
               (cond
                 ((eq? d 'U)
                  (let ((a (eer-first-unknown (cadr ift) (dk-asms))))
                    (if (not a) (error "eer-close!: undecided condition with no unknown atom"
                                       (expression->string (cadr ift))))
                    (use-em a
                      (lambda () (eer-push-split! a) (eer-close! (+ depth 1)))
                      (lambda () (eer-close! (+ depth 1))))))
                 (#t
                  (let ((val (if (eq? d 'T) (caddr ift) (cadddr ift))))
                    (eer-if! (eq? d 'T) ift)
                    (if (member (dk-goal) (dk-asms))
                        (ass)
                        (begin (subst (list '= ift val))
                               (eer-close! (+ depth 1))))))))))))))

;;; ---- plumbing ---------------------------------------------------------

(define (eer-interval-typing v asms)
  (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'IN) (equal? (cadr f) v)
                             (pair? (caddr f)) (eq? (car (caddr f)) 'INTERVAL)))
            asms))

;; An ENTRY index that carries no interval typing of its own but IS equated to
;; one that does (elem-g-entry-l-at-l: the row is l, the guard is c = l) gets
;; its typing here, so entry-of-matof and lam-b apply.
(define (eer-type-indices!)
  (let* ((g (dk-goal)) (e (cadr g)))
    (for-each
     (lambda (v)
       (if (and (symbol? v) (not (eer-interval-typing v (dk-asms))))
           (let ((eqf (any-pred (lambda (f)
                                  (and (pair? f) (eq? (car f) '=)
                                       (or (equal? (cadr f) v) (equal? (caddr f) v))
                                       (symbol? (cadr f)) (symbol? (caddr f))))
                                (dk-asms))))
             (if eqf
                 (let* ((u   (if (equal? (cadr eqf) v) (caddr eqf) (cadr eqf)))
                        (typ (eer-interval-typing u (dk-asms))))
                   (if typ
                       (begin
                         (if (not (member (list '= v u) (dk-asms)))
                             (have! (list '= v u)
                                    (lambda () (fact 'equality-symmetry u v) (ass))))
                         (have! (list 'IN v (caddr typ))
                                (lambda () (subst (list '= v u)) (ass))))))))))
     (list (caddr e) (cadddr e)))))

;; Push the statement's own index equations into the goal, so every equality
;; test in the tower is over variables the context decides outright.
(define (eer-push-eqs! landed)
  (for-each (lambda (f)
              (if (and (pair? f) (eq? (car f) '=) (symbol? (cadr f)) (symbol? (caddr f))
                       (not (equal? (cadr f) (caddr f)))
                       (dc-ment? (cadr f) (dk-goal)))
                  (subst f)))
            landed))

(define (eer-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'algebra))
      (begin
        (display "\n*** elem-entry-readoffs: ") (display name)
        (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ")
                                (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (proof-leaves))
        (error "elem-entry-readoffs: unfinished" name))))

;;; ---- entry-of-matof, guarded (2026-09-16) ------------------------------
;;;
;;; `entry-of-matof' is a THEOREM since the SIZE/MAT surgery
;;; (theorem-library/tuple-tabulation.scm), with premises (IN m NN), (IN n NN)
;;; and the DEFINEDNESS hypothesis
;;;     forall i_ in [1,m]. forall j_ in [1,n]. g(i_, j_) in SET
;;; ahead of its two index premises.  For these tabulators g(i_, j_) is an IF
;;; tower over ONE(A), ZERO(A) (and r), so the hypothesis is a typing fact:
;;; each value is in CARR A (ring-one-in, ring-zero-in, the r premise) and
;;; membership-implies-sethood gives SET.  That is proved ONCE per constructor
;;; (the four `*-entries-defined' lemmas at the head of the theorems), and
;;; `eer-entry-eqn!' cites it to land the equation
;;;     ENTRY(MATOF(n,n,LAM), a, b) = LAM(a, b)
;;; in a `have!' lane, so the citation chain stays out of the main context
;;; (where `prop' reads it).

;; For a goal (IN (IF c x y) SET): the same atom-wise resolution as
;; `eer-close!' -- decide c against the context; if it is undecided, split on
;; its first undecided EQUATION (never on the compound c: `use-em' on a
;; disjunction hands its bodies the disjuncts, ELEM-F's condition being one);
;; if decided, `eer-if!' reduces the IF.  A goal that is not an IF closes from
;; the context.
(define (eer-close-in! depth)
  (if (> depth 14) (error "eer-close-in!: tower deeper than 14"))
  (let ((g (dk-goal)))
    (if (and (pair? g) (eq? (car g) 'IN)
             (pair? (cadr g)) (eq? (car (cadr g)) 'IF))
        (let* ((ift (cadr g))
               (d   (eer-decide (cadr ift) (dk-asms))))
          (if (eq? d 'U)
              (let ((a (eer-first-unknown (cadr ift) (dk-asms))))
                (if (not a) (error "eer-close-in!: undecided condition with no unknown atom"
                                   (expression->string (cadr ift))))
                (use-em a
                  (lambda () (eer-close-in! (+ depth 1)))
                  (lambda () (eer-close-in! (+ depth 1)))))
              (let ((val (if (eq? d 'T) (caddr ift) (cadddr ift))))
                (eer-if! (eq? d 'T) ift)
                (subst (list '= ift val))
                (eer-close-in! (+ depth 1)))))
        (ass))))

;; x in CARR A in context: land x in SET.
(define (eer-set! x)
  (fact 'membership-implies-sethood x '(CARR A)))

;; The four definedness lemmas: the tabulator's value at every index pair is
;; a set.  Statement: forall PARAMS. IS-RING A => n in NN [=> r in CARR A] =>
;; forall i_ in [1,n], j_ in [1,n]. LAM(i_, j_) in SET, LAM being the
;; constructor's VNB-LAMBDA verbatim (structure-library/elementary-matrix.scm).
(define (eer-defined-lemma! name stmt)
  (sp (make-wff stmt))
  (dk-peel!)                                   ; IS-RING A, n in NN, (r), i_, j_
  (fact 'ring-one-in 'A)
  (fact 'ring-zero-in 'A)
  (eer-set! '(ONE A))
  (eer-set! '(ZERO A))
  (if (member '(IN r (CARR A)) (dk-asms)) (eer-set! 'r))
  (lam-b)                                      ; (IN <IF tower> SET)
  (eer-close-in! 0)
  (eer-qed! name))

;; FUNCTOID -> its definedness lemma.  The last three (IDENTMAT, UNITROW,
;; ZEROMAT: matrix.scm's tabulations over ONE/ZERO) were added 2026-09-16 with
;; the matrix.scm read-offs at the end of this file.
(define eer-defined-lemmas
  '((MATUNIT . matunit-entries-defined) (ELEM-F . elem-f-entries-defined)
    (ELEM-G . elem-g-entries-defined) (ELEM-H . elem-h-entries-defined)
    (IDENTMAT . identmat-entries-defined) (UNITROW . unitrow-entries-defined)
    (ZEROMAT . zeromat-entries-defined)))

;; A literal 1 as a dimension or an index (UNITROW is 1-by-n, read at row 1)
;; needs (IN 1 NN) / (IN 1 (INTERVAL 1 1)) in the MAIN context: the first for
;; entry-of-matof, the second also for the `lam-b' that follows.
(define (eer-literal-one! mv a)
  (if (and (eqv? mv 1) (not (member '(IN 1 NN) (dk-asms))))
      (fact 'nn-one-in))
  (if (and (eqv? a 1) (eqv? mv 1)
           (not (member '(IN 1 (INTERVAL 1 1)) (dk-asms))))
      (fact 'one-in-interval-1)))

;; Goal (= (ENTRY (MATOF m n LAM) a b) _), both indices typed in context, FT
;; the constructor term the MATOF unfolded from: land
;; (= (ENTRY (MATOF m n LAM) a b) (LAM a b)) and return it.  (Square m = n for
;; the four elementary constructors; rectangular since 2026-09-16.)
(define (eer-entry-eqn! ft)
  (let* ((e   (cadr (dk-goal)))
         (mf  (cadr e))
         (mv  (cadr mf)) (nv (caddr mf)) (lam (cadddr mf))
         (a   (caddr e)) (b (cadddr e))
         (lem (cdr (assq (car ft) eer-defined-lemmas)))
         (eqn (list '= e (list lam a b))))
    (eer-literal-one! mv a)
    (have! eqn
      (lambda ()
        (apply fact lem (cdr ft))              ; the definedness hypothesis
        (fact 'entry-of-matof mv nv lam a b)
        (ass)))
    (dk-focus-having! eqn)
    eqn))

;;; The value route: the right-hand side is a value (or a smaller tower).
(define (eer-run! name functoid stmt)
  (sp (make-wff stmt))
  (let ((landed (dk-peel!)))
    (eer-type-indices!)
    (let ((ft (cadr (cadr (dk-goal)))))
      (mac functoid)
      (subst (eer-entry-eqn! ft)))
    (lam-b)
    (eer-push-eqs! landed)
    (eer-close! 0))
  (eer-qed! name))

;;; The forward route: the right-hand side IS the tower, so the goal is
;;; entry-of-matof's own equation once the lambda is reduced in the HYPOTHESIS.
(define (eer-run-fwd! name functoid stmt)
  (sp (make-wff stmt))
  (dk-peel!)
  (let ((ft (cadr (cadr (dk-goal)))))
    (mac functoid)
    (let ((eqn (eer-entry-eqn! ft)))
      (lam-b-h eqn)
      (ass)))
  (eer-qed! name))

;;; ---- the theorems -----------------------------------------------------
;;;
;;; GUARDED 2026-09-16 (the SIZE/MAT surgery).  Every statement below gained,
;;; right after its binders, the premises
;;;     (IS-RING A)  (IN n NN)            -- all 38
;;;     (IN r (CARR A))                   -- the ELEM-G and ELEM-H ones
;;; Each is FORCED.  MATOF(n, n, g) is a description over MAT(n, n, ...):
;;;   * n not natural (n := ORD, say): MAT(n, n, X) is empty (mat-rows-in-nn),
;;;     so MATOF has no value, ENTRY of it does not denote, and `=' -- the
;;;     definedness predicate -- is false.
;;;   * A not a ring (A := 0, say): ONE(A) and ZERO(A) are projections of a
;;;     non-tuple and do not denote, so no index box value exists and the
;;;     matrix does not either (n >= 1); likewise for r a proper class with
;;;     k /= l both in [1, n] (ELEM-G) or k in [1, n] (ELEM-H).
;;; They are exactly what `entry-of-matof' now asks for; `r in CARR A' is the
;;; typing every citer already holds, rather than the bare `r in SET'.

;;; ---- the definedness lemmas (NEW 2026-09-16) ---------------------------

(eer-defined-lemma! 'matunit-entries-defined
  '(FORALL A (FORALL n (FORALL k (FORALL l
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                  (IF (AND (= i k) (= j l)) (ONE A) (ZERO A)))
                i_ j_)
               SET))))))))))))

(eer-defined-lemma! 'elem-f-entries-defined
  '(FORALL A (FORALL n (FORALL k (FORALL l
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                  (IF (OR (AND (= i k) (= j l))
                          (OR (AND (= i l) (= j k))
                              (AND (= i j) (AND (NOT (= i k)) (NOT (= i l))))))
                      (ONE A) (ZERO A)))
                i_ j_)
               SET))))))))))))

(eer-defined-lemma! 'elem-g-entries-defined
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
     (IMPLIES (IN r (CARR A))
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                  (IF (= i j) (ONE A)
                      (IF (AND (= i k) (= j l)) r (ZERO A))))
                i_ j_)
               SET))))))))))))))

(eer-defined-lemma! 'elem-h-entries-defined
  '(FORALL A (FORALL n (FORALL r (FORALL k
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
     (IMPLIES (IN r (CARR A))
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                  (IF (= i j) (IF (= i k) r (ONE A)) (ZERO A)))
                i_ j_)
               SET)))))))))))))

;;; ---- the read-offs ----------------------------------------------------

(eer-run-fwd! 'entry-of-matunit 'MATUNIT
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATUNIT A n k l) i j)
          (IF (AND (= i k) (= j l)) (ONE A) (ZERO A))))))))))))))

(eer-run! 'matunit-entry-off-row 'MATUNIT
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (MATUNIT A n k l) j c) (ZERO A))))))))))))))

(eer-run! 'matunit-entry-k-row 'MATUNIT
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
       (= (ENTRY (MATUNIT A n k l) k c) (IF (= c l) (ONE A) (ZERO A)))))))))))))

(eer-run-fwd! 'entry-of-elem-f 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-F A n k l) i j)
          (IF (OR (AND (= i k) (= j l))
                  (OR (AND (= i l) (= j k))
                      (AND (= i j) (AND (NOT (= i k)) (NOT (= i l))))))
              (ONE A) (ZERO A))))))))))))))

(eer-run-fwd! 'entry-of-elem-g 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL j
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-G A n r k l) i j)
          (IF (= i j) (ONE A)
              (IF (AND (= i k) (= j l)) r (ZERO A)))))))))))))))))

(eer-run-fwd! 'entry-of-elem-h 'ELEM-H
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL i (FORALL j
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ELEM-H A n r k) i j)
          (IF (= i j) (IF (= i k) r (ONE A)) (ZERO A)))))))))))))))

(eer-run! 'elem-g-entry-off-l-off-diag 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c l))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-G A n r k l) j c) (ZERO A)))))))))))))))))

(eer-run! 'elem-g-entry-off-l-diag 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-G A n r k l) c c) (ONE A))))))))))))))

(eer-run! 'elem-g-entry-l-vanish 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= j l))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (ELEM-G A n r k l) j c) (ZERO A))))))))))))))))))

(eer-run! 'elem-g-entry-l-at-l 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
       (= (ENTRY (ELEM-G A n r k l) l c) (ONE A))))))))))))))

(eer-run! 'elem-f-ck-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c k)
     (IMPLIES (NOT (= k l))
     (IMPLIES (NOT (= j l))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))))

(eer-run! 'elem-f-cl-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= k l))
     (IMPLIES (NOT (= j k))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))))

(eer-run! 'elem-f-co-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-F A n k l) j c) (ZERO A))))))))))))))))

(eer-run! 'elem-f-co-at 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
       (= (ENTRY (ELEM-F A n k l) c c) (ONE A)))))))))))))

(eer-run! 'elem-h-entry-off-diag 'ELEM-H
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL j (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= j c))
       (= (ENTRY (ELEM-H A n r k) j c) (ZERO A)))))))))))))))

(eer-run! 'elem-h-entry-diag 'ELEM-H
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN c (INTERVAL 1 n))
       (= (ENTRY (ELEM-H A n r k) c c) (IF (= c k) r (ONE A)))))))))))))

(eer-run! 'elem-f-rk-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (= i k) (IMPLIES (NOT (= k l)) (IMPLIES (NOT (= j l)) (= (ENTRY (ELEM-F A n k l) i j) (ZERO A))))))))))))))))

(eer-run! 'elem-f-rl-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (= i l) (IMPLIES (NOT (= k l)) (IMPLIES (NOT (= j k)) (= (ENTRY (ELEM-F A n k l) i j) (ZERO A))))))))))))))))

(eer-run! 'elem-f-ro-off 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (NOT (= i k)) (IMPLIES (NOT (= i l)) (IMPLIES (NOT (= j i)) (= (ENTRY (ELEM-F A n k l) i j) (ZERO A))))))))))))))))

(eer-run! 'elem-g-rk-vanish 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (= i k) (IMPLIES (NOT (= j k)) (IMPLIES (NOT (= j l)) (= (ENTRY (ELEM-G A n r k l) i j) (ZERO A))))))))))))))))))

(eer-run! 'elem-g-ro-off 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (NOT (= i k)) (IMPLIES (NOT (= j i)) (= (ENTRY (ELEM-G A n r k l) i j) (ZERO A)))))))))))))))))

(eer-run! 'elem-h-ro-off 'ELEM-H
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL i (FORALL j 
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n)) (IMPLIES (IN j (INTERVAL 1 n)) (IMPLIES (NOT (= j i)) (= (ENTRY (ELEM-H A n r k) i j) (ZERO A)))))))))))))))

;; (`elem-h-ro-at' stood here; REMOVED 2026-09-20, batch 11.  Same reason as
;; elem-f-ro-at below: on the diagonal it was alpha-equal to
;; `elem-h-entry-diag' above, which its call site now cites.)

;;; ---- BEGIN spliced block: the fifteen guarded read-offs ----------------

;;; ELEM-F column read-offs -------------------------------------------------

(eer-run! 'elem-f-ck-at 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN l (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c k)
     (= (ENTRY (ELEM-F A n k l) l c) (ONE A)))))))))))))

(eer-run! 'elem-f-cl-at 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (= (ENTRY (ELEM-F A n k l) k c) (ONE A)))))))))))))

(eer-run! 'elem-f-col-k 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-F A n k l) i k) (IF (= i l) (ONE A) (ZERO A))))))))))))))

(eer-run! 'elem-f-col-l 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN l (INTERVAL 1 n))
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-F A n k l) i l) (IF (= i k) (ONE A) (ZERO A))))))))))))))

(eer-run! 'elem-f-col-other 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c k))
     (IMPLIES (NOT (= c l))
     (= (ENTRY (ELEM-F A n k l) i c) (IF (= i c) (ONE A) (ZERO A))))))))))))))))

;;; ELEM-F row read-offs ----------------------------------------------------

(eer-run! 'elem-f-rk-at 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN l (INTERVAL 1 n))
     (IMPLIES (= i k)
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-F A n k l) i l) (ONE A))))))))))))))

(eer-run! 'elem-f-rl-at 'ELEM-F
  '(FORALL A (FORALL n (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (= i l)
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-F A n k l) i k) (ONE A))))))))))))))

;; (`elem-f-ro-at' stood here; REMOVED 2026-09-20, batch 11.  The diagonal
;; entry does not distinguish a row from a column read-off, so its statement
;; was alpha-equal to `elem-f-co-at' above; the row call site cites that one.)

;;; ELEM-G column read-offs -------------------------------------------------

(eer-run! 'elem-g-entry-l-at-k 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (= c l)
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-G A n r k l) k c) r)))))))))))))))

(eer-run! 'elem-g-col-k 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-G A n r k l) i k) (IF (= i k) (ONE A) (ZERO A))))))))))))))))

(eer-run! 'elem-g-col-l 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN l (INTERVAL 1 n))
     (= (ENTRY (ELEM-G A n r k l) i l)
        (IF (= i l) (ONE A) (IF (= i k) r (ZERO A))))))))))))))))

(eer-run! 'elem-g-col-other 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i (FORALL c
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN c (INTERVAL 1 n))
     (IMPLIES (NOT (= c l))
     (= (ENTRY (ELEM-G A n r k l) i c) (IF (= i c) (ONE A) (ZERO A)))))))))))))))))

;;; ELEM-G row read-offs ----------------------------------------------------

(eer-run! 'elem-g-rk-at-k 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN k (INTERVAL 1 n))
     (IMPLIES (= i k)
     (= (ENTRY (ELEM-G A n r k l) i k) (ONE A)))))))))))))))

(eer-run! 'elem-g-rk-at-l 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN l (INTERVAL 1 n))
     (IMPLIES (= i k)
     (IMPLIES (NOT (= k l))
     (= (ENTRY (ELEM-G A n r k l) i l) r)))))))))))))))

(eer-run! 'elem-g-ro-at 'ELEM-G
  '(FORALL A (FORALL n (FORALL r (FORALL k (FORALL l (FORALL i
     
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN r (CARR A)) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (NOT (= i k))
     (= (ENTRY (ELEM-G A n r k l) i i) (ONE A))))))))))))))

;;; ---- END spliced block --------------------------------------------------

;;; ---- BEGIN spliced block (2026-09-16): matrix.scm read-offs, and the -----
;;; ---- three elementary-matrix facts the header left for later -----------
;;;
;;; The FALSE-DEF sweep (scratchpad/surgery/FALSEDEF.md) found that several
;;; asserted matrix supports assumed, without saying so, that a dimension is a
;;; natural number, that A is a ring, or that a tabulated entry denotes.  They
;;; were guarded (the counterexamples are at the old sites in
;;; structure-library/matrix.scm and elementary-matrix.scm), and the ones that
;;; fall to this file's lane are PROVEN here instead of re-asserted:
;;;
;;;   IDENTMAT, UNITROW, ZEROMAT read-offs -- the same lane as MATUNIT /
;;;     ELEM-x: a definedness lemma per constructor, then `eer-run!' (value
;;;     route) or `eer-run-fwd!' (the right side IS the tabulated value).
;;;     `eer-entry-eqn!' was generalised to rectangular tabulations and to a
;;;     literal 1 as dimension/index for UNITROW.
;;;   elem-f-type -- matof-in-mat on the swap tabulator; its IF condition is a
;;;     disjunction, so the IN-resolver `eer-close-in!' (which splits on atoms,
;;;     never on the compound condition) is what closes it.  That is why it is
;;;     here and not in mat-typing-bundle beside elem-g-type / elem-h-type.
;;;   elem-f-symmetric -- matrix-entry-extensionality; the two entry towers are
;;;     the same propositional function of the index equations, and
;;;     `eer-close!' resolves both.
;;;   entry-of-block, the four SNOC read-offs -- entry-of-matof with a
;;;     definedness hypothesis discharged by entry-in-carrier (the tabulated
;;;     values are entries of a matrix inside its index box); `eer-carry!'
;;;     moves an index from one interval to a wider one.
;;;
;;; Load window: after tuple-tabulation (entry-of-matof), mat-basics,
;;; entry-in-carrier, interval-membership (one-in-interval-1), nn-order-ord,
;;; tuple-extensionality -- all earlier; before the first citers:
;;; matunit-shift-proof / elem-actions-proof (elem-f-type), elem-inverses-proof
;;; (entry-of-identmat), span-bricks-proof (UNITROW, ZEROMAT), smith-staircase
;;; and span-bricks2 (BLOCK, SNOC), mod-basis (IDENTMAT).

;;; ---- definedness lemmas ---------------------------------------------------

(eer-defined-lemma! 'identmat-entries-defined
  '(FORALL A (FORALL n
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 n))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 n))
                  (IF (= i j) (ONE A) (ZERO A)))
                i_ j_)
               SET))))))))))

(eer-defined-lemma! 'unitrow-entries-defined
  '(FORALL A (FORALL n (FORALL i
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 1))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST rw cl) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 n))
                  (IF (= cl i) (ONE A) (ZERO A)))
                i_ j_)
               SET)))))))))))

(eer-defined-lemma! 'zeromat-entries-defined
  '(FORALL A (FORALL m (FORALL n
     (IMPLIES (IS-RING A)
     (IMPLIES (IN m NN)
     (IMPLIES (IN n NN)
       (FORALL i_ (IMPLIES (IN i_ (INTERVAL 1 m))
         (FORALL j_ (IMPLIES (IN j_ (INTERVAL 1 n))
           (IN ((VNB-LAMBDA (LIST i j) (CARTESIAN (INTERVAL 1 m) (INTERVAL 1 n))
                  (ZERO A))
                i_ j_)
               SET))))))))))))

;;; ---- IDENTMAT / UNITROW / ZEROMAT read-offs (were matrix.scm supports) ----

(eer-run-fwd! 'entry-of-identmat 'IDENTMAT
  '(FORALL A (FORALL n (FORALL i (FORALL j
     (IMPLIES (IS-RING A)
     (IMPLIES (IN n NN)
     (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (IDENTMAT A n) i j) (IF (= i j) (ONE A) (ZERO A))))))))))))

(eer-run! 'identmat-entry-diag 'IDENTMAT
  '(FORALL A (FORALL n (FORALL i
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
       (= (ENTRY (IDENTMAT A n) i i) (ONE A)))))))))

(eer-run! 'identmat-entry-off 'IDENTMAT
  '(FORALL A (FORALL n (FORALL i (FORALL j
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (NOT (= i j))
       (= (ENTRY (IDENTMAT A n) i j) (ZERO A))))))))))))

(eer-run! 'unitrow-entry-at 'UNITROW
  '(FORALL A (FORALL n (FORALL i
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
       (= (ENTRY (UNITROW A n i) 1 i) (ONE A)))))))))

(eer-run! 'unitrow-entry-off 'UNITROW
  '(FORALL A (FORALL n (FORALL i (FORALL j
     (IMPLIES (IS-RING A) (IMPLIES (IN n NN) (IMPLIES (IN i (INTERVAL 1 n))
     (IMPLIES (IN j (INTERVAL 1 n))
     (IMPLIES (NOT (= j i))
       (= (ENTRY (UNITROW A n i) 1 j) (ZERO A))))))))))))

(eer-run-fwd! 'entry-of-zeromat 'ZEROMAT
  '(FORALL A (FORALL m (FORALL n (FORALL i (FORALL j
     (IMPLIES (IS-RING A)
     (IMPLIES (IN m NN)
     (IMPLIES (IN n NN)
     (IMPLIES (IN i (INTERVAL 1 m))
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (ZEROMAT A m n) i j) (ZERO A)))))))))))))

;;; ---- elem-f-type, elem-f-symmetric (were elementary-matrix.scm supports) --

(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A) (FORALL n (FORALL k (FORALL l (IMPLIES (IN n NN)
     (IN (ELEM-F A n k l) (MAT n n (CARR A)))))))))))
(dk-peel!)                                     ; IS-RING A, n in NN
(mac 'ELEM-F)
(dk-matof!)
(dk-peel!)                                     ; the two index typings
(lam-b)                                        ; (IN <IF tower> (CARR A))
(fact 'ring-one-in 'A)
(fact 'ring-zero-in 'A)
(eer-close-in! 0)
(eer-qed! 'elem-f-type)

;; `eer-close!' without the equation pushing: split on the equality ATOMS and
;; decide both towers propositionally.  The two towers of elem-f-symmetric are
;; the same propositional function of the five atoms i=k, j=l, i=l, j=k, i=j
;; (the k<->l swap permutes the disjuncts), so no equality reasoning is needed
;; -- and pushing an equation into the goal, as `eer-close!' does, spells the
;; atoms differently in the two towers (i = i beside i = k).
(define (eer-close-flat! depth)
  (if (> depth 14) (error "eer-close-flat!: tower deeper than 14"))
  (let ((g (dk-goal)))
    (if (member g (dk-asms))
        (ass)
        (let* ((lhs (cadr g)) (rhs (caddr g))
               (ift (cond ((and (pair? rhs) (eq? (car rhs) 'IF)) rhs)
                          ((and (pair? lhs) (eq? (car lhs) 'IF)) lhs)
                          (#t (error "eer-close-flat!: no IF left and goal not in context"
                                     (expression->string g))))))
          (let ((d (eer-decide (cadr ift) (dk-asms))))
            (if (eq? d 'U)
                (let ((a (eer-first-unknown (cadr ift) (dk-asms))))
                  (use-em a
                    (lambda () (eer-close-flat! (+ depth 1)))
                    (lambda () (eer-close-flat! (+ depth 1)))))
                (let ((val (if (eq? d 'T) (caddr ift) (cadddr ift))))
                  (eer-if! (eq? d 'T) ift)
                  (if (member (dk-goal) (dk-asms))
                      (ass)
                      (begin (subst (list '= ift val))
                             (eer-close-flat! (+ depth 1)))))))))))

(define eer-fkl '(ELEM-F A n k l))
(define eer-flk '(ELEM-F A n l k))
(define eer-fsym-ext
  (list 'FORALL 'i (list 'IMPLIES '(IN i (INTERVAL 1 n))
    (list 'FORALL 'j (list 'IMPLIES '(IN j (INTERVAL 1 n))
      (list '= (list 'ENTRY eer-fkl 'i 'j) (list 'ENTRY eer-flk 'i 'j)))))))

(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL n (FORALL k (FORALL l (IMPLIES (IN n NN)
       (= (ELEM-F A n k l) (ELEM-F A n l k))))))))))
(dk-peel!)                                     ; IS-RING A, n in NN
(fact 'elem-f-type 'A 'n 'k 'l)
(fact 'elem-f-type 'A 'n 'l 'k)
(have! eer-fsym-ext
  (lambda ()
    (dk-peel!)
    (let* ((g  (dk-goal))
           (e1 (cadr g)) (e2 (caddr g))
           (a  (caddr e1)) (b (cadddr e1)))
      (let ((q1 (dk-fact! 'entry-of-elem-f 'A 'n 'k 'l a b))
            (q2 (dk-fact! 'entry-of-elem-f 'A 'n 'l 'k a b)))
        (subst q1)
        (subst q2)
        (eer-close-flat! 0)))))
(dk-focus-having! eer-fsym-ext)
(fact 'matrix-entry-extensionality 'n 'n '(CARR A) eer-fkl eer-flk)
(ass)
(eer-qed! 'elem-f-symmetric)

;;; ---- BLOCK and SNOC read-offs (were matrix.scm supports) -----------------

;; With (IN v (INTERVAL 1 lo)), (IN hi NN) and (<= lo hi) in context -- lo a
;; natural as well -- land (IN v (INTERVAL 1 hi)).  (interval-widen is the
;; lemma, but it loads after this file.)
(define (eer-carry! v lo hi)
  (fact 'interval-elt-in-nn 1 lo v)
  (fact 'interval-lo 1 lo v)
  (fact 'interval-hi 1 lo v)
  (fact 'nn-le-trans-guarded v lo hi)
  (fact 'interval-mem-intro 1 hi v))

;; the eigenvariables of the two index typings the last peel landed, in order
(define (eer-index-vars landed)
  (map cadr (filter (lambda (f) (and (pair? f) (eq? (car f) 'IN)
                                     (pair? (caddr f)) (eq? (car (caddr f)) 'INTERVAL)))
                    landed)))

;; Goal (= (ENTRY (MATOF m n LAM) a b) RHS), indices typed: land entry-of-matof's
;; equation in a lane whose definedness hypothesis DEFINED! proves (focus on the
;; goal (IN (LAM x y) SET) with x, y typed; DEFINED! gets x and y), then
;; `lam-b-h' it, and return the reduced equation's right side.
(define (eer-matof-eqn! defined!)
  (let* ((e   (cadr (dk-goal)))
         (mf  (cadr e))
         (mv  (cadr mf)) (nv (caddr mf)) (lam (cadddr mf))
         (a   (caddr e)) (b (cadddr e))
         (def (list 'FORALL 'i_ (list 'IMPLIES (list 'IN 'i_ (list 'INTERVAL 1 mv))
                (list 'FORALL 'j_ (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 nv))
                  (list 'IN (list lam 'i_ 'j_) 'SET))))))
         (eqn (list '= e (list lam a b))))
    (have! def
      (lambda ()
        (let ((xy (eer-index-vars (dk-peel!))))
          (lam-b)
          (defined! (car xy) (cadr xy)))))
    (dk-focus-having! def)
    (have! eqn (lambda () (fact 'entry-of-matof mv nv lam a b) (ass)))
    (dk-focus-having! eqn)
    (lam-b-h eqn)
    (let ((q (find-first (lambda (f) (and (pair? f) (eq? (car f) '=) (equal? (cadr f) e)
                                          (not (equal? f eqn))))
                         (dk-asms))))
      (if (not q) (error "eer-matof-eqn!: lam-b-h landed no reduced equation"))
      q)))

;; (IN t X) in context: close (IN t SET)
(define (eer-set-from! t x)
  (fact 'membership-implies-sethood t x)
  (ass))

(sp (make-wff
  '(FORALL P (FORALL k (FORALL l (FORALL i (FORALL j (FORALL m (FORALL n (FORALL X
     (IMPLIES (IN k NN) (IMPLIES (IN l NN) (IMPLIES (IN P (MAT m n X)) (IMPLIES (<= k m) (IMPLIES (<= l n)
     (IMPLIES (IN i (INTERVAL 1 k)) (IMPLIES (IN j (INTERVAL 1 l))
       (= (ENTRY (BLOCK P k l) i j) (ENTRY P i j)))))))))))))))))))
(dk-peel!)
(fact 'mat-rows-in-nn 'm 'n 'X 'P)
(fact 'mat-cols-in-nn 'm 'n 'X 'P)
(mac 'BLOCK)
(eer-matof-eqn!
  (lambda (x y)                                ; goal (IN (ENTRY P x y) SET)
    (eer-carry! x 'k 'm)
    (eer-carry! y 'l 'n)
    (fact 'entry-in-carrier 'm 'n 'X 'P x y)
    (eer-set-from! (list 'ENTRY 'P x y) 'X)))
(ass)
(eer-qed! 'entry-of-block)

;; The SNOC tabulators: (IF (= p (succ n)) new (ENTRY old p q)) in one index p,
;; the other index q ranging over [1,1].  DEFINED! for both: split on the test.
(define (eer-snoc-defined! p q new old sv kind)
  ;; goal (IN (IF (= p (succ n)) new (ENTRY ...)) SET); p in [1, succ n]
  (let ((ift (cadr (dk-goal))))
    (use-em (cadr ift)
      (lambda ()
        (eer-if! #t ift)
        (subst (list '= ift (caddr ift)))
        (eer-set-from! new sv))
      (lambda ()
        (eer-if! #f ift)
        (subst (list '= ift (cadddr ift)))
        ;; p <= n: p <= succ n and p /= succ n
        (fact 'interval-elt-in-nn 1 '(succ n) p)
        (fact 'interval-lo 1 '(succ n) p)
        (fact 'interval-hi 1 '(succ n) p)
        (fact 'nn-le-succ-cases 'n p)
        (have! (list '<= p 'n) (lambda () (prop)))
        (dk-focus-having! (list '<= p 'n))
        (fact 'interval-mem-intro 1 'n p)
        (fact 'one-in-interval-1)
        (if (eq? kind 'col)
            (fact 'entry-in-carrier 'n 1 sv old p 1)
            (fact 'entry-in-carrier 1 'n sv old 1 p))
        (eer-set-from! (cadddr ift) sv)))))

;; index p in [1,n] (so p /= succ n): the tabulated value is the old entry
(define (eer-snoc-old! p ift)
  (fact 'interval-elt-in-nn 1 'n p)
  (fact 'interval-hi 1 'n p)
  (fact 'nn-le-imp-neq-succ 'n p)
  (eer-if! #f ift)
  (ass))

;; the index succ n: the tabulated value is the new element
(define (eer-snoc-new! ift)
  (have! (cadr ift) (lambda () (rfl)))
  (dk-focus-having! (cadr ift))
  (eer-if! #t ift)
  (ass))

;; (succ n) in [1, succ n]
(define (eer-succ-top!)
  (fact 'nn-le-refl '(succ n))
  (fact 'nn-one-le-succ 'n)
  (fact 'interval-mem-intro 1 '(succ n) '(succ n)))

(sp (make-wff
  '(FORALL w (FORALL n (FORALL v (FORALL i (FORALL X
     (IMPLIES (IN n NN)
     (IMPLIES (IN w (MAT n 1 X))
     (IMPLIES (IN v X)
     (IMPLIES (IN i (INTERVAL 1 n))
       (= (ENTRY (SNOC-COL w n v) i 1) (ENTRY w i 1)))))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(fact 'one-in-interval-1)
(fact 'nn-le-succ 'n)
(eer-carry! 'i 'n '(succ n))
(mac 'SNOC-COL)
(let ((q (eer-matof-eqn! (lambda (x y) (eer-snoc-defined! x y 'v 'w 'X 'col)))))
  (subst q)                                    ; goal (= <IF> (ENTRY w i 1))
  (eer-snoc-old! 'i (cadr (dk-goal))))
(eer-qed! 'entry-of-snoc-col)

(sp (make-wff
  '(FORALL w (FORALL n (FORALL v (FORALL X (IMPLIES (IN n NN)
     (IMPLIES (IN w (MAT n 1 X))
     (IMPLIES (IN v X)
     (= (ENTRY (SNOC-COL w n v) (succ n) 1) v))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(fact 'one-in-interval-1)
(eer-succ-top!)
(mac 'SNOC-COL)
(let ((q (eer-matof-eqn! (lambda (x y) (eer-snoc-defined! x y 'v 'w 'X 'col)))))
  (subst q)                                    ; goal (= <IF> v)
  (eer-snoc-new! (cadr (dk-goal))))
(eer-qed! 'snoc-col-last)

(sp (make-wff
  '(FORALL c (FORALL n (FORALL r (FORALL j (FORALL X
     (IMPLIES (IN n NN)
     (IMPLIES (IN c (MAT 1 n X))
     (IMPLIES (IN r X)
     (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (SNOC-ROW c n r) 1 j) (ENTRY c 1 j)))))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(fact 'one-in-interval-1)
(fact 'nn-le-succ 'n)
(eer-carry! 'j 'n '(succ n))
(mac 'SNOC-ROW)
(let ((q (eer-matof-eqn! (lambda (x y) (eer-snoc-defined! y x 'r 'c 'X 'row)))))
  (subst q)
  (eer-snoc-old! 'j (cadr (dk-goal))))
(eer-qed! 'entry-of-snoc-row)

(sp (make-wff
  '(FORALL c (FORALL n (FORALL r (FORALL X (IMPLIES (IN n NN)
     (IMPLIES (IN c (MAT 1 n X))
     (IMPLIES (IN r X)
     (= (ENTRY (SNOC-ROW c n r) 1 (succ n)) r))))))))))
(dk-peel!)
(fact 'nn-succ-closed 'n)
(fact 'nn-one-in)
(fact 'one-in-interval-1)
(eer-succ-top!)
(mac 'SNOC-ROW)
(let ((q (eer-matof-eqn! (lambda (x y) (eer-snoc-defined! y x 'r 'c 'X 'row)))))
  (subst q)
  (eer-snoc-new! (cadr (dk-goal))))
(eer-qed! 'snoc-row-last)

;;; ---- MATADD / MATSCALE read-offs (were matrix.scm supports) --------------
;;;
;;; These tabulate at (NTH 1 (SIZE P)) by (NTH 2 (SIZE P)), not at m by n.  The
;;; row index puts 1 <= m, so mat-size-rows / mat-size-cols say those two terms
;;; ARE m and n; the dimension and index typings are restated at the SIZE terms
;;; (so entry-of-matof and the beta see literally the tabulator's box), and the
;;; definedness lane carries its indices back to [1,m] x [1,n] for
;;; entry-in-carrier.

(define eer-r1 '(NTH 1 (SIZE P)))
(define eer-c1 '(NTH 2 (SIZE P)))

;; with (= T D) in context: land (IN T NN) and each (IN v (INTERVAL 1 T)) from
;; the D forms
(define (eer-restate! t d vs)
  (have! (list 'IN t 'NN) (lambda () (subst (list '= t d)) (ass)))
  (dk-focus-having! (list 'IN t 'NN))
  (for-each (lambda (v)
              (let ((f (list 'IN v (list 'INTERVAL 1 t))))
                (have! f (lambda () (subst (list '= t d)) (ass)))
                (dk-focus-having! f)))
            vs))

;; the converse, inside a definedness lane: (IN v (INTERVAL 1 T)) in context,
;; land (IN v (INTERVAL 1 D))
(define (eer-back! v t d)
  (let ((f (list 'IN v (list 'INTERVAL 1 d))))
    (have! f (lambda () (subst (list '= d t)) (ass)))
    (dk-focus-having! f)))

(define (eer-size-setup!)
  (fact 'mat-rows-in-nn 'm 'n '(CARR A) 'P)
  (fact 'mat-cols-in-nn 'm 'n '(CARR A) 'P)
  (dk-one-le-from! 'i 'm)
  (fact 'mat-size-rows 'm 'n '(CARR A) 'P)       ; NTH(1, SIZE P) = m
  (fact 'mat-size-cols 'm 'n '(CARR A) 'P)       ; NTH(2, SIZE P) = n
  (eer-restate! eer-r1 'm '(i))
  (eer-restate! eer-c1 'n '(j)))

(sp (make-wff
  '(FORALL A (FORALL m (FORALL n (FORALL P (FORALL Q
     (IMPLIES (IS-RING A)
     (IMPLIES (IN P (MAT m n (CARR A)))
     (IMPLIES (IN Q (MAT m n (CARR A)))
     (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATADD A P Q) i j)
          ((ADD A) (ENTRY P i j) (ENTRY Q i j)))))))))))))))))
(dk-peel!)
(eer-size-setup!)
(mac 'MATADD)
(eer-matof-eqn!
  (lambda (x y)                                ; goal (IN ((ADD A) P_xy Q_xy) SET)
    (eer-back! x eer-r1 'm)
    (eer-back! y eer-c1 'n)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P x y)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'Q x y)
    (fact 'ring-add-closed 'A (list 'ENTRY 'P x y) (list 'ENTRY 'Q x y))
    (eer-set-from! (list '(ADD A) (list 'ENTRY 'P x y) (list 'ENTRY 'Q x y)) '(CARR A))))
(ass)
(eer-qed! 'matadd-entry)

(sp (make-wff
  '(FORALL A (FORALL m (FORALL n (FORALL r (FORALL P
     (IMPLIES (IS-RING A)
     (IMPLIES (IN r (CARR A))
     (IMPLIES (IN P (MAT m n (CARR A)))
     (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
     (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
       (= (ENTRY (MATSCALE A r P) i j)
          ((MUL A) r (ENTRY P i j)))))))))))))))))
(dk-peel!)
(eer-size-setup!)
(mac 'MATSCALE)
(eer-matof-eqn!
  (lambda (x y)                                ; goal (IN ((MUL A) r P_xy) SET)
    (eer-back! x eer-r1 'm)
    (eer-back! y eer-c1 'n)
    (fact 'entry-in-carrier 'm 'n '(CARR A) 'P x y)
    (fact 'ring-carrier-closed-mul 'A 'r (list 'ENTRY 'P x y))
    (eer-set-from! (list '(MUL A) 'r (list 'ENTRY 'P x y)) '(CARR A))))
(ass)
(eer-qed! 'matscale-entry)

;;; ---- SUBMAT read-off (was a mat-equiv.scm support) -------------------------

(sp (make-wff
  '(FORALL S (FORALL p (FORALL q (FORALL i (FORALL j (FORALL X
     (IMPLIES (IN p NN) (IMPLIES (IN q NN)
     (IMPLIES (IN S (MAT (succ p) (succ q) X))
     (IMPLIES (IN i (INTERVAL 1 p)) (IMPLIES (IN j (INTERVAL 1 q))
       (= (ENTRY (SUBMAT S p q) i j) (ENTRY S (succ i) (succ j))))))))))))))))
(dk-peel!)
(mac 'SUBMAT)
(eer-matof-eqn!
  (lambda (x y)                                ; goal (IN (ENTRY S (succ x) (succ y)) SET)
    (for-each
     (lambda (v hi)                            ; succ v in [1, succ hi]
       (fact 'interval-elt-in-nn 1 hi v)
       (fact 'interval-hi 1 hi v)
       (fact 'nn-succ-closed v)
       (fact 'nn-succ-closed hi)
       (fact 'nn-one-le-succ v)
       (fact 'nn-succ-mono v hi)
       (fact 'interval-mem-intro 1 (list 'succ hi) (list 'succ v)))
     (list x y) '(p q))
    (fact 'entry-in-carrier '(succ p) '(succ q) 'X 'S (list 'succ x) (list 'succ y))
    (eer-set-from! (list 'ENTRY 'S (list 'succ x) (list 'succ y)) 'X)))
(ass)
(eer-qed! 'entry-of-submat)

;;; ---- END spliced block (2026-09-16) --------------------------------------
