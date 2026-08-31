;;; nn-parity-proof.scm -- Peano arithmetic on NN: from the two recursion
;;; equations (structure-library/nn-arith.scm) to parity and even-square.
;;;
;;; Everything here is PROVEN.  The only asserted inputs are nn-add-succ and
;;; nn-mul-succ (the definition of + and * by recursion on succ, which
;;; number-systems.scm never states); succ-injectivity comes from the ordinal
;;; axioms, and the rest is induction.
;;;
;;; The chain:
;;;   nn-one-is-succ-zero   1 = succ(0)                       (arith, ground)
;;;   nn-succ-inj           succ a = succ b => a = b          (ordinals)
;;;   nn-succ-nonzero       succ n /= 0                       (order lemmas)
;;;   nn-succ-plus-one      succ n = n + 1                    (nn-add-succ)
;;;   nn-add-cancel         a + c = b + c => a = b            (induction on c)
;;;   nn-mul-zero           a * 0 = 0                         (distrib + cancel)
;;;   nn-two-mul            2 * k = k + k                     (crs)
;;;   nn-plus-two           x + 2 = succ(succ x)              (nn-add-succ x2)
;;;   nn-nonzero-is-succ    n /= 0 => n = succ q              (induction)
;;;   nn-parity            n = 2k  or  n = succ(2k)           (induction)
;;;   nn-parity-exclusive   2x /= succ(2y)                    (induction)
;;;   nn-even-square        even(n*n) => even(n)              (parity + exclusive)
;;;
;;; "even" is spelled out as (FORSOME k (AND (IN k NN) (= n (* 2 k)))) rather
;;; than introduced as a predicate: one def-predicate would buy nothing here and
;;; would need its own unfold at every use.

;;; --- local kit (np- prefix: never name a top-level define like a tactic) ---
(define (np-leaves)
  (filter (lambda (s) (and (not (sequent-node-grounded? s))
                           (null? (sequent-node-in-arrows s))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (np-any pred lst)
  (let loop ((l lst)) (cond ((null? l) #f) ((pred (car l)) (car l)) (else (loop (cdr l))))))
(define (np-goalof s) (wff-formula (sequent-node-assertion s)))
(define (np-goal) (np-goalof (proof-state-focus *ps*)))
(define (np-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))

;;; Focus the unique open leaf whose goal satisfies PRED.  ERRORS on a miss:
;;; a focus helper that returns #f and leaves focus put hides every later bug.
(define (np-foc! pred)
  (let ((l (np-any (lambda (s) (pred (np-goalof s))) (np-leaves))))
    (if (not l) (error "np-foc!: no open leaf matches") (begin (dk-focus! l) l))))
(define (np-foc-eq! form)
  (np-foc! (lambda (g) (alpha-equiv? g form))))

;;; Close the FOCUSED goal from its own context: `ass' it, or -- if it is a
;;; conjunction -- di it and close each conjunct the same way.  Strictly local:
;;; it never scans the whole leaf set, so it cannot wander into a sibling branch.
(define (np-from-context!)
  (let ((g (np-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (np-from-context!))
                 (dk-opened (lambda () (di)))))
      ;; a GROUND membership -- (IN 2 NN) -- is not in context and never will be:
      ;; it is decided, not assumed.  Same rule `fact' uses for ground guards.
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g)))
       (arith))
      (else (ass)))))

;;; (np-cut! FORM [THUNK]) -- cut FORM, discharge the side goal with THUNK
;;; (default: straight from context), and return focus to the MAIN branch.
;;;
;;; Both halves matter.  `cut' opens two children and the engine picks the focus,
;;; so a driver that carries on blind lands wherever it lands; and the two
;;; children are told apart HERE by node identity, not by goal shape.  In this
;;; file that is not fussiness: the base and step branches of every induction
;;; below have the SAME goal (a = b), so any search-by-goal snaps into the wrong
;;; branch and every later command silently runs in it.  (It did.)
(define (np-cut! form #!optional thunk)
  (let* ((new  (dk-opened (lambda () (cut form))))
         (side (or (np-any (lambda (s) (alpha-equiv? (np-goalof s) form)) new)
                   (error "np-cut!: no side goal for" form)))
         (main (or (np-any (lambda (s) (not (eq? s side))) new)
                   (error "np-cut!: no main branch for" form))))
    (dk-focus! side)
    (if (default-object? thunk) (np-from-context!) (thunk))
    (dk-focus! main)
    main))

;;; (ni) opens base and step, and BOTH may be FORALL-headed -- the base is the
;;; body at 0, which still binds the inner variables.  The head is therefore no
;;; discriminant; the BINDER is.  Getting this wrong runs every base tactic
;;; inside the step branch, in silence.
(define (np-binder-is? v)
  (lambda (s) (let ((g (np-goalof s)))
                (and (pair? g) (eq? (car g) 'FORALL) (eq? (quantifier-var g) v)))))

(define (np-qed! name)
  (if (proof-done? *ps*)
      (qed name)
      (begin
        (display "\n*** nn-parity-proof: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ")
                    (display (expression->string (np-goalof l)))
                    (newline)
                    (for-each (lambda (w)
                                (display "      | ")
                                (display (expression->string (wff-formula w)))
                                (newline))
                              (list-head (sequent-node-assumptions l)
                                         (min 6 (length (sequent-node-assumptions l))))))
                  (proof-open-goals *ps*))
        (error "nn-parity-proof: unfinished proof" name))))

;;; =======================================================================
;;; 1 = succ(0).  Ground, so `arith' decides it.  Used as a macete to cross
;;; between the literal 1 and the successor form.
(sp (make-wff '(= 1 (succ 0))))
(arith)
(np-qed! 'nn-one-is-succ-zero)

;;; =======================================================================
;;; succ is injective on NN.  NOT asserted: succ_ORD is injective
;;; (ord-succ-injective) and agrees with succ on NN (ord-succ-nn), both kernel
;;; axioms in ordinals.scm.
(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (IMPLIES (= (succ a) (succ b)) (= a b))))))))
(di)(di)(di)(di)(di)
(fact 'nn-subset-ord 'a)
(fact 'nn-subset-ord 'b)
(fact 'ord-succ-nn 'a)
(fact 'ord-succ-nn 'b)
;; succ_ord(a) = succ(a) = succ(b) = succ_ord(b)
(np-cut! '(= (succ_ORD a) (succ_ORD b))
         (lambda ()
           (subst '(= (succ_ORD a) (succ a)))
           (subst '(= (succ_ORD b) (succ b)))
           (ass)))
;; ord-succ-injective's antecedent is a CONJUNCTION, which `fact' will not
;; split -- so cut it, close it from context, and then `fact' detaches in one go.
(np-cut! '(AND (IN a ORD) (AND (IN b ORD) (= (succ_ORD a) (succ_ORD b)))))
(fact 'ord-succ-injective 'a 'b)
(ass)
(np-qed! 'nn-succ-inj)

;;; =======================================================================
;;; succ n /= 0.  Straight out of the order calculus, with no contradiction and
;;; no rewriting: nn-le-imp-neq-succ at k:=n, j:=0 says 0 <= n => 0 /= succ n,
;;; and 0 <= n is nn-zero-le.  neq-sym turns it around.
;;;
;;; Note what does NOT appear: the guard (IN 0 NN) of nn-le-imp-neq-succ's inner
;;; universal.  It is a ground arithmetic truth, so `fact' now proves it on the
;;; spot (pc--land-ground-antecedent, proof-commands.scm) instead of demanding it
;;; in context.  Before that, this line needed a hand-cut typing of the literal.
;;; `di' takes the NOT goal apart too (NOT A is A => FALSITY), so after the two
;;; di's the hypothesis (succ n = 0) is in context and the goal is FALSITY; the
;;; landed NOT is then discharged by not-elim (`ai'), the idiom metric-top-proof
;;; uses.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (NOT (= (succ n) 0))))))
(di)(di)
(fact 'nn-zero-le 'n)                   ; 0 <= n
(fact 'nn-le-imp-neq-succ 'n 0)         ; ... => NOT (0 = succ n)
(fact 'neq-sym 0 '(succ n))             ; ... => NOT (succ n = 0)
(ai '(NOT (= (succ n) 0)))              ; not-elim against (succ n = 0): FALSITY
(np-qed! 'nn-succ-nonzero)

;;; =======================================================================
;;; succ n = n + 1.  THE bridge: (ni) hands you a symbolic (succ n), and every
;;; ring tool (crs, simp) speaks + and *.  Proved, from nn-add-succ at b := 0.
;;;
;;; `subst' takes an in-context equation in EITHER orientation
;;; (pi-eq-subst!, primitive-inferences.scm:491-494), so a landed (= X Y) can
;;; rewrite the goal's Y back to X.  That is what makes the hypothesis-side
;;; rewriting below unnecessary.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (succ n) (+ n 1))))))
(di)(di)
(mac 'nn-one-is-succ-zero)              ; goal: succ n = n + succ(0)
(fact 'nn-add-succ 'n 0)                ; n + succ 0 = succ (n + 0)
(fact 'nn-add-zero 'n)                  ; n + 0 = n
(fact 'nn-succ-closed 'n)               ; IN (succ n) NN -- see below
(subst '(= (+ n (succ 0)) (succ (+ n 0))))
(subst '(= (+ n 0) n))                  ; goal: succ n = succ n
;; and THAT is not closed by reflexivity for free: `=' is PARTIAL, so t = t IS
;; a definedness claim (pi-reflexivity!, primitive-inferences.scm:612).  succ(n)
;; is not syntactically self-defined, so the rule wants a context witness -- the
;; (IN (succ n) NN) landed just above.
(rfl)
(np-qed! 'nn-succ-plus-one)

;;; =======================================================================
;;; a * succ(b) = a*b + a -- the recursion equation for `*', PROVEN.
;;;
;;; It was a `reference' support in structure-library/nn-arith.scm, whose SCOPE
;;; note posed it as the next candidate for a `definitional' stamp by analogy
;;; with nn-add-succ ("measured and deliberately NOT stamped ... one explicit
;;; decision per fact").  No stamp is needed: unlike addition's recursion, the
;;; multiplicative one FOLLOWS from what number-systems.scm already states.
;;; succ(b) = b + 1 (nn-succ-plus-one, immediately above), then distributivity
;;; and the unit law, both `primitive':
;;;
;;;     a * succ(b) = a * (b + 1) = a*b + a*1 = a*b + a
;;;
;;; WHAT IT DOES NOT SETTLE.  The proof runs THROUGH nn-succ-plus-one, which is
;;; proved from nn-add-succ -- `definitional' since 2026-08-24, and stamped with
;;; a comment saying so.  So this theorem does not discharge that claim; it
;;; removes a SECOND, independent assertion that was never needed, and the
;;; asymmetry is the content: addition's recursion has to be assumed here,
;;; multiplication's does not.  The reverse move is NOT available -- deriving
;;; nn-add-succ from nn-succ-plus-one would be circular.
;;;
;;; PLACED HERE, not in a file of its own, because nn-succ-plus-one is produced
;;; by this file and consumed by line 216 below: no separate file can sit
;;; between the two.
(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
                 (FORALL b (IMPLIES (IN b NN)
                   (= (* a (succ b)) (+ (* a b) a))))))))
(di)
(fact 'nn-succ-plus-one 'b)
(subst '(= (succ b) (+ b 1)))            ; goal: a * (b + 1) = a*b + a
(fact 'nn-one-in)
(have! '(AND (IN a NN) (AND (IN b NN) (IN 1 NN))))
(fact 'nn-distributive 'a 'b 1)          ; a * (b + 1) = a*b + a*1
(subst '(= (* a (+ b 1)) (+ (* a b) (* a 1))))
(have! '(AND (IN a NN) (IN 1 NN)))
(fact 'nn-mul-comm 'a 1)                 ; a*1 = 1*a
(subst '(= (* a 1) (* 1 a)))
(fact 'nn-one-mul 'a)                    ; 1*a = a
(subst '(= (* 1 a) a))                   ; goal: a*b + a = a*b + a
;; `=' is PARTIAL, so t = t is a definedness claim (see nn-succ-plus-one above):
;; the closure facts are what license the `rfl', not decoration.
(have! '(AND (IN a NN) (IN b NN)))
(fact 'nn-mul-closed 'a 'b)
(have! '(AND (IN (* a b) NN) (IN a NN)))
(fact 'nn-add-closed '(* a b) 'a)
(rfl)
(np-qed! 'nn-mul-succ)

;;; =======================================================================
;;; nn-add-cancel USED TO BE HERE, proved by induction on c from nn-add-succ.
;;; It is gone, and that is the point: cancellation is a fact about GROUPS, and
;;; NN gets it because NN <= ZZ and ZZ's addition IS the surface `+'.  See
;;; theorem-library/cancellation.scm -- group-cancel-left, carried to the rings
;;; by the RING-ADDITIVE-AG view and to the integers by transport!.  Fifty lines
;;; of induction, deleted, for a fact that was never NN's to prove.

;;; =======================================================================
;;; x + 2 = succ(succ x).  Two applications of nn-add-succ, with 2 = succ(succ 0)
;;; supplied by `arith' (ground).
(sp (make-wff '(= 2 (succ (succ 0)))))
(arith)
(np-qed! 'nn-two-is-succ-succ-zero)

(sp (make-wff '(FORALL x (IMPLIES (IN x NN) (= (+ x 2) (succ (succ x)))))))
(di)(di)
(mac 'nn-two-is-succ-succ-zero)          ; goal: x + succ(succ 0) = succ(succ x)
(fact 'nn-add-succ 'x '(succ 0))         ; x + succ(succ 0) = succ(x + succ 0)
(fact 'nn-add-succ 'x 0)                 ; x + succ 0        = succ(x + 0)
(fact 'nn-add-zero 'x)                   ; x + 0 = x
(subst '(= (+ x (succ (succ 0))) (succ (+ x (succ 0)))))
(subst '(= (+ x (succ 0)) (succ (+ x 0))))
(subst '(= (+ x 0) x))
(fact 'nn-succ-closed 'x)
(fact 'nn-succ-closed '(succ x))         ; definedness for rfl (= is PARTIAL)
(rfl)
(np-qed! 'nn-plus-two)

;;; 2 * succ(k) = succ(succ(2*k)) -- the successor step of doubling.
(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
                 (= (* 2 (succ k)) (succ (succ (* 2 k))))))))
(di)(di)
(fact 'nn-mul-succ 2 'k)                 ; 2 * succ k = 2*k + 2   (guard (IN 2 NN): ground)
(fact 'nn-mul-closed 2 'k)               ; AND-antecedent
(np-cut! '(AND (IN 2 NN) (IN k NN)) (lambda () (np-from-context!)))
(fact 'nn-mul-closed 2 'k)               ; IN (* 2 k) NN
(fact 'nn-plus-two '(* 2 k))             ; (2*k) + 2 = succ(succ(2*k))
(subst '(= (* 2 (succ k)) (+ (* 2 k) 2)))   ; goal IS nn-plus-two at 2*k now
(ass)
(np-qed! 'nn-two-mul-succ)

;;; =======================================================================
;;; n /= 0 => n = succ(q) for some q in NN.  Induction: the base is vacuous
;;; (0 /= 0 is absurd), the step is its own witness.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
                 (IMPLIES (NOT (= n 0))
                   (FORSOME q (AND (IN q NN) (= n (succ q)))))))))
(define np-nz-branches (dk-opened (lambda () (ni))))
(define np-nz-step
  (or (np-any (np-binder-is? 'n) np-nz-branches) (error "nonzero-is-succ: no step")))
(define np-nz-base
  (or (np-any (lambda (s) (not (eq? s np-nz-step))) np-nz-branches)
      (error "nonzero-is-succ: no base")))

;; base: (NOT (= 0 0)) => ... -- absurd hypothesis.
(dk-focus! np-nz-base)
(di)                                     ; assume NOT (0 = 0)
(pbc)                                    ; goal FALSITY
(np-cut! '(= 0 0) (lambda () (arith)))
(ai '(NOT (= 0 0)))
;; step: succ(n) /= 0 => succ n = succ q, with q := n.
(dk-focus! np-nz-step)
(di)                                     ; n ; IN n NN
(di)                                     ; the IH (unused: the step is direct)
(di)                                     ; assume succ n /= 0
(ew 'n)                                  ; witness q := n
(fact 'nn-succ-closed 'n)                ; also the definedness `rfl' wants
;; goal (AND (IN n NN) (= (succ n) (succ n))): the left half is in context, the
;; right half is reflexivity -- NOT an assumption, so np-from-context! cannot do
;; it (`=' is partial, hence `rfl', hence the typing above).
(for-each (lambda (k)
            (dk-focus! k)
            (if (eq? (car (np-goal)) 'IN) (ass) (rfl)))
          (dk-opened (lambda () (di))))
(np-qed! 'nn-nonzero-is-succ)

;;; =======================================================================
;;; PARITY, the dichotomy:  every natural is 2k or succ(2k).
;;;
;;; This is the half that carries the weight, and the half no algebraic identity
;;; gives you: it is exactly where induction is unavoidable.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
                 (FORSOME k (AND (IN k NN)
                                 (OR (= n (* 2 k)) (= n (succ (* 2 k))))))))))
(define np-p-branches (dk-opened (lambda () (ni))))
(define np-p-step (or (np-any (np-binder-is? 'n) np-p-branches)
                      (error "nn-parity: no step branch")))
(define np-p-base (or (np-any (lambda (s) (not (eq? s np-p-step))) np-p-branches)
                      (error "nn-parity: no base branch")))

;;; base: 0 = 2*0.  Ground, so `arith' does the lot (including (IN 0 NN)).
(dk-focus! np-p-base)
(ew 0)
(for-each (lambda (k)
            (dk-focus! k)
            (if (eq? (car (np-goal)) 'OR) (begin (oi-l) (arith)) (arith)))
          (dk-opened (lambda () (di))))

;;; step: from n = 2w  or  n = succ(2w), get succ(n) = 2k' or succ(n) = succ(2k').
(dk-focus! np-p-step)
(di)                                     ; n ; IN n NN
(define np-p-ih (dk-landed-1 (lambda () (di))))          ; the IH (a FORSOME)
(ai np-p-ih)                                             ; skolemize it
;; The witness is a FRESH eigenvariable -- never guess its name.  Find the landed
;; disjunction and read the witness off it.
(define np-p-conj
  ;; ai lands the skolemized body as ONE conjunction: (IN w NN) and (OR ...).
  (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'AND)
                               (pair? (caddr f)) (eq? (car (caddr f)) 'OR)))
              (np-asms))
      (error "nn-parity: the skolemized IH did not land")))
(ai np-p-conj)                                           ; (IN w NN) and the OR
(define np-p-or
  (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (np-asms))
      (error "nn-parity: no disjunction in context")))
(define np-p-w (caddr (caddr (cadr np-p-or))))            ; the w in (= n (* 2 w))

;;; (IN (* 2 w) NN) -- wanted by rfl's definedness check in both cases.
(np-cut! (list 'AND '(IN 2 NN) (list 'IN np-p-w 'NN))
         (lambda () (np-from-context!)))
(fact 'nn-mul-closed 2 np-p-w)
(fact 'nn-succ-closed (list '* 2 np-p-w))

;;; Two cases.  Tell them apart by the disjunct each branch ASSUMED, never by the
;;; goal -- the goal is identical in both.
(define np-p-cases (dk-opened (lambda () (ai np-p-or))))
(define np-p-even-case
  (or (np-any (lambda (s) (np-any (lambda (w) (equal? (wff-formula w)
                                                      (list '= 'n (list '* 2 np-p-w))))
                                  (sequent-node-assumptions s)))
              np-p-cases)
      (error "nn-parity: no even case")))
(define np-p-odd-case
  (or (np-any (lambda (s) (not (eq? s np-p-even-case))) np-p-cases)
      (error "nn-parity: no odd case")))

;;; even case: n = 2w, so succ(n) = succ(2w) -- the RIGHT disjunct, same witness.
(dk-focus! np-p-even-case)
(ew np-p-w)
(for-each
  (lambda (k)
    (dk-focus! k)
    (if (eq? (car (np-goal)) 'OR)
        (begin (oi-r)
               (subst (list '= 'n (list '* 2 np-p-w)))     ; succ n -> succ(2w)
               (rfl))
        (ass)))
  (dk-opened (lambda () (di))))

;;; odd case: n = succ(2w), so succ(n) = succ(succ(2w)) = 2*succ(w) -- the LEFT
;;; disjunct, witness succ(w)  (nn-two-mul-succ).
(dk-focus! np-p-odd-case)
(fact 'nn-succ-closed np-p-w)
(fact 'nn-two-mul-succ np-p-w)                            ; 2*succ w = succ(succ(2w))
(ew (list 'succ np-p-w))
(for-each
  (lambda (k)
    (dk-focus! k)
    (if (eq? (car (np-goal)) 'OR)
        (begin (oi-l)
               (subst (list '= 'n (list 'succ (list '* 2 np-p-w))))   ; succ n -> succ(succ(2w))
               (subst (list '= (list '* 2 (list 'succ np-p-w))
                            (list 'succ (list 'succ (list '* 2 np-p-w)))))
               (rfl))
        (ass)))
  (dk-opened (lambda () (di))))
(np-qed! 'nn-parity)

;;; =======================================================================
;;; y = 0  or  y = succ(q).  (nn-nonzero-is-succ needs y /= 0 established first;
;;; this gives the case split with no contradiction to set up.)
(sp (make-wff '(FORALL y (IMPLIES (IN y NN)
                 (OR (= y 0) (FORSOME q (AND (IN q NN) (= y (succ q)))))))))
(define np-zs-branches (dk-opened (lambda () (ni))))
(define np-zs-step (or (np-any (np-binder-is? 'y) np-zs-branches)
                       (error "nn-zero-or-succ: no step")))
(define np-zs-base (or (np-any (lambda (s) (not (eq? s np-zs-step))) np-zs-branches)
                       (error "nn-zero-or-succ: no base")))
(dk-focus! np-zs-base)
(oi-l) (arith)                           ; 0 = 0
(dk-focus! np-zs-step)
(di)                                     ; y ; IN y NN
(di)                                     ; the IH (not needed: the step is direct)
(oi-r)
(ew 'y)                                  ; q := y
(fact 'nn-succ-closed 'y)
(for-each (lambda (k)
            (dk-focus! k)
            (if (eq? (car (np-goal)) 'IN) (ass) (rfl)))
          (dk-opened (lambda () (di))))
(np-qed! 'nn-zero-or-succ)

;;; =======================================================================
;;; EXCLUSIVITY:  2x is never succ(2y).  "No natural is both even and odd."
;;;
;;; This is the fact that makes even/odd a DICHOTOMY rather than a mere cover,
;;; and (transported to ZZ) it is exactly the user's `2k /= 1'.
(sp (make-wff '(FORALL x (IMPLIES (IN x NN)
                 (FORALL y (IMPLIES (IN y NN)
                   (NOT (= (* 2 x) (succ (* 2 y))))))))))
(define np-e-branches (dk-opened (lambda () (ni))))
(define np-e-step (or (np-any (np-binder-is? 'x) np-e-branches)
                      (error "nn-parity-exclusive: no step")))
(define np-e-base (or (np-any (lambda (s) (not (eq? s np-e-step))) np-e-branches)
                      (error "nn-parity-exclusive: no base")))

;;; base: 2*0 = 0, and 0 is not a successor.
(dk-focus! np-e-base)
(di)                                     ; y ; IN y NN
(di)                                     ; assume 2*0 = succ(2y); goal FALSITY
(np-cut! '(AND (IN 2 NN) (IN y NN)))
(fact 'nn-mul-closed 2 'y)               ; IN (* 2 y) NN
(np-cut! '(= (* 2 0) 0) (lambda () (arith)))
(np-cut! '(= 0 (succ (* 2 y)))
         (lambda ()
           (subst '(= 0 (* 2 0)))        ; 0 -> 2*0 (the equation, used in reverse)
           (ass)))
(fact 'nn-succ-nonzero '(* 2 y))         ; NOT (succ (2y) = 0)
(fact 'neq-sym '(succ (* 2 y)) 0)        ; NOT (0 = succ (2y))
(ai '(NOT (= 0 (succ (* 2 y)))))         ; against the cut: FALSITY

;;; step: 2*succ(x) = succ(succ(2x)), so a solution at succ(x) gives one at x.
(dk-focus! np-e-step)
(di)                                     ; x ; IN x NN
(define np-e-ih (dk-landed-1 (lambda () (di))))          ; IH: forall y. 2x /= succ(2y)
(di)                                     ; y ; IN y NN
(di)                                     ; assume 2*succ(x) = succ(2y); goal FALSITY
(np-cut! '(AND (IN 2 NN) (IN x NN)))
(fact 'nn-mul-closed 2 'x)
(fact 'nn-succ-closed '(* 2 x))
(fact 'nn-two-mul-succ 'x)               ; 2*succ x = succ(succ(2x))
(fact 'nn-zero-or-succ 'y)               ; y = 0  or  y = succ q
(define np-e-or
  (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (np-asms))
      (error "nn-parity-exclusive: no y-split in context")))
(define np-e-cases (dk-opened (lambda () (ai np-e-or))))
(define np-e-zero
  (or (np-any (lambda (s) (np-any (lambda (w) (equal? (wff-formula w) '(= y 0)))
                                  (sequent-node-assumptions s)))
              np-e-cases)
      (error "nn-parity-exclusive: no y=0 case")))
(define np-e-succ
  (or (np-any (lambda (s) (not (eq? s np-e-zero))) np-e-cases)
      (error "nn-parity-exclusive: no y=succ case")))

;;; y = 0: then succ(2y) = succ(0), so succ(succ(2x)) = succ(0), so succ(2x) = 0.
(dk-focus! np-e-zero)
(np-cut! '(= (succ (succ (* 2 x))) (succ (* 2 0)))
         (lambda ()
           (subst '(= (succ (succ (* 2 x))) (* 2 (succ x))))   ; reverse of two-mul-succ
           (subst '(= 0 y))                                     ; 0 -> y  (equation reversed)
           (ass)))
(fact 'nn-mul-closed 2 0)
(fact 'nn-succ-inj '(succ (* 2 x)) '(* 2 0))     ; succ(2x) = 2*0
(np-cut! '(= (* 2 0) 0) (lambda () (arith)))
(np-cut! '(= (succ (* 2 x)) 0)
         (lambda ()
           (subst '(= 0 (* 2 0)))        ; 0 -> 2*0: the goal has no 2*0 to rewrite
           (ass)))
(fact 'nn-succ-nonzero '(* 2 x))
(ai '(NOT (= (succ (* 2 x)) 0)))

;;; y = succ(q): then succ(2y) = succ(succ(succ(2q))), and stripping two succs
;;; gives 2x = succ(2q) -- which the IH forbids at q.
(dk-focus! np-e-succ)
;; this branch assumed the FORSOME, not its body: skolemize it first.
(define np-e-ex
  (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (np-asms))
      (error "nn-parity-exclusive: no existential in the y=succ case")))
(define np-e-conj (dk-landed-1 (lambda () (ai np-e-ex))))   ; (IN q NN) and y = succ q
(ai np-e-conj)                                             ; split that conjunction
(define np-e-q (cadr (caddr (caddr np-e-conj))))           ; the q in y = succ(q)
(np-cut! (list 'AND '(IN 2 NN) (list 'IN np-e-q 'NN)))
(fact 'nn-mul-closed 2 np-e-q)
(fact 'nn-succ-closed (list '* 2 np-e-q))
(fact 'nn-two-mul-succ np-e-q)                            ; 2*succ q = succ(succ(2q))
;; succ(succ(2x)) = succ(2y) = succ(2*succ q) = succ(succ(succ(2q)))
(np-cut! (list '= '(succ (succ (* 2 x)))
               (list 'succ (list 'succ (list 'succ (list '* 2 np-e-q)))))
         (lambda ()
           (subst '(= (succ (succ (* 2 x))) (* 2 (succ x))))
           (subst (list '= (list 'succ (list 'succ (list '* 2 np-e-q)))
                        (list '* 2 (list 'succ np-e-q))))
           (subst (list '= (list 'succ np-e-q) 'y))
           (ass)))
(fact 'nn-succ-closed (list 'succ (list '* 2 np-e-q)))
(fact 'nn-succ-inj '(succ (* 2 x)) (list 'succ (list 'succ (list '* 2 np-e-q))))
(fact 'nn-succ-inj '(* 2 x) (list 'succ (list '* 2 np-e-q)))   ; 2x = succ(2q)
(inst+ np-e-ih np-e-q)                                    ; IH at q: NOT (2x = succ(2q))
(ai (list 'NOT (list '= '(* 2 x) (list 'succ (list '* 2 np-e-q)))))
(np-qed! 'nn-parity-exclusive)

;;; =======================================================================
;;; nn-even-square : p*p even => p even, ON THE NATURALS.  The fact the sqrt(2)
;;; descent rests on -- and the reason the whole argument stays in NN.
;;;   even(n) := forsome k in NN. n = 2*k.
;;; By nn-parity p = 2w or p = succ(2w).  If p = 2w, done.  If p = succ(2w) then
;;; p*p = succ(2*(2w*w + w)) is ODD, and p*p = 2m is EVEN -- nn-parity-exclusive.
(sp (make-wff '(FORALL p (IMPLIES (IN p NN)
                 (IMPLIES (FORSOME m (AND (IN m NN) (= (* p p) (* 2 m))))
                          (FORSOME k (AND (IN k NN) (= p (* 2 k)))))))))
(di)(di)(di)                             ; p ; IN p NN ; assume (forsome m. p*p = 2m)
(define es-mex (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (np-asms))
                   (error "nn-even-square: no m")))
(ai es-mex)
(define es-mc (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                            (eq? (car (caddr f)) '=))) (np-asms))
                  (error "nn-even-square: no m body")))
(ai es-mc)
(define es-meq (or (np-any (lambda (f) (and (pair? f) (eq? (car f) '=)
                             (equal? (cadr f) '(* p p)))) (np-asms))
                   (error "nn-even-square: no p*p=2m")))
(define es-m (caddr (caddr es-meq)))     ; p*p = 2*m
(fact 'nn-parity 'p)                     ; p = 2w or p = succ(2w)
(define es-par (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (np-asms))
                   (error "nn-even-square: nn-parity did not land")))
(ai es-par)
(define es-pc (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'AND) (pair? (caddr f))
                            (eq? (car (caddr f)) 'OR))) (np-asms))
                  (error "nn-even-square: no parity body")))
(ai es-pc)
(define es-por (or (np-any (lambda (f) (and (pair? f) (eq? (car f) 'OR))) (np-asms))
                   (error "nn-even-square: no 2w/succ split")))
(define es-w (caddr (caddr (cadr es-por))))   ; p = 2*w
(fact 'nn-mul-closed 2 es-w)             ; (needs AND guard) -- 2w in NN
(np-cut! (list 'AND '(IN 2 NN) (list 'IN es-w 'NN)) (lambda () (np-from-context!)))
(fact 'nn-mul-closed 2 es-w)             ; 2w in NN
;; case split on p = 2w vs p = succ(2w).
(for-each
  (lambda (leaf)
    (dk-focus! leaf)
    (let ((peq (np-any (lambda (f) (and (pair? f) (eq? (car f) '=) (eq? (cadr f) 'p))) (np-asms))))
      (cond
        ((equal? peq (list '= 'p (list '* 2 es-w)))     ; p = 2w : EVEN, witness w
         (ew es-w)
         (for-each (lambda (k)
                     (dk-focus! k)
                     (if (eq? (car (np-goal)) 'IN) (np-from-context!) (ass)))
                   (dk-opened (lambda () (di)))))
        (else                                           ; p = succ(2w) : ODD, contradiction
         (pbc)                                          ; goal (forsome k...) -> assume NOT, FALSITY
         ;; p*p = 2m (even) but p = succ(2w) makes p*p odd: build the odd witness.
         ;; p*p = succ(2w)*succ(2w).  crs: = succ(succ( 2*(2*w*w + w) )) after
         ;; nn-two-mul-succ chains -- but simpler: derive succ(2j) = 2m form and
         ;; hit nn-parity-exclusive.  witness j = 2*w*w + 2*w  (p*p = succ(2j)).
         (let* ((ww  (list '* es-w es-w))
                (j   (list '+ (list '* 2 ww) (list '* 2 es-w))))
           ;; typings
           (np-cut! (list 'AND (list 'IN es-w 'NN) (list 'IN es-w 'NN)) (lambda () (np-from-context!)))
           (fact 'nn-mul-closed es-w es-w)              ; w*w
           (np-cut! (list 'AND '(IN 2 NN) (list 'IN ww 'NN)) (lambda () (np-from-context!)))
           (fact 'nn-mul-closed 2 ww)                   ; 2*w*w
           (np-cut! (list 'AND (list 'IN (list '* 2 ww) 'NN) (list 'IN (list '* 2 es-w) 'NN))
                    (lambda () (np-from-context!)))
           (fact 'nn-add-closed (list '* 2 ww) (list '* 2 es-w))   ; j in NN
           (np-cut! (list 'AND '(IN 2 NN) (list 'IN j 'NN)) (lambda () (np-from-context!)))
           (fact 'nn-mul-closed 2 j)                     ; 2j in NN (for succ(2j)=2j+1)
           (fact 'nn-parity-exclusive es-m j)           ; NOT (2m = succ(2j))
           ;; show 2m = succ(2j): 2m = p*p = succ(2w)*succ(2w) = succ(2j).
           (np-cut! (list '= (list '* 2 es-m) (list 'succ (list '* 2 j)))
                    (lambda ()
                      (subst (list '= (list '* 2 es-m) '(* p p)))   ; 2m -> p*p (reverse of es-meq)
                      (subst peq)                                    ; p -> succ(2w)
                      ;; goal succ(2w)*succ(2w) = succ(2j): pure identity? has succ.
                      (fact 'nn-succ-plus-one (list '* 2 es-w))      ; succ(2w) = 2w+1
                      (subst (list '= (list 'succ (list '* 2 es-w)) (list '+ (list '* 2 es-w) 1)))
                      (fact 'nn-succ-plus-one (list '* 2 j))         ; succ(2j) = 2j+1
                      (subst (list '= (list 'succ (list '* 2 j)) (list '+ (list '* 2 j) 1)))
                      (crs)))
           (ai (list 'NOT (list '= (list '* 2 es-m) (list 'succ (list '* 2 j))))))))))
  (dk-opened (lambda () (ai es-por))))
(np-qed! 'nn-even-square)
