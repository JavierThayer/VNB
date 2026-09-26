;;; prop.scm -- `prop': decide a propositional entailment, then PROVE it.
;;;
;;; WHAT IT IS FOR.  A proof reaches leaves that are propositionally trivial and
;;; still cost three hand-picked steps each: `x in a, x in b |- x in a or (x in b
;;; and not(x in a))' wants (oi-l)(ass); its sibling wants (oi-r) and a
;;; conjunction split; the branch where the context holds both `P' and `not P'
;;; wants (ai) on the negation.  Each is obvious, each is DIFFERENT, and picking
;;; the wrong one leaves you circling a leaf you can see through.  `prop' decides
;;; the whole class: if the goal follows from the context by propositional logic
;;; alone, it closes it; if it does not, it says why.
;;;
;;; WHAT IT IS NOT.  It is not an oracle and it adds no trust.  It DECIDES
;;; semantically (a three-valued truth evaluation over the atoms) and then
;;; DISCHARGES the goal through the ordinary tactics -- di / ai / oi-l / oi-r /
;;; ass / pbc / use-em / have! / detach!, every one of which is a kernel rule or
;;; a composite of them.  Nothing is asserted on the decision procedure's
;;; say-so: if the replay cannot close the goal it errors, and the proof stays
;;; open.  A `qed' over a proof that used `prop' bills exactly what it would
;;; have billed had you typed the steps yourself, which is nothing.
;;;
;;; HOW IT WORKS.  It splits on undecided ATOMS with `use-em' until the branch's
;;; assignment settles the leaf one way or the other: either the GOAL comes out
;;; TRUE, and is proved structurally, or some CONTEXT formula comes out FALSE,
;;; and is refuted structurally.  Since the entailment was checked first, every
;;; branch settles.  Proving and refuting are mutually recursive and each is
;;; driven by the assignment, so neither ever searches:
;;;
;;;   refute A (A is in the context and evaluates FALSE)
;;;     atom          not A is in context too -> (ai '(not A)) is NOT-ELIM, which
;;;                   closes the goal whatever the goal is
;;;     (not B)       B is TRUE -> prove B into the context, then (ai '(not B))
;;;     (and B C)     (ai) splits it; refute whichever conjunct is FALSE
;;;     (or B C)      (ai) branches; both disjuncts are FALSE, refute each
;;;     (implies B C) B is TRUE, C is FALSE -> prove B, detach! to land C, refute C
;;;     (iff B C)     (ai) gives both implications; refute the FALSE one
;;;
;;;   prove X (X evaluates TRUE, and is the current goal)
;;;     in context    (ass)
;;;     (and B C)     (di) splits the goal; prove each
;;;     (or B C)      (oi-l) / (oi-r) toward whichever disjunct is TRUE; prove it
;;;     (implies B C) (di) assumes B; prove C if TRUE, else B is FALSE and now in
;;;                   the context, so refute it
;;;     (not B)       (di) assumes B with goal FALSITY; refute B
;;;     (iff B C)     (di) gives both directions, each handled as implies
;;;
;;; Termination: every recursive call is on a strict subformula, and every split
;;; decides an atom that was undecided, of which there are finitely many.
;;;
;;; WHAT COUNTS AS AN ATOM.  Anything whose head is not AND / OR / NOT / IMPLIES
;;; / IFF: `x in a', an equation, and also a whole `forall([x], ...)'.  Quantified
;;; formulas are opaque propositions here -- that is what makes this
;;; PROPOSITIONAL logic -- and two of them count as the same atom when they are
;;; alpha-equivalent, since that is when the kernel's `ass' would match them.
;;;
;;; Loads after driver-kit (it calls use-em / have! / dk-*) and interactive.

(define *prop-atom-cap* 12
  ;; 2^12 = 4096 assignments, each a walk over the context: instant, and past
  ;; any leaf a person is looking at.  The cap exists so a goal carrying thirty
  ;; distinct atoms declines in a sentence instead of vanishing for an hour.
  )

(define *prop-connectives* '(AND OR NOT IMPLIES IFF))

(define (prop--conn f)
  (and (pair? f) (memq (car f) *prop-connectives*) (car f)))

;;; Atom identity is ALPHA-equivalence, matching what `ass' and the context
;;; membership test do; vnb-guard because alpha-equiv? can error on a malformed
;;; formula, and its warning record would otherwise read as true.
;;; `equal?' first: atom identity is asked once per atom per assignment, so this
;;; is the inner loop of the whole procedure, and the overwhelmingly common case
;;; is two occurrences of the same subtree.  alpha-equiv? is the fallback that
;;; makes two spellings of a bound variable one atom.
(define (prop--same? a b)
  (or (equal? a b)
      (eq? #t (vnb-guard (lambda () (alpha-equiv? a b))))))

(define (prop--all? pred lst)
  (or (null? lst) (and (pred (car lst)) (prop--all? pred (cdr lst)))))

(define (prop--atoms-of f acc)
  (let ((c (prop--conn f)))
    (cond ((eq? c 'NOT) (prop--atoms-of (not-body f) acc))
          (c (prop--atoms-of (binary-right f) (prop--atoms-of (binary-left f) acc)))
          ((memq f '(TRUTH FALSITY)) acc)
          ((any-pred (lambda (a) (prop--same? a f)) acc) acc)
          (else (append acc (list f))))))

(define (prop--atoms formulas)
  (let loop ((fs formulas) (acc '()))
    (if (null? fs) acc (loop (cdr fs) (prop--atoms-of (car fs) acc)))))

;;; THE ASSUMPTIONS CONNECTED TO THE GOAL, transitively through shared atoms.
;;;
;;; Why this exists (2026-08-22).  The cap counts the atoms of the WHOLE context,
;;; and `push-not-h' discharges its FORALL case through `prop' -- so in exactly
;;; the situation push-not was written for ("suppose it is NOT continuous",
;;; where the definition has just been unfolded and the context is therefore
;;; large) the push failed: 16 distinct atoms against a cap of 12, reported as
;;; `have!: THUNK left the side goal open' several steps later.  The push only
;;; ever needs the atoms of the formula under the NOT; the caller's context is
;;; irrelevant to it.
;;;
;;; SOUND, and by the same argument `ineq' uses for skipping a non-arithmetic
;;; premise: a goal that follows from a SUBSET of the assumptions follows from
;;; all of them, so dropping assumptions can only make `prop' prove LESS.  It is
;;; NOT an equivalence -- a context contradictory in a part disconnected from
;;; the goal entails everything, and the narrowed run will not see it -- which
;;; is why this is a FALLBACK tried only after the full context has been
;;; declined by the cap, never a replacement for it.  Nothing that closed
;;; before can stop closing.
;;; The relevant assumption sets by RADIUS, LARGEST FIRST: radius 0 is the
;;; empty set (the goal alone); radius r+1 adds every assumption sharing an atom
;;; with the goal or with radius r.  The last radius is prop--relevant's
;;; transitive closure.  Each set keeps the context's order.
(define (prop--radius-sets asms goal)
  (let loop ((keep '()) (pool asms) (atoms (prop--atoms (list goal))) (acc (list '())))
    (let ((hit (filter (lambda (f)
                         (any-pred (lambda (a) (any-pred (lambda (b) (prop--same? a b)) atoms))
                                   (prop--atoms (list f))))
                       pool)))
      (if (null? hit)
          acc
          (let ((keep2 (filter (lambda (f) (or (memq f keep) (memq f hit))) asms)))
            (loop keep2
                  (filter (lambda (f) (not (memq f hit))) pool)
                  (prop--atoms (cons goal keep2))
                  (cons keep2 acc)))))))

(define (prop--relevant asms goal)
  (let iterate ((keep '()) (pool asms) (atoms (prop--atoms (list goal))))
    (let split ((l pool) (hit '()) (miss '()) (acc atoms))
      (cond
        ((null? l)
         (if (null? hit)
             (reverse keep)
             (iterate (append keep (reverse hit)) (reverse miss) acc)))
        ((any-pred (lambda (a) (any-pred (lambda (b) (prop--same? a b)) acc))
                   (prop--atoms (list (car l))))
         (split (cdr l) (cons (car l) hit) miss (prop--atoms-of (car l) acc)))
        (else (split (cdr l) hit (cons (car l) miss) acc))))))

;;; ----------------------------------------------------------------------
;;; Three-valued evaluation.  'T / 'F / 'U (undetermined).  Kleene: a value is
;;; definite exactly when every completion of the assignment agrees, which is
;;; what lets the replay commit to a branch before all atoms are decided.

(define (prop--lookup atom asg)
  (let loop ((a asg))
    (cond ((null? a) 'U)
          ((prop--same? (caar a) atom) (cdar a))
          (else (loop (cdr a))))))

(define (prop--not3 v) (cond ((eq? v 'T) 'F) ((eq? v 'F) 'T) (else 'U)))

(define (prop--eval f asg)
  (let ((c (prop--conn f)))
    (cond
      ((eq? f 'TRUTH)   'T)
      ((eq? f 'FALSITY) 'F)
      ((eq? c 'NOT) (prop--not3 (prop--eval (not-body f) asg)))
      ((eq? c 'AND)
       (let ((l (prop--eval (binary-left f) asg)) (r (prop--eval (binary-right f) asg)))
         (cond ((or (eq? l 'F) (eq? r 'F)) 'F)
               ((and (eq? l 'T) (eq? r 'T)) 'T)
               (else 'U))))
      ((eq? c 'OR)
       (let ((l (prop--eval (binary-left f) asg)) (r (prop--eval (binary-right f) asg)))
         (cond ((or (eq? l 'T) (eq? r 'T)) 'T)
               ((and (eq? l 'F) (eq? r 'F)) 'F)
               (else 'U))))
      ((eq? c 'IMPLIES)
       (let ((l (prop--eval (binary-left f) asg)) (r (prop--eval (binary-right f) asg)))
         (cond ((eq? l 'F) 'T)
               ((eq? r 'T) 'T)
               ((and (eq? l 'T) (eq? r 'F)) 'F)
               (else 'U))))
      ((eq? c 'IFF)
       (let ((l (prop--eval (binary-left f) asg)) (r (prop--eval (binary-right f) asg)))
         (cond ((or (eq? l 'U) (eq? r 'U)) 'U)
               ((eq? l r) 'T)
               (else 'F))))
      (else (prop--lookup f asg)))))

;;; The decision.  Returns #f when PREMISES entail GOAL, or a COUNTERMODEL --
;;; the assignment satisfying every premise and falsifying the goal -- when they
;;; do not.
;;;
;;; PRUNED, not a flat 2^n walk.  A countermodel needs every premise TRUE and
;;; the goal FALSE, so the moment a partial assignment makes some premise
;;; definitely FALSE, or the goal definitely TRUE, no completion of it can be
;;; one and the whole subtree goes.  The three-valued evaluator is exactly the
;;; "definitely, under every completion" test that licenses the cut.  It matters
;;; because `prop' is probed on every what-now: unpruned, an eleven-atom context
;;; cost 280 ms per probe; pruned it is a few.
(define (prop--countermodel premises goal atoms)
  (let loop ((as atoms) (asg '()))
    (cond
      ((any-pred (lambda (p) (eq? 'F (prop--eval p asg))) premises) #f)
      ((eq? 'T (prop--eval goal asg)) #f)
      ((null? as)
       (and (prop--all? (lambda (p) (eq? 'T (prop--eval p asg))) premises)
            (eq? 'F (prop--eval goal asg))
            (list asg)))                      ; wrapped: '() is a real answer
      (else
       (or (loop (cdr as) (cons (cons (car as) 'T) asg))
           (loop (cdr as) (cons (cons (car as) 'F) asg)))))))

;;; ----------------------------------------------------------------------
;;; Replay.  Every step is checked: a tactic that does not fire is a bug in
;;; here, not a reason to carry on in the wrong branch.

(define (prop--step! label thunk)
  (let ((n (proof-state-focus *ps*)))
    (thunk)
    (if (not (dk-fired? n))
        (error (string-append "prop: " label " did not fire -- goal was")
               (expression->string (wff-formula (sequent-node-assertion n)))))))

(define (prop--in-context? f)
  (any-pred (lambda (a) (prop--same? a f)) (dk-asms)))

;;; The context formula this branch dies on: one evaluating FALSE.  Preferring a
;;; LITERAL keeps the refutation short -- an atom or its negation closes in one
;;; step, where a nested implication costs a cut and a detach.
(define (prop--find-false asg)
  (let ((false-ones (filter (lambda (a) (eq? 'F (prop--eval a asg))) (dk-asms))))
    (cond ((null? false-ones) #f)
          ((any-pred (lambda (a) (not (prop--conn a))) false-ones))
          ((any-pred (lambda (a) (and (eq? 'NOT (prop--conn a))
                                      (not (prop--conn (not-body a)))))
                     false-ones))
          (else (car false-ones)))))

;;; Is G literally `(OR P (NOT P))'?  `equal?', not alpha, because that is the
;;; test `em-prove!' itself applies before it will fire.
(define (prop--em-instance? g)
  (and (pair? g) (eq? (car g) 'OR) (= (length g) 3)
       (equal? (caddr g) (list 'NOT (cadr g)))))

(define (prop--undecided atoms asg)
  (any-pred (lambda (a) (eq? 'U (prop--lookup a asg))) atoms))

;;; Seed the assignment from the LITERALS already in the context, so `prop' does
;;; not split on something the context has settled -- which would also trip
;;; use-em's own guard against splitting a decided proposition.
(define (prop--seed)
  (let loop ((as (dk-asms)) (acc '()))
    (cond ((null? as) acc)
          ((not (prop--conn (car as)))
           (loop (cdr as) (cons (cons (car as) 'T) acc)))
          ((and (eq? 'NOT (prop--conn (car as)))
                (not (prop--conn (not-body (car as)))))
           (loop (cdr as) (cons (cons (not-body (car as)) 'F) acc)))
          (else (loop (cdr as) acc)))))

;;; PROVE X as the current goal.  X must evaluate 'T under ASG.
(define (prop--prove! x asg)
  (let ((c (prop--conn x)))
    (cond
      ((prop--in-context? x) (prop--step! "ass" ass))
      ((eq? c 'AND)
       (let ((kids (dk-opened (lambda () (prop--step! "di (and-intro)" di)))))
         (for-each (lambda (k)
                     (dk-focus! k)
                     (prop--prove! (dk-goal) asg))
                   kids)))
      ((eq? c 'OR)
       (if (eq? 'T (prop--eval (binary-left x) asg))
           (begin (prop--step! "oi-l" oi-l) (prop--prove! (binary-left x) asg))
           (begin (prop--step! "oi-r" oi-r) (prop--prove! (binary-right x) asg))))
      ((eq? c 'IMPLIES)
       (prop--step! "di (implies-intro)" di)
       (prop--after-assuming! (binary-left x) (binary-right x) asg))
      ((eq? c 'NOT)
       (prop--step! "di (not-intro)" di)          ; assumes the body, goal FALSITY
       (prop--refute! (not-body x) asg))
      ((eq? c 'IFF)
       (let ((kids (dk-opened (lambda () (prop--step! "di (iff-intro)" di))))
             (l (binary-left x)) (r (binary-right x)))
         (for-each (lambda (k)
                     (dk-focus! k)
                     ;; each direction assumed one side and must prove the other
                     (if (prop--same? (dk-goal) r)
                         (prop--after-assuming! l r asg)
                         (prop--after-assuming! r l asg)))
                   kids)))
      (else
       (error "prop: cannot prove this goal -- it is true under the assignment but not in the context"
              (expression->string x))))))

;;; After `di' has assumed ANTE with consequent CONS as the goal: either the
;;; consequent is true and we prove it, or the antecedent is false -- and it is
;;; now a context formula, so refuting it closes the branch.
(define (prop--after-assuming! ante cons- asg)
  (if (eq? 'T (prop--eval cons- asg))
      (prop--prove! cons- asg)
      (prop--refute! ante asg)))

;;; REFUTE A: A is a context formula evaluating 'F under ASG.  Closes the
;;; current goal, whatever it is (NOT-ELIM takes no subgoals).
(define (prop--refute! a asg)
  (let ((c (prop--conn a)))
    (cond
      ;; FALSITY itself: prove (not FALSITY) -- one di and an ass -- and use it.
      ((eq? a 'FALSITY)
       (have! '(NOT FALSITY)
              (lambda () (prop--step! "di (not-intro)" di) (prop--step! "ass" ass)))
       (prop--step! "ai (not-elim)" (lambda () (ai '(NOT FALSITY)))))
      ((eq? c 'NOT)
       (let ((b (not-body a)))
         (if (not (prop--in-context? b))
             (have! b (lambda () (prop--prove! b asg))))
         (prop--step! "ai (not-elim)" (lambda () (ai a)))))
      ((eq? c 'AND)
       (prop--step! "ai (and-elim)" (lambda () (ai a)))
       (prop--refute! (if (eq? 'F (prop--eval (binary-left a) asg))
                          (binary-left a)
                          (binary-right a))
                      asg))
      ((eq? c 'OR)
       (let ((kids (dk-opened (lambda () (prop--step! "ai (or-elim)" (lambda () (ai a))))))
             (l (binary-left a)) (r (binary-right a)))
         (for-each (lambda (k)
                     (dk-focus! k)
                     ;; each branch assumed one disjunct; both are false
                     (prop--refute! (if (prop--in-context? l) l r) asg))
                   kids)))
      ((eq? c 'IMPLIES)
       (let ((ante (binary-left a)) (cons- (binary-right a)))
         (if (not (prop--in-context? ante))
             (have! ante (lambda () (prop--prove! ante asg))))
         (prop--step! "detach!" (lambda () (detach! a)))
         (prop--refute! cons- asg)))
      ((eq? c 'IFF)
       (let ((l (binary-left a)) (r (binary-right a)))
         (prop--step! "ai (iff-elim)" (lambda () (ai a)))
         (let ((fwd (list 'IMPLIES l r)) (bwd (list 'IMPLIES r l)))
           (prop--refute! (if (eq? 'F (prop--eval fwd asg)) fwd bwd) asg))))
      (else                                     ; an atom: its negation is here
       (prop--step! "ai (not-elim)" (lambda () (ai (list 'NOT a))))))))

;;; Close the current branch.  Three ways, in order of cost: the goal is already
;;; an assumption; the goal is TRUE under this branch's assignment, so prove it;
;;; some context formula is FALSE, so refute it.  Failing all three, split on an
;;; undecided atom and close both halves.
;;;
;;; NOTE THE ABSENCE OF `pbc'.  The first draft opened with one -- C |- G iff
;;; C + {not G} is unsatisfiable is the tidy way to say what this does -- and it
;;; broke on `x in a or not(x in a)': `pbc' had put `not (P or not P)' in the
;;; context, and the `use-em' below cuts exactly `(P or not P)', whose
;;; obligation `em-prove!' discharges with a `pbc' of its own.  That second pbc
;;; re-assumes a formula already in the context, `context-add-assumption' is
;;; alpha-idempotent, and the cut self-loops instead of branching -- CLAUDE.md's
;;; own trap, reached through a helper two levels down.  Checking the GOAL
;;; against the assignment directly needs no pbc, and is shorter.
(define (prop--close! asg atoms)
  (let ((g (dk-goal)))
    (cond
      ((prop--in-context? g) (prop--step! "ass" ass))
      ((eq? 'T (prop--eval g asg)) (prop--prove! g asg))
      ((prop--find-false asg) => (lambda (bad) (prop--refute! bad asg)))
      ;; The goal IS excluded middle.  Splitting on its own atom would cut
      ;; `(OR p (not p))' -- the goal itself -- and a cut whose side goal
      ;; reproduces the focus sequent hash-conses back onto it, leaving one leaf
      ;; where two were wanted ("use-cases: cut produced no main branch").
      ;; `em-prove!' is the move for this shape and takes no split at all.
      ;; Reached only when the atom is still undecided: with it decided the goal
      ;; evaluates TRUE and the clause above proves it with a single oi.
      ((prop--em-instance? g) (prop--step! "em-prove!" em-prove!))
      (else
       (let ((p (prop--undecided atoms asg)))
         (if (not p)
             (error "prop: every atom is decided, the goal is not true and no context formula is false -- the branch is satisfiable, which the decision procedure denied"
                    (map expression->string (dk-asms))))
         (use-em p
                 (lambda () (prop--close! (cons (cons p 'T) asg) atoms))
                 (lambda () (prop--close! (cons (cons p 'F) asg) atoms))))))))

;;; ----------------------------------------------------------------------
;;; The tactic.

;;; All of `prop's reporting goes through here.  `quietly' -- which every
;;; copilot PROBE runs inside -- suppresses `show' and soft warnings but not a
;;; bare `display', so a `prop' in what-now's live-fire lane would print a
;;; countermodel into the panel every time it declined.
(define (prop--say thunk) (if (not *vnb-quiet*) (thunk)))

;;; One line, on the soft-warning channel, so the DECLINE is visible to someone
;;; driving from a workspace: there the whole consequence of a declined tactic
;;; is that the panel repaints unchanged, which reads as a key that does not
;;; work.  The detail below still goes to the REPL.
(define (prop--warn-line asg atoms)
  (vnb--print-warning
   (string-append
    "prop: does not follow propositionally -- false when "
    (let loop ((as atoms) (acc "") (first #t))
      (if (null? as)
          acc
          (loop (cdr as)
                (string-append acc (if first "" ", ")
                               (expression->string (car as))
                               (if (eq? 'T (prop--lookup (car as) asg))
                                   " true" " false"))
                #f))))))

(define (prop--report-countermodel asg atoms)
  (prop--warn-line asg atoms)
  (prop--say (lambda ()
  (display ";; prop: this does NOT follow by propositional logic.")
  (newline)
  (display ";; It is false when:")
  (newline)
  (for-each (lambda (a)
              (display ";;   ")
              (display (expression->string a))
              (display "  is  ")
              (display (if (eq? 'T (prop--lookup a asg)) "TRUE" "FALSE"))
              (newline))
            atoms)
  (display ";; Every quantified formula counts as one opaque atom here, so a goal")
  (newline)
  (display ";; needing an instantiation will land in this branch: supply the")
  (newline)
  (display ";; instance first (fact / inst+) and run (prop) again.")
  (newline)))
  #f)

(define (prop)
  (if (not *ps*)
      (begin (prop--say (lambda () (display ";; prop: no proof in progress.") (newline)))
             #f)
      (let* ((goal  (dk-goal))
             (asms  (dk-asms))
             (atoms (prop--atoms (cons goal asms))))
        ;; Over the cap on the FULL context, retry on the goal-connected part.
        ;; See prop--relevant: sound because a subset proof is a proof, and a
        ;; fallback rather than a replacement because it cannot see a
        ;; contradiction living in the disconnected remainder.
        ;; 2026-09-16: when the transitive closure is still over the cap, grow
        ;; the relevant set one HOP at a time from the goal (radius 1 = the
        ;; assumptions sharing an atom with the goal, radius 2 = those sharing an
        ;; atom with radius 1, ...) and keep the LARGEST radius that fits.  A
        ;; fixed goal-adjacent tier was tried first and missed facts that reach
        ;; the goal only through a guard -- `not(p = 0)' beside
        ;; `q = 0 => (p = 0 or r = 0)' when the goal is `not(q = 0)' (found by a
        ;; repair agent the same day).  Radius 0 is the goal alone, which is what
        ;; a tautological guard needs.  Same soundness argument as
        ;; prop--relevant: every candidate is a subset of the context.
        (if (> (length atoms) *prop-atom-cap*)
            (let try ((cands (prop--radius-sets asms goal)))   ; largest first
              (if (pair? cands)
                  (let ((rats (prop--atoms (cons goal (car cands)))))
                    (if (and (< (length rats) (length atoms))
                             (<= (length rats) *prop-atom-cap*))
                        (begin (set! asms (car cands)) (set! atoms rats))
                        (try (cdr cands)))))))
        (cond
          ((> (length atoms) *prop-atom-cap*)
           (prop--say (lambda ()
             (display ";; prop: ") (display (length atoms))
             (display " distinct atoms, over the cap of ")
             (display *prop-atom-cap*) (display " (*prop-atom-cap*).")
             (newline)
             (display ";; Narrowing to the goal's neighbourhood (every radius, down to the goal alone) did not get under it.")
             (newline)
             (display ";; Narrow the context first, or raise the cap knowing it is 2^n.")
             (newline)))
           #f)
          ((prop--countermodel asms goal atoms)
           => (lambda (cm) (prop--report-countermodel (car cm) atoms)))
          (else
           ;; RECORD (prop), NOT ITS EXPANSION.  The sub-steps do fire through
           ;; the ordinary tactics and are ordinary kernel inferences -- that is
           ;; what makes this debt-free -- but they are driven with `dk-focus!',
           ;; which moves the focus WITHOUT recording a command.  An emitted
           ;; script of the expansion therefore replays the right steps against
           ;; whatever leaf the engine happens to have focused, and dies at
           ;; `qed: proof is not complete'.  One `(prop)' replays exactly,
           ;; because prop is a decision procedure: same goal, same context,
           ;; same steps.  (Every composite that drives focus has this problem;
           ;; `minimize!' and a bodied `use-em' still do.)
           ;; The undo mark is taken OUTSIDE the fluid-let, for the same reason
           ;; the record-cmd! is: prop records ITSELF, so backup-one must take
           ;; back the whole decision, not its last internal step.  (Inside the
           ;; fluid-let *replaying?* is #t and vnb--take-mark returns #f.)
           (let ((mark (vnb--take-mark '(prop))))
             (fluid-let ((*replaying?* #t))
               (prop--close! (prop--seed) atoms))
             (vnb--undo-push! mark))
           (record-cmd! 'prop '())
           (vnb--capture-step! '(prop))
           #t)))))
