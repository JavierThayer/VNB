;;; push-not.scm -- (push-not-h k): push a NOT inward through one quantifier or
;;; implication in assumption k, and DISCHARGE the step through kernel rules.
;;;
;;; THE GAP IT FILLS.  Every "suppose it does NOT converge / is NOT bounded / is
;;; NOT continuous" argument in analysis opens by pushing a negation through the
;;; alternations of a definition.  VNB had no move for it: `prop' is
;;; propositional and treats every FORALL/FORSOME as an opaque atom, `contra' is
;;; arithmetic, and there is no NNF anywhere in the tree.  By hand each
;;; alternation is a `pbc', a `have!' with an `ew' lane inside, and an `ai' --
;;; about forty generic lines before any mathematics starts.  Found 2026-08-19
;;; while proving `subsequence-principle', whose driver had to route around it.
;;;
;;; WHAT IT IS NOT: it does not produce Negation Normal Form, and is not called
;;; `nnf-h' for that reason.  Full NNF would rewrite `A implies B' into
;;; `not A or B' throughout, turning VNB's readable guarded statements into
;;; disjunctions -- harder to read, not easier.  This stops at the first head
;;; that is neither a quantifier nor an implication, which is the user's rule
;;; and the right one: `forsome([x in s], not B)' is where you want to be.
;;;
;;; THE GUARDED SURFACE IS A FIXED POINT, which is what makes this readable.
;;; `forall([x in s], B)' parses to `(forall x (implies (in x s) B))', and
;;; pushing the NOT through gives `(forsome x (and (in x s) (not B)))', which is
;;; exactly what `forsome([x in s], not(B))' parses to -- checked, not assumed.
;;; The guard moves from the antecedent of an implication to the left conjunct
;;; of a conjunction and is never negated.
;;;
;;; ONE STEP PER CALL, and that is a fact about the output rather than a
;;; limitation chosen for convenience: after a quantifier step the NOT sits
;;; UNDER a binder, so there is nothing at the top level left to push.  The
;;; follow-up is always the same and the tactic names it -- `ai' to skolemize a
;;; landed FORSOME, `ai' to split a landed AND -- after which `push-not-h'
;;; applies again.  Four alternations is roughly eight one-line moves instead of
;;; forty.
;;;
;;; IT ADDS NO TRUST.  Every case discharges through `pbc' / `di' / `ew' / `ai'
;;; / `prop' / `have!', all of which are kernel rules or already-trusted
;;; composites; the demo derivation bills `modulo 0'.
;;;
;;; Loads after `prop' (which it uses) and `driver-kit' (`have!'), and BEFORE the
;;; theorem library -- deliberately.  `contra' is the cautionary tale: it loads
;;; at load.scm:1423, after every proof file, so no library proof can reach it
;;; and none does (measured: zero occurrences of `(contra)' under
;;; theorem-library/, calculus/ or structure-library/).

;;; -----------------------------------------------------------------------
;;; The syntactic step.  F is the formula UNDER the NOT; returns the pushed
;;; formula, or #f when F's head is neither a quantifier nor an implication.
;;;
;;; THE GUARDED UNIVERSAL IS ONE STEP, NOT TWO.  `forall([x in s], B)' is
;;; `(forall x (implies (in x s) B))', so pushing through the quantifier alone
;;; would land `forsome([x], not(x in s implies B))' -- correct, and not what
;;; anybody wants to read.  Pushing through the quantifier AND its guard lands
;;; `(forsome x (and (in x s) (not B)))', which is exactly what
;;; `forsome([x in s], not(B))' parses to.  The surface form is a fixed point of
;;; the transformation and this is where that is cashed in.  Same for the
;;; guarded existential.
;;; The TARGET, given the formula under the NOT and the context.  Shared by the
;;; tactic and the What Now lane, so the panel can never offer a move the tactic
;;; would refuse.  #f means "nothing to push through".
;;;
;;; DE MORGAN IS IN, on the user's call (2026-08-20: "in contrast to
;;; constructivists, I like arguments by contradiction") -- and with the useful
;;; case taken first.  `NOT (AND P Q)' in general only yields the disjunction,
;;; which forces a case split; but when one conjunct is ALREADY IN THE CONTEXT
;;; -- which is the situation every time, since the conjunct is the typing
;;; hypothesis you unfolded the definition with -- the negation of the OTHER
;;; conjunct follows outright and no split is needed.  `NOT converges-to' is
;;; exactly this: `NOT (AND typing (FORALL eps ...))' with the typing in hand.
(define (push-not--target body asms)
  (define (known? f) (any-pred (lambda (a) (alpha-equiv? a f)) asms))
  (and (pair? body) (= (length body) 3)
       (case (car body)
         ((and)
          (let ((p (cadr body)) (q (caddr body)))
            (cond ((known? p) (list 'not q))
                  ((known? q) (list 'not p))
                  (else (list 'or (list 'not p) (list 'not q))))))
         ((or) (list 'and (list 'not (cadr body)) (list 'not (caddr body))))
         (else (push-not--step body)))))

(define (push-not--step f)
  (and (pair? f) (= (length f) 3)
       (case (car f)
         ((forall)
          (let ((x (cadr f)) (a (caddr f)))
            (if (and (pair? a) (eq? (car a) 'implies) (= (length a) 3))
                (list 'forsome x (list 'and (cadr a) (list 'not (caddr a))))
                (list 'forsome x (list 'not a)))))
         ((forsome)
          (let ((x (cadr f)) (a (caddr f)))
            (if (and (pair? a) (eq? (car a) 'and) (= (length a) 3))
                (list 'forall x (list 'implies (cadr a) (list 'not (caddr a))))
                (list 'forall x (list 'not a)))))
         ((implies) (list 'and (cadr f) (list 'not (caddr f))))
         (else #f))))

;;; What `di' will strip from GOAL: leading FORALL binders and IMPLIES
;;; antecedents, in order.  `di' is greedy over that prefix (CLAUDE.md), and the
;;; FORALL case below has to know what it will be left holding.
(define (push-not--peel goal)
  (let loop ((g goal) (saw-forall #f))
    (cond ((not (pair? g)) (cons g saw-forall))
          ((and (eq? (car g) 'forall) (= (length g) 3))
           (loop (caddr g) #t))
          ((and (eq? (car g) 'implies) (= (length g) 3))
           (loop (caddr g) saw-forall))
          (else (cons g saw-forall)))))

;;; The variable `di' just introduced: the one free name the focus has now and
;;; did not have before.  Read off rather than assumed -- the eigenvariable
;;; counter is not something a tactic may predict (CLAUDE.md).
(define (push-not--new-var before)
  (let* ((sqn (proof-state-focus *ps*))
         (now (apply append
                     (cons (free-vars (wff-formula (sequent-node-assertion sqn)))
                           (map (lambda (a) (free-vars (wff-formula a)))
                                (sequent-node-assumptions sqn)))))
         (new (filter (lambda (v) (not (memq v before)))
                      (push-not--vars-only now))))
    (and (pair? new) (car new))))

(define (push-not--focus-vars)
  (let ((sqn (proof-state-focus *ps*)))
    (push-not--vars-only
     (apply append
            (cons (free-vars (wff-formula (sequent-node-assertion sqn)))
                  (map (lambda (a) (free-vars (wff-formula a)))
                       (sequent-node-assumptions sqn)))))))

;;; `free-vars' of the FALSITY goal reports `falsity' itself, and the goal after
;;; a `pbc' or a NOT-peel is exactly FALSITY -- so the "new free variable" scan
;;; below picked `falsity' as the eigenvariable and `(ew (quote falsity))' died
;;; with "make-wff: TRUTH/FALSITY in term position".  They are formulas, not
;;; variables; drop them.
(define (push-not--vars-only vs)
  (filter (lambda (v) (not (memq v (quote (truth falsity))))) vs))

;;; -----------------------------------------------------------------------
;;; (push-not-h k) -- k an assumption index or the raw formula.
(define (push-not-h k)
  (vnb-guard
   (lambda ()
     (let* ((hyp (->raw-formula/idx k)))
       (cond
         ((not (and (pair? hyp) (eq? (car hyp) 'not) (= (length hyp) 2)))
          (error "push-not-h: assumption is not a NOT --" (expression->string hyp)))
         (else
          (let* ((body   (cadr hyp))
                 (target (push-not--target
                          body
                          (map wff-formula
                               (sequent-node-assumptions (proof-state-focus *ps*))))))
            (cond
              ((not target)
               (error
                (string-append
                 "push-not-h: the NOT is already on "
                 (if (pair? body)
                     (string-append "an " (symbol->string (car body)))
                     "an atom")
                 " -- nothing to push through; this tactic goes through"
                 " quantifiers, implications, and (by De Morgan) and/or")
                (expression->string body)))
              ((any-pred (lambda (a) (alpha-equiv? (wff-formula a) target))
                         (sequent-node-assumptions (proof-state-focus *ps*)))
               (error "push-not-h: the pushed formula is already an assumption --"
                      (expression->string target)))
              (else (push-not--do hyp body target))))))))))

(define (push-not--do hyp body target)
  ;; `have!' cuts, and cutting a formula the focus is ALREADY trying to prove is
  ;; the alpha self-loop: the "main" child of the cut is the node you stand on,
  ;; one leaf opens instead of two, and there is no undo (CLAUDE.md).  When the
  ;; pushed formula IS the goal, run the derivation on the goal directly.
  (let* ((goal (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
         (on-goal? (alpha-equiv? goal target))
         (establish (lambda (thunk)
                      (if on-goal? (thunk) (have! target thunk)))))
    (case (car body)
      ;; The propositional cases -- NOT (IMPLIES a b), and the two De Morgan
      ;; shapes.  `prop' decides every one of them with the parts opaque, which
      ;; is exactly what they are, and discharges through the kernel.
      ((implies and or) (establish (lambda () (prop))) (push-not--report target))

      ;; NOT (FORSOME x p)  =>  FORALL x (NOT p), guard preserved.
      ;; `di' peels the FORALL, then the guard or the NOT; loop until the goal
      ;; is FALSITY, which is where the witness is standing in the context.
      ((forsome)
       (let ((x (cadr body)))
         (establish
          (lambda ()
            (let ((before (push-not--focus-vars)))
              (push-not--di-to-falsity)
              (let ((ev (or (push-not--new-var before) x)))
                (have! body (lambda () (ew ev) (prop)))
                (ai hyp)))))
         (push-not--report target)))

      ;; NOT (FORALL x a)  =>  FORSOME x (NOT a), guard preserved.  The only
      ;; case needing the full classical dance: assume the negation of the
      ;; target, derive (FORALL x a) from it, contradict the hypothesis.
      ((forall)
       (let* ((x (cadr body))
              (a (caddr body))
              (peeled (push-not--peel (if (and (pair? a) (eq? (car a) 'implies))
                                          (caddr a) a))))
         ;; `di' inside the lane is greedy over FORALL/IMPLIES.  Antecedents it
         ;; assumes are fine -- `prop' reassembles the chain from them.  A
         ;; FORALL it peels is not: the residual goal is then deeper than the
         ;; formula we have to rebuild and `prop' sees two unrelated atoms.
         ;; Refuse rather than strand a leaf.
         (if (cdr peeled)
             (error
              (string-append
               "push-not-h: the body under the FORALL has a nested universal, "
               "which `di' would peel past -- not handled; peel by hand")
              (expression->string a))
             (begin
               (establish
                (lambda ()
                  (pbc)
                  (let ((before (push-not--focus-vars)))
                    (have! body
                           (lambda ()
                             (di)
                             (let ((ev (or (push-not--new-var before) x)))
                               (pbc)
                               (have! target (lambda () (ew ev) (prop)))
                               (ai (list 'not target)))))
                    (ai hyp))))
               (push-not--report target)))))
      (else (error "push-not-h: unreachable" (expression->string body))))))

;;; `di' until the goal is FALSITY (or it stops making progress).  One call is
;;; greedy over a FORALL/IMPLIES prefix but stops before a NOT, and the NOT is
;;; exactly what has to come off for the witness to land in the context.
(define (push-not--di-to-falsity)
  (let loop ((n 0))
    (let ((g (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
      (when (and (< n 4) (not (eq? g 'falsity)))
        (di)
        (let ((g2 (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
          (if (not (equal? g g2)) (loop (+ n 1))))))))

(define (push-not--report target)
  (display ";; push-not-h: landed  ")
  (display (expression->string target))
  (newline)
  (case (car target)
    ((forsome) (display ";;   next: (ai <that>) to skolemize it, then push-not-h again."))
    ((forall)  (display ";;   next: (inst+ <that> 'term) to use it."))
    ((and)     (display ";;   next: (ai <that>) to split it, then push-not-h on the right conjunct."))
    ((or)      (display ";;   next: (use-cases <that>) -- De Morgan gives a genuine split here."))
    ((not)     (display ";;   next: push-not-h it again if its body is a quantifier.")))
  (newline)
  target)
