;;; mp.scm -- `(mp)': close a goal that is an INSTANCE of a universal you already
;;; have, with no arguments.
;;;
;;; THE MOVE.  The oldest inference there is:
;;;
;;;     forall([thing in human], thing in mortal),  socrates in human
;;;     |-  socrates in mortal
;;;
;;; VNB could always do this -- `(inst+ 2 'socrates) (ass)' -- but it made you
;;; supply the term, and supplying the term is the part that is not a decision.
;;; The user, 2026-09-12, showing the system to his granddaughters: "if there is
;;; one universal in the context it shouldn't be necessary".
;;;
;;; WHY IT NEEDS NO ARGUMENT, which is the whole point.  The term is not
;;; guessed, ranked or searched for: it is DERIVED.  Matching the universal's
;;; conclusion against the goal, with the bound variable as the only schema
;;; variable, either determines the binder or fails outright --
;;;
;;;     conclusion (IN thing mortal)  vs  goal (IN socrates mortal)
;;;        -> ((thing . socrates))                      [the term, computed]
;;;     conclusion (IN thing mortal)  vs  goal (IN socrates greek)
;;;        -> #f                                        [declines, correctly]
;;;
;;; -- and the guard is then checked against the context rather than assumed.
;;; So this is the same NO-CHOICE criterion `grind' uses to decide what it may
;;; saturate ("none of these involves a lemma CHOICE or a witness/eigenvar
;;; CHOICE"): instantiation was excluded from grind because it is USUALLY a
;;; choice, and here it is not one.
;;;
;;; WHY IT IS NOT IN `grind'.  It could be, and that would make the command the
;;; user already types finish the proof.  But `grind' is in scout's search
;;; alphabet and is called by hundreds of library drivers, many of which read
;;; `(grind) (inst+ ...) (ass)'.  A grind that CLOSES a goal it used to leave
;;; open strands the steps after it.  Additive first; folding it into grind is a
;;; separate change with a measurement attached.
;;;
;;; TRUST.  None added.  It runs the ordinary `inst+' and `ass' -- forall-elim,
;;; detach, assumption -- so a `qed' over an `mp'-closed proof bills exactly
;;; what typing the two steps by hand would bill, which is nothing.
;;;
;;; SCOPE (v1).  One binder.  A multi-binder universal `forall([a in A, b in B],
;;; ...)' needs either simultaneous substitution or repeated instantiation, and
;;; CLAUDE.md is explicit that iterating `subst-free' is NOT simultaneous
;;; substitution -- the defect that cost a day in the macete rewriter.  With a
;;; single binder that hazard does not arise.  Multi-binder declines audibly.

;;; The context's assumptions, as raw formulas.
(define (mp--asms sqn)
  (map wff-formula (sequent-node-assumptions sqn)))

;;; Is FORM in the context, up to alpha?  (alpha-equiv? takes RAW formulas.)
(define (mp--in-context? form asms)
  (let loop ((as asms))
    (cond ((null? as) #f)
          ((alpha-equiv? (car as) form) #t)
          (else (loop (cdr as))))))

;;; A single-binder universal, split into (binder guard conclusion).
;;; `forall([x in A], P)' is (FORALL x (IMPLIES (IN x A) P)); an unguarded
;;; `forall x. P' is (FORALL x P) and has guard #f.  Returns #f for anything
;;; else -- including a nested universal, which v1 declines rather than
;;; half-handles.
(define (mp--split u)
  (and (pair? u)
       (memq (car u) '(FORALL forall))
       (pair? (cdr u)) (pair? (cddr u))
       (let ((v (cadr u)) (body (caddr u)))
         (and (symbol? v)
              (let* ((guarded (and (pair? body)
                                   (memq (car body) '(IMPLIES implies))
                                   (pair? (cdr body)) (pair? (cddr body))))
                     (guard   (and guarded (cadr body)))
                     (concl   (if guarded (caddr body) body)))
                ;; a nested universal is out of scope for v1
                (and (not (and (pair? concl) (memq (car concl) '(FORALL forall))))
                     (list v guard concl)))))))

;;; The candidates: every context universal whose conclusion matches the goal
;;; with the binder determined, and whose guard (if any) the context already
;;; proves at that term.  Each entry is (universal binder term guard-instance).
(define (mp--candidates sqn)
  (let* ((goal (wff-formula (sequent-node-assertion sqn)))
         (asms (mp--asms sqn)))
    (let loop ((as asms) (out '()))
      (if (null? as)
          (reverse out)
          (let* ((u (car as))
                 (s (mp--split u)))
            (if (not s)
                (loop (cdr as) out)
                (let* ((v     (car s))
                       (guard (cadr s))
                       (concl (caddr s))
                       (m     (match-expr concl goal (list v))))
                  (if (not (and (pair? m) (assq v m)))
                      (loop (cdr as) out)
                      (let* ((term (cdr (assq v m)))
                             (gi   (and guard (subst-free v term guard))))
                        (if (and gi (not (mp--in-context? gi asms)))
                            (loop (cdr as) out)     ; guard not discharged
                            (loop (cdr as)
                                  (cons (list u v term gi) out))))))))))))

;;; Report, when there is nothing to do or too much.  Naming the candidates
;;; matters more than picking one: a closer that silently chooses between two
;;; universals is a closer you cannot predict.
(define (mp--report-none)
  (vnb--warn "mp"
    (string-append
     "no universal in the context has this goal as an instance "
     "(matching the conclusion against the goal determines no term, "
     "or its guard is not in the context)")))

;;; The 1-based position of FORM in the assumption list -- the number the Focus
;;; Workspace shows, and the one `inst+' accepts.  Computed here rather than
;;; borrowed from suggest.scm so this file stands alone; the arithmetic is two
;;; lines and the dependency would be the only one it has.
(define (mp--index-of form asms)
  (let loop ((as asms) (i 1))
    (cond ((null? as) #f)
          ((alpha-equiv? (car as) form) i)
          (else (loop (cdr as) (+ i 1))))))

;;; Print the fallback as something you can actually run.  The first version
;;; echoed the whole universal back -- `(inst+ (forall thing (implies ...)) ...)'
;;; -- which is neither readable nor pasteable; every what-now lane renders a
;;; universal as its assumption NUMBER for exactly this reason.
(define (mp--report-many cands asms)
  (display ";; mp: ") (display (length cands))
  (display " universals in your context have this goal as an instance.")
  (newline)
  (display ";;   Both apply, so the choice is yours -- run one of:")
  (newline)
  (for-each (lambda (c)
              (let ((i (mp--index-of (car c) asms)))
                (display ";;   (inst+ ")
                (if i (display i) (write (car c)))
                (display " '") (write (caddr c))
                (display ")  (ass)") (newline)))
            cands)
  (vnb--warn "mp" "more than one universal applies; use inst+ with the one you mean"))

;;; ---------------------------------------------------------------- the tactic
;;; Records ITSELF, not its expansion, for the reason prop does: the sub-steps
;;; are ordinary kernel inferences (which is what makes this debt-free), but an
;;; emitted script of the expansion is fragile where one `(mp)' replays exactly
;;; -- same goal, same context, same derived term.  The undo mark is taken
;;; OUTSIDE the fluid-let so `backup-one' takes back the whole move.
(define (mp)
  (if (or (not *ps*) (proof-done? *ps*))
      (vnb--warn "mp" "no open goal")
      (let* ((sqn   (proof-state-focus *ps*))
             (cands (mp--candidates sqn)))
        (cond
         ((null? cands) (mp--report-none))
         ((pair? (cdr cands)) (mp--report-many cands (mp--asms sqn)))
         (else
          (let* ((c    (car cands))
                 (u    (car c))
                 (term (caddr c))
                 (mark (vnb--take-mark '(mp))))
            (fluid-let ((*replaying?* #t))
              (inst+ u term)
              (ass))
            (vnb--undo-push! mark)
            (record-cmd! 'mp '())
            (vnb--capture-step! '(mp))
            #t))))))

;;; ---------------------------------------------------------------- grind-and-mp
;;; The user's call, 2026-09-12: do NOT fold this into `grind' -- "leaving it
;;; separate makes it a good teaching tool for basic logic".  The combined form
;;; is still worth having, for a different reason than convenience.
;;;
;;; On a sentence typed as it reads --
;;;
;;;     forall([thing in human], thing in mortal) and socrates in human
;;;       implies socrates in mortal
;;;
;;; -- the goal is not yet a syllogism: it is an implication whose antecedent is
;;; a conjunction.  `grind' does the BOOKKEEPING (split the AND, move the
;;; antecedents into the assumptions), leaving exactly
;;;
;;;     socrates in human, forall([thing in human], thing in mortal)
;;;        |-  socrates in mortal
;;;
;;; and `mp' then does the LOGIC: universal instantiation, then modus ponens.
;;; Those are two different kinds of step, which is precisely why they remain
;;; two tactics; this one only runs them in order.
;;;
;;; It records NOTHING of its own.  The sub-steps record themselves, so the page
;;; reads `((grind) (mp))' -- the two moves a student would make -- and no case
;;; in `apply-recorded-cmd!' is needed.  `grind' runs QUIETLY because on an
;;; already-tidy goal it legitimately declines, and that decline is not a
;;; failure here: `mp' is still the point of the command.
(define (grind-and-mp)
  (quietly (lambda () (grind)))
  (mp))
