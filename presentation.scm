;;; presentation.scm -- THE RESOLUTION DIAL.
;;;
;;; Parsing and printing are inverses.  PRESENTATION is a third operation,
;;; deliberately LOSSY, whose purpose is that a human with bounded capacity can
;;; see what a sequent says.  It is not a mode but a DIAL, and the rungs it
;;; turns through were already there before this file:
;;;
;;;   r0   the kernel S-expression                     (write)
;;;   r1   surface syntax                              (expr->str / parse)
;;;        <- BIJECTIVE.  The 2026-08-24 round-trip gate lives exactly here:
;;;           a printed term must re-parse to the term that was printed.
;;;   r2   guards and typings elided                   (this file)
;;;   r3   r2, plus structures destructured and deep subterms elided
;;;
;;; So the "third operation beside parse and print" is not a new kind of thing.
;;; It is the dial turned past the last invertible notch, and the existing
;;; round-trip gate DEFINES where that notch is.  r1 is the default and this
;;; file changes NOTHING at r1: the hook returns #f and sequents.scm renders as
;;; it always did.
;;;
;;; TWO CONSTRAINTS, both the user's, and both are why this is a filter rather
;;; than a set of modes wearing a resolution costume.
;;;
;;; 1. THE RUNGS NEST.  Turning the dial up must only ever SUBTRACT.  Nested in
;;;    information CONTENT, not in characters: everything readable at r(n+1) is
;;;    readable at r(n).  A rung that renders a citation chain as prose while
;;;    introducing a lemma name that was not on screen is ADDING, and is not a
;;;    rung of this dial.  Every transformation below is a deletion, with one
;;;    apparent exception argued at DESTRUCTURING.
;;;
;;; 2. THE APERTURE IS ON SCREEN.  A lossy render that does not announce its own
;;;    lossiness is the defect class of `(f)' printing as `f' and `card*(a)'
;;;    parsing as a product: consistent, plausible, and not what is there.  So
;;;    every elision leaves a counted mark, and the notch is named on the line.
;;;    `(f)' was dangerous because you could not tell you were being lied to; a
;;;    dial you can see the setting of discloses the lie.
;;;
;;; WHAT IS NOT HERE, deliberately.  The user's own sketch of a destructured
;;; ring binder reads  forall([x, +, *, I, 0] in ring, ...)  -- the CONVENTIONAL
;;; operator symbols, not the declared slot names.  That mapping (ADD -> +,
;;; IDEN -> I) exists nowhere in the tree and cannot be guessed: inventing it in
;;; the renderer would put a symbol on screen that no declaration supports,
;;; which is constraint 1 violated.  It wants a `notation!' key beside each
;;; structure, one decision per structure, and that is a vocabulary question for
;;; the user.  Until then r3 destructures to the DECLARED slot names, which are
;;; what `declare-structure' says and what `describe-structure' prints.

;;; =======================================================================
;;; The dial.
;;; =======================================================================

;;; The current notch.  1 = surface syntax = what the prover has always shown.
(define *presentation-resolution* 1)

(define *presentation-min-notch* 0)
(define *presentation-max-notch* 3)

;;; Turned on, `sp' consults the goal-driven heuristic ONCE and sets the dial;
;;; see THE AUTO-NOTCH below for why "once" is the whole design.  Off by default:
;;; a dial that moves when nobody touched it is the defect this file exists to
;;; avoid.
(define *presentation-auto* #f)

;;; `sp' calls this with the fresh proof state (interactive.scm, one line before
;;; the opening `show').  It is the ONLY automatic writer of the dial, and it
;;; runs once per proof.
(set! *sp-presentation-hook*
  (lambda (ps)
    (when *presentation-auto*
      (set! *presentation-resolution*
            (suggest-resolution (sequent-node-sequent (proof-state-focus ps)))))))

;;; =======================================================================
;;; What counts as a typing.
;;;
;;; `(IN t S)' -- membership -- and nothing else.  Not `IS-RING(s)': that is a
;;; hypothesis with mathematical content, and hiding it would hide the reason a
;;; step is licensed.  A structure-class guard `(IN s METRIC-SPACE)' IS a typing
;;; by this test and is elided at r2 like any other; at r3 it is what triggers
;;; destructuring, and then the structure is named in the aperture line, so it
;;; does not vanish.
;;; =======================================================================

(define (pres-typing? f)
  (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)))

;;; A guarded binder: (FORALL x (IMPLIES (IN x A) body)).
(define (pres-guarded-binder? f)
  (and (pair? f) (memq (car f) '(FORALL FORSOME)) (= (length f) 3)
       (symbol? (cadr f))
       (let ((b (caddr f)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (pres-typing? (cadr b))
              (eq? (cadr (cadr b)) (cadr f))))))

(define (pres-binder-guard f) (cadr (caddr f)))     ; the (IN x A)
(define (pres-binder-body  f) (caddr (caddr f)))

;;; =======================================================================
;;; The counters.  Every elision is counted, and the counts are what the
;;; aperture line reports; nothing is dropped silently.
;;; =======================================================================

(define pres--guards 0)
(define pres--typings 0)
(define pres--depth 0)
(define pres--structures '())          ; ((var structure-name slot ...) ...)

(define (pres--reset!)
  (set! pres--guards 0) (set! pres--typings 0) (set! pres--depth 0)
  (set! pres--structures '()))

;;; =======================================================================
;;; r2 -- STRIP THE GUARDS.
;;;
;;; (FORALL x (IMPLIES (IN x A) body)) -> (FORALL x body), which expr->str then
;;; prints as forall([x], body) instead of forall([x in A], body).  Pure
;;; deletion: the variable, the body and every other connective survive.
;;; =======================================================================

(define (pres-strip-guards f)
  (cond ((not (pair? f)) f)
        ((pres-guarded-binder? f)
         (set! pres--guards (+ pres--guards 1))
         (list (car f) (cadr f) (pres-strip-guards (pres-binder-body f))))
        (else (map pres-strip-guards f))))

;;; =======================================================================
;;; r3 -- DESTRUCTURING, and the argument that it still only subtracts.
;;;
;;; Under a binder that types s into a declared structure -- either the class
;;; guard `(IN s RING)' or a hypothesis `IS-RING(s)' -- every accessor
;;; application `(ADD s)' is rewritten to the bare slot symbol `add', and
;;; `(CARR s)' to `carr'.  What is REMOVED is which structure the operation came
;;; from: with two rings in one sequent the render becomes ambiguous, and the
;;; user's design says in terms that it may.  What might look ADDED is the slot
;;; names -- but they are not invented here: they are what the structure's own
;;; `declare-structure' declares, and the aperture line prints the dictionary
;;; (`s: ring(carr, add, mul, neg, zero, one)') beside the sequent.  So the
;;; names are on screen, and the render is r1 minus the structure argument.
;;;
;;; It is applied ONLY to accessors of the structure the variable is declared
;;; in.  An accessor of another structure applied to the same variable is left
;;; alone -- there is nothing to say about it and a silent collapse would be the
;;; ambiguity without the disclosure.
;;; =======================================================================

(define (pres--is-x-structure head)
  ;; IS-RING -> RING, when RING is a declared structure.
  (let ((s (symbol->string head)))
    (and (> (string-length s) 3)
         (string=? (substring s 0 3) "IS-")
         (let ((n (string->symbol (substring s 3 (string-length s)))))
           (and (lookup-structure n) n)))))

(define (pres--slots sname)
  (let ((sd (lookup-structure sname)))
    (and sd (map car (structure-def-slots sd)))))

;;; Collapse (ACC var) -> acc, for every ACC declared by SNAME.
(define (pres-destructure f var sname)
  (let ((slots (pres--slots sname)))
    (if (not slots) f
        (let walk ((g f))
          (cond ((not (pair? g)) g)
                ((and (= (length g) 2) (symbol? (car g)) (eq? (cadr g) var)
                      (memq (car g) slots))
                 (car g))
                (else (map walk g)))))))

;;; Every variable anywhere in the sequent that is typed into a declared
;;; structure, with that structure.  Read off the WHOLE sequent -- context and
;;; goal together -- because the binding of a slot name is established by one
;;; formula and used in another: presentation is per-SEQUENT, not per-formula,
;;; and that was the design's first constraint long before the dial had rungs.
(define (pres--structure-vars formulas)
  (let ((found '()))
    (define (note! var sname)
      (if (and (symbol? var) sname (not (assq var found)))
          (set! found (cons (cons var sname) found))))
    (define (walk g)
      (when (pair? g)
        ;; (IN s RING) -- the structure-class guard
        (if (and (eq? (car g) 'IN) (= (length g) 3) (symbol? (cadr g))
                 (symbol? (caddr g)) (lookup-structure (caddr g)))
            (note! (cadr g) (caddr g)))
        ;; (IS-RING s) -- the predicate
        (if (and (= (length g) 2) (symbol? (car g)) (symbol? (cadr g)))
            (note! (cadr g) (pres--is-x-structure (car g))))
        (for-each walk (cdr g))))
    (for-each walk formulas)
    (reverse found)))

;;; =======================================================================
;;; r3 -- DEPTH ELISION.  A subterm nested deeper than the budget is replaced by
;;; the mark `...'.  Deletion, counted, and the count is on the line.
;;; =======================================================================

(define *presentation-depth-budget* 6)

(define (pres-elide-depth f budget)
  (let walk ((g f) (d 0))
    (cond ((not (pair? g)) g)
          ((memq (car g) '(FORALL FORSOME AND OR IMPLIES IFF NOT))
           ;; connectives and binders do not count against the budget: the
           ;; SHAPE of the statement is what a reader navigates by.
           (cons (car g) (map (lambda (x) (walk x d)) (cdr g))))
          ((>= d budget) (set! pres--depth (+ pres--depth 1)) '|...|)
          (else (cons (walk (car g) (+ d 1))
                      (map (lambda (x) (walk x (+ d 1))) (cdr g)))))))

;;; =======================================================================
;;; THE PRESENTER.
;;; =======================================================================

;;; A formula at a notch.  RENDERING ONLY: the result is not a wff, is not
;;; required to parse, and must never be handed back to the prover.
(define (pres-formula f notch structure-vars)
  (let* ((g (if (>= notch 2) (pres-strip-guards f) f))
         (g (if (>= notch 3)
                (let loop ((vs structure-vars) (acc g))
                  (if (null? vs) acc
                      (loop (cdr vs) (pres-destructure acc (caar vs) (cdar vs)))))
                g))
         (g (if (>= notch 3) (pres-elide-depth g *presentation-depth-budget*) g)))
    g))

(define (pres-sequent->string s notch)
  (pres--reset!)
  (let* ((asms (map wff-formula (sequent-assumptions s)))
         (goal (wff-formula (sequent-assertion s)))
         (svars (if (>= notch 3) (pres--structure-vars (cons goal asms)) '()))
         ;; the CONTEXT loses its typing hypotheses; the GOAL never does -- a
         ;; goal that IS a typing is the whole statement.
         (keep (if (>= notch 2)
                   (filter (lambda (a)
                             (if (pres-typing? a)
                                 (begin (set! pres--typings (+ pres--typings 1)) #f)
                                 #t))
                           asms)
                   asms))
         (astrs (map (lambda (a) (expression->string (pres-formula a notch svars))) keep))
         (gstr  (expression->string (pres-formula goal notch svars))))
    (string-append
     (if (null? astrs) "()" (str-join astrs ", "))
     "  =>  " gstr
     (pres--aperture notch svars))))

;;; THE APERTURE.  Never empty above r1: the notch is always named, and each
;;; kind of elision reports its count.  The structure dictionary is printed
;;; here rather than inlined in the binder, so that the presented formula stays
;;; an ordinary S-expression and the slot names are still on screen.
(define (pres--aperture notch svars)
  (string-append
   "\n     | r" (number->string notch)
   (if (null? svars) ""
       (string-append "  "
         (str-join (map (lambda (v)
                          (string-append (symbol->string (car v)) ": "
                                         (symbol->string (cdr v))
                                         "(" (str-join (map symbol->string
                                                            (or (pres--slots (cdr v)) '()))
                                                       ", ") ")"))
                        svars)
                   "; ")))
   (if (> pres--guards 0)
       (string-append "  |  " (number->string pres--guards) " guard(s) hidden") "")
   (if (> pres--typings 0)
       (string-append "  |  " (number->string pres--typings) " typing(s) hidden") "")
   (if (> pres--depth 0)
       (string-append "  |  " (number->string pres--depth) " subterm(s) elided") "")
   " |"))

;;; The hook sequents.scm calls.  #f at r0 and r1 -- r1 is rendered by the
;;; printer that has always rendered it, so the default path is untouched.
(set! *presentation-hook*
  (lambda (s)
    (cond ((= *presentation-resolution* 0) (pres-sequent->r0 s))
          ((and (>= *presentation-resolution* 2)
                (<= *presentation-resolution* *presentation-max-notch*))
           (pres-sequent->string s *presentation-resolution*))
          (else #f))))

;;; r0 -- the kernel S-expression, which is what every rung above is a filter
;;; of.  It is a rung of the same dial and not a debugging aside: `write' is the
;;; one rendering that is certainly faithful, and having it under the same
;;; command is what lets a reader check a suspicious r2 line against the truth
;;; without leaving the display.
(define (pres-sequent->r0 s)
  (let ((asms (map wff-formula (sequent-assumptions s)))
        (goal (wff-formula (sequent-assertion s))))
    (string-append
     (if (null? asms) "()"
         (str-join (map (lambda (a) (with-output-to-string (lambda () (write a)))) asms)
                   ", "))
     "  =>  "
     (with-output-to-string (lambda () (write goal)))
     "\n     | r0  (kernel S-expression) |")))

;;; =======================================================================
;;; THE DIAL ON A BARE FORMULA.
;;;
;;; `sequent->string' is the display path for a proof STATE, so the hook above
;;; reaches a formula only when a proof is holding it.  A formula on its own --
;;; a theorem looked up, a statement being drafted, a hypothesis pasted from
;;; somewhere -- wants the same dial, and this is it.  Same transformations,
;;; same aperture, no proof required.
;;; =======================================================================

(define (pres-formula->string f notch)
  (pres--reset!)
  (let* ((svars (if (>= notch 3) (pres--structure-vars (list f)) '())))
    (if (= notch 0)
        (string-append (with-output-to-string (lambda () (write f)))
                       "\n     | r0  (kernel S-expression) |")
        (let ((body (expression->string (pres-formula f notch svars))))
          (if (<= notch 1)
              body
              (string-append body (pres--aperture notch svars)))))))

;;; (dial-wff x [n]) -- present ONE formula at notch n (default: the dial's
;;; current setting).  x may be a wff, a "surface string", or a raw
;;; S-expression, so it takes whatever is to hand:
;;;
;;;   (dial-wff (lookup-theorem 'metric-limit-unique) 2)
;;;   (dial-wff "forall([r in ring, a in carr(r)], (add(r))(a,a) in carr(r))" 3)
;;;   (dial-wff '(FORALL x (IMPLIES (IN x RR) (<= x x))) 0)
(define (dial-wff x #!optional n)
  (let* ((f (cond ((wff? x) (wff-formula x))
                  ((string? x) (wff-formula (make-wff-from-string x)))
                  ((or (pair? x) (symbol? x)) x)
                  (else (error "dial-wff: expected a wff, a \"string\", or an S-expr" x))))
         (notch (if (default-object? n) *presentation-resolution* n)))
    (if (or (not (integer? notch))
            (< notch *presentation-min-notch*) (> notch *presentation-max-notch*))
        (begin (display "dial-wff: expected a notch 0-")
               (display *presentation-max-notch*) (newline) #f)
        (let ((str (pres-formula->string f notch)))
          (display str) (newline) str))))

;;; =======================================================================
;;; THE AUTO-NOTCH -- the dial reads the GOAL, not the reader.
;;;
;;; The heuristic is deliberately crude and deliberately WRITTEN DOWN: a
;;; two-symbol goal renders raw, and a goal carrying a wall of typing conjuncts
;;; filters harder.  What matters is not the constants but the discipline
;;; around them:
;;;
;;;   IT SUGGESTS A STARTING NOTCH AND THEN STAYS PUT.
;;;
;;; The known defect of a per-sequent auto-notch is that the aperture moves
;;; without anyone touching it, so two consecutive steps of one proof could
;;; render at different resolutions -- and a reader who cannot tell whether the
;;; formula changed or the lens did is worse off than at any fixed notch.  So
;;; the suggestion is consulted ONCE, at `sp', and sets the GLOBAL dial; every
;;; later sequent in that proof renders at the notch the first one chose, until
;;; a human turns it.  `(res 'auto)' re-consults it on demand.
;;;
;;; Global-with-override rather than genuinely per-object, and that is a choice,
;;; not a discovery: per-object would render each leaf at its own best notch and
;;; give up any comparison between two leaves of the same proof.
;;; =======================================================================

(define (pres--size f)
  (let walk ((g f) (n 0))
    (cond ((not (pair? g)) (+ n 1))
          (else (fold-left (lambda (acc x) (walk x acc)) (+ n 1) g)))))

(define (pres--count-guards f)
  (let walk ((g f) (n 0))
    (cond ((not (pair? g)) n)
          ((pres-guarded-binder? g) (walk (pres-binder-body g) (+ n 1)))
          (else (fold-left (lambda (acc x) (walk x acc)) n g)))))

;;; The score, and the two thresholds.  Reported by `(res 'why)' so the number
;;; that moved the dial is never invisible.
(define (pres-sequent-score s)
  (let* ((asms (map wff-formula (sequent-assumptions s)))
         (goal (wff-formula (sequent-assertion s))))
    (+ (pres--size goal)
       (* 3 (length (filter pres-typing? asms)))
       (* 2 (pres--count-guards goal)))))

(define *presentation-r2-threshold* 40)
(define *presentation-r3-threshold* 120)

(define (suggest-resolution s)
  (let ((score (pres-sequent-score s)))
    (cond ((< score *presentation-r2-threshold*) 1)
          ((< score *presentation-r3-threshold*) 2)
          (else 3))))

;;; =======================================================================
;;; THE SURFACE COMMAND.
;;;
;;;   (dial)        report the notch, and what it is costing
;;;   (dial n)      set it
;;;   (dial 'auto)  take the suggestion for the CURRENT focus, once
;;;   (dial 'why)   the score and the thresholds behind the suggestion
;;;
;;; and for a formula rather than a proof state, (dial-wff x [n]) above.
;;;
;;; NOT `res': `RES' is a registered kernel head (restriction), and the reader
;;; folds case, so a command by that name would read as the constant on any
;;; surface where both can appear.  `dial' is the user's own word for it.
;;; =======================================================================

(define (dial #!optional arg)
  (cond
   ((default-object? arg)
    (display "presentation resolution: r") (display *presentation-resolution*)
    (display (case *presentation-resolution*
               ((0) "  (kernel S-expression)")
               ((1) "  (surface syntax -- invertible; the default)")
               ((2) "  (guards and typings elided)")
               ((3) "  (structures destructured, deep subterms elided)")
               (else "")))
    (newline)
    *presentation-resolution*)
   ((eq? arg 'auto)
    (if (not *ps*)
        (begin (display "dial: no current proof to read.\n") #f)
        (let ((n (suggest-resolution (sequent-node-sequent (proof-state-focus *ps*)))))
          (set! *presentation-resolution* n)
          (display "presentation resolution: r") (display n)
          (display "  (suggested from the goal; it now STAYS PUT)\n")
          (show)
          n)))
   ((eq? arg 'why)
    (if (not *ps*)
        (begin (display "dial: no current proof to read.\n") #f)
        (let* ((s (sequent-node-sequent (proof-state-focus *ps*)))
               (score (pres-sequent-score s)))
          (display "goal score ") (display score)
          (display "  (r2 at ") (display *presentation-r2-threshold*)
          (display ", r3 at ") (display *presentation-r3-threshold*)
          (display ") -> suggests r") (display (suggest-resolution s)) (newline)
          score)))
   ((and (integer? arg) (>= arg *presentation-min-notch*)
         (<= arg *presentation-max-notch*))
    (set! *presentation-resolution* arg)
    (show)
    arg)
   (else
    (display "dial: expected a notch 0-")
    (display *presentation-max-notch*)
    (display ", or 'auto, or 'why.\n")
    #f)))
