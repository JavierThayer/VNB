;;; driver-kit.scm -- the proof-driving helpers that more than one file needs.
;;;
;;; THE RULE THIS FILE EXISTS TO ENFORCE:
;;;
;;;   Every proof-driving Scheme procedure is EITHER defined here -- loaded
;;;   before any proof file -- OR defined locally in an environment exclusive to
;;;   the file that defines it.
;;;
;;; The second half is enforced by `load.scm': once this file has loaded, every
;;; `theorem-library/' and `calculus/' file is loaded into a fresh
;;; `extend-top-level-environment'.  Its `define's cannot escape; its `set!'s of
;;; *ps* and friends still reach the real bindings, and it still sees every
;;; tactic, macro (`bc*') and procedure defined here and below.
;;;
;;; WHY.  Before this file, both halves of that rule were false, and nobody had
;;; declared it.  `proof-leaves' and `any-pred' were defined exactly once in the
;;; whole tree -- inside theorem-library/nn-least-element.scm, a PROOF SCRIPT,
;;; under the comment "helpers (subset of prop-3-15-proof.scm)" -- and were then
;;; used by interactive.scm, by macetes.scm, and by eighteen other drivers.  It
;;; worked only because Scheme resolves a free variable at call time: every one
;;; of those call sites sits in a lambda body that does not run during the load.
;;; Move nn-least-element later in load.scm, or obey CLAUDE.md's own prefix rule
;;; inside it, and the `in-rr' tactic and the PSS name search die at the REPL,
;;; far from the cause.  deriv-constant-proof.scm did the same on a larger scale:
;;; a thirteen-procedure `dc-' toolkit, under the comment "file-local proof
;;; helpers", consumed by nine later drivers.
;;;
;;; Loads after `interactive' / `input-context' (whose tactics these call) and
;;; before `proof-debt', `minimize' and every proof file.
;;;
;;; A driver that needs a helper NOBODY else needs should still define it
;;; locally, with the file's prefix.  This file is for the shared ones only.

;;; -----------------------------------------------------------------------
;;; The prop-3-15 kit, hoisted out of theorem-library/nn-least-element.scm.
;;; `any-pred' is `find-first' (deduction-graphs.scm) under another name; both
;;; spellings are in use across ~20 drivers, so keep the alias rather than churn
;;; every call site.

(define (any-pred pred lst) (find-first pred lst))

;;; The kit's name for `proof-open-leaves' (proof-commands.scm) on the live
;;; proof.  It used to spell the filter out again here; one predicate, one
;;; definition, so the panel and the drivers cannot drift on what "open" means.
(define (proof-leaves) (proof-open-leaves *ps*))

;;; -----------------------------------------------------------------------
;;; The dc- kit, hoisted out of theorem-library/deriv-constant-proof.scm.
;;; Bodies verbatim.  Consumed by deriv-monotone, generalized-mvt, mvt-bounds,
;;; taylor, vector-taylor, hahn-banach, hahn-banach-full, norm-as-sup and
;;; noetherian-maximal.  (dc-rr-of! and dc-up-eq! stay in deriv-constant-proof:
;;; they close over that proof's own `a', `b', MGOAL and TYPAND.)

(define (dc-gf) (and *ps* (wff-formula (sequent-node-assertion (proof-state-focus *ps*)))))
(define (dc-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (dc-find pred) (let loop ((as (dc-asms)))
  (cond ((null? as) #f) ((pred (car as)) (car as)) (else (loop (cdr as))))))
(define (dc-head? h) (lambda (a) (and (pair? a) (eq? (car a) h))))
(define (dc-ment? sym form) (cond ((eq? form sym) #t)
  ((pair? form) (or (dc-ment? sym (car form)) (dc-ment? sym (cdr form)))) (else #f)))
(define (dc-split) (let loop ((n 0)) (let ((a (dc-find (dc-head? 'AND))))
  (cond ((and a (< n 16)) (ai a) (loop (+ n 1))) (else n)))))
(define (dc-focus! raw)   ; focus the leaf whose goal prints the same as `raw'
  (let ((target (expression->string raw)))
    (let loop ((ls (proof-leaves)))
      (cond ((null? ls) (error "dc-focus!: none equal" target))
            ((string=? (expression->string (wff-formula (sequent-node-assertion (car ls)))) target)
             (set-proof-state-focus! *ps* (car ls)) (car ls))
            (else (loop (cdr ls)))))))
(define (dc-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (set-proof-state-focus! *ps* al) (di) (loop (+ g 1))))))
(define (dc-have! mem back)  ; cut a real-membership fact, prove by in-rr, return to `back'
  (cut mem) (in-rr) (dc-focus! back))
(define (dc-detach-impl! ant)   ; detach the ctx IMPLIES whose antecedent prints as `ant'
  (let ((target (expression->string ant)))
    (let loop ((as (dc-asms)))
      (cond ((null? as) (error "dc-detach-impl!: no IMPLIES with antecedent" target))
            ((and (pair? (car as)) (eq? (caar as) 'IMPLIES)
                  (string=? (expression->string (cadr (car as))) target))
             (detach! (car as)))
            (else (loop (cdr as)))))))
(define (dc-open-leaves) (filter (lambda (s) (not (sequent-node-grounded? s))) (proof-leaves)))
(define (dc-dump tag) (display ";;; [")(display tag)(display "] done?=")(display (proof-done? *ps*))
  (display " open=")(display (length (dc-open-leaves)))(newline)
  (display ";;;   goal=")(write (expression->string (dc-gf)))(newline)
  (for-each (lambda (s) (display ";;;   OPEN ")(write (expression->string (wff-formula (sequent-node-assertion s))))(newline))
            (dc-open-leaves)))
(define (dc-focus-case! marker)   ; focus the open leaf whose ctx contains `marker'
  (let ((mstr (expression->string marker)))
    (let loop ((ls (proof-leaves)))
      (cond ((null? ls) (error "dc-focus-case!: none" mstr))
            ((and (not (sequent-node-grounded? (car ls)))
                  (any-pred (lambda (a) (string=? (expression->string a) mstr))
                            (map wff-formula (sequent-node-assumptions (car ls)))))
             (set-proof-state-focus! *ps* (car ls)) (car ls))
            (else (loop (cdr ls)))))))

;;; -----------------------------------------------------------------------
;;; Two one-offs that also escaped their files.

;; hoisted out of theorem-library/hahn-banach-proof.scm (used by three drivers).
;; dc-detach-impl! that returns #f on a miss instead of erroring.
(define (hb-detach-opt! ant)
  (let ((target (expression->string ant)))
    (let loop ((as (dc-asms)))
      (cond ((null? as) #f)
            ((and (pair? (car as)) (eq? (caar as) 'IMPLIES)
                  (string=? (expression->string (cadr (car as))) target))
             (detach! (car as)))
            (else (loop (cdr as)))))))

;; hoisted out of theorem-library/hahn-banach-full-proof.scm (used by norm-as-sup).
(define (hbf-focus-open! pred)
  (let loop ((ls (dc-open-leaves)))
    (cond ((null? ls) (error "hbf-focus-open!: none match"))
          ((pred (wff-formula (sequent-node-assertion (car ls))))
           (set-proof-state-focus! *ps* (car ls)) (car ls))
          (else (loop (cdr ls))))))

;;; -----------------------------------------------------------------------
;;; The dk- kit: NAME A TACTIC'S OUTPUT BY WHAT IT LANDED, NOT BY WHAT IT
;;; LOOKS LIKE.
;;;
;;; CLAUDE.md says "never navigate by goal shape alone", about LEAVES.  The same
;;; lesson holds one level down, about ASSUMPTIONS, and it is what stalled the
;;; spans-submodule-fg descent: the inductive step's context carries the IH, the
;;; instantiated IH, and the spans of both bm and bm' -- four assumptions with
;;; the same head and near-identical shape.  A `dc-find'-style shape match picks
;;; the wrong one; worse, a `mac-h' or `ai' handed a RECONSTRUCTED formula (one
;;; the driver rebuilds, with its own guess at the eigenvariable names) does not
;;; match any assumption at all, silently no-ops, and every later command runs in
;;; the wrong branch.
;;;
;;; The cure is to stop guessing.  Run the tactic, DIFF the assumption list, and
;;; keep what appeared.  What comes back is the assumption itself -- the exact
;;; term the engine built, eigenvariables and all -- so the next `mac-h'/`ai'/
;;; `detach!' is fed a formula that is in the context BY CONSTRUCTION.
;;;
;;; `dk-landed' ERRORS when a tactic lands nothing.  A silent no-op is the bug;
;;; making it loud here is the whole point.  (`dk-landed*' is the rare, explicit
;;; "may land nothing" variant.)

(define (dk-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))

;;; RECORD THE FOCUS MOVE.  A composite that drives branches -- use-cases /
;;; use-em with bodies, have!, from-context!, use-induction -- moves focus with
;;; this, and until 2026-08-15 that move went unrecorded.  The emitted script
;;; then listed the composite's steps with no indication of WHICH leaf each ran
;;; on, and replaying it applied them to whatever leaf the engine had focused:
;;; a COMPLETE proof emitting a script that dies at `qed: proof is not
;;; complete'.  `focus' numbers `proof-open-leaves', so recording this node's
;;; index in that same list makes the emitted script reproduce the move --
;;; `focus-on' is literally `set-proof-state-focus!', so the replayed command
;;; does exactly what this did.  Suppressed under *replaying?*, hence silent in
;;; every copilot probe.
(define (dk--leaf-index node)
  (let loop ((ls (proof-open-leaves *ps*)) (k 1))
    (cond ((null? ls) #f)
          ((eq? (car ls) node) k)
          (else (loop (cdr ls) (+ k 1))))))

(define (dk-focus! node)
  (let ((k (dk--leaf-index node)))
    ;; The mark is taken BEFORE the focus moves, and pushed only when the move
    ;; is recorded -- so backup-one and the script agree on what a step is.
    (let ((mark (and k (vnb--take-mark (list 'focus k)))))
      (set-proof-state-focus! *ps* node)
      (when k (vnb--undo-push! mark) (record-cmd! 'focus (list k))))
    node))
(define (dk-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (dk-head? h) (lambda (f) (and (pair? f) (eq? (car f) h))))

(define (dk--drop-one s lst)            ; remove ONE occurrence (contexts hold duplicates)
  (cond ((null? lst) '())
        ((string=? s (car lst)) (cdr lst))
        (else (cons (car lst) (dk--drop-one s (cdr lst))))))

;; run `thunk'; return the assumptions it ADDED to the focus context, in context
;; order.  May be empty.
(define (dk-landed* thunk)
  (let ((before (map expression->string (dk-asms))))
    (thunk)
    (let loop ((as (dk-asms)) (bs before) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((s (expression->string (car as))))
            (if (member s bs)
                (loop (cdr as) (dk--drop-one s bs) acc)
                (loop (cdr as) bs (cons (car as) acc))))))))

(define (dk-landed thunk)
  (let ((new (dk-landed* thunk)))
    (if (null? new)
        (error "dk-landed: the tactic landed no assumption -- silent no-op")
        new)))

(define (dk-landed-1 thunk)             ; exactly one new assumption; return it
  (let ((new (dk-landed thunk)))
    (if (null? (cdr new))
        (car new)
        (error "dk-landed-1: expected 1 new assumption, got"
               (map expression->string new)))))

(define (dk-landed-find thunk pred)     ; the UNIQUE new assumption satisfying `pred'
  (let* ((new (dk-landed thunk))
         (hits (filter pred new)))
    (cond ((null? hits)
           (error "dk-landed-find: no new assumption matches; landed"
                  (map expression->string new)))
          ((pair? (cdr hits))
           (error "dk-landed-find: ambiguous; matched" (map expression->string hits)))
          (else (car hits)))))

;; `fact' lands its WHOLE instantiation chain: the theorem, each partly-peeled
;; form, and the fully detached result.  The result is the one no other landed
;; formula sits inside -- the deepest.  (dk-landed-1 would just error here, which
;; is how this was found.)
(define (dk-contains? form sub)
  (cond ((equal? form sub) #t)
        ((pair? form) (or (dk-contains? (car form) sub) (dk-contains? (cdr form) sub)))
        (else #f)))

(define (dk-deepest thunk)
  (let ((new (dk-landed thunk)))
    (or (find-first (lambda (a)
                      (not (find-first (lambda (b) (and (not (eq? a b)) (dk-contains? a b))) new)))
                    new)
        (car new))))

(define (dk-fact! . args) (dk-deepest (lambda () (apply fact args))))

;; `ai' the landed conjunctions until none is left; return every leaf conjunct
;; the whole cascade produced.  (`ai' of an AND lands its two conjuncts; a SPANS
;; body or an IS-SUBMODULE unfolding is a right-nested tower of them.)
(define (dk-split! f)
  (let loop ((todo (dk-landed (lambda () (ai f)))) (acc '()))
    (cond ((null? todo) (reverse acc))
          ((and (pair? (car todo)) (eq? (caar todo) 'AND))
           (loop (append (dk-landed (lambda () (ai (car todo)))) (cdr todo)) acc))
          (else (loop (cdr todo) (cons (car todo) acc))))))

;; leaves a branching tactic OPENED (same trick, one level up)
(define (dk-opened thunk)
  (let ((before (proof-leaves)))
    (thunk)
    (filter (lambda (l) (not (memq l before))) (proof-leaves))))

;; did the last primitive inference actually fire on this node?  Every rule gives
;; its focus node an in-arrow.
(define (dk-fired? node) (not (null? (sequent-node-in-arrows node))))

;;; -----------------------------------------------------------------------
;;; have! / from-context! -- the "let it be so, here's why" step and a structural
;;; closer.  Promoted from the sqrt(2) descent; shared by that proof and `vlet'.

(define (dk-goal-of s) (wff-formula (sequent-node-assertion s)))
(define (dk-asms-of s) (map wff-formula (sequent-node-assumptions s)))

;; ground the FOCUS goal by its structure:
;;   AND        -> di-split and recurse on each conjunct
;;   (IN a*b NN) -> nn-mul-closed on the factors, then ass  (typing bookkeeping)
;;   (IN k NN), k a numeral -> arith
;;   otherwise  -> ass (the goal is a context assumption up to alpha)
(define (from-context!)
  (let ((g (dk-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'NN)
            (pair? (cadr g)) (eq? (car (cadr g)) '*))
       (fact 'nn-mul-closed (cadr (cadr g)) (caddr (cadr g))) (ass))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g))) (arith))
      (else (ass)))))

;; (have! CLAIM)         -- cut CLAIM, prove its side goal with from-context!
;; (have! CLAIM THUNK)   -- ... prove it with THUNK instead
;; Leaves focus on the MAIN branch (CLAIM now a context assumption).  Errors --
;; never silently no-ops -- if CLAIM is already in context up to alpha (the cut
;; self-loops: one child, no main branch).
(define (have! form0 . opt)
  ;; COERCE FIRST.  `cut' accepts a raw S-expression, a string in the concrete
  ;; syntax or a <wff>, and coerces internally -- but the side-goal search below
  ;; compares the ARGUMENT against the goals `cut' produced, so an uncoerced
  ;; string or wff never matches anything and the call dies with
  ;;
  ;;   have!: no side goal for "forall([u in pts(ms)], ...)"
  ;;
  ;; which reads as though the cut failed when it in fact succeeded.  Found
  ;; 2026-08-19 walking a user's own route through the ultrametric goal: the
  ;; natural thing to type is the surface string, and the natural thing to type
  ;; was the one form that could not work.  `use-cases' coerces its disjuncts
  ;; for exactly this reason (see the note at use-cases); this did not.
  (let* ((form  (->raw-formula form0))
         (thunk (and (pair? opt) (car opt)))
         (new  (dk-opened (lambda () (cut form))))
         (side (or (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) form)) new)
                   (error "have!: no side goal for" form)))
         (main (or (any-pred (lambda (s) (not (eq? s side))) new)
                   (error "have!: no main branch (CLAIM already in context up to alpha?)" form))))
    (dk-focus! side) (if thunk (thunk) (from-context!))
    ;; The side goal MUST be closed here.  Without this check have! would move to
    ;; main with CLAIM assumed but its proof left as a dangling open leaf -- not
    ;; unsound (qed still refuses) but the failure surfaces far away, at qed.  Fail
    ;; loudly AT the offending have! instead (the `dk-' kit's "make it error" rule).
    ;; Name the path that actually ran.  This message used to say "THUNK left
    ;; the side goal open" even when no THUNK was passed, sending the caller to
    ;; look for a bug in a thunk they never wrote; the real cause in that case is
    ;; that the DEFAULT is `from-context!', which is not a prover -- it closes a
    ;; claim already in context (plus two arithmetic shapes) and nothing else.
    (if (not (sequent-node-grounded? side))
        (error (if thunk
                   "have!: THUNK left the side goal open (claim not established)"
                   "have!: from-context! could not establish the claim -- no THUNK given, and the default only closes a claim already in context up to alpha (or an AND of such, or ground arithmetic).  Supply a THUNK, or use `cut' if you mean to discharge the obligation later")
               form))
    (dk-focus! main) main))

;;; -----------------------------------------------------------------------
;;; use-cases -- reason by cases on a disjunction.  Two steps, matching the
;;; textbook rule:
;;;   (1) ESTABLISH the disjunction (OR A1 ... AN): `cut' it, opening an
;;;       obligation side goal (prove the cases are exhaustive) plus a main
;;;       branch that now assumes it.  SKIPPED when the disjunction is already a
;;;       context hypothesis -- re-cutting an in-context formula is a silent alpha
;;;       self-loop in this kernel (dg-post! hash-conses by alpha-equivalence).
;;;   (2) SPLIT it (symmetric OR-elimination via `ai'): one leaf per disjunct,
;;;       branch k assuming ONLY Ak.  Nested binary ORs are flattened.
;;; TWO ways to call it:
;;;   (use-cases DISJUNCTS BODY1 ... BODYN)  -- POSITIONAL.  DISJUNCTS is a list
;;;       (A1 ... AN); BODYk is a thunk run on the k-th branch (context S0 + Ak).
;;;       Branches come back in disjunct order, so bodies match by POSITION -- no
;;;       marker/label needed, the position is the index.  Returns the obligation
;;;       NODE (or #f when the OR was already in context) for you to discharge.
;;;   (use-cases DISJUNCTS)  -- DATA.  No bodies: returns an alist
;;;       (obligation . NODE-or-#f) (cases . ((MARKER . NODE) ...)), MARKER = the
;;;       disjunct.  Drive it with `cases-obligation' + `for-each-case' when you
;;;       want data-driven dispatch instead of positional bodies.
;;; DISJUNCTS may also be a single pre-built (OR ...) (e.g. a trichotomy already in
;;; context).  Symmetric OR-elim: branch k assumes ONLY Ak.  Shared "branch, then
;;; label" core that use-induction / use-infinite-descent layer over.
;; A disjunct may be written in ANY of the three surface forms a tactic accepts:
;; a raw S-expression, a string in the concrete syntax, or a wff-in-context from
;; `make-wff'.  `cut' would coerce a string itself, but only AFTER the OR-tower
;; is assembled -- so an uncoerced disjunct ends up embedded inside the tower and
;; every later alpha-comparison against a landed hypothesis misses.  Coerce each
;; disjunct FIRST, and the three spellings become interchangeable:
;;   (use-cases '((= x 0) (= x 1)) ass ass)
;;   (use-cases '("x = 0" "x = 1") ass ass)
;;   (use-cases (list (make-wff "x = 0") (make-wff "x = 1")) ass ass)
(define (use-cases--raw d)
  (cond ((wff? d)    (wff-formula d))
        ((string? d) (->raw-formula d))
        (else        d)))

(define (use-cases--disjuncts->or ds0)
  (let ((ds (map use-cases--raw ds0)))
    (let build ((ds ds))
      (cond ((null? ds) (error "use-cases: no disjuncts"))
            ((null? (cdr ds)) (car ds))
            (else (list 'OR (car ds) (build (cdr ds))))))))

;; step (2): eliminate an in-context binary OR, flattening nested ORs.
(define (use-cases--split or-form)
  (if (not (and (pair? or-form) (eq? (car or-form) 'OR) (= (length or-form) 3)))
      (error "use-cases: not a binary disjunction" or-form))
  (let* ((a   (cadr or-form))
         (b   (caddr or-form))
         (new (dk-opened (lambda () (ai or-form)))))
    (define (leaf-with disj)
      (or (any-pred (lambda (s) (any-pred (lambda (h) (alpha-equiv? h disj)) (dk-asms-of s))) new)
          (error "use-cases: no branch landed the disjunct" disj)))
    (define (branch disj)
      (let ((leaf (leaf-with disj)))
        (if (and (pair? disj) (eq? (car disj) 'OR))
            (begin (dk-focus! leaf) (use-cases--split disj))   ; flatten a nested OR
            (list (cons disj leaf)))))
    (append (branch a) (branch b))))

(define (use-cases first0 . bodies)
  (let* ((first   (if (list? first0) first0 (use-cases--raw first0)))  ; a lone OR, any spelling
         (or-form (if (and (pair? first) (eq? (car first) 'OR))
                      first                                       ; a pre-built (OR ...)
                      (use-cases--disjuncts->or first)))          ; first = disjunct list
         (in? (any-pred (lambda (h) (alpha-equiv? h or-form))
                        (dk-asms-of (proof-state-focus *ps*))))
         (oblig #f))
    (if (not in?)                                                 ; step (1): cut unless present
        (let* ((new  (dk-opened (lambda () (cut or-form))))
               (side (or (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) or-form)) new)
                         (error "use-cases: cut produced no obligation goal")))
               (main (or (any-pred (lambda (s) (not (eq? s side))) new)
                         (error "use-cases: cut produced no main branch"))))
          (set! oblig side)
          (dk-focus! main)))
    (let ((cases (use-cases--split or-form)))                     ; step (2)
      (if (null? bodies)
          (list (cons 'obligation oblig) (cons 'cases cases))     ; DATA mode
          (begin                                                  ; POSITIONAL mode
            (if (not (= (length bodies) (length cases)))
                (error "use-cases: body count /= disjunct count" (length bodies) (length cases)))
            (for-each (lambda (mc th) (dk-focus! (cdr mc)) (th)) cases bodies)
            oblig)))))

;; (cases-obligation RESULT) -- the exhaustiveness side goal, or #f if none.
(define (cases-obligation result)
  (let ((o (and (pair? result) (assq 'obligation result)))) (and o (cdr o))))

;; (for-each-case RESULT BODY) -- focus each branch's leaf, call (BODY MARKER).
;; Accepts a use-cases RESULT (an alist with a 'cases key) or a bare (MARKER . NODE) list.
(define (for-each-case result body)
  (let* ((c (and (pair? result) (assq 'cases result)))
         (branches (if c (cdr c) result)))
    (for-each (lambda (mc) (dk-focus! (cdr mc)) (body (car mc))) branches)))

;;; -----------------------------------------------------------------------
;;; use-em -- the EXCLUDED-MIDDLE case split, i.e. use-cases on (P, NOT P) with
;;; the exhaustiveness obligation discharged for you.
;;;
;;; This is the one obligation use-cases can always close by itself, and three
;;; drivers had each hand-rolled the same twenty-line closure (mu-em in
;;; matunit-shift-proof.scm, and its copies in smith-clear-proof.scm and
;;; elem-actions-proof.scm).  The closure is classical and debt-free: assume the
;;; disjunction false (pbc); then P alone re-derives it (or-intro left) and NOT P
;;; alone re-derives it (or-intro right), and either way the negated disjunction
;;; gives FALSITY.
;;;
;;;   (use-em P BODY-TRUE BODY-FALSE)  -- POSITIONAL, like use-cases; BODY-TRUE
;;;       runs on the branch assuming P, BODY-FALSE on the branch assuming NOT P.
;;;   (use-em P)                       -- DATA; returns use-cases' alist, whose
;;;       (obligation . NODE) is already closed.
;;; Nothing is cut when (OR P (NOT P)) is already a hypothesis -- use-cases'
;;; alpha-self-loop guard covers that case too.
;;;
;;; It REFUSES to split on a proposition the context already decides: see
;;; `use-em--decided' below for why that is an error and not a warning.

;; close a goal that IS (OR P (NOT P)).  Errors if it is not.
(define (em-prove!)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'OR) (= (length g) 3)
                  (equal? (caddr g) (list 'NOT (cadr g)))))
        (error "em-prove!: goal is not (OR P (NOT P))" g))
    (let ((notg (list 'NOT g)) (P (cadr g)))
      (pbc)                                     ; assume (NOT g); goal FALSITY
      (have! (list 'NOT P)                      ; ... first, NOT P
             (lambda ()
               (di)                             ; assume P; goal FALSITY
               (have! g (lambda () (oi-l) (ass)))
               (ai notg)))
      (have! g (lambda () (oi-r) (ass)))        ; ... now the other disjunct
      (ai notg))))

;;; The proposition to split on, when the caller does not name one: the LEFT
;;; DISJUNCT of a disjunctive goal.  On `x in a or x in complement-in(b,a)' the
;;; split that helps is on `x in a' -- the right disjunct is the one whose proof
;;; needs the negation -- and that is not a guess, it is the only case split the
;;; goal's shape offers.  Errors elsewhere rather than inventing one.
(define (use-em--default-p)
  (let ((g (dk-goal)))
    (if (and (pair? g) (memq (car g) '(OR or)) (= (length g) 3))
        (cadr g)
        (error "use-em: no proposition given, and the goal is not a disjunction" g))))

;;; (use-em P body-true body-false)  -- split on P
;;; (use-em P)                       -- split, return the branches as data
;;; (use-em body-true body-false)    -- split on the goal's LEFT DISJUNCT
;;; (use-em)                         -- ... and return the branches as data
;;;
;;; The last two exist because the argument was compulsory and on a disjunctive
;;; goal it is deducible: a user staring at `x in a or x in ...' should not have
;;; to retype `x in a' to ask for the only split available.  A first argument
;;; that is a PROCEDURE is a body, not a proposition, which is what makes the
;;; two forms distinguishable.
(define (use-em . args)
  (let* ((named  (and (pair? args) (not (procedure? (car args)))))
         (P0     (if named (car args) (use-em--default-p)))
         (bodies (if named (cdr args) args)))
    (apply use-em--on P0 bodies)))

;;; A split on a proposition the context ALREADY DECIDES is not a case split.
;;; Say P is an assumption.  Then the P-branch adds nothing --
;;; `context-add-assumption' is alpha-idempotent (sequents.scm:51), so that
;;; branch is hash-consed back onto the node it was split from -- and the NOT-P
;;; branch has a contradictory context, closable only by NOT-elim off the pair.
;;; The caller has spent a split, gained nothing, and is left looking at a leaf
;;; that reads like an obligation and is not one.  If NOT P is the assumption,
;;; the same holds mirrored.  There is no undo in the tree, so this ERRORS
;;; rather than warning: an unwanted branch cannot be taken back, and a warning
;;; on a REPL that has already scrolled is a warning nobody reads.
;;;
;;; Returns (SIDE . INDEX): SIDE is 'P when the assumption IS the proposition
;;; and 'NOT when it is its negation; INDEX is the 1-based assumption number, so
;;; the message can name the thing the caller is looking at.  `alpha-equiv?' can
;;; error on a malformed formula, hence `(eq? #t (vnb-guard ...))' -- vnb-guard
;;; returns a warning RECORD on failure, and a record is true.
(define (use-em--decided P)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) #f)
          ((eq? #t (vnb-guard (lambda () (alpha-equiv? (car as) P)))) (cons 'P i))
          ((and (pair? (car as)) (eq? (caar as) 'NOT)
                (eq? #t (vnb-guard (lambda () (alpha-equiv? (cadr (car as)) P)))))
           (cons 'NOT i))
          (else (loop (cdr as) (+ i 1))))))

;;; The move the caller wanted, when the decided proposition is also a disjunct
;;; of the goal: or-introduction on that side, then `ass'.  Only offered when
;;; the ASSUMPTION is P itself -- if the context holds NOT P then P is not what
;;; closes the goal and naming an `oi' would send the caller down a dead branch.
(define (use-em--decided-advice P side)
  (let ((g (dk-goal)))
    (and (eq? side 'P)
         (pair? g) (memq (car g) '(OR or)) (= (length g) 3)
         (cond ((eq? #t (vnb-guard (lambda () (alpha-equiv? (cadr g) P)))) "oi-l")
               ((eq? #t (vnb-guard (lambda () (alpha-equiv? (caddr g) P)))) "oi-r")
               (else #f)))))

(define (use-em--decided-error P dec)
  (let* ((side (car dec))
         (i    (number->string (cdr dec)))
         (adv  (use-em--decided-advice P side)))
    (error (string-append
            "use-em: the context already decides this proposition -- assumption "
            i (if (eq? side 'P) " IS it" " is its negation")
            " -- so the split is vacuous on one branch and contradictory on the other"
            (if adv
                (string-append ", and it is a disjunct of the goal: use ("
                               adv ") then (ass)")
                ""))
           P)))

(define (use-em--on P0 . bodies)
  (let* ((P      (use-cases--raw P0))        ; raw / string / wff, like use-cases
         (dec    (use-em--decided P))
         (ignore (if dec (use-em--decided-error P dec)))
         (result (use-cases (list P (list 'NOT P))))
         (oblig  (cases-obligation result))
         (cases  (cdr (assq 'cases result))))
    (if oblig (begin (dk-focus! oblig) (em-prove!)))
    (cond ((null? bodies) result)
          ((not (= (length bodies) 2))
           (error "use-em: expected 2 bodies (P, NOT P), got" (length bodies)))
          (else (for-each (lambda (mc th) (dk-focus! (cdr mc)) (th)) cases bodies)
                oblig))))

;;; -----------------------------------------------------------------------
;;; use-induction -- NN-induction on a goal (forall v (implies (in v nn) INNER)),
;;; with the frame bookkeeping done: it runs `ni', labels the two branches (the
;;; STEP is the one whose goal is still (forall v ...) -- discriminated by the
;;; binder, not by shape), and PEELS the step so v and (in v nn) are introduced
;;; and the induction hypothesis is landed and captured.  Returns an alist:
;;;   (base . NODE)  goal INNER[v:=0]
;;;   (step . NODE)  goal INNER[v:=succ v], with (in v nn) and the IH in context
;;;   (ih   . FORM)  the captured IH INNER[v] (eigenvar-safe -- taken by diff)
;;;   (var  . v)     the induction variable
;;; The one creative step -- base proof and step argument -- is left to the caller;
;;; use-infinite-descent layers on this (its minimality step is an induction).
(define (use-induction)
  (let ((goal (dk-goal-of (proof-state-focus *ps*))))
    (if (not (and (pair? goal) (eq? (car goal) 'FORALL)))
        (error "use-induction: goal is not (forall v (implies (in v nn) ...))" goal))
    (let* ((v        (quantifier-var goal))
           (branches (dk-opened (lambda () (ni))))
           (step (or (any-pred (lambda (s) (let ((g (dk-goal-of s)))
                                             (and (pair? g) (eq? (car g) 'FORALL)
                                                  (eq? (quantifier-var g) v))))
                               branches)
                     (error "use-induction: no step branch (goal (forall v ...))")))
           (base (or (any-pred (lambda (s) (not (eq? s step))) branches)
                     (error "use-induction: no base branch"))))
      (dk-focus! step)
      (di)                                          ; introduce v, land (in v nn)
      (let ((ih (dk-landed-1 (lambda () (di)))))     ; land + capture the IH
        (list (cons 'base base)
              (cons 'step (proof-state-focus *ps*)) ; goal now INNER[v:=succ v]
              (cons 'ih   ih)
              (cons 'var  v))))))

;;; -----------------------------------------------------------------------
;;; use-infinite-descent -- the frame for a least-counterexample proof (Fermat's
;;; infinite descent).  Set the goal up as FALSITY with the counterexample opened
;;; into context (e.g. after the leading di's), then:
;;;   (use-infinite-descent VAR GUARD MEASURE NONEMPTY-THUNK [TYPE-THUNK])
;;; wraps `minimize!' on (VAR): it picks the counterexample with MEASURE least,
;;; unpacks minimize!'s return, discharges the two obligations any minimization
;;; owes -- TYPE (forall v. GUARD => MEASURE in NN; generic di/di/sk--split!/ass
;;; when MEASURE=VAR and GUARD's conjunct is (IN VAR NN), else pass TYPE-THUNK) and
;;; NONEMPTY (forsome v. GUARD; the caller's NONEMPTY-THUNK supplies the witness --
;;; the one creative bit) -- and leaves focus on the FALSITY branch.  Returns an
;;; alist: (witness . w) the minimal counterexample; (guard . GUARD[VAR:=w]);
;;; (minimal . M) the minimality hypothesis forall v. GUARD(v) => MEASURE(w) <=
;;; MEASURE(v); (main . NODE) the FALSITY leaf.  The caller writes ONLY the descent
;;; step: from w, build a strictly smaller counterexample and contradict `minimal'.
;;; (Layers on well-ordering, which is where the "step is itself an induction" is.)
(define (use-infinite-descent var guard measure nonempty-thunk . opt)
  (let* ((type-thunk (and (pair? opt) (car opt)))
         (R    (minimize! (list var) guard measure))
         (w    (car (car R)))                    ; (car ws) -- the minimal witness
         (tob  (cadr R))                          ; TYPE obligation node or #f
         (nob  (caddr R))                         ; NONEMPTY obligation node or #f
         (main (proof-state-focus *ps*))
         (minf (any-pred (lambda (f) (and (pair? f) (eq? (car f) 'FORALL)))
                         (dk-asms-of main))))
    (when tob
      (dk-focus! tob)
      (if type-thunk (type-thunk) (begin (di) (di) (sk--split!) (ass))))
    (when nob (dk-focus! nob) (nonempty-thunk))
    (dk-focus! main)
    (list (cons 'witness w)
          (cons 'guard   (subst-free var w guard))
          (cons 'minimal minf)
          (cons 'main    main))))

;;; -----------------------------------------------------------------------
;;; GOAL-SIDE VOCABULARY.  The frame tactics above open branches from the
;;; HYPOTHESIS side (a disjunction, an induction, a descent).  These do the same
;;; job on the GOAL side: a rule that splits the goal into named parts, with a
;;; body per part.
;;;
;;; They exist because the alternative had taken over the drivers.  Splitting a
;;; two-part goal was coming out as
;;;
;;;   (for-each (lambda (leaf)
;;;               (dk-focus! leaf)
;;;               (if (eq? (car (dk-goal)) 'IN) <this> <that>))
;;;             (dk-opened (lambda () (sep-mi))))
;;;
;;; -- five lines of leaf plumbing per split, nested three deep in
;;; ord-no-injection and zz-bezout-proof, and dispatching on the goal's HEAD,
;;; which is the shape-matching CLAUDE.md warns against: two halves of a split
;;; can perfectly well share a head.
;;;
;;; Each helper below instead COMPUTES the two subgoals from the goal it is
;;; about to split -- `both!' reads the AND's conjuncts, `in-sep!' builds the
;;; domain membership out of the SEP's own domain -- and matches the opened
;;; leaves against them by alpha-equivalence.  The assignment cannot be wrong,
;;; and it errors rather than silently running a body on the wrong branch.

;; (both! B1 B2) -- goal (AND p q); B1 proves p, B2 proves q.
(define (both! b1 b2)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'AND) (= (length g) 3)))
        (error "both!: goal is not a binary AND" g))
    (let* ((p (cadr g)) (q (caddr g))
           (ls (dk-opened (lambda () (di))))
           (lp (or (any-pred (lambda (l) (alpha-equiv? (dk-goal-of l) p)) ls)
                   (error "both!: no subgoal for the first conjunct" p)))
           (lq (or (any-pred (lambda (l) (and (not (eq? l lp))
                                              (alpha-equiv? (dk-goal-of l) q))) ls)
                   (error "both!: no subgoal for the second conjunct" q))))
      (dk-focus! lp) (b1)
      (dk-focus! lq) (b2))))

;; (in-sep! B-DOM B-PROP) -- goal (IN t (SEP x A p)); B-DOM proves (IN t A),
;; B-PROP proves p[x:=t].  Those are exactly the two subgoals pi-sep-mem-intro!
;; opens, and the domain one is rebuilt here from the SEP, not guessed.
(define (in-sep! b-dom b-prop)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'IN)
                  (pair? (caddr g)) (eq? (car (caddr g)) 'SEP)))
        (error "in-sep!: goal is not (IN t (SEP x A p))" g))
    (let* ((t   (cadr g))
           (dom `(IN ,t ,(caddr (caddr g))))
           (ls  (dk-opened (lambda () (sep-mi))))
           (ld  (or (any-pred (lambda (l) (alpha-equiv? (dk-goal-of l) dom)) ls)
                    (error "in-sep!: no domain subgoal" dom)))
           (lp  (or (any-pred (lambda (l) (not (eq? l ld))) ls)
                    (error "in-sep!: no property subgoal" g))))
      (dk-focus! ld) (b-dom)
      (dk-focus! lp) (b-prop))))

;; (witness! T BODY) -- goal (FORSOME v p); exhibit T and let BODY prove p[v:=T].
;; Names the move; `ew' alone reads as though the witness were arbitrary.
(define (witness! t body) (ew t) (body))

;; (subset-by-element!) -- goal (SUBSET A B); unfold to the elementwise form and
;; introduce the element.  Returns the eigenvariable, so the caller can name it:
;;   (let ((x (subset-by-element!))) ... )   "let x be an element of A".
(define (subset-by-element!)
  (mac 'subset-def)
  (let ((landed (dk-landed-1 (lambda () (di)))))
    (cadr landed)))                          ; from the landed (IN x A)

;; (inst*! F T1 T2 ...) -- instantiate the in-context universal F at T1, T2, ...
;; in turn, detaching each guard that is already in context, and return the
;; formula that finally landed.  `inst+' does one binder and stops at the next
;; FORALL; three drivers had each rewritten this fold.
(define (inst*! f . terms)
  (let loop ((f f) (ts terms))
    (if (null? ts)
        f
        (loop (dk-deepest (lambda () (inst+ f (car ts)))) (cdr ts)))))

;; (choose! S WITNESS BODY) -- "pick an element of S".  Lands
;; (IN (CHOICE S) S) in the context, discharging the ONE obligation choice owes:
;; that S is inhabited, for which WITNESS is the exhibited member and BODY the
;; proof that it belongs.  When S is a SEP the membership is split into its two
;; halves as well (that is what a caller always wants next), and the landed
;; conjuncts are returned.
;;
;; choice-axiom (theory.scm) is GLOBAL choice -- S may be a proper class -- so
;; this works for a SEP over ORD, which is what the Burali-Forti argument needs.
(define (choose! s witness body)
  (have! `(FORSOME z_ (IN z_ ,s)) (lambda () (witness! witness body)))
  (let ((mem (dk-fact! 'choice-axiom s)))
    (if (and (pair? s) (eq? (car s) 'SEP))
        (dk-landed (lambda () (sep-me mem)))
        (list mem))))


;;; -----------------------------------------------------------------------
;;; eps-chain -- the n-epsilon argument, in one call.
;;;
;;;   (eps-chain S '(x0 x1 ... xn))   on a goal   (< ((DIST S) x0 xn) eps)
;;;
;;; A mathematician writes "d(x0,xn) <= d(x0,x1) + ... + d(x[n-1],xn) < eps" and
;;; considers the matter closed.  Three things stand between that sentence and
;;; the checker, and only the first is mathematics:
;;;
;;;   1. the n-1 triangle instances, right-nested;
;;;   2. an RR certificate for EVERY distance atom.  `ineq' will not reason about
;;;      an atom it cannot type -- "uncertified atoms => refuse"
;;;      (structure-library/ineq-oracle.scm) -- and WITHOUT these it reports
;;;      "goal not a linear-RR consequence of the named assumptions", which reads
;;;      like a linearisation failure and is nothing of the kind.  This is the
;;;      step no human writes and the one that makes the obvious attempt fail;
;;;   3. the composition, which is linear in the distance atoms and so falls to a
;;;      single Fourier-Motzkin certificate however many hops there are.
;;;
;;; The HOP BOUNDS are the caller's business: this composes, it does not
;;; discover.  State them DIVISION-FREE -- hops under e1..en with e1+...+en <=
;;; eps -- rather than n copies of eps/n; eps/n is then an instance, and no
;;; `recip' enters the goal.
;;;
;;; Adds NO trusted surface: metric-triangle is proven (metric-laws.scm),
;;; metric-dist-real is a warranted support (metric-space.scm), and `ineq' is an
;;; oracle already in the trusted base.
;;;
;;; Self-contained on purpose: driver-kit loads at load.scm:411 and calc at :425,
;;; so borrowing `calc--order-premises' would be a forward reference that happens
;;; to work only because Scheme resolves free variables at call time.  The index
;;; logic below is calc's, copied deliberately rather than depended upon.

;;; The premises handed to `ineq'.  NOT simply "every order assumption": an
;;; order fact whose atoms the oracle cannot certify in RR POISONS the call.
;;; `ineq-atom-rr-ok?' (structure-library/ineq-oracle.scm) runs over the union
;;; of the atoms of every ACCEPTED premise, and a premise that is arithmetic in
;;; SHAPE is accepted -- so one `cap <= n_' over NN-typed indices, which every
;;; eps-argument's context carries by construction, makes the whole call refuse
;;; with "goal not a linear-RR consequence".
;;;
;;; Measured 2026-08-23, and it is why this engine had never closed anything:
;;; on `d(f m, f n_) <= eps' from `d(f m, L) <= h', `d(f n_, L) <= h', `h+h=eps'
;;; -- the leaf of converges-implies-cauchy -- the unfiltered version failed and
;;; the SAME context with the five relevant premises named by hand closed at
;;; once.  The two NN threshold facts `cap <= m', `cap <= n_' were the whole
;;; difference.  `contra--usable-indices' (contra.scm) filters for exactly this
;;; reason; contra.scm loads at load.scm:1814 and driver-kit at :499, so the
;;; test is re-implemented here rather than borrowed -- as this file's header
;;; says of calc's index logic.
(define *eps-chain-arith-heads* '(+ - * recip abs succ binplus binneg bintimes))

(define (eps-chain--atoms-of term acc)
  (cond ((number? term) acc)
        ((symbol? term) (if (member term acc) acc (cons term acc)))
        ((pair? term)
         (if (memq (car term) *eps-chain-arith-heads*)
             (let lp ((l (cdr term)) (a acc))
               (if (null? l) a (lp (cdr l) (eps-chain--atoms-of (car l) a))))
             (if (member term acc) acc (cons term acc))))
        (else acc)))

(define (eps-chain--rr-ok? t)
  (or (and (pair? t) (eq? (car t) 'abs))          ; rr-abs-closed
      (let loop ((as (dk-asms)))
        (and (pair? as)
             (or (let ((f (car as)))
                   (and (pair? f) (eq? (car f) 'IN) (= (length f) 3)
                        (equal? (cadr f) t) (eq? (caddr f) 'RR)))
                 (loop (cdr as)))))))

(define (eps-chain--order-premises)      ; 1-based indices of the USABLE order assumptions
  (let loop ((as (dk-asms)) (i 1) (acc '()))
    (cond ((null? as) (reverse acc))
          ((and (pair? (car as)) (memq (caar as) '(< <= = ==))
                (= (length (car as)) 3)
                (let ((ats (eps-chain--atoms-of (caddr (car as))
                             (eps-chain--atoms-of (cadr (car as)) '()))))
                  (let allok ((vs ats))
                    (or (null? vs)
                        (and (eps-chain--rr-ok? (car vs)) (allok (cdr vs)))))))
           (loop (cdr as) (+ i 1) (cons i acc)))
          (else (loop (cdr as) (+ i 1) acc)))))

;; every distance atom the argument mentions: each hop, and each point to the far
;; end.  Deduplicated -- the last hop IS a to-the-far-end pair, and citing
;; metric-dist-real twice for it would land nothing the second time and error.
(define (eps-chain--atoms pts)
  (let ((xn (car (last-pair pts))))
    (let loop ((p pts) (acc '()))
      (if (null? (cdr p))
          (reverse acc)
          (let* ((hop (cons (car p) (cadr p)))
                 (far (cons (car p) xn))
                 (acc (if (member hop acc) acc (cons hop acc)))
                 (acc (if (member far acc) acc (cons far acc))))
            (loop (cdr p) acc))))))

(define (eps-chain s pts)
  (if (or (not (pair? pts)) (null? (cdr pts)))
      (error "eps-chain: need at least two points" pts))
  (let* ((node (proof-state-focus *ps*))
         (g    (dk-goal))
         (x0   (car pts))
         (xn   (car (last-pair pts))))
    (if (not (and (pair? g) (memq (car g) '(< <=))))
        (error "eps-chain: goal is not an inequality" g))
    (if (not (equal? (cadr g) `((DIST ,s) ,x0 ,xn)))
        (error "eps-chain: goal's left side is not d(first,last) of the chain"
               (cadr g) `((DIST ,s) ,x0 ,xn)))
    ;; (1) the triangle instances
    (let loop ((p pts))
      (if (pair? (cddr p))
          (begin (dk-fact! 'metric-triangle s (car p) (cadr p) xn)
                 (loop (cdr p)))))
    ;; (2) certify the atoms -- the step that decides whether (3) can happen
    (for-each (lambda (pr) (dk-fact! 'metric-dist-real s (car pr) (cdr pr)))
              (eps-chain--atoms pts))
    ;; (3) compose
    (apply ineq (eps-chain--order-premises))
    ;; a silent no-op IS the bug (CLAUDE.md): say so where it happened.
    (if (not (sequent-node-grounded? node))
        (error "eps-chain: ineq did not close the goal -- are the hop bounds in context, and do they sum under the bound?"
               (dk-goal-of node)))
    node))

;;; -----------------------------------------------------------------------
;;; Arm the containment.  From here on prover-load gives every theorem-library/
;;; and calculus/ file its own top-level environment (load.scm).
;;; -----------------------------------------------------------------------
;;; Focus and citation BY CONTENT.
;;;
;;; The kit already had dk-focus! (focus a node you hold) and dk-opened (the
;;; nodes a branching tactic just made).  What it did not have is a way to say
;;; WHICH of them you mean, so every driver hand-rolled one -- and a focus
;;; helper that misses silently hides every command after it.  These error.
;;;
;;; Promoted from theorem-library/nn-pairing.scm when a second file
;;; (nn-order-proof) needed the same three.

;;; Focus the UNIQUE open leaf whose goal, printed, contains FRAG.
(define (dk-focus-goal! frag)
  (let ((hits (filter (lambda (l)
                        (string-search-forward
                         frag (wff->string (sequent-node-assertion l)) 0))
                      (proof-leaves))))
    (cond ((null? hits)          (error "dk-focus-goal!: no leaf matching" frag))
          ((not (null? (cdr hits))) (error "dk-focus-goal!: ambiguous" frag))
          (else (dk-focus! (car hits))))))

;;; Focus the node among NODES carrying FORM in its CONTEXT.  Sibling branches
;;; routinely share a goal, so a case split can only be told apart by context.
(define (dk-focus-ctx! form nodes)
  (let ((hit (any-pred (lambda (s)
                         (any-pred (lambda (a) (equal? a form))
                                   (map wff-formula (sequent-node-assumptions s))))
                       nodes)))
    (if (not hit) (error "dk-focus-ctx!: no branch with" form))
    (dk-focus! hit)))

;;; ai the context assumption whose head is HEAD, citing the formula FROM the
;;; context rather than reconstructing it -- a reconstructed formula matches
;;; nothing and no-ops.  Note ai takes the RAW S-expression, not a wff: handing
;;; it a wff reports "cannot decompose", which reads like a decomposition
;;; failure and is really a lookup miss.
(define (dk-ai-head! head)
  (let ((f (any-pred (lambda (a) (and (pair? a) (eq? (car a) head))) (dk-asms))))
    (if (not f) (error "dk-ai-head!: no assumption with head" head))
    (dk-landed (lambda () (ai f)))))

;;; ai on a NOT is NOT-ELIM: it CLOSES the branch and lands nothing, so it must
;;; not go through dk-landed, which errors when nothing lands.  Separate entry
;;; point rather than a special case, so the caller says which it means.
(define (dk-ai-not!)
  (let ((f (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'NOT))) (dk-asms))))
    (if (not f) (error "dk-ai-not!: no NOT assumption"))
    (ai f)))

;;; di until the goal's head is HEAD.  di is GREEDY -- one call takes the whole
;;; leading FORALL/IMPLIES prefix -- so counting di's is not a way to land on a
;;; chosen goal; guard on the head instead.  Errors rather than looping.
(define (dk-peel-to! head)
  (let loop ((n 0))
    (cond ((eq? (car (dk-goal)) head) 'done)
          ((> n 8) (error "dk-peel-to!: never reached" head (dk-goal)))
          (else (di) (loop (+ n 1))))))

;;; (ew TERM) on a guarded existential, then di-split the resulting AND: the
;;; (IN ...) typing conjunct goes to TYPE-THUNK, the body to BODY-THUNK.
(define (dk-ew-split! term type-thunk body-thunk)
  (ew term)
  (for-each (lambda (k)
              (dk-focus! k)
              (if (eq? (car (dk-goal)) 'IN) (type-thunk) (body-thunk)))
            (dk-opened (lambda () (di)))))

(define *driver-kit-env* (the-environment))
(set! *contain-proof-files?* #t)
(display ";; driver-kit: proof files from here on load in private environments")
(newline)

;;; -----------------------------------------------------------------------
;;; dk-lam-t! -- lam-t, with its SETHOOD obligation discharged.
;;;
;;; The 2026-08-02 soundness repair gave (VNB-LAMBDA bspec A body) its domain
;;; and gave `lambda-type' a SECOND subgoal, (IN A SET): membership in FUN(A,B)
;;; implies sethood (membership-implies-sethood), and a class function on a
;;; proper-class domain is a proper class, so the rule owes it.  For every
;;; domain the library actually uses that obligation is a one-liner, and paying
;;; it by hand at each of the lam-t sites would be N patches for one fact.
;;;
;;; Closes the (IN A SET) leaf, leaves focus on the TYPING leaf, and returns it
;;; -- so `(dk-lam-t!)' is a drop-in for `(lam-t)' in an existing driver.
(define (dk-set-close! A)
  (cond ((symbol? A)
         (case A
           ((NN) (fact 'nn-is-set)) ((RR) (fact 'rr-is-set))
           ((ZZ) (fact 'zz-is-set)) ((QQ) (fact 'qq-is-set))
           ((CC) (fact 'cc-is-set)) ((SET) #f)
           ((EMPTY-SET) (fact 'empty-set-is-set))
           ((ORD) #f)                      ; ORD is a PROPER class -- burali-forti
           (else #f)))
        ((and (pair? A) (eq? (car A) 'INTERVAL))
         (fact 'interval-in-set (cadr A) (caddr A)))
        ((and (pair? A) (eq? (car A) 'CARTESIAN))
         (dk-set-close! (cadr A))
         (dk-set-close! (caddr A))
         (fact 'cartesian-set-iff (cadr A) (caddr A)))
        (else #f))
  (ass))

(define (dk-lam-t!)
  (let* ((before (proof-leaves)))
    (lam-t)
    (let* ((new  (filter (lambda (l) (not (memq l before))) (proof-leaves)))
           (sets (filter (lambda (l)
                           (let ((g (dk-goal-of l)))
                             (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))))
                         new))
           (typ  (filter (lambda (l) (not (memq l sets))) new)))
      (for-each (lambda (l)
                  (set-proof-state-focus! *ps* l)
                  (dk-set-close! (cadr (dk-goal-of l))))
                sets)
      (if (pair? typ)
          (begin (set-proof-state-focus! *ps* (car typ)) (car typ))
          (error "dk-lam-t!: lam-t left no typing goal")))))

;;; -----------------------------------------------------------------------
;;; Taking operation-SLOT applications down to the surface operator.
;;;
;;; Since 2026-08-29 a numeric instance's ADD/MUL/NEG slot holds a tupled
;;; VNB-LAMBDA rather than the shared constant `binplus' -- one object cannot be
;;; a set function with five different domains, and asserting so proved
;;; NN = ZZ = QQ = RR = CC and thence FALSITY (numeric-instances.scm).  The
;;; consequence for drivers: `crs' and the law citations meet
;;; (vnb-lambda(...))(u,v) where they used to meet u + v, and the read-offs that
;;; fix that (lam-slot-add-apply and siblings) are GUARDED -- as they must be,
;;; since off the carrier the application is outside the lambda's domain.
;;;
;;; Guarded means this is a LOOP, not a rewrite:
;;;   * a guarded macete does not fire until its side condition is in context,
;;;     so arguments must be TYPED first;
;;;   * the applications NEST.  In L(L(u,v),w) only the inner redex has typed
;;;     arguments; the outer then needs (u+v) in C, the carrier's closure axiom
;;;     applied to a term that did not exist until the inner rewrite happened.
;;; Each pass strips one level and types the result for the next.
;;;
;;; CLOSURE is an alist from the operation head to the carrier's closure axiom,
;;; e.g. ((+ . zz-add-closed) (* . zz-mul-closed) (- . zz-neg-closed)).

(define (dk-subterms t)
  (if (pair? t) (cons t (append-map dk-subterms (cdr t))) (list t)))

;;; Is F an assumption of the focus, up to alpha?  `member' with equal? misses a
;;; context formula differing only in bound-variable names.
(define (dk-asm? f)
  (let any ((as (dk-asms)))
    (and (pair? as) (or (alpha-equiv? (car as) f) (any (cdr as))))))

;;; cut F, prove the side goal from context, leave focus on the main branch.
;;;
;;; WHY NOT `have!'.  have! requires BOTH branches of the cut to be NEW leaves
;;; and errors "no side goal" otherwise.  Sequent nodes are hash-consed on
;;; assertion-up-to-alpha PLUS context, so a claim an earlier branch already
;;; proved under the same context lands on a node that is already GROUNDED --
;;; not an open leaf, so dk-opened reports one new leaf rather than two, and
;;; have! reads that as failure when it means the obligation was discharged
;;; before we arrived.  Never infer success or failure from how many leaves a
;;; rule opens; ask whether the node is grounded.
;;; (dk-have! CLAIM) / (dk-have! CLAIM THUNK) -- like have!, but tolerant of the
;;; two things hash-consing does to a cut: the claim may ALREADY be in context
;;; (then this is a no-op, where have! errors "no main branch"), and its side
;;; goal may already be GROUNDED (then there is no new side leaf, where have!
;;; errors "no side goal").  Both are success, not failure.
(define (dk-have! form0 . opt)
  (let ((f (->raw-formula form0))
        (thunk (and (pair? opt) (car opt))))
    (if (not (dk-asm? f))
        (let* ((new  (dk-opened (lambda () (cut f))))
               (side (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) f)) new))
               (main (any-pred (lambda (s) (not (eq? s side))) new)))
          (when side
            (dk-focus! side)
            (if thunk (thunk) (from-context!))
            (if (not (sequent-node-grounded? side))
                (error "dk-have!: could not establish" f)))
          (if main
              (dk-focus! main)
              (error "dk-have!: cut left no main branch for" f))))))

(define (dk-saturate-slot-ops! carrier closure)
  (let loop ((fuel 12))
    (let ((before (dk-goal)))
      ;; (1) type every arithmetic subterm whose arguments are already typed
      (for-each
       (lambda (t)
         (let ((hit (and (pair? t) (assq (car t) closure))))
           (when hit
             (let ((args (cdr t)))
               (when (and (not (dk-asm? (list 'IN t carrier)))
                          (let all ((as args))
                            (or (null? as)
                                (and (dk-asm? (list 'IN (car as) carrier))
                                     (all (cdr as))))))
                 (quietly
                  (lambda ()
                    (if (pair? (cdr args))
                        (begin (dk-have! (list 'AND (list 'IN (car args)  carrier)
                                                    (list 'IN (cadr args) carrier)))
                               (fact (cdr hit) (car args) (cadr args)))
                        (fact (cdr hit) (car args))))))))))
       (dk-subterms (dk-goal)))
      ;; (2) fire the read-offs; each is a no-op where it does not apply
      (quietly (lambda ()
                 (mac 'lam-slot-add-apply)
                 (mac 'lam-slot-mul-apply)
                 (mac 'lam-slot-neg-apply)))
      (when (and (> fuel 0) (not (equal? (dk-goal) before)))
        (loop (- fuel 1))))))

;;; -----------------------------------------------------------------------
;;; THE PARTIAL-SUM RECURRENCE, WITH ITS GUARD DISCHARGED.
;;;
;;; `series-partial-sum-succ' has been GUARDED since 2026-08-29 on its two
;;; ARGUMENTS being real -- SPS(f,k) in RR and f(k) in RR -- because the
;;; operation slot of RR's additive group now holds a genuine set function on
;;; CARTESIAN(RR,RR) rather than the total constant `binplus'.  (One object
;;; cannot be a set function with five different domains; asserting so proved
;;; NN = ZZ = QQ = RR = CC and, through cc-i-squared, FALSITY.)  Unguarded the
;;; statement is now FALSE: off the reals the left side is an application
;;; outside its domain while the right side is not.
;;;
;;; The guard is on the ARGUMENTS rather than on `IN f (FUN NN RR)' deliberately.
;;; series-linearity.scm proves the POINTWISE forms because the Bernstein basis
;;; family is in FUN(ZZ, CARR R) and is not an element of FUN(NN,RR) at all; a
;;; membership guard would have made that whole file uncitable.  The argument
;;; guard is the weakest hypothesis that serves both, and every caller can meet
;;; it -- a FUN-typed sequence by fun-apply-type-c, a pointwise-real one directly.
;;;
;;; There are 32 call sites across a dozen files, and each needs both facts in
;;; context BEFORE the rewrite.  By hand that is six lines a site; this is one.
;;;
;;; WHAT IT DOES NOT DO: invent a sequence's realness.  A TRANSFER sequence
;;; constrained only by a pointwise equation (h(k) = f(k) + g(k)) has no realness
;;; hypothesis of its own, and the caller must establish it first -- dk-have!
;;; with a lane that instantiates the equation and closes from the sequences that
;;; do carry realness.  What this does is find whatever IS available -- a
;;; pointwise universal in context, a FUN membership, or the ptwise theorem --
;;; and turn it into the two instances the guard asks for.

;;; A context universal saying SEQ is pointwise real, or #f.  The index class is
;;; not constrained: NN for an ordinary sequence, ZZ for the Bernstein families.
(define (dk--ptwise-real-in-ctx seq)
  (any-pred
   (lambda (f)
     (and (pair? f) (eq? (car f) 'FORALL)
          (let ((body (caddr f)))
            (and (pair? body) (eq? (car body) 'IMPLIES)
                 (let ((c (caddr body)))
                   (and (pair? c) (eq? (car c) 'IN) (eq? (caddr c) 'RR)
                        (pair? (cadr c)) (equal? (car (cadr c)) seq)))))))
   (dk-asms)))

(define (dk--known? name)
  (and (hash-table-ref/default *theorem-table* name #f) #t))

;;; Land (IN T RR) unless it is already there.  LANE is run only when needed.
(define (dk--ensure-real! t lane)
  (if (not (dk-asm? (list 'IN t 'RR))) (quietly lane)))

(define (dk-sps-succ! seq idx)
  (let* ((sps (list 'SERIES-PARTIAL-SUM seq idx))
         (val (list seq idx)))
    ;; (1) the partial sum at idx is real
    (dk--ensure-real! sps
      (lambda ()
        (cond ((dk--known? 'series-partial-sum-in-rr-ptwise)
               (fact 'series-partial-sum-in-rr-ptwise idx seq))
              ((dk--known? 'series-partial-sum-in-rr)
               (fact 'series-partial-sum-in-rr idx seq))
              (else #f))))
    ;; (2) the term at idx is real
    (dk--ensure-real! val
      (lambda ()
        (let ((pw (dk--ptwise-real-in-ctx seq)))
          (if pw
              (inst+ pw idx)
              (fact 'fun-apply-type-c seq 'NN 'RR idx)))))
    ;; (3) fire the recurrence and rewrite the goal with it
    (fact 'series-partial-sum-succ seq idx)
    (subst (list '== (list 'SERIES-PARTIAL-SUM seq (list 'succ idx))
                     (list '+ sps val)))))
