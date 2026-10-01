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
             (dk-focus! (car ls)))
            (else (loop (cdr ls)))))))
(define (dc-grind!) (let loop ((g 0)) (quietly (lambda () (ass-all)))
  (let ((al (any-pred (lambda (s) (let ((gg (wff-formula (sequent-node-assertion s))))
              (and (not (sequent-node-grounded? s)) (pair? gg) (eq? (car gg) 'AND)))) (proof-leaves))))
    (when (and al (< g 40)) (dk-focus! al) (di) (loop (+ g 1))))))
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
             (dk-focus! (car ls)))
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
           (dk-focus! (car ls)))
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
;;;
;;; CAPTURE THE FORMULA WHEN IT LANDS, AND CITE BEFORE YOU DESTROY (the rule,
;;; not a helper -- batch 12-D and 12-B each lost a run to it, and batch 13-D
;;; decided it is not code).  Two halves, one habit:
;;;
;;;   * KEEP WHAT A CITATION RETURNS.  `dk-fact!' / `dk-apply!' / `inst*!' hand
;;;     back the context's OWN term -- eigenvariables, binder names and all.
;;;     Going back for it later by SHAPE is the failure this kit exists to
;;;     prevent: an eps-universal is re-found by matching `(FORALL ... POS-RR
;;;     ...)', the context holds four of them, and the wrong one is instantiated
;;;     silently.  Bind it:  (let ((univ (dk-fact! 'thm ...))) ... (dk-apply!
;;;     univ eps) ...).  A formula the driver REBUILDS matches nothing.
;;;   * CITE EVERYTHING YOU WILL WANT FROM A HYPOTHESIS BEFORE YOU OPEN IT.
;;;     `mac-h', `slot-h', `ai', `sep-me', `dk-split!' and `dk-skolem!' REPLACE
;;;     the formula they open, and what they consumed is gone from that branch.
;;;     Either cite first, or open it inside a LANE, where the consumption is
;;;     confined to the side branch -- which is what `dk-project!' below is.

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
    ;; 2026-09-15: a node that is NOT an open leaf used to be focused SILENTLY and
    ;; UNRECORDED -- four of the five page-audit failures (zz-bezout, makeset2-split,
    ;; the two exemplifications) were driver loops focusing a snapshot element that
    ;; in-rr's trailing ass-all had already grounded.  Now: an ungrounded non-leaf is
    ;; recorded as `focus-id' (its node number reproduces); a GROUNDED node is
    ;; refused with a warning and focus is left where it was, so the page and the
    ;; live run cannot disagree about it.
    (cond (k
           (let ((mark (vnb--take-mark (list 'focus k))))
             (set-proof-state-focus! *ps* node)
             (vnb--undo-push! mark) (record-cmd! 'focus (list k))))
          ((sequent-node-grounded? node)
           (display ";VNB warning: dk-focus!: node ") (write (sequent-node-number node))
           (display " is already GROUNDED -- focus not moved (a stale leaf snapshot?)")
           (newline))
          (else
           (let ((n (sequent-node-number node)))
             (let ((mark (vnb--take-mark (list 'focus-id n))))
               (set-proof-state-focus! *ps* node)
               (vnb--undo-push! mark) (record-cmd! 'focus-id (list n))))))
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

;; the deepest of a list of landed formulas: the one no other sits inside.
(define (dk--deepest-of new)
  (or (find-first (lambda (a)
                    (not (find-first (lambda (b) (and (not (eq? a b)) (dk-contains? a b))) new)))
                  new)
      (car new)))

(define (dk-deepest thunk) (dk--deepest-of (dk-landed thunk)))

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
;;   (IN k C), k a numeral -> ass when the goal is in context, else arith
;;   otherwise  -> ass (the goal is a context assumption up to alpha)
;;
;; THE NUMERAL CASE TRIES `ass' FIRST (2026-09-24, batch 27-B, item 13).  It
;; used to send every (IN <numeral> C) to `arith', which decides membership in
;; the NUMBER classes only: on (IN 1 SET) -- a hypothesis the caller had just
;; landed -- `arith' warned "not a true closed arithmetic sentence" and the goal
;; stayed open, so `have!' then reported the claim as unprovable.  A goal the
;; context holds is closed by `ass' whatever its class.
(define (from-context!)
  (let ((g (dk-goal)))
    (cond
      ((and (pair? g) (eq? (car g) 'AND))
       (for-each (lambda (k) (dk-focus! k) (from-context!)) (dk-opened (lambda () (di)))))
      ((and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'NN)
            (pair? (cadr g)) (eq? (car (cadr g)) '*))
       ;; nn-mul-closed's antecedent is a CONJUNCTION, which `fact' will not
       ;; split: without the have! it lands the implication and the `ass' misses
       ;; (found 2026-09-17, zz-division).
       (let ((x (cadr (cadr g))) (y (caddr (cadr g))))
         (dk-have! (list 'AND (list 'IN x 'NN) (list 'IN y 'NN))
                   (lambda () (from-context!)))
         (fact 'nn-mul-closed x y) (ass)))
      ((and (pair? g) (eq? (car g) 'IN) (number? (cadr g)))
       (if (dk-asm? g) (ass) (arith)))
      (else (ass)))))

;; (have! CLAIM)         -- cut CLAIM, prove its side goal with from-context!
;; (have! CLAIM THUNK)   -- ... prove it with THUNK instead
;; Leaves focus on the MAIN branch (CLAIM now a context assumption).  Errors --
;; never silently no-ops -- if CLAIM is already in context up to alpha (the cut
;; self-loops: one child, no main branch).
;;
;; IT TAKES TWO ARGUMENTS AND SAYS SO (2026-09-20, batch 13-D).  It used to
;; accept and IGNORE any further argument, and that is how a driver form closed
;; one paren SHORT reads: the following top-level forms become extra arguments
;; of the `have!' above them, MIT evaluates arguments RIGHT TO LEFT, so the last
;; form of the file runs first and the error surfaces pages from its cause
;; (12-B lost a run to it; CLAUDE.md records the trap).  A scan of all 6697
;; `(have! ' call sites in the tree found none with three arguments and none
;; whose second argument is anything but a thunk, so this rejects both:
;;   * more than two arguments             -- the paren-short shape;
;;   * a second argument that is not a procedure (#f, meaning "no thunk", is
;;     still accepted: `(apply have! form opt)' with an empty lane passes it).
(define (have!--check-args form0 opt)
  (if (pair? opt)
      (begin
        (if (pair? (cdr opt))
            (error (string-append
                    "have!: takes CLAIM and at most one THUNK, but was given "
                    (number->string (+ 1 (length opt)))
                    " arguments -- a driver form closed one paren SHORT swallows"
                    " the following top-level forms as extra arguments of this"
                    " have! (and MIT evaluates them RIGHT TO LEFT)")
                   (expression->string (->raw-formula form0))))
        (if (not (or (procedure? (car opt)) (eq? (car opt) #f)))
            (error (string-append
                    "have!: the second argument must be a THUNK (a procedure),"
                    " not " (if (pair? (car opt)) "a list" "this value")
                    " -- a form closed one paren short lands its VALUE here")
                   (car opt))))))

(define (have! form0 . opt)
  (have!--check-args form0 opt)
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

;;; A DISJUNCTIVE P IS REFUSED (2026-09-24, batch 27-B, item 13).  The split
;;; goes through `use-cases', which FLATTENS nested ORs: on P = (OR A B) the
;;; disjunction (OR P (NOT P)) comes back as THREE cases, A, B and NOT P.  The
;;; two bodies were then paired with the first two by `for-each', which stops
;;; at the shorter list: BODY-FALSE ran on the B branch and the NOT-P branch
;;; was dropped without a word.  Split a disjunction with `use-cases' and one
;;; body per disjunct instead.
(define (use-em--on P0 . bodies)
  (let* ((P      (use-cases--raw P0))        ; raw / string / wff, like use-cases
         (ignore0 (if (and (pair? P) (memq (car P) '(OR or)))
                      (error (string-append
                              "use-em: the proposition is a DISJUNCTION, and use-cases"
                              " would flatten (OR P (NOT P)) into its disjuncts plus NOT P --"
                              " the bodies would run on the wrong branches.  Use"
                              " (use-cases (list A B (list 'NOT P)) ...) instead")
                             (expression->string P))))
         (dec    (use-em--decided P))
         (ignore (if dec (use-em--decided-error P dec)))
         (result (use-cases (list P (list 'NOT P))))
         (oblig  (cases-obligation result))
         (cases  (cdr (assq 'cases result))))
    (if oblig (begin (dk-focus! oblig) (em-prove!)))
    (cond ((null? bodies) result)
          ((not (= (length bodies) 2))
           (error "use-em: expected 2 bodies (P, NOT P), got" (length bodies)))
          ((not (= (length cases) 2))
           (error "use-em: the split produced" (length cases) "cases, not 2"))
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
;; posts, and the domain one is rebuilt here from the SEP, not guessed.
;; (in-sep! B-PROP) -- the same, with the domain subgoal closed by from-context!.
;;
;; EITHER SUBGOAL MAY COME BACK ALREADY DISCHARGED.  Sequent nodes are
;; hash-consed on assertion-up-to-alpha PLUS context, so when the domain
;; membership was proved earlier under this same context -- the ordinary case,
;; since the caller usually has (IN t A) in hand -- `sep-mi' posts a node that is
;; already GROUNDED, and only ONE new leaf comes back.  This used to error "no
;; domain subgoal", reporting the obligation's discharge as a failure, and 7-J
;; wrote a tolerant copy (r8j-in-sep!, rake-seq-compact-tb.scm) rather than fix
;; it.  Never infer success or failure from how many leaves a rule opens
;; (dk-have! carries the same note).  When a subgoal IS missing, the node this
;; was called on must be GROUNDED by the time the bodies have run, and that is
;; checked: a leaf that went missing because it is an open leaf someone else
;; holds would otherwise be left behind silently.
(define (in-sep! b-dom . opt)
  (let ((g    (dk-goal))
        (home (proof-state-focus *ps*)))
    (if (not (and (pair? g) (eq? (car g) 'IN)
                  (pair? (caddr g)) (eq? (car (caddr g)) 'SEP)))
        (error "in-sep!: goal is not (IN t (SEP x A p))" g))
    (let* ((one?   (null? opt))
           (b-prop (if one? b-dom (car opt)))
           (b-dom  (if one? from-context! b-dom))
           (t   (cadr g))
           (dom `(IN ,t ,(caddr (caddr g))))
           (ls  (dk-opened (lambda () (sep-mi))))
           (ld  (any-pred (lambda (l) (alpha-equiv? (dk-goal-of l) dom)) ls))
           (lp  (any-pred (lambda (l) (not (eq? l ld))) ls)))
      (if ld (begin (dk-focus! ld) (b-dom)))
      (if lp (begin (dk-focus! lp) (b-prop)))
      (if (and ld lp)
          #t
          (if (sequent-node-grounded? home)
              #t
              (error "in-sep!: sep-mi left the membership open and posted no leaf for"
                     (expression->string (if ld (cadddr (caddr g)) dom))))))))

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
;; choice-axiom (library.scm) is GLOBAL choice -- S may be a proper class -- so
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

;;; `ineq' WITHOUT POSITIONAL INDICES.  Its arguments are 1-based positions in
;;; the CURRENT assumption list, so a driver that writes `(ineq 1 2)' is right
;;; only for the context its author happened to have.  When it is wrong the
;;; oracle does not say "no such premise" -- it reports "goal not a linear-RR
;;; consequence", blaming the GOAL -- and inside `quietly' that is silent: the
;;; proof stalls, `qed' aborts the load, and whoever loads the script is left
;;; standing on a leaf with no explanation.  (Cost the user three rounds of
;;; chasing the wrong thing, 2026-09-08/09.)
;;;
;;; `ineq!' hands over the premises `eps-chain' already vets -- the order facts
;;; whose atoms the oracle can certify in RR.  That filter is the point: passing
;;; EVERY order assumption is what made the eps engine fail for months, because
;;; one NN-typed threshold `cap <= n_' poisons the whole call (see the block
;;; above).  Reuse it; do not write a second, weaker selector.
(define (ineq!)
  (let ((ps (eps-chain--order-premises)))
    (if (null? ps)
        (error "ineq!: no usable order premise in context")
        (apply ineq ps))))

;;; The same, when the premises matter and you want to name them: by FORMULA,
;;; resolved to indices at call time, ERRORING on one that is not there.
;;;
;;; FIVE rake files rebuilt this in one week (rhb-ineq!, r8d-ineq!, r8h-ineq,
;;; r8j-ineq, sd-ineq), which is what a procedure under a name nobody looks for
;;; costs: it has been here since 2026-09-08 as `ineq-on!', outside the `dk-'
;;; namespace every driver greps.  `dk-ineq!' is the name; `ineq-on!' stays as
;;; an alias for the files that already call it.  Two things the copies wanted
;;; and it did not have: a premise may be given as a string or a <wff> (it is
;;; coerced), and one that matches only up to bound-variable renaming is
;;; accepted -- though an EXACT match anywhere in the context wins, so the index
;;; is the one the caller meant.  The error names the premise in surface syntax.
(define (dk--premise-index f who)
  (let loop ((as (dk-asms)) (i 1) (alpha #f))
    (cond ((null? as)
           (or alpha
               (error (string-append who ": premise not in context --")
                      (expression->string f))))
          ((equal? (car as) f) i)
          ((and (not alpha)
                (eq? #t (vnb-guard (lambda () (alpha-equiv? (car as) f)))))
           (loop (cdr as) (+ i 1) i))
          (else (loop (cdr as) (+ i 1) alpha)))))

;;; WITH NO PREMISE IT IS BARE `(ineq)' (2026-09-20, batch 13-D).  It used to
;;; ERROR -- "no premise named (bare (ineq) passes ZERO premises)" -- which is
;;; true of `ineq' and no reason to refuse: the zero-premise call is the honest
;;; way to ask the oracle to close a goal that needs no hypothesis at all
;;; (0 <= abs(x), 1 <= 1 + 1), and a driver that has switched to `dk-ineq!'
;;; should not have to switch back for it (12-G met this).
(define (dk-ineq! . formulas)
  (if (null? formulas)
      (ineq)
      (apply ineq (map (lambda (f) (dk--premise-index (->raw-formula f) "dk-ineq!"))
                       formulas))))

(define (ineq-on! . formulas) (apply dk-ineq! formulas))


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

;;; -----------------------------------------------------------------------
;;; THE PEEL / SPLIT / PICK KIT -- the helpers every driver had been copying.
;;;
;;; Measured 2026-09-14, the day three COMP-induction drivers landed with the
;;; same seven procedures under three prefixes (csn-, nfb-, mcb-): the tree
;;; then held ~90 `<prefix>-peel!', ~40 `<prefix>-skolem!', ~10 `<prefix>-di-var!'
;;; and a dozen conjunction-splitters, verbatim or nearly.  These are the shared
;;; ones.  Every one ERRORS on a miss -- a helper that returns #f and leaves
;;; focus put hides the bug for weeks (CLAUDE.md, "Writing proof drivers").

;;; (dk-peel!) -- `di' while the goal's head is FORALL or IMPLIES; return every
;;; assumption the peeling landed (may be empty: an unguarded universal lands
;;; nothing).  Stops at AND (which `di' would SPLIT) and at NOT (which it would
;;; assume).  Loops on PROGRESS, never on a count: `di' is greedy over a guarded
;;; binder list and stops at the next binder, so counting is wrong both ways.
;;; A `di' that leaves the goal unchanged (it only warns) is an error here.
(define (dk-peel!)
  (dk-landed*
   (lambda ()
     (let loop ()
       (let ((g (dk-goal)))
         (if (and (pair? g) (memq (car g) '(FORALL IMPLIES)))
             (begin
               (di)
               (if (equal? (dk-goal) g)
                   (error "dk-peel!: di made no progress on" (expression->string g)))
               (loop))))))))

;;; (dk-split-all!)         -- `ai' every conjunction in the CONTEXT to exhaustion.
;;; (dk-split-all! LANDED)  -- split only the conjunctions among LANDED (a list
;;;                            of context formulas, e.g. what dk-peel! returned).
;;; Returns the atoms produced.  The context form tolerates a duplicate
;;; conjunction (contexts hold duplicates, and `ai' of the second copy lands
;;; nothing new) but errors if `ai' leaves the conjunction standing.
(define (dk--count-equal f lst)
  (let loop ((l lst) (n 0))
    (cond ((null? l) n)
          ((equal? (car l) f) (loop (cdr l) (+ n 1)))
          (else (loop (cdr l) n)))))
(define (dk-split-all! . opt)
  (if (pair? opt)
      (let loop ((fs (car opt)) (acc '()))
        (cond ((null? fs) (reverse acc))
              ((and (pair? (car fs)) (eq? (caar fs) 'AND))
               (loop (cdr fs) (append (reverse (dk-split! (car fs))) acc)))
              (else (loop (cdr fs) acc))))
      (let loop ((acc '()))
        (let ((a (find-first (dk-head? 'AND) (dk-asms))))
          (if (not a)
              (reverse acc)
              (let* ((before (dk--count-equal a (dk-asms)))
                     (new    (dk-landed* (lambda () (ai a)))))
                (if (>= (dk--count-equal a (dk-asms)) before)
                    (error "dk-split-all!: ai left the conjunction in place"
                           (expression->string a)))
                (loop (append (reverse (filter (lambda (f) (not ((dk-head? 'AND) f))) new))
                              acc))))))))

;;; (dk-pick PRED WHAT) -- the first context assumption satisfying PRED; WHAT is
;;; the English name of what you were looking for, for the error.  Discriminate
;;; on a CONSEQUENT or on a context formula unique to the branch, never on a
;;; head alone (sibling branches share heads).
(define (dk-pick pred what)
  (let ((fs (filter pred (dk-asms))))
    (if (null? fs) (error "dk-pick: nothing matching" what) (car fs))))

;;; (dk-only! F1 F2 ...) -- drop every assumption but the ones named.  `prop'
;;; has an atom cap (*prop-atom-cap*, 12; the search is 2^n) and `fact' lands
;;; its whole instantiation chain, so a two-line forward assembly can put a
;;; goal over the cap on its own.  Compared up to alpha (`keep--kept?'), but pass
;;; the context's own formulas (what dk-fact! / inst*! returned) anyway.
;;;
;;; Since 2026-09-23 this is the surface command `keep' (interactive.scm): ONE
;;; recorded step, where it used to record one `wk' per dropped assumption, and
;;; the weakening stays on the focus leaf (it used to drift to a sibling when a
;;; weakened sequent was hash-consed onto a grounded node, and go on weakening
;;; THERE).  Nothing to drop: no step, no inert notice (a driver's `dk-only!' on
;;; an already-small context is not a dead step the user took).  ERRORS when the
;;; `keep' failed; returns #t when the leaf is still open with only the keepers,
;;; #f when the kept sequent was already proven and the leaf is closed -- the
;;; focus is then on another leaf, so a driver that goes on must re-focus.
(define (dk-only! . keepers)
  (let ((leaf (proof-state-focus *ps*)))
    (if (not (any (lambda (f) (not (keep--kept? f keepers))) (dk-asms)))
        #t
        (begin
          (apply keep keepers)
          (cond ((sequent-node-grounded? leaf) #f)
                ((and (not (eq? (proof-state-focus *ps*) leaf))
                      (not (any (lambda (f) (not (keep--kept? f keepers))) (dk-asms))))
                 #t)
                (else (error "dk-only!: keep failed on node"
                             (sequent-node-number leaf))))))))

;;; (dk-apply! F T1 ...) -- instantiate the in-context universal F at T1 ...,
;;; then detach its guards TO EXHAUSTION, erroring if one is not in context;
;;; return what finally landed.  `inst*!' detaches only the guards ALREADY in
;;; context and stops at the first it cannot, handing back the implication.
;;;
;;; DO NOT wrap `inst*!' (or `inst+', `fact') in `dk-landed-1': each lands its
;;; whole instantiation chain -- the universal at the term, each partly-peeled
;;; form, the detached result -- so the thunk lands several formulas and
;;; dk-landed-1 errors "expected 1".  That is why the `dk-landed-1' here sits
;;; around the `detach!' alone (found 2026-09-14 by the card-subset-nn driver).
(define (dk-apply! f . terms)
  (let loop ((r (apply inst*! f terms)))
    (if (and (pair? r) (eq? (car r) 'IMPLIES))
        (loop (dk-landed-1 (lambda () (detach! r))))
        r)))

;;; (dk-di-var!)             -- `di' one GUARDED binder; return its eigenvariable,
;;;                             read off the landed typing (IN v A).
;;; (dk-di-var! GOAL-VAR-OF) -- `di' one binder (guarded or not); return the
;;;                             eigenvariable GOAL-VAR-OF reads off the NEW goal.
;;; Never guess the name from the binder: `di' renames when the name is taken.
;;; Both forms error when nothing new appeared.
(define (dk-di-var! . opt)
  (if (pair? opt)
      (let ((before (free-vars (dk-goal))))
        (di)
        (let ((v ((car opt) (dk-goal))))
          (if (or (not (symbol? v)) (memq v before))
              (error "dk-di-var!: no new eigenvariable in" (expression->string (dk-goal))))
          v))
      (let* ((landed (dk-landed (lambda () (di))))
             (f (car landed)))
        (if (and (pair? f) (eq? (car f) 'IN) (symbol? (cadr f)))
            (cadr f)
            (error "dk-di-var!: di landed no typing (IN v A); landed"
                   (map expression->string landed))))))

;;; (dk-conj-close! [CLOSER]) -- split a conjunctive GOAL to its leaves (a
;;; right-nested AND tower goes all the way down) and run CLOSER, a thunk, with
;;; focus on each leaf.  Default CLOSER is `from-context!'.  This is the one
;;; helper behind rob-close-and!, prl-split-and!, mcb-conj-close! and the
;;; `(for-each ... (dk-opened (lambda () (di))))' loop every `ew' used to be
;;; followed by.  Focus is left on the last leaf CLOSER ran on.
(define (dk-conj-close! . opt)
  (let ((closer (if (pair? opt) (car opt) from-context!)))
    (let walk ()
      (let ((g (dk-goal)))
        (if (and (pair? g) (eq? (car g) 'AND))
            (for-each (lambda (k) (dk-focus! k) (walk))
                      (dk-opened (lambda () (di))))
            (closer))))))

;;; (dk-skolem! EX) -- skolemize the FORSOME EX that is ALREADY IN THE CONTEXT
;;; (`obtain' cannot see one: it diffs around its own lane).  `ai' it, split
;;; whatever conjunction landed, and return the eigenvariable, read off by
;;; free-variable set difference -- never guessed from the binder.  Errors if
;;; nothing fresh appeared, or if more than one variable did (nested FORSOMEs:
;;; call it once per binder).
;;;
;;; (dk-skolem! EX SPLIT) -- SPLIT says how far to split what landed (2026-09-24,
;;; batch 27-B, item 13): #t, the default, splits every conjunction to its
;;; leaves (the recursive `dk-split!', as before); 'TOP splits only the one
;;; conjunction `ai' landed, so a CONJUNCTIVE GUARD inside it -- (AND (P x)
;;; (Q x)), the antecedent a later `detach!' wants whole, since `fact' will not
;;; rebuild a conjunction -- survives; #f splits nothing.
(define (dk-skolem! ex . opt)
  ;; A CONJUNCTION whose one conjunct is the existential (2026-09-30: the repaired
  ;; `image-membership-iff' lands `w in SET and forsome x in S. phi(x) = w'): split
  ;; it, keep the other conjuncts in context, skolemise the existential.
  (if (and (pair? ex) (eq? (car ex) 'AND))
      (let* ((parts (dk-split! ex))
             (exs   (filter (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) parts)))
        (cond ((null? exs) (error "dk-skolem!: no existential among the conjuncts of" (expression->string ex)))
              ((pair? (cdr exs)) (error "dk-skolem!: more than one existential among the conjuncts of" (expression->string ex)))
              (else (apply dk-skolem! (car exs) opt))))
      (dk-skolem--one! ex opt)))

(define (dk-skolem--one! ex opt)
  (let* ((split  (if (pair? opt) (car opt) #t))
         (fvs    (lambda ()
                   (let loop ((as (dk-asms)) (acc '()))
                     (if (null? as) acc (loop (cdr as) (append (free-vars (car as)) acc))))))
         (fv0    (fvs))
         (landed (dk-landed (lambda () (ai ex)))))
    (for-each (lambda (f)
                (if (and (pair? f) (eq? (car f) 'AND))
                    (cond ((eq? split #t) (dk-split! f))
                          ((eq? split 'top) (dk-landed (lambda () (ai f))))
                          ((eq? split #f) #f)
                          (#t (error "dk-skolem!: SPLIT is #t, 'top or #f, not" split)))))
              landed)
    (let ((fresh (delete-duplicates (filter (lambda (v) (not (memq v fv0))) (fvs)))))
      (cond ((null? fresh) (error "dk-skolem!: no eigenvariable appeared for" (expression->string ex)))
            ((pair? (cdr fresh)) (error "dk-skolem!: more than one fresh variable" fresh))
            (else (car fresh))))))

;;; (dk-halve! EPS) -- "let d = eps/2".  Requires (POS-RR EPS) in context.
;;; Cites rr-pos-halvable (theorem-library/rr-halving) at EPS, skolemizes the
;;; existential and lands, split and in the context,
;;;
;;;     (POS-RR d)   (= (+ d d) EPS)   (IN d RR)   (< 0 d)
;;;
;;; returning d.  The typing and the strict inequality come by CITATION
;;; (rr-pos-rr-in-rr, rr-lt-of-pos-rr -- theorem-library/pos-rr-bridges), not
;;; by unfolding: `mac-h' REPLACES the assumption it unfolds, and (POS-RR d) is
;;; what the caller's next `inst+' of an eps-universal detaches against.  Every
;;; consumer of rr-pos-halvable had rebuilt this by hand -- skolemize, split,
;;; `mac-h pos-rr', split again, `(mac '<) (from-context!)' -- and several had
;;; met the destruction trap (cont-agree-off-pt.scm's comment records it).
;;; A file using this must load after pos-rr-bridges (right after
;;; rr-order-basics in load.scm), which rr-halving's own citers all do.
(define (dk-halve! eps)
  (let ((hex (dk-fact! 'rr-pos-halvable eps)))
    (if (not (and (pair? hex) (eq? (car hex) 'FORSOME)))
        (error "dk-halve!: rr-pos-halvable did not detach -- is (POS-RR eps) in context?  landed"
               (expression->string hex)))
    (let ((d (dk-skolem! hex)))
      (let ((ty (dk-fact! 'rr-pos-rr-in-rr d))
            (lt (dk-fact! 'rr-lt-of-pos-rr d)))
        (if (not (equal? ty (list 'IN d 'RR)))
            (error "dk-halve!: rr-pos-rr-in-rr did not detach; landed" (expression->string ty)))
        (if (not (equal? lt (list '< 0 d)))
            (error "dk-halve!: rr-lt-of-pos-rr did not detach; landed" (expression->string lt))))
      d)))

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
                  (dk-focus! l)
                  (dk-set-close! (cadr (dk-goal-of l))))
                sets)
      (if (pair? typ)
          (dk-focus! (car typ))
          (error "dk-lam-t!: lam-t left no typing goal")))))

;;; -----------------------------------------------------------------------
;;; dk-lam-fun! -- prove a lambda FUN-typing goal by the forward typing chain.
;;;
;;;     focus goal:  (IN (VNB-LAMBDA b A body) (FUN A B))
;;;
;;; Contract.  Applies `lam-t' (which opens the pointwise typing and the sethood
;;; of A), closes the sethood leaf (interval-in-set / cartesian-set-iff / the
;;; numeric sets), peels the pointwise universal, and closes the resulting
;;; (IN body' B) by `dk-typ-close!' -- a forward saturation keyed on the HEAD of
;;; the term: ENTRY -> entry-in-carrier, (MUL r) -> ring-carrier-closed-mul,
;;; (ACT md) -> module-act-type, (OPR (MODULE-VECTOR-AG md)) -> mvag-op +
;;; module-vadd-type, FINSUM -> finsum-type (typing the summand by a recursive
;;; dk-lam-fun!), LIST -> pair-in-cartesian, NTH of a CARTESIAN member ->
;;; cartesian-nth, an applied VNB-LAMBDA -> lam-b after typing its argument, and
;;; a numeric codomain -> in-rr.  A class mismatch between what the chain lands
;;; and what the goal names is bridged by ras-carr / mvag-carr.
;;;
;;; ERRORS, never no-ops: every branch checks the leaf it was handed is GROUNDED
;;; before returning, and an unknown head names itself in the error.  Every
;;; move is a surface tactic or dk-focus!, so the recorded script replays.
;;;
;;; 2026-09-14: built for the 28 "lambda FUN-typing bricks" of the matrix arc
;;; (matprod-summand-type, the te-typ / ms-typ families, mra/mrs), which were
;;; asserted one at a time with warrants reciting exactly this chain.

(define (dk-lam-fun--node) (proof-state-focus *ps*))

(define (dk-lam-fun--grounded! node who what)
  (if (not (sequent-node-grounded? node))
      (error (string-append who ": leaf not closed --") what)))

;;; (ass) that ERRORS if the leaf stays open.
(define (dk-typ--ass! who)
  (let ((node (dk-lam-fun--node)) (g (dk-goal)))
    (quietly (lambda () (ass)))
    (dk-lam-fun--grounded! node who (expression->string g))))

;;; The context assumption (IN t X) for this exact t, or #f.
(define (dk-typ--asm-class t)
  (let ((a (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (cadr a) t)))
                       (dk-asms))))
    (and a (caddr a))))

;;; Does the context type P as a matrix?  Returns (m n X) or #f.
(define (dk-typ--mat-of P)
  (let ((a (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN) (equal? (cadr a) P)
                                        (pair? (caddr a)) (eq? (car (caddr a)) 'MAT)))
                       (dk-asms))))
    (and a (cdr (caddr a)))))

;;; The product guard matmul-type / matact-type carry since 2026-09-16:
;;; (IMPLIES (= N 0) (OR (= M 0) (= K 0))).  Land it when the context makes it
;;; cheap -- already there; a repeated dimension (N is M or K), by `prop'; or
;;; (<= 1 N) in context, via dk-nonzero! then `prop'.  Returns #f otherwise.
(define (dk-typ--product-guard! m n k)
  (let ((g (list 'IMPLIES (list '= n 0) (list 'OR (list '= m 0) (list '= k 0)))))
    (cond ((dk-asm? g) #t)
          ((or (equal? n m) (equal? n k))
           (quietly (lambda () (dk-have-prop! g))) #t)
          ((dk-asm? (list '<= 1 n))
           (if (not (dk-asm? (list 'NOT (list '= n 0)))) (quietly (lambda () (dk-nonzero! n))))
           (quietly (lambda () (dk-have-prop! g))) #t)
          (else #f))))

;;; -----------------------------------------------------------------------
;;; THE MATRIX TYPING CHAIN.
;;;
;;; Ensure (IN P (MAT m n X)) is in context and return (m n X).  A matrix
;;; EXPRESSION is typed by its constructor's typing theorem, after its matrix
;;; operands have been typed by the same chain: MATMUL -> matmul-type,
;;; MATACT -> matact-type, MATUNIT -> matunit-type, and (2026-09-18, for the
;;; owed-leaf hook) the other fourteen MATOF constructors --
;;;
;;;   (IDENTMAT a n)        identmat-type   a n            -> MAT n n (CARR a)
;;;   (ZEROMAT a m n)       zeromat-type    a m n          -> MAT m n (CARR a)
;;;   (UNITROW a n i)       unitrow-type    a n i          -> MAT 1 n (CARR a)
;;;   (ELEM-F a n k l)      elem-f-type     a n k l        -> MAT n n (CARR a)
;;;   (ELEM-G a n r k l)    elem-g-type     a n r k l      -> MAT n n (CARR a)
;;;   (ELEM-H a n r k)      elem-h-type     a n r k        -> MAT n n (CARR a)
;;;   (MATADD a p q)        matadd-type     a m n p q      -> MAT m n (CARR a)
;;;   (MATSCALE a r p)      matscale-type   a m n r p      -> MAT m n (CARR a)
;;;   (MATNEG a p)          matneg-type     a m n p        -> MAT m n (CARR a)
;;;   (BLOCK p k l)         block-type      m n cls p k l  -> MAT k l cls
;;;   (BORDER a b mm p q)   border-type     a b mm p q     -> MAT (succ p) (succ q) (CARR a)
;;;   (SUBMAT s p q)        submat-type     a p q s        -> MAT p q (CARR a)
;;;   (SNOC-COL w n v)      snoc-col-type   cls n w v      -> MAT (succ n) 1 cls
;;;   (SNOC-ROW c n r)      snoc-row-type   cls n c r      -> MAT 1 (succ n) cls
;;;
;;; The DIMENSIONS and the ELEMENT CLASS are read off the term where the
;;; constructor carries them (ZEROMAT, SUBMAT, SNOC-*) and off the MAT typing
;;; of the matrix ARGUMENT otherwise (MATADD, BLOCK, ...), recursively through
;;; this same procedure -- which is how MATMUL has always worked.  Where the
;;; theorem's premise spells a dimension or a class (submat-type wants
;;; (MAT (succ p) (succ q) (CARR a)); matadd-type wants both operands at the
;;; SAME (m, n, CARR a)) the landed typing is CHECKED against it.
;;;
;;; EVERY BRANCH ERRORS, never returns #f, when a premise it needs is not in
;;; context, and it errors BEFORE citing anything -- the owed-leaf hook runs
;;; the chain inside `vnb-guard', so an error simply leaves the owed leaf open,
;;; and checking first keeps a half-run branch from stranding a cut leaf that
;;; nothing can close.

;;; A matrix in context whose ROW count is B (dk-typ--dim-in-nn!'s own search,
;;; as a predicate, so a caller can error before citing anything).
(define (dk-typ--rowcount-mat b)
  (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                               (pair? (caddr a)) (eq? (car (caddr a)) 'MAT)
                               (equal? (cadr (caddr a)) b)))
              (dk-asms)))

(define (dk-typ--fail who msg)
  (error (string-append "dk-typ-close!: " who " -- " msg)))

(define (dk-typ--assert! ok who msg)
  (if (not ok) (dk-typ--fail who msg)))

;;; (IN b NN), from the context, from b being a numeral, or off a matrix in
;;; context whose row count it is.  Errors otherwise.
(define (dk-typ--need-nn! b who)
  (dk-typ--assert! (or (dk-asm? (list 'IN b 'NN)) (number? b) (dk-typ--rowcount-mat b))
                   who (string-append "no (IN " (expression->string b) " NN) in context"))
  (dk-typ--dim-in-nn! b))

;;; A context assumption the citation needs verbatim.  Errors if absent.
(define (dk-typ--need! f who)
  (dk-typ--assert! (dk-asm? f) who
                   (string-append "not in context: " (expression->string f)))
  #t)

;;; (<= a b): in context, or reflexivity, or ground arithmetic.  Errors otherwise.
(define (dk-typ--need-le! a b who)
  (cond ((dk-asm? (list '<= a b)) #t)
        ((and (equal? a b) (dk-asm? (list 'IN a 'NN)))
         (quietly (lambda () (fact 'nn-le-refl a))))
        ((and (number? a) (number? b) (<= a b))
         (dk-have! (list '<= a b) (lambda () (arith))))
        (#t (dk-typ--fail who (string-append "not in context: "
                                             (expression->string (list '<= a b)))))))

;;; (CARR a) -> a, else #f.
(define (dk-typ--carr-of cls)
  (and (pair? cls) (eq? (car cls) 'CARR) (= (length cls) 2) (cadr cls)))

;;; Type a matrix ARGUMENT by the chain and CHECK the typing against what the
;;; citing theorem's premise spells.  ROWS / COLS / CLS are #f where the
;;; theorem leaves them free.  Returns the (m n X) it landed.
(define (dk-typ--mat-at! arg rows cols cls who)
  (let ((mt (dk-typ--mat! arg)))
    (dk-typ--assert!
     (and (or (not rows) (equal? (car mt) rows))
          (or (not cols) (equal? (cadr mt) cols))
          (or (not cls)  (equal? (caddr mt) cls)))
     who (string-append "the typing of " (expression->string arg) " is "
                        (expression->string (cons 'MAT mt)) ", not "
                        (expression->string
                         (list 'MAT (or rows '?) (or cols '?) (or cls '?)))))
    mt))

;;; A ring carrier class, and the ring is one the context knows.  Returns the ring.
(define (dk-typ--ring-of-class! cls who)
  (let ((rng (dk-typ--carr-of cls)))
    (dk-typ--assert! rng who (string-append "the element class "
                                            (expression->string cls)
                                            " is not a ring carrier"))
    rng))

(define (dk-typ--mat! P)
  (or (dk-typ--mat-of P)
      (begin
        (if (not (pair? P))
            ;; a VARIABLE: the one indirect typing the library states is
            ;; IS-INVERTIBLE-MAT a n P  =>  P in MAT n n (CARR a)  (2026-09-18)
            (let ((inv (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IS-INVERTIBLE-MAT)
                                                    (= (length f) 4) (equal? (cadddr f) P)))
                                   (dk-asms))))
              (if inv
                  (quietly (lambda () (fact 'invertible-mat-is-mat (cadr inv) (caddr inv) P)))
                  (error "dk-typ-close!: no MAT typing in context for" (expression->string P)))))
        (let ((as (cdr P)) (arity (- (length P) 1)))
          (cond
            ;; ---- the two products and the unit matrix (2026-09-14) ----------
            ((and (eq? (car P) 'MATUNIT) (= arity 4))   ; (MATUNIT a n k l)
             (dk-typ--ring! (car as))
             (if (not (dk-asm? (list 'IN (cadr as) 'NN)))
                 (error "dk-typ-close!: matunit-type needs (IN n NN) in context, for n ="
                        (expression->string (cadr as))))
             (quietly (lambda () (apply fact 'matunit-type as))))
            ((and (eq? (car P) 'MATMUL) (= arity 3))    ; (MATMUL a p q)
             (let* ((rg (car as)) (m1 (dk-typ--mat! (cadr as))) (m2 (dk-typ--mat! (caddr as))))
               (dk-typ--ring! rg)
               (if (not (dk-typ--product-guard! (car m1) (cadr m1) (cadr m2)))
                   (error "dk-typ-close!: matmul-type's guard (n = 0 => m = 0 or k = 0) is not in context and not cheap, for"
                          (expression->string P)))
               (quietly (lambda () (fact 'matmul-type rg (car m1) (cadr m1) (cadr m2)
                                         (cadr as) (caddr as))))))
            ((and (eq? (car P) 'MATACT) (= arity 3))    ; (MATACT md p u)
             (let* ((md (car as)) (m1 (dk-typ--mat! (cadr as))) (m2 (dk-typ--mat! (caddr as))))
               (if (not (dk-asm? (list 'IS-MODULE md)))
                   (error "dk-typ-close!: no IS-MODULE in context for" (expression->string md)))
               (if (not (dk-typ--product-guard! (car m1) (cadr m1) (cadr m2)))
                   (error "dk-typ-close!: matact-type's guard (n = 0 => m = 0 or q = 0) is not in context and not cheap, for"
                          (expression->string P)))
               (quietly (lambda () (fact 'matact-type md (car m1) (cadr m1) (cadr m2)
                                         (cadr as) (caddr as))))))

            ;; ---- the constant matrices (2026-09-18) ------------------------
            ;; (IDENTMAT a n) : MAT n n (CARR a)
            ((and (eq? (car P) 'IDENTMAT) (= arity 2))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "identmat-type")
             (quietly (lambda () (fact 'identmat-type (car as) (cadr as)))))
            ;; (ZEROMAT a m n) : MAT m n (CARR a)
            ((and (eq? (car P) 'ZEROMAT) (= arity 3))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "zeromat-type")
             (dk-typ--need-nn! (caddr as) "zeromat-type")
             (quietly (lambda () (apply fact 'zeromat-type as))))
            ;; (UNITROW a n i) : MAT 1 n (CARR a)
            ((and (eq? (car P) 'UNITROW) (= arity 3))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "unitrow-type")
             (quietly (lambda () (apply fact 'unitrow-type as))))

            ;; ---- the three elementary matrices -----------------------------
            ;; (ELEM-F a n k l) : MAT n n (CARR a)   -- the row swap
            ((and (eq? (car P) 'ELEM-F) (= arity 4))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "elem-f-type")
             (quietly (lambda () (apply fact 'elem-f-type as))))
            ;; (ELEM-G a n r k l) : MAT n n (CARR a) -- add r times row l to row k
            ((and (eq? (car P) 'ELEM-G) (= arity 5))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "elem-g-type")
             (dk-typ--need! (list 'IN (caddr as) (list 'CARR (car as))) "elem-g-type")
             (quietly (lambda () (apply fact 'elem-g-type as))))
            ;; (ELEM-H a n r k) : MAT n n (CARR a)   -- scale row k by r
            ((and (eq? (car P) 'ELEM-H) (= arity 4))
             (dk-typ--ring! (car as))
             (dk-typ--need-nn! (cadr as) "elem-h-type")
             (dk-typ--need! (list 'IN (caddr as) (list 'CARR (car as))) "elem-h-type")
             (quietly (lambda () (apply fact 'elem-h-type as))))

            ;; ---- the entrywise operations ---------------------------------
            ;; (MATADD a p q) : both operands at the SAME (m, n, CARR a)
            ((and (eq? (car P) 'MATADD) (= arity 3))
             (let* ((rng (car as))
                    (cls (list 'CARR rng))
                    (m1  (dk-typ--mat-at! (cadr as) #f #f cls "matadd-type")))
               (dk-typ--mat-at! (caddr as) (car m1) (cadr m1) cls "matadd-type")
               (dk-typ--ring! rng)
               (quietly (lambda () (fact 'matadd-type rng (car m1) (cadr m1)
                                         (cadr as) (caddr as))))))
            ;; (MATSCALE a r p) : MAT m n (CARR a), r in CARR a
            ((and (eq? (car P) 'MATSCALE) (= arity 3))
             (let* ((rng (car as))
                    (cls (list 'CARR rng))
                    (m1  (dk-typ--mat-at! (caddr as) #f #f cls "matscale-type")))
               (dk-typ--ring! rng)
               (dk-typ--need! (list 'IN (cadr as) cls) "matscale-type")
               (quietly (lambda () (fact 'matscale-type rng (car m1) (cadr m1)
                                         (cadr as) (caddr as))))))
            ;; (MATNEG a p) : MAT m n (CARR a)
            ((and (eq? (car P) 'MATNEG) (= arity 2))
             (let* ((rng (car as))
                    (cls (list 'CARR rng))
                    (m1  (dk-typ--mat-at! (cadr as) #f #f cls "matneg-type")))
               (dk-typ--ring! rng)
               (quietly (lambda () (fact 'matneg-type rng (car m1) (cadr m1) (cadr as))))))

            ;; ---- the reshaping constructors -------------------------------
            ;; (BLOCK p k l) : the leading k-by-l block of an m-by-n matrix.
            ;; block-type types NO dimension of P, so m, n and the class all come
            ;; off P's own typing; k <= m and l <= n are the content.
            ((and (eq? (car P) 'BLOCK) (= arity 3))
             (let* ((m1 (dk-typ--mat! (car as)))
                    (kk (cadr as)) (ll (caddr as)))
               (dk-typ--need-nn! kk "block-type")
               (dk-typ--need-nn! ll "block-type")
               (dk-typ--need-le! kk (car m1) "block-type")
               (dk-typ--need-le! ll (cadr m1) "block-type")
               (quietly (lambda () (fact 'block-type (car m1) (cadr m1) (caddr m1)
                                         (car as) kk ll)))))
            ;; (BORDER a b mm p q) : [[b,0],[0,mm]], mm a p-by-q matrix over a
            ((and (eq? (car P) 'BORDER) (= arity 5))
             (let* ((rng (car as)) (bb (cadr as)) (mm (caddr as))
                    (pdim (cadddr as)) (qdim (list-ref as 4))
                    (cls (list 'CARR rng)))
               (dk-typ--mat-at! mm pdim qdim cls "border-type")
               (dk-typ--ring! rng)
               (dk-typ--need-nn! pdim "border-type")
               (dk-typ--need-nn! qdim "border-type")
               (dk-typ--need! (list 'IN bb cls) "border-type")
               (quietly (lambda () (fact 'border-type rng bb mm pdim qdim)))))
            ;; (SUBMAT s p q) : the lower-right p-by-q block of a
            ;; (succ p)-by-(succ q) matrix -- the dimensions of s are SPELLED by
            ;; submat-type's premise, so they are checked, not read off.
            ((and (eq? (car P) 'SUBMAT) (= arity 3))
             (let* ((sm (car as)) (pdim (cadr as)) (qdim (caddr as))
                    (m1 (dk-typ--mat-at! sm (list 'succ pdim) (list 'succ qdim) #f
                                         "submat-type"))
                    (rng (dk-typ--ring-of-class! (caddr m1) "submat-type")))
               (dk-typ--need-nn! pdim "submat-type")
               (dk-typ--need-nn! qdim "submat-type")
               (quietly (lambda () (fact 'submat-type rng pdim qdim sm)))))
            ;; (SNOC-COL w n v) : append the entry v to the column w
            ((and (eq? (car P) 'SNOC-COL) (= arity 3))
             (let* ((wv (car as)) (nn (cadr as)) (vv (caddr as))
                    (m1 (dk-typ--mat-at! wv nn 1 #f "snoc-col-type"))
                    (cls (caddr m1)))
               (dk-typ--need-nn! nn "snoc-col-type")
               (dk-typ--need! (list 'IN vv cls) "snoc-col-type")
               (quietly (lambda () (fact 'snoc-col-type cls nn wv vv)))))
            ;; (SNOC-ROW c n r) : append the entry r to the row c
            ((and (eq? (car P) 'SNOC-ROW) (= arity 3))
             (let* ((cv (car as)) (nn (cadr as)) (rv (caddr as))
                    (m1 (dk-typ--mat-at! cv 1 nn #f "snoc-row-type"))
                    (cls (caddr m1)))
               (dk-typ--need-nn! nn "snoc-row-type")
               (dk-typ--need! (list 'IN rv cls) "snoc-row-type")
               (quietly (lambda () (fact 'snoc-row-type cls nn cv rv)))))

            (else (error "dk-typ-close!: no MAT typing in context for"
                         (expression->string P)))))
        (or (dk-typ--mat-of P)
            (error "dk-typ-close!: matrix typing did not land for" (expression->string P))))))

;;; -----------------------------------------------------------------------
;;; FINSUM and LINCOMB, for the owed-leaf hook (2026-09-18).
;;;
;;; Both are ONE citation once their premises are in context, and both errors
;;; below fire before anything is cited.
;;;
;;;   (FINSUM ag f s) in (CARR ag)   finsum-type          ag s f
;;;                                  finsum-type-ptwise   ag s f
;;;   (LINCOMB md n c u) in (VEC md) lincomb-type         md n c u
;;;
;;; finsum-type wants the summand as a FUN(s, CARR ag) -- which is what a
;;; VNB-LAMBDA typed one line earlier by `dk-lam-fun!' leaves in context --
;;; and finsum-type-ptwise wants the POINTWISE typing instead, which is the
;;; form a back-peeled summand carries.  Whichever the context holds is used;
;;; neither is RE-PROVED here, because the hook has no business opening a
;;; lambda-typing lane behind the driver's back.

;;; (IN s SET) and (IN (CARD s) NN) for a FINSUM index set: cited for an
;;; INTERVAL, read from the context otherwise.
(define (dk-typ--index-set! s who)
  (cond ((and (pair? s) (eq? (car s) 'INTERVAL) (= (length s) 3))
         (quietly (lambda () (fact 'interval-in-set (cadr s) (caddr s))))
         (dk-typ--need-nn! (caddr s) who)
         (quietly (lambda () (fact 'interval-card-in-nn (cadr s) (caddr s)))))
        (#t
         (dk-typ--need! (list 'IN s 'SET) who)
         (dk-typ--need! (list 'IN (list 'CARD s) 'NN) who))))

;;; The pointwise typing (FORALL z. z in s => f(z) in CARR(ag)), up to alpha.
(define (dk-typ--ptwise-asm? ag f s)
  (dk-asm? (list 'FORALL 'dkz_
                 (list 'IMPLIES (list 'IN 'dkz_ s)
                       (list 'IN (list f 'dkz_) (list 'CARR ag))))))

;;; Land (IN (FINSUM ag f s) (CARR ag)).  Errors if neither typing is in context.
(define (dk-typ--finsum! t)
  (let ((ag (cadr t)) (f (caddr t)) (s (cadddr t)))
    (dk-typ--assert! (or (dk-asm? (list 'IN f (list 'FUN s (list 'CARR ag))))
                         (dk-typ--ptwise-asm? ag f s))
                     "finsum-type"
                     (string-append "the summand " (expression->string f)
                                    " is typed neither into FUN("
                                    (expression->string s) ", CARR("
                                    (expression->string ag) ")) nor pointwise"))
    (dk-typ--ag! ag)
    (dk-typ--index-set! s "finsum-type")
    (if (dk-asm? (list 'IN f (list 'FUN s (list 'CARR ag))))
        (quietly (lambda () (fact 'finsum-type ag s f)))
        (quietly (lambda () (fact 'finsum-type-ptwise ag s f))))
    (dk-typ--assert! (dk-asm? (list 'IN t (list 'CARR ag)))
                     "finsum-type" "the typing did not land")))

;;; Land (IN (LINCOMB md n c u) (VEC md)).
(define (dk-typ--lincomb! t)
  (let ((md (cadr t)) (nn (caddr t)) (cv (cadddr t)) (uv (list-ref t 4)))
    (dk-typ--need! (list 'IS-MODULE md) "lincomb-type")
    (dk-typ--mat-at! cv 1 nn (list 'CARR (list 'SCAL md)) "lincomb-type")
    (dk-typ--mat-at! uv nn 1 (list 'VEC md) "lincomb-type")
    (quietly (lambda () (fact 'lincomb-type md nn cv uv)))
    (dk-typ--assert! (dk-asm? (list 'IN t (list 'VEC md)))
                     "lincomb-type" "the typing did not land")))

;;; The heads dk-typ--mat! can type.
(define *dk-mat-constructors*
  '(MATMUL MATACT MATUNIT IDENTMAT ZEROMAT UNITROW ELEM-F ELEM-G ELEM-H
    MATADD MATSCALE MATNEG BLOCK BORDER SUBMAT SNOC-COL SNOC-ROW))

;;; A structure-carrier equation the library holds, relating classes C and X:
;;; returns the (thm . args) that lands (= lhs rhs) with {lhs, rhs} = {C, X},
;;; or #f.  ras-carr: CARR(RING-ADDITIVE-AG r) = CARR r;
;;; mvag-carr: CARR(MODULE-VECTOR-AG md) = VEC md.
(define (dk-typ--class-eq C X)
  (define (carr-of-view? c view)
    (and (pair? c) (eq? (car c) 'CARR) (pair? (cadr c)) (eq? (car (cadr c)) view)))
  (cond ((and (carr-of-view? C 'RING-ADDITIVE-AG) (equal? X (list 'CARR (cadr (cadr C)))))
         (list 'ras-carr (cadr (cadr C))))
        ((and (carr-of-view? X 'RING-ADDITIVE-AG) (equal? C (list 'CARR (cadr (cadr X)))))
         (list 'ras-carr (cadr (cadr X))))
        ((and (carr-of-view? C 'MODULE-VECTOR-AG) (equal? X (list 'VEC (cadr (cadr C)))))
         (list 'mvag-carr (cadr (cadr C))))
        ((and (carr-of-view? X 'MODULE-VECTOR-AG) (equal? C (list 'VEC (cadr (cadr X)))))
         (list 'mvag-carr (cadr (cadr X))))
        (else #f)))

;;; FINISH a typing leaf (IN t C): the chain has landed (IN t X).  Close by
;;; `ass' when X = C, else rewrite the goal's C into X by the carrier equation.
(define (dk-typ--finish!)
  (let* ((g (dk-goal)) (t (cadr g)) (C (caddr g)))
    (cond
      ((dk-asm? g) (dk-typ--ass! "dk-typ-close!"))
      (else
       (let* ((X (dk-typ--asm-class t))
              (eq (and X (dk-typ--class-eq C X))))
         (if (not eq)
             (error "dk-typ-close!: chain landed nothing usable for"
                    (expression->string g)
                    (if X (string-append "landed class " (expression->string X)) "")))
         (quietly (lambda () (apply fact eq)))
         ;; either orientation is in context now; rewrite C -> X in the goal
         (subst (list '= C X))
         (dk-typ--ass! "dk-typ-close!"))))))

;;; Land (IN t C) in the context: no-op if present, else cut + close on the side.
(define (dk-typ--ensure! t C)
  (dk-have! (list 'IN t C) dk-typ-close!))

;;; IS-RING r in context, or derivable in one step (SCAL of a module).
(define (dk-typ--ring! r)
  (cond ((dk-asm? (list 'IS-RING r)) #t)
        ((and (pair? r) (eq? (car r) 'SCAL) (dk-asm? (list 'IS-MODULE (cadr r))))
         (quietly (lambda () (fact 'module-scalar-ring (cadr r)))) #t)
        (else (error "dk-typ-close!: no IS-RING in context for" (expression->string r)))))

;;; IS-ABELIAN-GROUP ag, for the two views the library sums in.
(define (dk-typ--ag! ag)
  (cond ((dk-asm? (list 'IS-ABELIAN-GROUP ag)) #t)
        ((and (pair? ag) (eq? (car ag) 'RING-ADDITIVE-AG))
         (dk-typ--ring! (cadr ag))
         (quietly (lambda () (fact 'ring-additive-ag-is-abelian-group (cadr ag)))))
        ((and (pair? ag) (eq? (car ag) 'MODULE-VECTOR-AG)
              (dk-asm? (list 'IS-MODULE (cadr ag))))
         (quietly (lambda () (fact 'module-vector-ag-is-abelian-group (cadr ag)))))
        (else (error "dk-typ-close!: not an abelian group the chain knows:"
                     (expression->string ag)))))

;;; (IN b NN) for an interval bound that is a matrix dimension: read it off a
;;; matrix typed in context by mat-rows-in-nn (row count only -- mat-basics
;;; deliberately declines the column read-off).
(define (dk-typ--dim-in-nn! b)
  (cond ((dk-asm? (list 'IN b 'NN)) #t)
        ((number? b) (dk-typ--ensure! b 'NN))
        (else
         (let ((a (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN)
                                               (pair? (caddr a)) (eq? (car (caddr a)) 'MAT)
                                               (equal? (cadr (caddr a)) b)))
                              (dk-asms))))
           (if (not a)
               (error "dk-typ-close!: no matrix in context with row count" b))
           (let ((M (caddr a)))
             (quietly (lambda () (fact 'mat-rows-in-nn (cadr M) (caddr M) (cadddr M) (cadr a)))))))))

;;; Ground order facts between numerals (an index into a 1-by-n matrix is the
;;; literal 1): nn-le-refl when the two sides coincide, the arith oracle otherwise.
(define (dk-typ--ground-le! a b)
  (cond ((dk-asm? (list '<= a b)) #t)
        ((and (equal? a b) (dk-asm? (list 'IN a 'NN)))
         (quietly (lambda () (fact 'nn-le-refl a))))
        (else (dk-have! (list '<= a b) (lambda () (arith))))))

(define (dk-typ--numeral-in-nn! i)
  (cond ((dk-asm? (list 'IN i 'NN)) #t)
        ((eqv? i 1) (quietly (lambda () (fact 'nn-one-in))))
        (else (dk-have! (list 'IN i 'NN) (lambda () (arith))))))

;;; Close the focus goal (IN t C) by the forward typing chain.
(define (dk-typ-close!)
  (let* ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)))
        (error "dk-typ-close!: focus goal is not a membership" (expression->string g)))
    (let ((t (cadr g)) (C (caddr g)))
      (cond
        ;; already there, or there up to a carrier equation
        ((or (dk-asm? g) (let ((X (dk-typ--asm-class t))) (and X (dk-typ--class-eq C X))))
         (dk-typ--finish!))
        ;; a NUMERAL in an interval with numeral bounds  ->  interval-mem-intro
        ((and (number? t) (pair? C) (eq? (car C) 'INTERVAL)
              (number? (cadr C)) (number? (caddr C)))
         (dk-typ--numeral-in-nn! t)
         (dk-typ--ground-le! (cadr C) t)
         (dk-typ--ground-le! t (caddr C))
         (quietly (lambda () (fact 'interval-mem-intro (cadr C) (caddr C) t)))
         (dk-typ--finish!))
        ;; numeric codomain: in-rr owns it
        ((memq C '(RR ZZ QQ NN CC))
         (let ((node (dk-lam-fun--node)))
           (quietly (lambda () (in-rr)))
           (dk-lam-fun--grounded! node "dk-typ-close!" (expression->string g))))
        ;; a MATRIX CONSTRUCTOR into a MAT  ->  the matrix typing chain
        ((and (pair? t) (memq (car t) *dk-mat-constructors*)
              (pair? C) (eq? (car C) 'MAT))
         (dk-typ--mat! t)
         (dk-typ--finish!))
        ;; (LINCOMB md n c u)  ->  lincomb-type
        ((and (pair? t) (eq? (car t) 'LINCOMB) (= (length t) 5))
         (dk-typ--lincomb! t)
         (dk-typ--finish!))
        ;; ENTRY P i j  ->  entry-in-carrier
        ((and (pair? t) (eq? (car t) 'ENTRY))
         (let ((P (cadr t)) (i (caddr t)) (j (cadddr t)))
           (let ((mat (dk-typ--mat! P)))
             (let ((m (car mat)) (n (cadr mat)) (X (caddr mat)))
               (dk-typ--ensure! i (list 'INTERVAL 1 m))
               (dk-typ--ensure! j (list 'INTERVAL 1 n))
               (quietly (lambda () (fact 'entry-in-carrier m n X P i j)))
               (dk-typ--finish!)))))
        ;; ((MUL r) a b)  ->  ring-carrier-closed-mul
        ((and (pair? t) (= (length t) 3) (pair? (car t)) (eq? (caar t) 'MUL))
         (let ((r (cadr (car t))) (a (cadr t)) (b (caddr t)))
           (dk-typ--ring! r)
           (dk-typ--ensure! a (list 'CARR r))
           (dk-typ--ensure! b (list 'CARR r))
           (quietly (lambda () (fact 'ring-carrier-closed-mul r a b)))
           (dk-typ--finish!)))
        ;; ((ACT md) r x)  ->  module-act-type
        ((and (pair? t) (= (length t) 3) (pair? (car t)) (eq? (caar t) 'ACT))
         (let ((md (cadr (car t))) (r (cadr t)) (x (caddr t)))
           (if (not (dk-asm? (list 'IS-MODULE md)))
               (error "dk-typ-close!: no IS-MODULE in context for" (expression->string md)))
           (dk-typ--ensure! r (list 'CARR (list 'SCAL md)))
           (dk-typ--ensure! x (list 'VEC md))
           (quietly (lambda () (fact 'module-act-type md r x)))
           (dk-typ--finish!)))
        ;; ((OPR (MODULE-VECTOR-AG md)) a b)  ->  mvag-op, then module-vadd-type
        ((and (pair? t) (= (length t) 3) (pair? (car t)) (eq? (caar t) 'OPR)
              (pair? (cadr (car t))) (eq? (car (cadr (car t))) 'MODULE-VECTOR-AG))
         (let ((md (cadr (cadr (car t)))) (a (cadr t)) (b (caddr t)))
           (if (not (dk-asm? (list 'IS-MODULE md)))
               (error "dk-typ-close!: no IS-MODULE in context for" (expression->string md)))
           (mac 'mvag-op)                 ; OPR is in operator position: macete, not subst
           (dk-typ--ensure! a (list 'VEC md))
           (dk-typ--ensure! b (list 'VEC md))
           (quietly (lambda () (fact 'module-vadd-type md a b)))
           (dk-typ--finish!)))
        ;; (FINSUM ag f S)  ->  finsum-type
        ((and (pair? t) (eq? (car t) 'FINSUM))
         (let ((ag (cadr t)) (f (caddr t)) (S (cadddr t)))
           (dk-typ--ag! ag)
           (if (not (and (pair? S) (eq? (car S) 'INTERVAL)))
               (error "dk-typ-close!: FINSUM over a non-interval index set"
                      (expression->string S)))
           (quietly (lambda () (fact 'interval-in-set (cadr S) (caddr S))))
           (dk-typ--dim-in-nn! (caddr S))
           (quietly (lambda () (fact 'interval-card-in-nn (cadr S) (caddr S))))
           (dk-have! (list 'IN f (list 'FUN S (list 'CARR ag))) dk-lam-fun!)
           (quietly (lambda () (fact 'finsum-type ag S f)))
           (dk-typ--finish!)))
        ;; (LIST a b) in CARTESIAN(X, Y)  ->  pair-in-cartesian
        ((and (pair? t) (eq? (car t) 'LIST) (= (length t) 3)
              (pair? C) (eq? (car C) 'CARTESIAN) (= (length C) 3))
         (dk-typ--ensure! (cadr t) (cadr C))
         (dk-typ--ensure! (caddr t) (caddr C))
         (quietly (lambda () (fact 'pair-in-cartesian (cadr C) (caddr C) (cadr t) (caddr t))))
         (dk-typ--finish!))
        ;; (NTH k z) with z in CARTESIAN(a, b)  ->  cartesian-nth
        ((and (pair? t) (eq? (car t) 'NTH) (= (length t) 3)
              (let ((zc (dk-typ--asm-class (caddr t))))
                (and (pair? zc) (eq? (car zc) 'CARTESIAN) (= (length zc) 3))))
         ;; `zt' / `zc', not `z' / `Z': MIT folds case, so those would be ONE binding
         (let* ((zt (caddr t)) (zc (dk-typ--asm-class zt)))
           (dk-split! (dk-fact! 'cartesian-nth zt (cadr zc) (caddr zc)))
           (dk-typ--finish!)))
        ;; ((VNB-LAMBDA v D b) arg)  ->  type the argument, then beta
        ((and (pair? t) (= (length t) 2) (pair? (car t)) (eq? (caar t) 'VNB-LAMBDA)
              (= (length (car t)) 4))
         (let ((D (caddr (car t))) (arg (cadr t)))
           (dk-typ--ensure! arg D)
           (let ((node (dk-lam-fun--node)))
             (lam-b)
             ;; a tupled argument leaves (NTH k (LIST ...)) behind; reduce it if so
             (if (dk-contains? (dk-goal) 'NTH) (quietly (lambda () (nth-r))))
             (dk-typ-close!)
             (dk-lam-fun--grounded! node "dk-typ-close!" (expression->string g)))))
        ;; a nested lambda typed into FUN: recurse
        ((and (pair? t) (eq? (car t) 'VNB-LAMBDA) (pair? C) (eq? (car C) 'FUN))
         (dk-lam-fun!))
        (else
         (error "dk-typ-close!: no typing rule for the head of"
                (expression->string t) "in goal" (expression->string g)))))))

;;; Sethood of a lambda domain, ERRORING if it stays open.
(define (dk-lam-fun--sethood!)
  (let* ((node (dk-lam-fun--node)) (g (dk-goal)) (A (cadr g)))
    (cond
      ((and (pair? A) (eq? (car A) 'CARTESIAN))
       (mac 'cartesian-set-iff)
       (for-each (lambda (leaf) (dk-focus! leaf) (dk-lam-fun--sethood!))
                 (dk-opened (lambda () (di)))))
      (else (dk-set-close! A)))
    (dk-lam-fun--grounded! node "dk-lam-fun!" (string-append "sethood " (expression->string g)))))

(define (dk-lam-fun!)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                  (pair? (cadr g)) (eq? (car (cadr g)) 'VNB-LAMBDA)
                  (pair? (caddr g)) (eq? (car (caddr g)) 'FUN)))
        (error "dk-lam-fun!: focus goal is not (IN (VNB-LAMBDA ...) (FUN ...)):"
               (expression->string g)))
    (let* ((node (dk-lam-fun--node))
           (new  (dk-opened (lambda () (lam-t))))
           (sets (filter (lambda (l) (let ((h (dk-goal-of l)))
                                       (and (pair? h) (eq? (car h) 'IN) (eq? (caddr h) 'SET))))
                         new))
           (typ  (filter (lambda (l) (not (memq l sets))) new)))
      (if (null? new) (error "dk-lam-fun!: lam-t did not fire on" (expression->string g)))
      (for-each (lambda (l) (dk-focus! l) (dk-lam-fun--sethood!)) sets)
      (when (pair? typ)                 ; absent only if hash-consing found it grounded
        (dk-focus! (car typ))
        (let peel ()
          (let ((h (car (dk-goal))))
            (when (memq h '(FORALL IMPLIES)) (di) (peel))))
        (dk-typ-close!))
      (dk-lam-fun--grounded! node "dk-lam-fun!" (expression->string g)))))

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
;;;
;;; A CLAIM THAT IS THE FOCUS GOAL IS PROVED IN PLACE (2026-09-24, batch 27-B,
;;; item 9).  A `cut' of the focus goal is a self-loop -- the side goal IS the
;;; focus node -- so this used to die "cut left no main branch", and three files
;;; wrapped it (tcl-have!, dtr-have!, daf-have!: "or, when CLAIM is the focus
;;; goal itself, run THUNK on it").  Now THUNK (or from-context!) runs on the
;;; focus leaf, which must end GROUNDED, else this errors.  The goal is then
;;; CLOSED and the focus has moved to another leaf: the value is #t in that case
;;; alone, so a caller that goes on can tell and re-focus.
(define (dk-have! form0 . opt)
  (let ((f (->raw-formula form0))
        (thunk (and (pair? opt) (car opt))))
    (cond
     ((dk-asm? f) #f)
     ((eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) f))))
      (let ((leaf (proof-state-focus *ps*)))
        (if thunk (thunk) (from-context!))
        (if (not (sequent-node-grounded? leaf))
            (error "dk-have!: the claim is the focus goal, and the lane left it open" f))
        #t))
     (#t
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
              (error "dk-have!: cut left no main branch for" f)))))))

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

;;; -----------------------------------------------------------------------
;;; Matrix-layer helpers (2026-09-16, the SIZE/MAT change).  Three files of the
;;; matrix arc need them: mat-basics, mat-typing-bundle, matunit-matact-type.

;;; (dk-focus-having! F) -- focus the open leaf whose context holds F (equal?);
;;; ERRORS if there is none.  The re-focus after a `have!' whose lane moved
;;; focus elsewhere.
(define (dk-focus-having! f)
  (let ((l (find-first (lambda (l) (member f (dk-asms-of l))) (proof-leaves))))
    (if (not l) (error "dk-focus-having!: no open leaf holds" (expression->string f)))
    (dk-focus! l)))

;;; (dk-one-le-from! I HI) -- with (IN I (INTERVAL 1 HI)) and (IN HI NN) in
;;; context, land (<= 1 HI) (and I in NN, 1 <= I, I <= HI on the way).
(define (dk-one-le-from! iv hi)
  (fact 'interval-elt-in-nn 1 hi iv)
  (fact 'interval-lo 1 hi iv)
  (fact 'interval-hi 1 hi iv)
  (fact 'nn-one-in)
  (fact 'nn-le-trans-guarded 1 iv hi))

;;; (dk-matof!) -- on a goal (IN (MATOF m n g) (MAT m n X)): backchain through
;;; matof-in-mat, close the (IN m NN) / (IN n NN) premises it owes from the
;;; context, and leave focus on the one remaining leaf, the entry hypothesis.
;;; ERRORS unless exactly one other leaf opened.
(define (dk-matof!)
  (let* ((opened (dk-opened (lambda () (bc* 'matof-in-mat))))
         (nn     (filter (lambda (l) (let ((g (dk-goal-of l)))
                                       (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'NN))))
                         opened))
         (rest   (filter (lambda (l) (not (memq l nn))) opened)))
    (for-each (lambda (l) (dk-focus! l) (ass)) nn)
    (if (not (= 1 (length rest)))
        (error "dk-matof!: expected one entry leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) rest)))
    (dk-focus! (car rest))))

;;; (dk-one-le! V) -- with (IN V NN) and (NOT (= V 0)) in context, land (<= 1 V):
;;; V is a successor (nn-nonzero-is-succ) and 1 <= succ(q) (nn-one-le-succ).
;;; Leaves focus on the branch that holds it.  Was copied into four files as
;;; tt-/mtb-/ma-one-le! during the SIZE/MAT repair (2026-09-16).
(define (dk-one-le! v)
  (let* ((ex (dk-fact! 'nn-nonzero-is-succ v))
         (q  (dk-skolem! ex)))
    (fact 'nn-one-le-succ q)
    (have! (list '<= 1 v)
      (lambda () (subst (list '= v (list 'succ q))) (ass)))
    (dk-focus-having! (list '<= 1 v))))

;;; (dk-nonzero! V) -- with (<= 1 V) in context, land (NOT (= V 0)): assuming
;;; V = 0 turns the hypothesis into 1 <= 0, which `arith' refutes.
(define (dk-nonzero! v)
  (let ((f (list 'NOT (list '= v 0))))
    (have! f
      (lambda ()
        (di)                                     ; V = 0 |- FALSITY
        (have! '(<= 1 0)
          (lambda () (subst (list '= 0 v)) (ass)))
        (dk-focus-having! '(<= 1 0))
        (have! '(NOT (<= 1 0)) (lambda () (arith)))
        (dk-focus-having! '(NOT (<= 1 0)))
        (ai '(NOT (<= 1 0)))))
    (dk-focus-having! f)))

;;; (dk-have-prop! F) -- land F, a propositional consequence of the context
;;; (typically a product guard such as (IMPLIES (= n 0) (OR (= n 0) (= k 0)))),
;;; by `prop', and leave focus on the branch that holds it.  No-op if F is
;;; already an assumption (a `have!' of a present formula is a self-loop).
(define (dk-have-prop! f)
  (if (not (dk-asm? f)) (have! f (lambda () (prop))))
  (dk-focus-having! f))

;;; (dk-vacuous! I V) -- with (IN I (INTERVAL 1 V)), (IN V NN) and (= V 0) in
;;; context, close the focus goal, whatever it is: 1 <= I <= V = 0 is absurd.
;;; Copied into three files as ma-/ms-/mb-vacuous! during the 2026-09-16 repair.
(define (dk-vacuous! iv v)
  (dk-one-le-from! iv v)
  (have! '(<= 1 0) (lambda () (subst (list '= 0 v)) (ass)))
  (dk-focus-having! '(<= 1 0))
  (have! '(NOT (<= 1 0)) (lambda () (arith)))
  (dk-focus-having! '(NOT (<= 1 0)))
  (pbc)
  (ai '(NOT (<= 1 0))))

;;; (dk-lincomb-transport-guards! V) -- with (NOT (= V 0)) in context, land the
;;; product guards a Lemma 3.40 transport owes at the shapes (1,V,V,1) and
;;; (1,V,V,V): matmul-type (1,V,V), matact-type (V,V,1), matact-assoc G1 = G2
;;; at (1,V,V,1), matmul-assoc G1, G2 at (1,V,V,V).  Copied into mod-basis and
;;; spans-transport during the 2026-09-16 repair.
(define (dk-lincomb-transport-guards! v)
  (for-each dk-have-prop!
    `((IMPLIES (= ,v 0) (OR (= 1 0) (= ,v 0)))
      (IMPLIES (= ,v 0) (OR (= ,v 0) (= 1 0)))
      (IMPLIES (= ,v 0) (OR (= 1 0) (AND (= ,v 0) (= 1 0))))
      (IMPLIES (= ,v 0) (OR (= 1 0) (AND (= ,v 0) (= ,v 0))))
      (IMPLIES (= ,v 0) (OR (= ,v 0) (AND (= ,v 0) (= 1 0)))))))


;;; -----------------------------------------------------------------------
;;; dk-discharge-owed! -- the OWED-LEAF hook (2026-09-18; see interactive.scm's
;;; vnb--run!).  A fresh leaf (= t t) posted by the LUTINS instantiation rule
;;; is closed here when the term's typing is one citation away: any of the
;;; seventeen matrix constructors through the matrix typing chain
;;; (*dk-mat-constructors*), a FINSUM through finsum-type / finsum-type-ptwise,
;;; a LINCOMB through lincomb-type, an ENTRY through entry-in-carrier,
;;; arithmetic through in-rr.  Best effort: anything else, or any failure,
;;; leaves the leaf open for the driver (or `qed') to report.  Never raises;
;;; restores the focus the command left.
;;; run THUNK; on any error return #f and print NOTHING (the hook's decline is
;;; not a failure of the proof -- the leaf simply stays open for the driver)
(define (dk--silently thunk)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler (lambda (e) (k #f)) thunk))))
(define (dk-discharge-owed! leaf)
  ;; TRANSACTIONAL (2026-09-18 evening): an attempt that does not close the
  ;; leaf is rolled back -- graph, focus, script, trace, undo stack -- so a
  ;; failed closer leaves no half-cut leaf behind (the recip(0) suite check
  ;; found three leaves where two were owed).
  (let* ((home  (proof-state-focus *ps*))
         (mark  (vnb--take-mark '(dk-discharge-owed!)))
         (depth (length *vnb-undo-stack*)))
    (dk--silently
     (lambda ()
       (let* ((g (dk-goal-of leaf)) (t (cadr g)))
         (dk-focus! leaf)
         (quietly
          (lambda ()
            (cond
              ((and (pair? t) (memq (car t) *dk-mat-constructors*))
               (dk-typ--mat! t) (rfl))
              ((and (pair? t) (eq? (car t) 'ENTRY) (= (length t) 4))
               (let* ((mat (dk-typ--mat! (cadr t))) (X (caddr mat)))
                 (dk-have! (list 'IN t X) (lambda () (dk-typ-close!)))
                 (rfl)))
              ((and (pair? t) (eq? (car t) 'FINSUM) (= (length t) 4))
               (dk-typ--finsum! t) (rfl))
              ((and (pair? t) (eq? (car t) 'LINCOMB) (= (length t) 5))
               (dk-typ--lincomb! t) (rfl))
              ;; SERIES-PARTIAL-SUM f k : f in FUN(NN,RR), k in NN -> in RR
              ((and (pair? t) (eq? (car t) 'SERIES-PARTIAL-SUM) (= (length t) 3))
               (fact 'series-partial-sum-in-rr (caddr t) (cadr t)) (rfl))
              ((and (pair? t) (memq (car t) '(+ - * / recip abs min max ^)))
               (dk-have! (list 'IN t 'RR) (lambda () (in-rr)))
               (rfl))
              (#t #f)))))))
    (if (and mark (not (sequent-node-grounded? leaf)))
        (begin                                   ; roll the attempt back
          (dg-rollback! (vnb-undo-mark-dg-mark mark))
          (set-proof-state-focus! *ps* (vnb-undo-mark-focus mark))
          (set! *proof-script* (vnb-undo-mark-script mark))
          (set! *live-trace*   (vnb-undo-mark-trace mark))
          (let loop () (when (> (length *vnb-undo-stack*) depth)
                         (set! *vnb-undo-stack* (cdr *vnb-undo-stack*)) (loop)))))
    (if (and home (not (sequent-node-grounded? home))
             (not (eq? home (proof-state-focus *ps*))))
        (dk-focus! home))))
(set! *owed-leaf-hook* dk-discharge-owed!)


;;; =======================================================================
;;; BATCH 8 (2026-09-19).  The helpers the rake wrote once per file.
;;; Each was copied three or more times during the batches 6-7 waves; the
;;; comment on each names the copies it replaces.  Every one drives SURFACE
;;; tactics only and moves focus through `dk-focus!', so the recorded script
;;; replays (CLAUDE.md, "Script replay and the page").
;;; =======================================================================

;;; -----------------------------------------------------------------------
;;; THE LEAF SET.  `proof-open-goals' is every UNGROUNDED node, which includes
;;; every justified ancestor still waiting on its children; the nodes a driver
;;; can work on are the ones no rule has fired on yet.  Two rake agents lost a
;;; run each to that difference on 2026-09-19 (7-I, 7-L), and three files had
;;; hand-written the filter (rn-open, zr-open, dc-open-leaves).  One name.
(define (dk-open-leaves) (proof-open-leaves *ps*))

;;; -----------------------------------------------------------------------
;;; THE <= CHAIN.  "a <= b <= c <= d, so a <= d" is one line of mathematics and
;;; fifteen of driver: rr-leq-transitive is guarded on all three arguments being
;;; real AND takes its two order premises as ONE conjunction, which `fact' will
;;; not split.  Batch 7-F wrote r8f-le-trans! / r8f-le-add! / r8f-eq-le! for it
;;; (directional-derivative.scm); this is that kit, guarded against re-landing a
;;; fact the context already holds.
;;;
;;; NOT `ineq': the oracle DROPS a non-linear premise silently (a product of two
;;; non-constant terms) and then blames the goal (CLAUDE.md, 2026-09-19).  A
;;; chain of citations is what those estimates want.

;;; Land (IN T RR) unless it is already there.  Returns the typing.
(define (dk-real! t)
  (let ((typ (list 'IN t 'RR)))
    (if (not (dk-asm? typ)) (dk-have! typ (lambda () (in-rr))))
    typ))

(define (dk--occurs? sub e)
  (cond ((equal? sub e) #t)
        ((pair? e) (or (dk--occurs? sub (car e)) (dk--occurs? sub (cdr e))))
        (#t #f)))

;;; (dk-eq-le! B C) -- with (= B C) in context (either orientation), land (<= B C).
;;; THE DIRECTION IS CHOSEN BY CONTAINMENT: `subst' rewrites EVERY occurrence, so
;;; the side that CONTAINS the other has to be the one rewritten away -- on
;;; x = 0 + (0 + x) the other orientation rewrites x inside its own right-hand
;;; side and the goal never becomes reflexive.
(define (dk-eq-le! b c)
  (let ((le (list '<= b c)))
    (if (not (dk-asm? le))
        (if (dk--occurs? c b)
            (begin (dk-real! c)
                   (dk-have! le (lambda () (subst (list '= b c))
                                        (fact 'rr-leq-reflexive c) (ass))))
            (begin (dk-real! b)
                   (dk-have! le (lambda () (subst (list '= c b))
                                        (fact 'rr-leq-reflexive b) (ass))))))
    le))

;;; (dk-le-trans! A B C) -- (<= A B) and (<= B C) in context; land (<= A C).
(define (dk-le-trans! a b c)
  (let ((le (list '<= a c)))
    (if (not (dk-asm? le))
        (begin
          (for-each dk-real! (list a b c))
          (dk-have! (list 'AND (list 'IN a 'RR)
                          (list 'AND (list 'IN b 'RR) (list 'IN c 'RR))))
          (dk-have! (list 'AND (list '<= a b) (list '<= b c)))
          (fact 'rr-leq-transitive a b c)))
    le))

;;; (dk-le-add! A B U V) -- (<= A B) and (<= U V) in context; land (<= A+U B+V).
(define (dk-le-add! a b u v)
  (let ((le (list '<= (list '+ a u) (list '+ b v))))
    (if (not (dk-asm? le))
        (begin
          (for-each dk-real! (list a b u v))
          (dk-have! (list 'AND (list '<= a b) (list '<= u v)))
          (fact 'rr-le-add a b u v)))
    le))

;;; One rung of a chain: (<= A B) if the context holds it, else the equation
;;; between them turned into one.  ERRORS when the context holds neither.
(define (dk--step-le! a b)
  (cond ((dk-asm? (list '<= a b)) (list '<= a b))
        ((or (dk-asm? (list '= a b)) (dk-asm? (list '= b a))
             (dk-asm? (list '== a b)) (dk-asm? (list '== b a)))
         (dk-eq-le! a b))
        (#t (error "dk-le-chain!: the context holds neither an inequality nor an equation between"
                   (expression->string a) (expression->string b)))))

;;; (dk-le-chain! T1 T2 ... TN) -- land (<= T1 TN) from the rungs the context
;;; holds, each of which may be an inequality or an equation; the typings are
;;; landed first, as rr-leq-transitive's guard demands.  Closes the focus goal
;;; when it IS (<= T1 TN), and returns the formula either way.
(define (dk-le-chain! . terms)
  (if (or (null? terms) (null? (cdr terms)))
      (error "dk-le-chain!: needs at least two terms" terms))
  (let ((t1 (car terms)))
    (let loop ((a t1) (rest (cdr terms)))
      (if (null? rest)
          (let ((le (list '<= t1 a)))
            (if (eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) le)))) (ass))
            le)
          (let ((b (car rest)))
            (dk--step-le! a b)
            (if (not (equal? a t1)) (dk-le-trans! t1 a b))
            (loop b (cdr rest)))))))

;;; -----------------------------------------------------------------------
;;; BETA, WITH THE OWED TYPINGS CLOSED.
;;;
;;; `lam-b' POSTS THE ARGUMENT TYPING AS A LEAF even when that typing is already
;;; in the context: it opens the reduced goal AND one (IN arg dom) obligation per
;;; redex, and a driver that walks on leaves the obligations behind -- the parent
;;; never grounds and the enclosing `have!' fails with "THUNK left the side goal
;;; open", naming the CLAIM and not the leaf.  And a FIXED-COUNT `lam-b' leaves an
;;; inert step when nothing is left to reduce, so the loop is on a REDEX TEST.
;;; (7-K's r8k-lam-b!, 7-L's r8l-beta!, and the same loop in four more files.)
(define (dk--redex? e)
  (cond ((not (pair? e)) #f)
        ((and (pair? (car e)) (eq? (car (car e)) 'VNB-LAMBDA)) #t)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((dk--redex? (car l)) #t)
                    (#t (loop (cdr l))))))))

;;; Run THUNK; close every leaf it opened whose goal is a typing ALREADY in
;;; context; leave focus on the one leaf that is not, and return it (#f when the
;;; reduction closed the branch outright).  An obligation that is NOT in context
;;; is the caller's to discharge and this cannot guess which leaf is which, so
;;; two survivors is an ERROR, naming both: focusing the wrong one silently is
;;; the failure this kit exists to prevent.
;;;
;;; The obligation a licensed redex does not owe is never posted at all
;;; (pi--beta-licensed?), so the leaves this closes are the TUPLED ones: a
;;; multi-binder lambda applied to a, b is licensed COMPONENTWISE, and a context
;;; that types the pair (IN (LIST a b) (CARTESIAN A B)) and not its components
;;; owes -- the very formula it holds.
(define (dk--close-owed-typings! thunk)
  (let ((opened (dk-opened thunk))
        (rest   '()))
    (for-each (lambda (leaf)
                (dk-focus! leaf)
                (let ((g (dk-goal)))
                  (cond ((and (pair? g) (eq? (car g) 'IN) (dk-asm? g)) (ass))
                        ;; the value's sethood beta owes since 2026-10-01: the routes of
                        ;; dk-sethood!; a leaf it cannot close is reported like the rest
                        ((and (pair? g) (eq? (car g) 'IN) (= (length g) 3) (eq? (caddr g) 'SET)
                              (call-with-current-continuation
                                (lambda (k)
                                  (with-exception-handler (lambda (e) (k #f))
                                    (lambda () (dk-sethood! (cadr g)) #t)))))
                         #t)
                        (else (set! rest (cons leaf rest))))))
              opened)
    (cond ((null? rest) #f)
          ((null? (cdr rest)) (dk-focus! (car rest)) (car rest))
          (#t (error "dk-lam-b!: beta owes an obligation the context does not hold"
                     (map (lambda (l) (expression->string (dk-goal-of l))) rest))))))

;;; (dk-lam-b!) -- beta-reduce the GOAL to a fixpoint, closing each owed
;;; argument typing the context already carries, focus left on the reduced goal.
;;; RETURNS WHETHER THE LEAF IT STARTED ON IS GROUNDED (2026-09-24, batch 27-B,
;;; item 12; it used to return the reduced goal, which no caller read): #t when
;;; the reduction closed the branch -- the reduced goal was in context, say --
;;; and the focus has then MOVED to another leaf, so the caller's next closer
;;; must not run: (if (not (dk-lam-b!)) (ass)), or (dk-close-if! dk-lam-b!
;;; ass).  #f when the reduced goal is open and in focus.  Four files guarded the
;;; closer by hand (`(if (not (sequent-node-grounded? ...)))' after a beta).
;;; ERRORS when the goal holds no redex at all: a `lam-b' that reduces nothing
;;; prints "nothing changed ... The step was NOT recorded" and is otherwise
;;; silent, which is the no-op this exists to make loud.
;;; `dk--close-owed-typings!' answers #f for TWO different things: beta closed
;;; the branch outright (every leaf it opened was a typing the context held), and
;;; beta did NOTHING AT ALL (it opened no leaf).  The second happens whenever the
;;; kernel declines the step -- since 2026-09-20 an inference REFUSED by the
;;; independent rule checker is one such case (12-E met it on a beta chain) --
;;; and reading it as "the branch closed" hands the driver a silent no-op: the
;;; caller walks on, the leaf is still open, and the failure surfaces pages later
;;; at the enclosing `have!'.  The two are told apart by the leaf we started on:
;;; it is GROUNDED when the branch closed, and still an open leaf when nothing
;;; happened.
(define (dk--beta-done? tag leaf0 goal0)
  (cond ((sequent-node-grounded? leaf0) #f)     ; the branch closed: nothing owed
        (#t (error (string-append
                     tag ": beta changed nothing and the leaf is still open"
                     " -- the inference may have been REFUSED by the rule checker"
                     " (look above for `dg-apply-rule!'), or no redex was licensed")
                   (expression->string goal0)))))

(define (dk-lam-b!)
  (if (not (dk--redex? (dk-goal)))
      (error "dk-lam-b!: no redex in the goal" (expression->string (dk-goal))))
  (let ((home (proof-state-focus *ps*)))
    (dk--lam-b-loop!)
    (sequent-node-grounded? home)))

(define (dk--lam-b-loop!)
  (let loop ((n 0) (main (proof-state-focus *ps*)))
    (let ((before (dk-goal))
          (leaf0  (proof-state-focus *ps*)))
      (if (and (< n 8) (dk--redex? before))
          (let ((m (dk--close-owed-typings! (lambda () (lam-b)))))
            (if (not m)
                (dk--beta-done? "dk-lam-b!" leaf0 before)
                (if (equal? (dk-goal) before)
                    (error "dk-lam-b!: lam-b left the goal unchanged"
                           (expression->string before))
                    (loop (+ n 1) m))))
          (dk-goal)))))

;;; (dk-lam-b-h! EQ) -- the same for a redex in a HYPOTHESIS (`lam-b' reaches
;;; only the goal).  RETURNS WHETHER THE LEAF IT STARTED ON IS GROUNDED
;;; (2026-09-24, batch 27-B, item 12), exactly as `dk-lam-b!' does: #t when the
;;; reduced hypothesis closed the branch (it WAS the goal, say) and the focus
;;; has moved on -- the case 25-B and 26-A met, where a following `(ass)'
;;; drifted to the main goal; #f when the leaf is open and in focus.  It used
;;; to return that leaf or #f.  A `lam-b-h' that did nothing is an ERROR, for
;;; the reason beside `dk--beta-done?'.
(define (dk-lam-b-h! eq)
  (let* ((leaf0 (proof-state-focus *ps*))
         (goal0 (dk-goal))
         (m     (dk--close-owed-typings! (lambda () (lam-b-h eq)))))
    (if (not m) (dk--beta-done? "dk-lam-b-h!" leaf0 goal0))
    (sequent-node-grounded? leaf0)))

;;; -----------------------------------------------------------------------
;;; (dk-each-leaf! THUNK VISIT) -- run THUNK, a BRANCHING tactic, and visit each
;;; leaf it opened with VISIT, focus moved through dk-focus!.  Returns the leaves.
;;; ERRORS when the tactic opened none: that is the silent no-op (a `sep-mi' or
;;; `di' that did not fire leaves VISIT running on the caller's own leaf).
;;; (r8g-each-leaf!, r8j-each-leaf!, and the `(for-each ... (dk-opened ...))'
;;; line in a dozen more.)
(define (dk-each-leaf! thunk visit)
  (let ((opened (dk-opened thunk)))
    (if (null? opened) (error "dk-each-leaf!: the tactic opened no leaf"))
    (for-each (lambda (leaf) (dk-focus! leaf) (visit)) opened)
    opened))

;;; -----------------------------------------------------------------------
;;; (have-f! CLAIM) / (have-f! CLAIM THUNK) -- `have!', returning the CLAIM as
;;; the context now holds it rather than the main NODE.  `have!' returns the
;;; node, so every driver that wants to `ai' / `mac-h' / `detach!' what it just
;;; cut has to keep the formula itself -- and a RECONSTRUCTED formula matches
;;; nothing and no-ops.  This hands back the context's own term.
(define (have-f! form0 . opt)
  (let ((f (->raw-formula form0)))
    (apply have! form0 opt)
    (or (any-pred (lambda (a) (eq? #t (vnb-guard (lambda () (alpha-equiv? a f)))))
                  (dk-asms))
        (error "have-f!: the claim is not in the context after have!"
               (expression->string f)))))

;;; -----------------------------------------------------------------------
;;; (choose-mem! S WITNESS BODY) -- "pick an element of S", LEAVING the
;;; membership: lands and returns (IN (CHOICE S) S), with choice's one
;;; obligation (S is inhabited) discharged by WITNESS and BODY.  `choose!' does
;;; the same and then CONSUMES the membership with `sep-me' when S is a SEP,
;;; which is right when the caller wants the two halves and wrong when the
;;; membership itself is what is wanted next (7-K's r8k-choose!).
;;; The existential's binder is `cv_', a name no predicate body in the library
;;; uses: a driver-built binder spelled like an eigenvariable or like a binder of
;;; the statement is RENAMED by subst-free, and every later lookup of the rebuilt
;;; term then matches nothing, silently (CLAUDE.md, 2026-09-19).
(define (choose-mem! s witness body)
  (if (memq 'cv_ (free-vars s))
      (error "choose-mem!: cv_ is free in the set term" (expression->string s)))
  (have! (list 'FORSOME 'cv_ (list 'IN 'cv_ s))
         (lambda () (witness! witness body)))
  (dk-fact! 'choice-axiom s))


;;; =======================================================================
;;; BATCH 11-D (2026-09-20) -- the helpers batches 9-A, 10 and 11-E asked for.
;;; Each replaces three or more verbatim copies, and each has a suite check
;;; (test-suite.scm, "driver kit (batch 11-D)"), the drift one with its control.
;;; =======================================================================

;;; -----------------------------------------------------------------------
;;; HEADS, TOLERATING AN ATOM.  A discriminator written as `(car (caddr goal))'
;;; dies -- or, worse, picks the wrong branch -- on a goal whose class is a bare
;;; variable or an atomic constant: `bu-mi' opens exactly such a leaf, (IN v c_),
;;; beside the one being discriminated, and EMPTY-SET is an atom (batch 9-A and
;;; 11-E both lost time to it; iof-head? was the local copy).  `dk-head?' is the
;;; curried predicate on a FORMULA and already tolerates atoms; these are the
;;; two shapes it does not cover.
(define (dk-head e) (and (pair? e) (car e)))
(define (dk-head-is? e h) (eq? (dk-head e) h))
(define (dk-goal-head? h) (lambda (n) (eq? (dk-head (dk-goal-of n)) h)))

;;; -----------------------------------------------------------------------
;;; FOCUS DRIFT (docs/batch8-2026-09-19.md 4.7; three sightings: dk-only!,
;;; `slot').  A tactic that rewrites or weakens can GROUND its own leaf -- by
;;; hash-consing onto a node already proven, or simply by closing it -- and the
;;; focus then moves to a SIBLING.  The next line of the driver, written as the
;;; closer for the leaf just worked on, fires on that sibling instead.  It is
;;; silent: the sibling usually closes, and the proof ends with a leaf nobody
;;; drove.  MEASURED (scratchpad/b11d/kit-probe.scm): on a two-leaf AND, an
;;; `rfl' that grounds the first leaf moves the focus to the second, and a bare
;;; following `(ass)' closes the second.
;;;
;;; (dk-close-if! THUNK CLOSER): run THUNK on the focus leaf N, run CLOSER only
;;; if N is still OPEN and still the FOCUS, and return whether N is grounded.
;;; The third case -- N open, focus moved -- is the drift, and it is reported
;;; rather than papered over: the caller gets #f and a warning naming both nodes.
(define (dk-close-if! thunk closer)
  (let ((node (proof-state-focus *ps*)))
    (thunk)
    (cond ((sequent-node-grounded? node) #t)
          ((eq? node (proof-state-focus *ps*))
           (closer)
           (sequent-node-grounded? node))
          (#t
           (display ";VNB warning: dk-close-if!: the thunk left node ")
           (write (sequent-node-number node))
           (display " OPEN and moved the focus to ")
           (write (sequent-node-number (proof-state-focus *ps*)))
           (display " -- the closer was NOT run.")
           (newline)
           #f))))

;;; -----------------------------------------------------------------------
;;; (dk-close-all! THUNK) -- run a BRANCHING tactic and close every leaf it
;;; opened with `ass'.  Four or more verbatim copies (iof-close-all!,
;;; rkb-close-all!, the `(for-each (lambda (n) (dk-focus! n) (ass)) (dk-opened
;;; ...))' line).  Returns the leaves it closed.
;;;
;;; IT TOLERATES A LEAF HASH-CONSING HAS ALREADY GROUNDED, as `in-sep!' does
;;; (2026-09-20, batch 13-D; 12-F asked for it).  Sequent nodes are hash-consed
;;; on assertion-up-to-alpha PLUS context, so a subgoal proved earlier under
;;; this same context comes back GROUNDED and is not an open leaf at all: the
;;; tactic then opens FEWER leaves than its arity, and possibly none.  Never
;;; infer failure from how many leaves a rule opens -- ask whether the node is
;;; grounded.  It used to go through `dk-each-leaf!', whose error ("the tactic
;;; opened no leaf") reported the obligation's DISCHARGE as a failure, which is
;;; the same defect `in-sep!' carried until 2026-09-19.  When nothing opened
;;; and the node is still OPEN, that IS the silent no-op, and it still errors.
(define (dk-close-all! thunk)
  (let* ((home   (proof-state-focus *ps*))
         (opened (dk-opened thunk)))
    (cond ((pair? opened)
           (for-each (lambda (leaf)
                       ;; a sibling's proof may have grounded this one meanwhile
                       (if (not (sequent-node-grounded? leaf))
                           (begin (dk-focus! leaf) (ass))))
                     opened)
           opened)
          ((sequent-node-grounded? home) '())
          (#t (error "dk-close-all!: the tactic opened no leaf and the node is still open"
                     (expression->string (dk-goal-of home)))))))

;;; -----------------------------------------------------------------------
;;; (dk-iff! WHICH? FWD BWD) -- split an IFF goal and drive both directions,
;;; discriminated on the GOAL and never on the order `dk-opened' returns.
;;; `di' on an IFF opens two leaves and lands each direction's ANTECEDENT, so
;;; each leaf's goal is already the CONSEQUENT: WHICH? is a predicate on that
;;; consequent, and `(dk-head? 'IN)' is the usual one.  Errors when `di' opened
;;; other than two leaves, and when WHICH? picks both or neither -- the two
;;; ways a hand-written copy silently drives one direction twice.
(define (dk-iff! which? fwd bwd)
  (let ((ls (dk-opened (lambda () (di)))))
    (if (not (= (length ls) 2))
        (error "dk-iff!: di opened" (length ls) "leaf(s), not 2"))
    (let ((a (filter (lambda (n) (which? (dk-goal-of n))) ls)))
      (if (not (= (length a) 1))
          (error "dk-iff!: the discriminator picked" (length a) "of the 2 leaves"))
      (dk-focus! (car a)) (fwd)
      (dk-focus! (car (filter (lambda (n) (not (eq? n (car a)))) ls))) (bwd)
      ls)))


;;; =======================================================================
;;; BATCH 13-D (2026-09-20).  The four helpers batch 12's agents each wrote
;;; again, and the rule that is NOT one (see "CAPTURE THE FORMULA WHEN IT
;;; LANDS" in this file's dk- header).  Every one drives SURFACE tactics only,
;;; moves focus through `dk-focus!', and ERRORS rather than returning #f on a
;;; miss.  Each has a suite check with its control (test-suite.scm, "driver kit
;;; (batch 13-D)").
;;; =======================================================================

;;; The context's OWN copy of F (alpha-equivalent), or #f.  A formula the
;;; driver rebuilt is not the one `mac-h' / `ai' / `detach!' will match, so a
;;; helper that is about to hand a formula to one of them asks for this first.
(define (dk-ctx-form f)
  (any-pred (lambda (a) (eq? #t (vnb-guard (lambda () (alpha-equiv? a f)))))
            (dk-asms)))

;;; Close the lane a `dk-project!' opened: the hypothesis has been opened on
;;; this branch, so the claim is either in the context outright (`ass'), or in
;;; it once the landed conjunction is split, or a propositional consequence of
;;; the pieces (`prop' -- debt-free, and what a projection out of a three-way
;;; AND wants).  The test is on the LANE'S OWN NODE, never on the current
;;; focus: a tactic that closes its leaf moves the focus to a SIBLING, and a
;;; further tactic aimed at "the leaf" would then fire there (the focus drift,
;;; docs/batch8-2026-09-19.md 4.7).  Leaves the reporting to `dk-have!', which
;;; errors when the lane did not establish the claim.
(define (dk--lane-close!)
  (let ((lane (proof-state-focus *ps*)))
    (define (still-open?) (not (sequent-node-grounded? lane)))
    (if (still-open?) (vnb-guard (lambda () (ass))))
    (if (still-open?) (vnb-guard (lambda () (dk-split-all!))))
    (if (still-open?) (vnb-guard (lambda () (ass))))
    (if (still-open?) (vnb-guard (lambda () (prop))))
    (not (still-open?))))

;;; -----------------------------------------------------------------------
;;; (dk-project! CONCL THUNK)     -- read CONCL off a hypothesis THUNK opens
;;; (dk-project! CONCL NAME HYP)  -- ... where the opening is (mac-h NAME HYP)
;;;
;;; THE `have!' LANE, PACKAGED.  `mac-h', `slot-h', `ai', `sep-me' and
;;; `dk-split!' REPLACE the formula they open: the projection is landed and the
;;; hypothesis is GONE from that branch.  Three batch-12 agents lost a guard
;;; that way, and the failure is not where it happens -- a later `fact' whose
;;; antecedent was the destroyed guard lands its IMPLICATION silently, and the
;;; proof dies branches away (CLAUDE.md, "The tactics' real behaviour").
;;;
;;; The cure every one of them then wrote by hand is to do the opening inside a
;;; `have!' LANE: the side branch's context is a copy, so what `mac-h' consumes
;;; there is consumed there only, and the main branch keeps the hypothesis AND
;;; gains CONCL.  Five verbatim copies in the tree -- ulr--pos-parts! and
;;; ulr--from-ccint! (uniform-limit-regulated.scm), msub-pos-parts! and
;;; msub-ball-parts! (metric-subspace-laws.scm), bm-pos-parts!
;;; (bdd-metric-convergence.scm), rbm-pos-parts! (rake-bdd-metric.scm).
;;;
;;; In the lane: run the opener, `ai' every conjunction it landed, then `ass',
;;; then `prop' (both debt-free; `prop' is what a projection out of a three-way
;;; AND needs).  A lane that does not close is an ERROR, at the call.
;;; Returns the CONTEXT'S OWN copy of CONCL -- not the argument -- so the
;;; caller can hand it straight to `mac-h' / `detach!' / `dk-split!'.
;;; No-op, returning that same formula, when CONCL is already in context.
(define (dk-project! concl0 opener . opt)
  (let* ((concl (->raw-formula concl0))
         (open! (cond ((procedure? opener) opener)
                      ((and (symbol? opener) (pair? opt))
                       (let ((hyp (->raw-formula (car opt))))
                         (lambda ()
                           (mac-h opener (or (dk-ctx-form hyp)
                                             (error "dk-project!: the hypothesis is not in context"
                                                    (expression->string hyp)))))))
                      (#t (error "dk-project!: the opener is neither a THUNK nor a macete NAME with its HYPOTHESIS"
                                 opener)))))
    (if (not (dk-asm? concl))
        (dk-have! concl (lambda () (open!) (dk--lane-close!))))
    (or (dk-ctx-form concl)
        (error "dk-project!: the projection is not in the context after the lane"
               (expression->string concl)))))

;;; -----------------------------------------------------------------------
;;; (dk-pos-parts! E) -- with (POS-RR E) in context, land
;;;
;;;     (IN E RR)   (< 0 E)   (<= 0 E)   (NOT (= 0 E))
;;;
;;; and their conjunction (AND (IN E RR) (AND (<= 0 E) (NOT (= 0 E)))), which
;;; is what `ball-is-open' / `ball-center-in' are guarded on (`fact' will not
;;; split a conjunctive antecedent).  Returns that conjunction, as the context
;;; holds it.  (POS-RR E) SURVIVES, and so does (< 0 E).
;;;
;;; SIX COPIES, and five of them destroy something.  rko-pos-parts!
;;; (rake-open-sets.scm) unfolds the strict inequality with `mac-h', which
;;; CONSUMES (< 0 E) -- the very atom the next `ineq' or `rr-lt-*' citation
;;; wants; mcl-pos-parts! (metric-closure-laws.scm) noticed and cites
;;; rr-lt-of-pos-rr a SECOND time to put it back; bm-, rbm- and ulr- unfold
;;; POS-RR itself with `mac-h', which is the destruction CLAUDE.md names
;;; ("Get d in RR, 0 < d from POS-RR d by CITATION, never by mac-h 'pos-rr").
;;; Here the two atoms come by citation and only the SPLIT of (< 0 E) happens
;;; in a lane, so nothing in the main branch is consumed.
;;;
;;; Cites rr-pos-rr-in-rr and rr-lt-of-pos-rr (theorem-library/pos-rr-bridges),
;;; so a file using it must load after that one -- as dk-halve! already does.
(define (dk-pos-parts! e)
  (let* ((rr   (list 'IN e 'RR))
         (lt   (list '< 0 e))
         (le   (list '<= 0 e))
         (ne   (list 'NOT (list '= 0 e)))
         (both (list 'AND le ne))
         (conj (list 'AND rr both)))
    (if (not (dk-asm? rr)) (fact 'rr-pos-rr-in-rr e))
    (if (not (dk-asm? rr))
        (error "dk-pos-parts!: (IN e RR) did not land -- is (POS-RR e) in context?  e ="
               (expression->string e)))
    (if (not (dk-asm? lt)) (fact 'rr-lt-of-pos-rr e))
    (if (not (dk-asm? lt))
        (error "dk-pos-parts!: (< 0 e) did not land -- is (POS-RR e) in context?  e ="
               (expression->string e)))
    (if (not (and (dk-asm? le) (dk-asm? ne)))
        (begin
          (dk-project! both (lambda () (mac-h '< (dk-ctx-form lt))))
          (dk-split-all! (list (or (dk-ctx-form both) both)))))
    (if (not (dk-asm? conj)) (dk-have! conj))
    (or (dk-ctx-form conj)
        (error "dk-pos-parts!: the conjunction did not land for" (expression->string e)))))

;;; -----------------------------------------------------------------------
;;; (dk-read-off! THM ARG ...) -- cite the GUARDED value equation THM at the
;;; ARGs and rewrite the GOAL by the equation THAT LANDED.
;;;
;;; The shape is `fact' + `subst', and batch 12-D wrote it five times in one
;;; file (rake-completion-complete.scm: r12d-diag-at, rko2-dist-seq-at,
;;; r7q-dhat-sym, ...).  What it buys is not the two lines: it is that the
;;; `subst' is handed the CONTEXT'S equation rather than one the driver
;;; retyped.  A rebuilt term matches nothing and `subst' then no-ops silently,
;;; and a guarded equation is exactly where that bites -- the guard's discharge
;;; is what decides whether the detached equation is the one you wrote down.
;;;
;;; `subst' rewrites in the direction of its ARGUMENT, s -> t, and takes `=='
;;; as `='; the landed orientation is used.  Backwards is one line by hand:
;;; (let ((eq (dk-fact! 'thm ...))) (subst (list '= (caddr eq) (cadr eq)))).
;;; ERRORS when the citation lands no equation, and when the goal is unchanged
;;; -- the silent no-op this exists to make loud.  Returns the equation.
(define (dk-read-off! thm . args)
  (let ((eq (apply dk-fact! thm args)))
    (if (not (and (pair? eq) (memq (car eq) '(= ==)) (= (length eq) 3)))
        (error (string-append "dk-read-off!: " (symbol->string thm)
                              " did not land an equation -- it landed")
               (expression->string eq)))
    (let ((before (dk-goal)))
      (subst eq)
      (if (equal? (dk-goal) before)
          (error (string-append
                  "dk-read-off!: the equation did not rewrite the goal"
                  " (is the goal's term the LEFT side?  backwards is"
                  " (subst (list '= RHS LHS)))")
                 (expression->string eq)))
      eq)))

;;; -----------------------------------------------------------------------
;;; (detach-with! CH BODY) -- CH is an instantiation chain that stopped at an
;;; IMPLIES (its antecedent is not in context); prove that antecedent with
;;; BODY and detach.
;;;
;;; THE ANTECEDENT IS READ OFF CH, never rebuilt from the printed statement:
;;; that is the whole point, and it is why the two copies (rml-detach-with!,
;;; rake-matrix-laws.scm; rgc-detach-with!, rake-generates-coeff.scm -- line
;;; for line the same) each carry the comment.  `dk-apply!' does this when the
;;; antecedent is ALREADY in context; this is the case where it has to be
;;; proved first, and `fact' will not split a conjunctive one.
;;;
;;; Returns the detached consequent as the context holds it.  ERRORS when CH is
;;; not an implication, and when `detach!' lands nothing and the consequent is
;;; not in context either.
(define (detach-with! ch body)
  (if (not (and (pair? ch) (eq? (car ch) 'IMPLIES) (= (length ch) 3)))
      (error "detach-with!: not an implication" (expression->string ch)))
  (let ((ante (cadr ch))
        (conseq (caddr ch)))
    (have! ante body)
    (dk-focus-having! ante)
    (let ((new (dk-landed* (lambda () (detach! ch)))))
      (cond ((pair? new) (dk--deepest-of new))
            ((dk-ctx-form conseq))
            (#t (error "detach-with!: detach! landed nothing and the consequent is not in context"
                       (expression->string conseq)))))))


;;; =======================================================================
;;; BATCH 27-B (2026-09-24) -- THE KIT PASS.  The helpers batches 22-26 each
;;; wrote locally, and that the next agent copied.  Every one drives SURFACE
;;; tactics only, moves focus through `dk-focus!', and ERRORS rather than
;;; returning quietly on a miss.  Each has a suite check (test-suite.scm,
;;; "driver kit (batch 27-B)"), with a CONTROL on the old code where the item
;;; repairs a defect.  The local copies they replace are listed at each helper;
;;; retiring them is the integrator's.  Binders the helpers BUILD are spelled
;;; `dk?_' with a two-letter tag no predicate body and no statement uses (a
;;; driver-built binder that collides is RENAMED by subst-free, and every later
;;; lookup of the rebuilt term then misses, silently -- CLAUDE.md 2026-09-19).
;;; =======================================================================

;;; The first name of CANDIDATES occurring in none of TERMS; errors when all do.
(define (dk--fresh-binder candidates terms who)
  (or (find-first (lambda (v) (not (any (lambda (t) (dk-contains? t v)) terms)))
                  candidates)
      (error (string-append who ": every candidate binder occurs in the terms") candidates)))

;;; -----------------------------------------------------------------------
;;; (dk-cite! THM ARG ...) -- `dk-fact!' that RETURNS THE INSTANCE WHETHER IT
;;; LANDS OR IS ALREADY IN CONTEXT (item 9).  `fact' of an instance the context
;;; already holds lands nothing, and `dk-fact!' -- rightly strict, since landing
;;; nothing is usually the silent no-op -- then errors (25-B finding 6, 26-A 4d,
;;; 25-C 4d: re-citing nn-succ-plus-one).  Here the instance `fact' WOULD land
;;; is computed the way cmd-fact (proof-commands.scm) computes it: the leading
;;; universals instantiated at the ARGs one at a time by `subst-free', then
;;; every antecedent the context holds (up to alpha) or that is a true ground
;;; arithmetic sentence detached; the context's own copy is returned.  Errors
;;; when nothing landed and that instance is not in context either.
(define (dk--fact-instance thm terms)
  (let loop ((f (lookup-theorem thm)) (ts terms))
    (cond ((and (pair? f) (eq? (car f) 'FORALL) (pair? ts))
           (loop (subst-free (quantifier-var f) (car ts) (quantifier-body f)) (cdr ts)))
          ((and (pair? f) (eq? (car f) 'IMPLIES)
                (or (dk-asm? (cadr f)) (eq? #t (arith-eval-formula (cadr f)))))
           (loop (caddr f) ts))
          (#t f))))

(define (dk-cite! thm . args)
  (let* ((terms (map ->raw-formula args))
         (new   (dk-landed* (lambda () (apply fact thm terms)))))
    (if (pair? new)
        (dk--deepest-of new)
        (let ((want (dk--fact-instance thm terms)))
          (or (dk-ctx-form want)
              (error (string-append "dk-cite!: " (symbol->string thm)
                                    " landed nothing, and its instance is not in context")
                     (expression->string want)))))))

;;; -----------------------------------------------------------------------
;;; THE LANE AND ITS LEAF (item 5).  A tactic that closes its branch -- a beta
;;; whose reduced goal is in context, a `subst' that makes the goal an
;;; assumption -- moves the focus to a SIBLING, and the closer the driver wrote
;;; next then fires THERE (the focus drift, docs/batch8-2026-09-19.md 4.7).
;;; `dk--beta-done?' already asks "is THE LEAF I STARTED ON grounded"; this is
;;; that question for a whole lane:
;;;
;;;   (dk-lane THUNK)     -- a thunk that runs THUNK remembering the focus leaf
;;;                          it started on (nested lanes each remember their own)
;;;   (dk-lane-open?)     -- is that leaf still ungrounded?  (errors outside a lane)
;;;   (dk-lane-if! CLOSER) -- run CLOSER only while it is; return whether it is
;;;                          grounded afterwards
;;;
;;; so the `(if (not (sequent-node-grounded? ...)) (ass))' lines of the lfn-,
;;; rga-, lil- and cpsl- files become (dk-lane-if! ass).  Hand it to `dk-have!',
;;; `detach-with!' or `dk-chain!' as the lane body:
;;;   (dk-have! claim (dk-lane (lambda () (dk-lam-b!) (dk-lane-if! rfl))))
;;; MODEL: lil-lane / lil-goal-open? (line-int-laws.scm).
(define *dk-lane-leaf* #f)

(define (dk-lane thunk)
  (lambda ()
    (fluid-let ((*dk-lane-leaf* (proof-state-focus *ps*)))
      (thunk))))

(define (dk-lane-open?)
  (if (not *dk-lane-leaf*)
      (error "dk-lane-open?: not inside a dk-lane"))
  (not (sequent-node-grounded? *dk-lane-leaf*)))

(define (dk-lane-if! closer)
  (if (dk-lane-open?) (closer))
  (not (dk-lane-open?)))

;;; -----------------------------------------------------------------------
;;; (dk-chain! CH PROVERS) -- RUN AN IMPLICATION CHAIN TO ITS END (item 4).
;;; CH is what `fact' / `inst*!' / `dk-cite!' returned.  While it is an
;;; IMPLIES: an antecedent the context holds (up to alpha) is detached; any
;;; other is proved on a LANE by the first (PRED . THUNK) of PROVERS whose PRED
;;; accepts it -- or, when PROVERS is a procedure, by the thunk (PROVERS ANTE)
;;; returns -- and detached (`detach-with!').  The thunk runs inside `dk-lane'.
;;; A CH that is NOT an implication is returned as it is: `fact' auto-detaches
;;; every antecedent already in context, so on a second use the chain comes back
;;; as its bare consequent, and `detach-with!' then errors "not an implication"
;;; (25-C finding 5).  Returns the consequent as the context holds it.
;;; MODELS: pul-chain! (primitive-uniform-limit.scm), lil-chain!
;;; (line-int-laws.scm), dtr-chain! (det-rows.scm), daf-chain!
;;; (det-alternating-form.scm).
(define (dk--chain-prover provers ante)
  (let ((th (if (procedure? provers)
                (provers ante)
                (let ((pr (find-first (lambda (p) ((car p) ante)) provers)))
                  (and pr (cdr pr))))))
    (if (not (procedure? th))
        (error "dk-chain!: no prover accepts the antecedent" (expression->string ante)))
    th))

(define (dk-chain! ch provers)
  (let loop ((r ch))
    (if (and (pair? r) (eq? (car r) 'IMPLIES) (= (length r) 3))
        (let ((ante (cadr r)) (conseq (caddr r)))
          (if (dk-asm? ante)
              (let ((new (dk-landed* (lambda () (detach! (or (dk-ctx-form r) r))))))
                (loop (cond ((pair? new) (dk--deepest-of new))
                            ((dk-ctx-form conseq))
                            (#t (error "dk-chain!: detach! landed nothing"
                                       (expression->string r))))))
              (loop (detach-with! (or (dk-ctx-form r) r)
                                  (dk-lane (dk--chain-prover provers ante))))))
        (or (dk-ctx-form r) r))))

;;; -----------------------------------------------------------------------
;;; (dk-lam-type! TYPER [SET-CLOSER]) -- `lam-t' on the focus goal
;;; (IN (VNB-LAMBDA v A body) (FUN A B)), acting on the leaves THIS lam-t
;;; opened and nothing else (item 6).  The children are read off the inference
;;; lam-t added to the focus node -- never off a global before/after diff of
;;; the leaf list -- and each is handled only if it is ungrounded AND new:
;;;   * the sethood leaf (IN A SET): `dk-set-close!', or SET-CLOSER (a thunk);
;;;   * the pointwise typing leaf: TYPER, a thunk run with focus on it (goal
;;;     (FORALL v (IMPLIES (IN v A) (IN body B)))), which must ground it.
;;; A child hash-consing already GROUNDED needs nothing; a child hash-consed
;;; onto an ALREADY-OPEN sibling -- the same sequent, which the caller drives
;;; anyway -- is left to that sibling.  This REPAIRS dk-lam-t!, which diffs the
;;; leaf list and errors "lam-t left no typing goal" in both cases (25-A 4a:
;;; the first conjunct of IS-NORMALLY-CONVERGENT is the typing lam-t posts).
;;; Returns whether the focus node it started on is grounded (#f when a child
;;; was left to an open sibling).  Focus afterwards: wherever the last closer
;;; left it -- re-focus.  MODELS: cpsl-lam-t! (cc-power-series-laws.scm), the
;;; lam-t leaf loops of line-int-fundamental.scm and regulated-algebra.scm.
(define (dk-lam-type! typer . opt)
  (let* ((home   (proof-state-focus *ps*))
         (arrows (sequent-node-in-arrows home))
         (before (dk-open-leaves)))
    (lam-t)
    (let ((new-arrows (filter (lambda (a) (not (memq a arrows)))
                              (sequent-node-in-arrows home))))
      (if (not (= (length new-arrows) 1))
          (error "dk-lam-type!: lam-t did not fire on the focus goal"
                 (expression->string (dk-goal-of home))))
      (for-each
       (lambda (child)
         (if (and (not (sequent-node-grounded? child))
                  (not (memq child before))
                  (memq child (dk-open-leaves)))
             (let ((g (dk-goal-of child)))
               (dk-focus! child)
               (if (and (pair? g) (eq? (car g) 'IN) (eq? (caddr g) 'SET))
                   (if (pair? opt) ((car opt)) (dk-set-close! (cadr g)))
                   (typer))
               (if (not (sequent-node-grounded? child))
                   (error (if (dk-head-is? g 'IN)
                              "dk-lam-type!: the sethood leaf is still open"
                              "dk-lam-type!: TYPER left the typing leaf open")
                          (expression->string g))))))
       (inference-node-hypotheses (car new-arrows)))
      (sequent-node-grounded? home))))

;;; -----------------------------------------------------------------------
;;; (dk-absurd! PREMISE ...) -- close FALSITY from contradictory LINEAR
;;; premises, named by formula (item 7).  `ineq' declines a FALSITY goal even
;;; when its premises are contradictory, so: (< 0 0) is proved from them by
;;; `dk-ineq!' on a lane, and rr-lt-irrefl at 0 refutes it.  On any other goal
;;; this is `dk-ineq!' (the model's behaviour, which its callers rely on).
;;; Errors when the goal is not closed.  MODEL: cpsl-absurd!
;;; (cc-power-series-laws.scm); dtr-nn! / daf-nn! did the same through
;;; (<= 1 0) and `arith'.
(define (dk-absurd! . prems)
  (if (eq? (dk-goal) 'FALSITY)
      (let ((leaf (proof-state-focus *ps*)))
        (dk-have! '(< 0 0) (lambda () (apply dk-ineq! prems)))
        (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
        (let ((neg (dk-cite! 'rr-lt-irrefl 0)))
          (ai neg))
        (if (not (sequent-node-grounded? leaf))
            (error "dk-absurd!: FALSITY is still open after refuting (< 0 0)")))
      (apply dk-ineq! prems)))

;;; -----------------------------------------------------------------------
;;; (dk-nn! PREMISE ...) -- NN LINEAR ARITHMETIC BY LIFTING (item 3).  Close
;;; the focus goal -- an atom (<, <=, =) or its negation -- over natural
;;; numbers by `ineq'.  `ineq' works over RR and is POISONED by an atom it
;;; cannot certify (25-C finding 4): so every maximal non-arithmetic term t of
;;; the goal and of the named PREMISEs with (IN t NN) in context is lifted --
;;; (IN t RR) by nn-in-rr, (<= 0 t) by nn-zero-le, the latter passed as a
;;; premise -- and every (succ x) becomes x + 1 by nn-succ-plus-one (with
;;; (IN (succ x) RR) landed, so the equation is certifiable), also a premise.
;;; A negated goal is refuted: its atom is assumed and `dk-absurd!' closes
;;; FALSITY.  PREMISEs are formulas in context, as for `dk-ineq!'.
;;; MODELS: dtr-lift! / dtr-nn! (det-rows.scm), daf-lift! / daf-nn!
;;; (det-alternating-form.scm).
(define (dk--nn-leaves e acc)
  (cond ((number? e) acc)
        ((and (pair? e) (memq (car e) '(+ - * < <= = NOT AND)))
         (fold-left (lambda (a s) (dk--nn-leaves s a)) acc (cdr e)))
        ((and (pair? e) (eq? (car e) 'succ) (pair? (cdr e)))    ; lifted whole
         (if (member e acc) acc (cons e acc)))
        ((member e acc) acc)
        (#t (cons e acc))))

;; lift one term; return the premises it contributes.  (succ x) lifts x first.
(define (dk--nn-lift! t)
  (cond ((and (pair? t) (eq? (car t) 'succ))
         (let* ((x   (cadr t))
                (sub (dk--nn-lift! x)))
           (if (not (dk-asm? (list 'IN t 'NN))) (dk-cite! 'nn-succ-closed x))
           (if (not (dk-asm? (list 'IN t 'RR))) (dk-cite! 'nn-in-rr t))
           (cons (dk-cite! 'nn-succ-plus-one x) sub)))
        ((dk-asm? (list 'IN t 'NN))
         (if (not (dk-asm? (list 'IN t 'RR))) (dk-cite! 'nn-in-rr t))
         (list (dk-cite! 'nn-zero-le t)))
        (#t '())))

(define (dk-nn! . prems0)
  (let* ((prems (map ->raw-formula prems0))
         (g     (dk-goal))
         (neg?  (and (pair? g) (eq? (car g) 'NOT)))
         (atom  (if neg? (cadr g) g))
         (terms (reverse (fold-left (lambda (a f) (dk--nn-leaves f a)) '() (cons atom prems))))
         (extra (delete-duplicates (append-map dk--nn-lift! terms))))
    (if neg?
        (begin
          (dk-landed (lambda () (di)))
          (apply dk-absurd! (append prems extra (list atom))))
        (apply dk-ineq! (append prems extra)))))

;;; -----------------------------------------------------------------------
;;; (dk-crs-opaque! [TYPER]) -- `crs' ON A GOAL WITH recip OR A BINDER IN IT
;;; (item 2).  `crs' declines anything containing recip, and CLAUDE.md's
;;; recipe is "prove the identity with the coefficient QUANTIFIED, instantiate
;;; after".  Mechanised: every (recip ...) subterm and every maximal
;;; non-arithmetic subterm holding a VNB-LAMBDA -- the walk descends through
;;; binary + - * and power only -- becomes a fresh universally quantified REAL;
;;; the generalised identity is proved by `crs' on a lane and instantiated back
;;; at those subterms, which TYPER (a procedure of the term, landing (IN t RR);
;;; default: rr-recip-closed for a recip, `dk-real!' -- in-rr -- otherwise)
;;; types first, so the instantiation certifies them.  Over RR only.  With no such subterm this is `crs'.
;;; MODEL: tcl-crs! / tcl-recips (taylor-cluster.scm).
(define (dk--crs-opaques e)
  (let walk ((e e) (acc '()))
    (cond ((not (pair? e)) acc)
          ((and (memq (car e) '(+ - * power)) (= (length e) 3))
           (walk (caddr e) (walk (cadr e) acc)))
          ((or (eq? (car e) 'recip) (dk-contains? e 'VNB-LAMBDA))
           (if (member e acc) acc (append acc (list e))))
          (#t acc))))

(define (dk--replace e from to)
  (cond ((equal? e from) to)
        ((pair? e) (map (lambda (s) (dk--replace s from to)) e))
        (#t e)))

;;; The default TYPER: (recip u) by rr-recip-closed, from (IN u RR) and
;;; (NOT (= u 0)) -- which must be in context: `in-rr' does not derive it --
;;; anything else by `dk-real!'.
(define (dk--crs-real! t)
  (if (and (pair? t) (eq? (car t) 'recip) (pair? (cdr t)))
      (let* ((u   (cadr t))
             (typ (list 'IN t 'RR))
             (nz  (list 'NOT (list '= u 0))))
        (if (not (dk-asm? typ))
            (begin
              (if (not (dk-asm? nz))
                  (error "dk-crs-opaque!: to type a recip the context must hold" (expression->string nz)))
              (dk-real! u)
              (dk-have! (list 'AND (list 'IN u 'RR) nz) (lambda () (dk-conj-close! ass)))
              (dk-cite! 'rr-recip-closed u)
              (if (not (dk-asm? typ))
                  (error "dk-crs-opaque!: rr-recip-closed did not land" (expression->string typ)))))
        typ)
      (dk-real! t)))

(define (dk-crs-opaque! . opt)
  (let* ((typer (if (pair? opt) (car opt) dk--crs-real!))
         (g     (dk-goal))
         (rs    (if (memq (car g) '(= ==))
                    (let ((r1 (dk--crs-opaques (cadr g))))
                      (append r1 (filter (lambda (r) (not (member r r1)))
                                         (dk--crs-opaques (caddr g)))))
                    (dk--crs-opaques g))))
    (if (null? rs)
        (crs)
        (let* ((pool (filter (lambda (v) (not (dk-contains? g v)))
                             '(dkca_ dkcb_ dkcc_ dkcd_ dkce_ dkcf_ dkcg_ dkch_
                               dkci_ dkcj_ dkck_ dkcl_)))
               (vs   (if (> (length rs) (length pool))
                           (error "dk-crs-opaque!: more opaque subterms than fresh names"
                                  (length rs))
                           (list-head pool (length rs))))
               (g2   (let loop ((g g) (rs rs) (vs vs))
                       (if (null? rs) g (loop (dk--replace g (car rs) (car vs))
                                              (cdr rs) (cdr vs)))))
               (univ (let loop ((vs (reverse vs)) (body g2))
                       (if (null? vs) body
                           (loop (cdr vs)
                                 (list 'FORALL (car vs)
                                       (list 'IMPLIES (list 'IN (car vs) 'RR) body))))))
               (leaf (proof-state-focus *ps*)))
          (for-each typer rs)
          (dk-have! univ (lambda () (dk-peel!) (crs)))
          (apply dk-apply! (dk-ctx-form univ) rs)
          (if (not (sequent-node-grounded? leaf)) (ass))
          (if (not (sequent-node-grounded? leaf))
              (error "dk-crs-opaque!: the instance did not close the goal"
                     (expression->string g)))))))

;;; -----------------------------------------------------------------------
;;; (dk-fun-ext! LHS RHS DOM COD TYPE-L TYPE-R PTWISE) -- FUNCTION
;;; EXTENSIONALITY AT THE POINT OF USE (item 1).  Lands (= LHS RHS), both
;;; members of FUN(DOM, COD) (COD #f: of FUN(DOM)), by
;;; fun-domain-extensionality.  TYPE-L / TYPE-R are thunks proving the two
;;; typings (#f: they are in context); the FUN(DOM) typings the theorem wants
;;; are read off by fun-codomain-iff on a lane, so the hypotheses survive.
;;; PTWISE is a procedure of the eigenvariable v proving (= (LHS v) (RHS v)).
;;; THE POINTWISE UNIVERSAL IS PROVED UNDER A FRESH BINDER occurring in
;;; neither side, then detached up to alpha: the theorem's own binder is `x',
;;; which every polynomial term binds too; `di' keeps the name and a later beta
;;; substitutes x under an inner binder x -- capture-renaming, "symbol x is
;;; both bound and free", and a lookup that silently misses (25-B finding 2).
;;; When (= LHS RHS) is the focus goal it is closed (see `dk-have!').
;;; Returns the equation as the context holds it, or #t when it closed the goal.
;;; MODEL: tcl-ext! / tcl-fun-dom! (taylor-cluster.scm).
(define (dk--fun-dom! f dom cod)
  (dk-have! (list 'IN f (list 'FUN dom))
    (lambda ()
      (mac-h 'fun-codomain-iff (dk-ctx-form (list 'IN f (list 'FUN dom cod))))
      (dk-split-all!)
      (ass))))

(define (dk-fun-ext! lhs rhs dom cod type-l type-r ptwise)
  (let* ((eqn  (list '= lhs rhs))
         (zv   (dk--fresh-binder '(dkxa_ dkxb_ dkxc_ dkxd_ dkxe_ dkxf_) (list lhs rhs dom)
                                 "dk-fun-ext!"))
         (fa   (list 'FORALL zv (list 'IMPLIES (list 'IN zv dom)
                                      (list '= (list lhs zv) (list rhs zv)))))
         (r    (dk-have! eqn
                 (lambda ()
                   (let ((cls (lambda (f) (if cod (list 'FUN dom cod) (list 'FUN dom)))))
                     (dk-have! (list 'IN lhs (cls lhs)) type-l)
                     (dk-have! (list 'IN rhs (cls rhs)) type-r))
                   (if cod (begin (dk--fun-dom! lhs dom cod) (dk--fun-dom! rhs dom cod)))
                   (dk-have! fa (lambda () (ptwise (dk-di-var!))))
                   (let ((ch (dk-cite! 'fun-domain-extensionality dom lhs rhs)))
                     (if (and (pair? ch) (eq? (car ch) 'IMPLIES)) (detach! ch)))
                   (ass)))))
    (if (eq? r #t) #t (or (dk-ctx-form eqn) (error "dk-fun-ext!: the equation did not land"
                                                    (expression->string eqn))))))

;;; -----------------------------------------------------------------------
;;; (dk-congr! EQ TEMPLATE [REL]) -- THE CONGRUENCE STEP (item 10): from the
;;; equation EQ = (= A B) in context (either orientation), land
;;; (REL (TEMPLATE A) (TEMPLATE B)); TEMPLATE is a procedure of a term, REL
;;; '= (default) or '==.  `subst' cannot do it directly when one side CONTAINS
;;; the other (H = BORDER(1, SUBMAT(H))): it rewrites every occurrence,
;;; including the one inside.  So on a lane the CONTAINING side is rewritten to
;;; the contained one -- (subst (= B A)) when B contains A, else (subst (= A
;;; B)) -- which makes both sides of the claim one term, closed by `rfl' (`='
;;; certifies definedness: type the term first) or `qrfl' (`==').  The kernel
;;; has no congruence rule for `='; apply-congruence-2 is a THEOREM about
;;; applications of a registered constant, not this.  Returns the claim as the
;;; context holds it, or #t when it closed the focus goal.  MODEL: the
;;; "(subst B -> H) then rfl" lanes of det-alternating-form.scm (26-B 3).
(define (dk-congr! eq0 template . opt)
  (let* ((eq   (->raw-formula eq0))
         (rel  (if (pair? opt) (car opt) '=))
         (a    (cadr eq))
         (b    (caddr eq))
         (claim (list rel (template a) (template b))))
    (if (not (and (pair? eq) (memq (car eq) '(= ==)) (= (length eq) 3)))
        (error "dk-congr!: not an equation" (expression->string eq)))
    (if (not (or (dk-asm? eq) (dk-asm? (list (car eq) b a))))
        (error "dk-congr!: the equation is not in context" (expression->string eq)))
    (let ((r (dk-have! claim
               (dk-lane
                (lambda ()
                  (if (not (equal? a b))
                      (subst (if (dk--occurs? a b) (list '= b a) (list '= a b))))
                  (dk-lane-if! (if (eq? rel '==) qrfl rfl)))))))
      (if (eq? r #t) #t
          (or (dk-ctx-form claim)
              (error "dk-congr!: the claim did not land" (expression->string claim)))))))

;;; -----------------------------------------------------------------------
;;; (dk-abstract! DOM COD BODY-OF TYPER) -- A FAMILY AS A FUNCTION SYMBOL
;;; (item 8).  BODY-OF is a procedure of the index term.  Proves
;;;   exists G. G in FUN(DOM, COD) and forall k in DOM. G(k) == BODY-OF(k)
;;; with the witness VNB-LAMBDA(k, DOM, BODY-OF(k)), skolemises it, and returns
;;; (G . VALUE-EQUATION), the universal as the context holds it.  G applied at
;;; an index is NEVER a redex, so a family used inside a sequence -- G(k)(x)
;;; under vnb-lambda(k, nn, ...) -- needs no beta under the binder, where the
;;; owed argument typing is unprovable (22-B finding 3: the clamped family
;;; EXTEND-CONST(g_k, a, b) and the Caratheodory witnesses).  Rewrite G(k) away
;;; at a TYPED index with (subst (dk-apply! VALUE-EQUATION k)).  TYPER is a
;;; procedure of the eigenvariable k proving (IN (BODY-OF k) COD), with
;;; (IN k DOM) in context; DOM's sethood is closed by `dk-set-close!'.
;;; MODEL: pul-clamped! (primitive-uniform-limit.scm).
(define (dk-abstract! dom cod body-of typer)
  (let ((probe (body-of 'dkaj_)))
    (if (or (dk-contains? probe 'dkak_) (dk-contains? probe 'dkag_)
            (dk-contains? dom 'dkak_) (dk-contains? cod 'dkag_))
        (error "dk-abstract!: the family already uses the binders dkak_ / dkag_"
               (expression->string probe))))
  (let* ((body  (body-of 'dkak_))
         (lam   (list 'VNB-LAMBDA 'dkak_ dom body))
         (vals  (lambda (g) (list 'FORALL 'dkak_ (list 'IMPLIES (list 'IN 'dkak_ dom)
                                                    (list '== (list g 'dkak_) body)))))
         (claim (list 'FORSOME 'dkag_ (list 'AND (list 'IN 'dkag_ (list 'FUN dom cod))
                                            (vals 'dkag_)))))
    (dk-have! claim
      (lambda ()
        (ew lam)
        (dk-conj-close!
          (lambda ()
            (if (dk-head-is? (dk-goal) 'IN)
                (dk-lam-type! (lambda () (typer (dk-di-var!))))
                (begin (dk-di-var!)
                       (if (not (dk-lam-b!)) (qrfl))))))))
    (let* ((g  (dk-skolem! (or (dk-ctx-form claim)
                               (error "dk-abstract!: the existential did not land"))))
           (ve (or (dk-ctx-form (vals g))
                   (error "dk-abstract!: the value equation did not land"
                          (expression->string (vals g))))))
      (cons g ve))))

;;; -----------------------------------------------------------------------
;;; (dk-name! T) / (dk-name! T CLASS) -- NAME A TERM AS A FRESH SYMBOL (batch 40,
;;; 2026-09-28).  Proves  exists v in CLASS. v = T  (CLASS defaults to RR) with
;;; the witness T -- its conjuncts close by `ass' (the typing (IN T CLASS) must
;;; ALREADY be in context) and `rfl' (which the typing certifies DEFINED) --
;;; skolemises it, and returns the fresh symbol v, with (IN v CLASS) and
;;; (= v T) landed.  The cure for `ineq' dropping a premise that is not linear
;;; (a compound product, a cubic) and then blaming the goal: name the product,
;;; state what is known of it about the NAME, and hand `dk-ineq!' the equation
;;; (= v T) as a premise.  The claim goes through `dk-have!' (an existential
;;; already in context is not proved twice) and the binder `dknv_' is used by no
;;; predicate body.  Errors, before any step, when T is not typed in CLASS in
;;; context: type it first.  MODELS (verbatim copies, retired): cpsl-name!
;;; (cc-power-series-laws.scm), clh-name! (cc-log-holomorphic.scm).
(define (dk-name! t0 . opt)
  (let* ((t      (->raw-formula t0))
         (cls    (if (pair? opt) (->raw-formula (car opt)) 'RR))
         (typing (list 'IN t cls))
         (ex     (list 'FORSOME 'dknv_ (list 'AND (list 'IN 'dknv_ cls) (list '= 'dknv_ t)))))
    (if (or (dk-contains? t 'dknv_) (dk-contains? cls 'dknv_))
        (error "dk-name!: the term already uses the binder dknv_" (expression->string t)))
    (if (not (dk-asm? typing))
        (error "dk-name!: the term is not typed -- type it first; not in context:"
               (expression->string typing)))
    (dk-have! ex
      (lambda ()
        (ew t)
        (dk-conj-close! (lambda () (if (dk-head-is? (dk-goal) '=) (rfl) (ass))))))
    (dk-skolem! (or (dk-ctx-form ex)
                    (error "dk-name!: the existential did not land" (expression->string ex))))))

;;; -----------------------------------------------------------------------
;;; (iff-for LHS) -- the context's IFF whose left-hand side is LHS (up to
;;; alpha), as the context holds it (item 15).  `fact' of a membership IFF
;;; lands BOTH the instance and the universal, and `dk-deepest' cannot tell
;;; them apart (neither contains the other); a RECONSTRUCTED instance matches
;;; nothing.  Errors, listing the IFFs in context, when none matches.
;;; MODELS (verbatim copies): r5u-iff-for (rake-combinatorics2.scm), r7t-
;;; (rake-finsum-cm-union.scm), r7s- (rake-sum-set-defined.scm), r12e-
;;; (rake-prod-of-sums.scm), r7m- (rake-finsum-union.scm), rkp-
;;; (rake-combinatorics.scm), r6g- (rake-choose-succ.scm), psd-iff-for
;;; (rake-prod-set-defined.scm).
(define (iff-for lhs0)
  (let* ((lhs  (->raw-formula lhs0))
         (iffs (filter (dk-head? 'IFF) (dk-asms))))
    (or (find-first (lambda (f) (eq? #t (vnb-guard (lambda () (alpha-equiv? (cadr f) lhs)))))
                    iffs)
        (error "iff-for: no IFF in context has the left-hand side"
               (expression->string lhs)
               (map expression->string iffs)))))

;;; -----------------------------------------------------------------------
;;; THE IF RESOLVER (item 15).  `if-true' / `if-false' open TWO leaves -- the
;;; CONDITION, and the MAIN goal with (= IFT branch) ASSUMED; the goal is NOT
;;; rewritten -- and the copies below each discriminated them, closed the
;;; condition, and `subst'ed the equation by hand.
;;;
;;; (dk-if-branch! TRUE? IFT CLOSE-COND K) -- resolve the (IF c a b) term IFT
;;; on the side TRUE? names: CLOSE-COND (a thunk; #f means `ass') closes the
;;; condition leaf -- c, or (NOT c) -- which must then be GROUNDED; the main
;;; leaf gets (subst (= IFT branch)) and K (a thunk) runs on it.  The leaves
;;; are told apart by the GOAL, never by where focus lands; a condition leaf
;;; that hash-consing had already grounded is not opened at all, and that is
;;; success.
;;; (dk-case-if! IFT K) -- split on IFT's condition with `use-em' and resolve
;;; it on both branches; K is called as (K TRUE? BRANCH-VALUE) on each.
;;; MODELS: dtr-if-branch! / dtr-case-if! (det-rows.scm), daf-if-branch! /
;;; daf-case-if! (det-alternating-form.scm), rkd-if-branch! (rake-identmat.scm),
;;; rsa-if! (regulated-step-approx.scm), rpl-if-close! (regulated-primitive-
;;; laws.scm), pul-if-close! (primitive-uniform-limit.scm).
(define (dk-if-branch! true? ift close-cond k)
  (if (not (and (pair? ift) (eq? (car ift) 'IF) (= (length ift) 4)))
      (error "dk-if-branch!: not an (IF c a b) term" (expression->string ift)))
  (let* ((c      (cadr ift))
         (val    (if true? (caddr ift) (cadddr ift)))
         (want   (if true? c (list 'NOT c)))
         (opened (dk-opened (lambda () (if true? (if-true ift) (if-false ift)))))
         (conds  (filter (lambda (l) (eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal-of l) want)))))
                         opened))
         (mains  (filter (lambda (l) (not (memq l conds))) opened)))
    (if (not (and (<= (length conds) 1) (= 1 (length mains))))
        (error "dk-if-branch!: expected one condition leaf and one main leaf, got"
               (map (lambda (l) (expression->string (dk-goal-of l))) opened)))
    (if (pair? conds)
        (begin
          (dk-focus! (car conds))
          (if close-cond (close-cond) (ass))
          (if (not (sequent-node-grounded? (car conds)))
              (error "dk-if-branch!: the condition is not established" (expression->string want)))))
    (dk-focus! (car mains))
    (subst (list '= ift val))
    (k)))

(define (dk-case-if! ift k)
  (use-em (cadr ift)
    (lambda () (dk-if-branch! #t ift #f (lambda () (k #t (caddr ift)))))
    (lambda () (dk-if-branch! #f ift #f (lambda () (k #f (cadddr ift)))))))


;;; =======================================================================
;;; NOTES-37 (2026-09-24).  type-term / dk-type! and ew-poly.
;;;
;;; The user's goal  x in ZZ, y in ZZ |- forsome([a in ZZ], (x + y)^3 = x^3 + y*a)
;;; met nothing that would move: `crs' declines an existential (correctly), and
;;; once the witness had been supplied by hand the TYPING leaf
;;; 3 * x^2 + (3 * (x * y) + y^2) in ZZ had no closer -- `in-rr' stopped at the
;;; power (no branch for `power' in any class, and no ZZ / QQ / NN power law in
;;; the library), `fact zz-mul-closed' lands an implication whose conjunctive
;;; antecedent `fact' will not split, and `from-context!' / `arith' decline.
;;;
;;; Two commands, both DRIVERS over surface commands (the model is `prop':
;;; decide purely first, then discharge through ordinary recorded steps, and on
;;; a decline leave the proof exactly as it was).  Neither adds a kernel rule, a
;;; support or a stamp; neither records a step of its own.  The page of a proof
;;; that uses them carries the steps they took (cut / fact / ass / subst / crs /
;;; ew / di / focus-id), which is what makes it re-runnable.
;;; =======================================================================

;;; -----------------------------------------------------------------------
;;; A TRANSACTION.  Run THUNK (quietly, errors caught); keep its effects only
;;; when it returns true.  Otherwise put back the graph, the focus, the script,
;;; the mint record, the live trace, the undo stack and the hidden citations --
;;; everything a recorded step writes -- so the proof is as it was.  The
;;; eigenvariable counter is not restored (it is monotonic by design, see
;;; `backup-one').  Works under a what-now probe too: it reads the graph mark
;;; directly, where `vnb--take-mark' returns #f while *replaying?* is bound.
(define (dk--transaction thunk)
  (let* ((ps     *ps*)
         (dgm    (dg-take-mark (proof-state-dg ps)))
         (focus  (proof-state-focus ps))
         (script *proof-script*)
         (mints  *proof-mints*)
         (fmark  *fresh-mark-at-last-record*)
         (trace  *live-trace*)
         (undo   *vnb-undo-stack*)
         (hidden *proof-hidden-citations*)
         (r      (dk--silently (lambda () (quietly thunk)))))
    (or r
        (begin
          (dg-rollback! dgm)
          (set! *ps* ps)
          (set-proof-state-focus! ps focus)
          (set! *proof-script* script)
          (set! *proof-mints* mints)
          (set! *fresh-mark-at-last-record* fmark)
          (set! *live-trace* trace)
          (set! *vnb-undo-stack* undo)
          (set! *proof-hidden-citations* hidden)
          #f))))

;;; -----------------------------------------------------------------------
;;; type-term -- close (IN t C), C one of NN ZZ QQ RR CC, by the carrier's
;;; closure laws, bottom-up over t.
;;;
;;; THE PLAN FIRST.  `type-term--plan' is PURE: it reads the focus context and
;;; the theorem table and returns a tree saying how each subterm will be typed,
;;; or #f.  Nothing is run unless the whole tree exists, so a decline changes
;;; nothing.  A plan node is one of
;;;
;;;   (ctx  TYP)                       TYP is already in context
;;;   (num  TYP)                       a numeral: `arith' decides it
;;;   (leaf TYP)                       an atom or an application: in-rr's own
;;;                                    leaf cases (the inclusion bridge NN -> ZZ
;;;                                    -> QQ -> RR -> CC, CCINT -> RR, ...; f(a)
;;;                                    with f in FUN(A, C))
;;;   (law  TYP KIDS THM ARGS CONJ)    cite THM at ARGS; CONJ, when not #f, is
;;;                                    the conjunctive antecedent to land first
;;;                                    (`fact' will not split one)
;;;   (eq   TYP KIDS E)                no law for this head in C: land the
;;;                                    typing of an equal term E built from heads
;;;                                    that have one, prove t = E by `crs', and
;;;                                    rewrite by it
;;;
;;; The `eq' route is what types a POWER in ZZ, QQ or NN: there is no power
;;; law in those classes, but x^3 = x * (x * x) is a commutative-ring identity
;;; and x * (x * x) is two citations of the multiplication law.  It also types
;;; the flat n-ary + and * of the parser (nested to binary), subtraction in QQ
;;; (a - b = a + (-b): QQ has no subtraction law), and the bridge heads
;;; binplus / bintimes / binneg.  NN has no negation, so a `-' in NN declines.
;;;
;;; RR and CC powers cite power-real-closed / power-typing-nonneg, so a
;;; non-numeral exponent n in NN is fine there; in ZZ / QQ / NN the exponent
;;; must be a numeral.  Division and recip decline.
(define *type-term-classes* '(NN ZZ QQ RR CC))

(define (type-term--thm name)
  (and (hash-table-ref/default *theorem-table* name #f) name))

(define (type-term--numeral-ok? n C)
  (and (number? n) (exact? n) (rational? n)
       (cond ((eq? C 'NN) (and (integer? n) (>= n 0)))
             ((eq? C 'ZZ) (integer? n))
             ((memq C '(QQ RR CC)) #t)
             (#t #f))))

;;; Is T (IN _ D) for a ring domain D in the focus context?  (What `crs'
;;; demands of a generator: ring-vars-ok?, ring-simplify.scm.)
(define (type-term--ring-typed? t)
  (any (lambda (a) (and (pair? a) (eq? (car a) 'IN) (= (length a) 3)
                        (equal? (cadr a) t) (ring-domain? (caddr a))))
       (dk-asms)))

;;; A leaf in-rr can close: an inclusion route from the class the context types
;;; it in, or an application f(a) with f in FUN(A, C) and a typable in A.
(define (type-term--leaf-ok? t C)
  (or (let* ((K     (in-rr--ctx-class t))
             (head  (cond ((pair? K) (car K)) ((symbol? K) K) (#t #f)))
             (route (and head (not (eq? head C)) (in-rr--inclusion-route head C))))
        (and route (every type-term--thm route) #t))
      (and (pair? t) (= (length t) 2) (not (memq (car t) '(- power)))
           (let ((dom (in-rr--fun-dom (car t) C)))
             (and dom (type-term--plan (cadr t) dom) #t)))))

(define (type-term--nest op xs)          ; right-nested binary op over XS
  (if (null? (cdr xs)) (car xs) (list op (car xs) (type-term--nest op (cdr xs)))))

(define (type-term--nest-left op xs)     ; left-nested: a - b - c = (a - b) - c
  (let loop ((acc (car xs)) (rest (cdr xs)))
    (if (null? rest) acc (loop (list op acc (car rest)) (cdr rest)))))

(define (type-term--product b k)          ; b * (b * ... ), k >= 0 factors
  (cond ((= k 0) 1)
        ((= k 1) b)
        (#t (list '* b (type-term--product b (- k 1))))))

;;; The `eq' route: TYP, KIDS = the plan of E plus a plan for every generator
;;; `crs' will read off t = E that the context does not already type in a ring
;;; domain.  #f when any of them cannot be planned.
(define (type-term--eq-plan t C E)
  (let ((pe (type-term--plan E C))
        (gens (cvnb-eq-source-generators (cvnb-expand-pow t) (cvnb-expand-pow E))))
    (and pe
         (let loop ((gs gens) (acc '()))
           (cond ((null? gs) (list 'eq (list 'IN t C) (append acc (list pe)) E))
                 ((type-term--ring-typed? (car gs)) (loop (cdr gs) acc))
                 (#t (let ((pg (type-term--plan (car gs) C)))
                       (and pg (loop (cdr gs) (append acc (list pg)))))))))))

(define (type-term--law-plan t C thm args classes conj?)
  (let ((kids (map type-term--plan args classes)))
    (and thm (every (lambda (k) k) kids)
         (list 'law (list 'IN t C) kids thm args
               (and conj?
                    (list 'AND (list 'IN (car args) (car classes))
                          (list 'IN (cadr args) (cadr classes))))))))

(define (type-term--plan t C)
  (let ((typ (list 'IN t C)))
    (cond
      ((dk-asm? typ) (list 'ctx typ))
      ((not (memq C *type-term-classes*))
       (and (type-term--leaf-ok? t C) (list 'leaf typ)))
      ((number? t) (and (type-term--numeral-ok? t C) (list 'num typ)))
      ((symbol? t) (and (type-term--leaf-ok? t C) (list 'leaf typ)))
      ((not (pair? t)) #f)
      (#t
       (let* ((h (car t)) (args (cdr t)) (n (length args)))
         (cond
           ;; + and * : the binary law, or nest a flat node
           ((and (memq h '(+ *)) (= n 2))
            (type-term--law-plan t C (in-rr--closure-thm h C 2) args (list C C) #t))
           ((and (memq h '(+ *)) (> n 2))
            (type-term--eq-plan t C (type-term--nest h args)))
           ;; unary minus
           ((and (eq? h '-) (= n 1))
            (type-term--law-plan t C (in-rr--closure-thm '- C 1) args (list C) #f))
           ;; subtraction: the law (curried), else a + (-b)
           ((and (eq? h '-) (= n 2) (in-rr--closure-thm '- C 2))
            (type-term--law-plan t C (in-rr--closure-thm '- C 2) args (list C C) #f))
           ((and (eq? h '-) (= n 2) (in-rr--closure-thm '- C 1))
            (type-term--eq-plan t C (list '+ (car args) (list '- (cadr args)))))
           ((and (eq? h '-) (> n 2))
            (type-term--eq-plan t C (type-term--nest-left '- args)))
           ;; the bridge heads, back to the surface
           ((and (memq h '(binplus bintimes)) (= n 2))
            (type-term--eq-plan t C (cons (if (eq? h 'binplus) '+ '*) args)))
           ((and (eq? h 'binneg) (= n 1))
            (type-term--eq-plan t C (list '- (car args))))
           ;; powers
           ((and (eq? h 'power) (= n 2))
            (let ((b (car args)) (k (cadr args)))
              (cond
                ((and (eq? C 'RR) (type-term--thm 'power-real-closed))
                 (type-term--law-plan t C 'power-real-closed args (list 'RR 'NN) #f))
                ((and (eq? C 'CC) (type-term--thm 'power-typing-nonneg))
                 (type-term--law-plan t C 'power-typing-nonneg args (list 'CC 'NN) #t))
                ((and (number? k) (exact? k) (integer? k) (>= k 0))
                 (type-term--eq-plan t C (type-term--product b k)))
                (#t #f))))
           ;; anything else is a leaf or nothing
           (#t (and (type-term--leaf-ok? t C) (list 'leaf typ)))))))))

;;; Carry out a plan: land its typing in the focus context (on the MAIN branch,
;;; each subterm's typing proved in its own `dk-have!' lane so the lane's
;;; citations stay out of the main context), or, when the typing IS the focus
;;; goal, prove it in place (`dk-have!' does that).  Returns the typing.
(define (type-term--exec! p)
  (let ((kind (car p)) (typ (cadr p)))
    (cond
      ((dk-asm? typ) typ)
      ((eq? kind 'ctx) typ)
      ((eq? kind 'num) (dk-have! typ) typ)
      ((eq? kind 'leaf) (dk-have! typ (lambda () (in-rr--close!))) typ)
      ((eq? kind 'law)
       (let ((kids (list-ref p 2)) (thm (list-ref p 3))
             (args (list-ref p 4)) (conj (list-ref p 5)))
         (for-each type-term--exec! kids)
         (dk-have! typ (lambda ()
                         (if conj (dk-have! conj))
                         (apply fact thm args)
                         (ass)))
         typ))
      ((eq? kind 'eq)
       (let* ((kids (list-ref p 2)) (E (list-ref p 3))
              (eqn  (list '= (cadr typ) E)))
         (for-each type-term--exec! kids)
         (dk-have! typ (lambda ()
                         (dk-have! eqn (lambda () (crs)))
                         (subst eqn)
                         (ass)))
         typ))
      (#t (error "type-term--exec!: unknown plan node" p)))))

;;; Close the FOCUS goal (IN T C) by PLAN, transactionally.  #t when closed.
(define (type-term--close-with! plan)
  (let ((leaf (proof-state-focus *ps*)))
    (dk--transaction
     (lambda ()
       (if (dk-asm? (cadr plan)) (ass) (type-term--exec! plan))
       (sequent-node-grounded? leaf)))))

;;; The hook `in-rr' calls on a head it has no branch for (interactive.scm).
(define (type-term--close-focus! t C)
  (let ((plan (type-term--plan t C)))
    (and plan (type-term--close-with! plan))))

(define (type-term--decline! msg . irritants)
  (vnb--print-warning
   (apply string-append "type-term: " msg
          (map (lambda (x) (string-append " " (expression->string x))) irritants)))
  #f)

;;; (type-term) -- the surface command.
;;;
;;; ANY CLASS (batch 41, 2026-09-28; the user: "Typing issue? Got you covered --
;;; type-term").  The command used to refuse a class other than NN ZZ QQ RR CC before
;;; asking the planner, although the planner has a route for any class: the context
;;; (an inclusion NN in ZZ in ... from a subclass typing), and an application f(a) with
;;; f in FUN(A, C) in context and a typable in A -- recursively, so f(3 * x + 1) in B
;;; is typed from f in fun(zz, B) and x in zz.  The gate is gone: the planner is asked
;;; on every membership goal and the command declines only when there is no plan.  A
;;; closure law is still sought only in a number class (type-term--plan's own branch).
(define (type-term)
  (let ((g (and (proof-state? *ps*) (not (proof-done? *ps*)) (dk-goal))))
    (cond
      ((not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)))
       (type-term--decline! "the goal is not a membership (IN t C)"))
      (#t
       (let ((plan (type-term--plan (cadr g) (caddr g))))
         (cond
           ((and (not plan) (not (memq (caddr g) *type-term-classes*)))
            (type-term--decline!
             "no typing: the class is not a number class, and neither the context (a typing in a subclass) nor an application f(a) with f in FUN(A, C) in context and a typable in A types the term:"
             g))
           ((not plan)
            (type-term--decline!
             "no typing: an atom is not typed in the class or a subclass, or an operation has no closure law there (NN has no minus; ZZ/QQ/NN powers need a numeral exponent; / and recip are not handled):"
             g))
           ((type-term--close-with! plan) (show) #t)
           (#t (type-term--decline! "the plan did not close the goal; nothing changed:" g))))))))

;;; (dk-type! T [C]) -- the kit twin: land (IN T C) (C defaults to RR) in the
;;; focus context, or close the focus goal when that is it; return the typing.
;;; ERRORS when no plan exists (the kit's rule: a miss is an error, not #f).
(define (dk-type! t . opt)
  (let* ((C (if (pair? opt) (car opt) 'RR))
         (typ (list 'IN t C)))
    (if (dk-asm? typ)
        typ
        (let ((plan (type-term--plan t C)))
          (if (not plan) (error "dk-type!: no typing plan for" (expression->string typ)))
          (type-term--exec! plan)
          typ))))

;;; -----------------------------------------------------------------------
;;; ew-poly -- an existential whose witness a polynomial DIVISION computes.
;;;
;;; Goal (FORSOME a (AND (IN a C) (= L R))) or (FORSOME a (= L R)), with `a'
;;; occurring exactly once in L = R and L - R, in the sum-of-monomials normal
;;; form of comm-ring-simplify (ZZ[generators], a among them), of degree at
;;; most one in a: L - R = A*a + B.  The witness is -B / A, by exact division
;;; of polynomials (grlex order; the division is exact iff the leading monomial
;;; of the divisor divides the leading monomial of every remainder).  Declines
;;; when a occurs other than once, a side is not a polynomial, the degree in a
;;; exceeds one, A is 0, the division leaves a remainder, or (C in ZZ or NN, or
;;; no guard) a quotient coefficient is not an integer.  Then: `ew' the witness
;;; rebuilt as a surface term (+ - * ^, highest degree first), `di' the AND,
;;; `type-term' the typing leaf, `crs' the identity.  Every step is checked
;;; before anything runs; the run is transactional besides.

;;; grlex, generators ordered by gen<? (the smaller the more significant).
(define (ew-poly--mono>? w1 w2)
  (let ((l1 (length w1)) (l2 (length w2)))
    (cond ((> l1 l2) #t)
          ((< l1 l2) #f)
          (#t (let loop ((a w1) (b w2))
                (cond ((null? a) #f)
                      ((equal? (car a) (car b)) (loop (cdr a) (cdr b)))
                      (#t (gen<? (car a) (car b)))))))))

(define (ew-poly--lead p)
  (let loop ((best (car p)) (rest (cdr p)))
    (cond ((null? rest) best)
          ((ew-poly--mono>? (caar rest) (car best)) (loop (car rest) (cdr rest)))
          (#t (loop best (cdr rest))))))

;;; W / D as multisets (both sorted), or #f when D does not divide W.
(define (ew-poly--mono-div w d)
  (cond ((null? d) w)
        ((null? w) #f)
        ((equal? (car w) (car d)) (ew-poly--mono-div (cdr w) (cdr d)))
        ((gen<? (car w) (car d))
         (let ((r (ew-poly--mono-div (cdr w) d))) (and r (cons (car w) r))))
        (#t #f)))

;;; NUM / DEN with remainder: (Q . R), NUM = Q * DEN + R, no monomial of R
;;; divisible by the leading monomial of DEN (the standard multivariate
;;; division, grlex).  The division is EXACT iff R is empty.  Coefficients
;;; divide in QQ; the caller decides whether a non-integer one is acceptable.
(define (ew-poly--divide-rem num den)
  (let ((ld (ew-poly--lead den)))
    (let loop ((r num) (q '()) (rem '()) (fuel 2000))
      (cond
        ((or (null? r) (<= fuel 0)) (cons q (poly-add rem r)))
        (#t
         (let* ((lr (ew-poly--lead r))
                (m  (ew-poly--mono-div (car lr) (car ld))))
           (if m
               (let ((tm (list (cons m (/ (cdr lr) (cdr ld))))))
                 (loop (poly-add r (poly-neg (cpoly-mul tm den)))
                       (poly-add q tm) rem (- fuel 1)))
               (let ((lt (list lr)))
                 (loop (poly-add r (poly-neg lt)) q (poly-add rem lt) (- fuel 1))))))))))

;;; NUM / DEN exactly, or #f.
(define (ew-poly--divide num den)
  (let ((qr (ew-poly--divide-rem num den)))
    (and (null? (cdr qr)) (car qr))))

(define (ew-poly--count v e)
  (cond ((equal? e v) 1)
        ((pair? e) (+ (ew-poly--count v (car e)) (ew-poly--count v (cdr e))))
        (#t 0)))

(define (ew-poly--remove-one v w)
  (cond ((null? w) '())
        ((equal? (car w) v) (cdr w))
        (#t (cons (car w) (ew-poly--remove-one v (cdr w))))))

;;; A monomial (sorted generators) as a right-nested product, g^n for repeats.
(define (ew-poly--mono->term w)
  (let loop ((gs w) (factors '()))
    (if (null? gs)
        (type-term--nest '* (reverse factors))
        (let count ((rest (cdr gs)) (n 1))
          (if (and (pair? rest) (equal? (car rest) (car gs)))
              (count (cdr rest) (+ n 1))
              (loop rest (cons (if (= n 1) (car gs) (list 'power (car gs) n))
                               factors)))))))

;;; A polynomial as a surface term: the FLAT normal form `expand' writes (below),
;;; highest degree first -- 3 * x ^ 2 + 3 * x * y + y ^ 2, the reading a person
;;; writes.  type-term types its flat n-ary nodes through the crs route.
(define (ew-poly--poly->term p) (expand--poly->term p))

;;; The goal's shape: (v C eqn), C #f when unguarded; or #f.
(define (ew-poly--shape g)
  (and (pair? g) (eq? (car g) 'FORSOME) (= (length g) 3)
       (let ((v (quantifier-var g)) (b (quantifier-body g)))
         (cond
           ((and (pair? b) (eq? (car b) '=) (= (length b) 3)) (list v #f b))
           ((and (pair? b) (eq? (car b) 'AND) (= (length b) 3)
                 (let ((a (cadr b)) (e (caddr b)))
                   (and (pair? a) (eq? (car a) 'IN) (= (length a) 3) (eq? (cadr a) v)
                        (pair? e) (eq? (car e) '=) (= (length e) 3))))
            (list v (caddr (cadr b)) (caddr b)))
           (#t #f)))))

;;; PURE.  Everything ew-poly works out about goal G, as an alist:
;;;   status    ok | nonexact | decline | not-shape
;;;   reason    a string (every status but ok)
;;;   v C       the witness variable and the guard class (#f when unguarded)
;;;   num den   the division NUM / DEN that gives the witness (normal forms;
;;;             the sign put on the leading coefficient of DEN)
;;;   rem       the remainder (nonexact), witness (ok: the surface term)
;;; `not-shape' is a goal that is not forsome(a, L = R) at all; every other
;;; status is about a goal of that shape, and what-now reports each of them.
(define (ew-poly--analyse g)
  (let ((sh (ew-poly--shape g)))
    (define (out status . kv) (cons (cons 'status status) kv))
    (if (not sh)
        (out 'not-shape (cons 'reason "the goal is not forsome(a, L = R) or forsome([a in C], L = R)"))
        (let* ((v (car sh)) (C (cadr sh)) (eqn (caddr sh))
               (occ (ew-poly--count v eqn))
               (base (list (cons 'v v) (cons 'C C))))
          (define (decline msg . more)
            (append (list (cons 'status 'decline) (cons 'reason msg)) more base))
          (if (not (= occ 1))
              (decline (string-append "the witness variable " (symbol->string v) " occurs "
                                      (number->string occ)
                                      " times in the equation; ew-poly wants exactly one"))
              (let ((pL (cvnb->poly (cvnb-expand-pow (cadr eqn))))
                    (pR (cvnb->poly (cvnb-expand-pow (caddr eqn)))))
                (if (not (and pL pR))
                    (decline "a side of the equation is not a polynomial (+ - * ^ over ring terms)")
                    (let* ((P (poly-add pL (poly-neg pR)))
                           (deg (lambda (w) (length (filter (lambda (x) (equal? x v)) w)))))
                      (if (any (lambda (tm) (> (deg (car tm)) 1)) P)
                          (decline "the equation is not linear in the witness variable")
                          (let* ((A0 (cpoly-normalize
                                      (map (lambda (tm) (cons (ew-poly--remove-one v (car tm)) (cdr tm)))
                                           (filter (lambda (tm) (= (deg (car tm)) 1)) P))))
                                 (B  (filter (lambda (tm) (= (deg (car tm)) 0)) P))
                                 ;; witness = -B / A; show it with DEN's leading coefficient positive
                                 (flip (and (pair? A0) (negative? (cdr (ew-poly--lead A0)))))
                                 (den  (if flip (poly-neg A0) A0))
                                 (num  (if flip B (poly-neg B)))
                                 (nd   (list (cons 'num num) (cons 'den den))))
                            (if (null? A0)
                                (decline "the coefficient of the witness variable is 0")
                                (let* ((qr (ew-poly--divide-rem num den)) (W (car qr)))
                                  (cond
                                    ((pair? (cdr qr))
                                     (append (list (cons 'status 'nonexact)
                                                   (cons 'reason "the division is not exact")
                                                   (cons 'rem (cdr qr)))
                                             nd base))
                                    ((and (not (memq C '(QQ RR CC)))
                                          (any (lambda (tm) (not (integer? (cdr tm)))) W))
                                     (apply decline "the quotient has a non-integer coefficient" nd))
                                    ((pair? (poly-add (cpoly-mul den W) (poly-neg num)))
                                     (apply decline "internal: the quotient does not solve the equation" nd))
                                    (#t (append (list (cons 'status 'ok)
                                                      (cons 'witness (ew-poly--poly->term W)))
                                                nd base)))))))))))))))

(define (ew-poly--get a key) (let ((p (assq key a))) (and p (cdr p))))

;;; PURE.  The witness for goal G as a surface term, or a STRING saying why not.
(define (ew-poly--witness g)
  (let ((a (ew-poly--analyse g)))
    (if (eq? (ew-poly--get a 'status) 'ok)
        (ew-poly--get a 'witness)
        (ew-poly--get a 'reason))))

;;; For what-now / scout: the witness term for the FOCUS goal, or #f.
(define (ew-poly--witness-for-focus)
  (and (proof-state? *ps*) (not (proof-done? *ps*))
       (let ((w (ew-poly--witness (dk-goal))))
         (and (not (string? w)) w))))

(define (ew-poly--decline! msg)
  (vnb--print-warning (string-append "ew-poly: " msg "; nothing changed"))
  #f)

;;; The generators `crs' will read off the instantiated identity that the
;;; context does not type in a ring domain: plan a typing for each in CLS.
;;; Returns the list of plans, or #f when one cannot be planned.
(define (ew-poly--gen-plans eqn cls)
  (let loop ((gs (cvnb-eq-source-generators (cvnb-expand-pow (cadr eqn))
                                            (cvnb-expand-pow (caddr eqn))))
             (acc '()))
    (cond ((null? gs) (reverse acc))
          ((type-term--ring-typed? (car gs)) (loop (cdr gs) acc))
          (#t (let ((p (type-term--plan (car gs) cls)))
                (and p (loop (cdr gs) (cons p acc))))))))

;;; (ew-poly) -- the surface command.
(define (ew-poly)
  (let ((g (and (proof-state? *ps*) (not (proof-done? *ps*)) (dk-goal))))
    (if (not g)
        (ew-poly--decline! "no open goal")
        (let ((w (ew-poly--witness g)))
          (if (string? w)
              (ew-poly--decline! w)
              (let* ((sh   (ew-poly--shape g))
                     (v    (car sh)) (C (cadr sh))
                     (eqn  (subst-free v w (caddr sh)))
                     (typ-plan (and C (type-term--plan w C)))
                     (gen-plans (ew-poly--gen-plans
                                 eqn (if (and C (memq C *type-term-classes*)) C 'RR))))
                (cond
                  ((and C (not typ-plan))
                   (ew-poly--decline!
                    (string-append "the witness " (expression->string w)
                                   " cannot be typed in " (expression->string C))))
                  ((not gen-plans)
                   (ew-poly--decline! "an atom of the identity is not typed in a number class, so crs cannot close it"))
                  (#t
                   (let ((leaf (proof-state-focus *ps*)))
                     (if (dk--transaction
                          (lambda ()
                            (ew w)
                            (let ((close-eq!
                                   (lambda ()
                                     (for-each type-term--exec! gen-plans)
                                     (crs))))
                              (if C
                                  (for-each
                                   (lambda (l)
                                     (when (not (sequent-node-grounded? l))
                                       (dk-focus! l)
                                       (if (eq? (car (dk-goal)) 'IN)
                                           (if (dk-asm? (dk-goal)) (ass) (type-term--exec! typ-plan))
                                           (close-eq!))))
                                   (dk-opened (lambda () (di))))
                                  (close-eq!)))
                            (sequent-node-grounded? leaf)))
                         (begin (show) #t)
                         (ew-poly--decline!
                          (string-append "the witness " (expression->string w)
                                         " was computed, but the steps did not close the goal"))))))))))))

;;; -----------------------------------------------------------------------
;;; expand -- SHOW the expansion as a proof step (notes-39, 2026-09-25).
;;;
;;; The user: "The goal isn't just to stamp PROVED onto a statement and leave
;;; some slop behind as a proof, but to actually learn something."  crs and
;;; ew-poly normalise polynomials INSIDE a closer, and the reader never sees the
;;; expansion.  (expand) makes it a step: every side of an equation in the focus
;;; goal -- the goal itself, the body of an existential, a conjunct -- that is a
;;; polynomial in context-typed atoms is replaced by its sum-of-monomials normal
;;; form (crs's), highest degree first.  On
;;;     forsome([a in zz], (x + y) ^ 3 = x ^ 3 + y * a)
;;; it leaves
;;;     forsome([a in zz], x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 = x ^ 3 + y * a)
;;;
;;; THROUGH THE SURFACE.  For each side t: t = nf(t) is proved by `crs' on a
;;; lane (dk-have!), and the goal is rewritten by `subst'.  The two steps are
;;; checked by the comm-ring-simplify and eq-subst checkers; nothing new is
;;; trusted.  Recorded as those steps, so the page replays them.
;;;
;;; WHICH SIDES.  A side is rewritten only when (a) it is a polynomial term
;;; (+ - * ^, binplus/bintimes/binneg, over opaque generators), (b) it mentions
;;; no variable bound in the goal at that position -- the witness variable of an
;;; existential is not a term of the context, so x ^ 3 + y * a is left alone, and
;;; `crs' could not type it anyway -- (c) every generator is typed in a number
;;; class in the context (what `crs' demands), and (d) its normal form differs
;;; from it.  DECLINES, with the reason and nothing recorded, when no side
;;; qualifies.  Transactional like the other two.
(define (expand--flat-mono c w)          ; c * g1^e1 * g2^e2 ..., flat
  (let loop ((gs w) (fs '()))
    (if (null? gs)
        (let ((fs (reverse fs)))
          (cond ((null? fs) c)
                ((= c 1) (if (null? (cdr fs)) (car fs) (cons '* fs)))
                (#t (cons '* (cons c fs)))))
        (let count ((rest (cdr gs)) (n 1))
          (if (and (pair? rest) (equal? (car rest) (car gs)))
              (count (cdr rest) (+ n 1))
              (loop rest (cons (if (= n 1) (car gs) (list 'power (car gs) n)) fs)))))))

;;; The normal form as a FLAT surface term: highest degree first, then crs's
;;; own order within a degree; positive terms summed, negative ones subtracted.
(define (expand--poly->term p)
  (if (null? p)
      0
      (let* ((ts  (sort p (lambda (a b) (> (length (car a)) (length (car b))))))
             (pos (filter (lambda (tm) (> (cdr tm) 0)) ts))
             (neg (filter (lambda (tm) (< (cdr tm) 0)) ts))
             (->t (lambda (tm) (expand--flat-mono (abs (cdr tm)) (car tm))))
             (sum (lambda (xs) (if (null? (cdr xs)) (->t (car xs)) (cons '+ (map ->t xs))))))
        (cond ((null? neg) (sum pos))
              ((null? pos) (list '- (sum neg)))
              (#t (cons '- (cons (sum pos) (map ->t neg))))))))

(define (expand--poly-head? t)
  (and (pair? t) (memq (car t) '(+ - * power binplus bintimes binneg)) #t))

;;; The normal form of side T, or a STRING saying why T is not rewritten, or #f
;;; when T is not an arithmetic term at all.
(define (expand--side-nf t bound)
  (and (expand--poly-head? t)
       (let ((p (cvnb->poly (cvnb-expand-pow t))))
         (cond
           ((not p) #f)
           ((any (lambda (v) (memq v bound)) (free-vars t))
            (string-append (expression->string t)
                           " mentions a variable bound in the goal, so it is not a term of the context"))
           ((not (every type-term--ring-typed?
                        (cvnb-source-generators (cvnb-expand-pow t))))
            (string-append "an atom of " (expression->string t)
                           " is not typed in a number class in the context"))
           (#t (let ((nf (expand--poly->term p)))
                 (and (not (equal? nf t)) nf)))))))

;;; The equation sides of G at the positions crs normalises, as (t . bound).
(define (expand--sides g bound)
  (cond
    ((and (pair? g) (eq? (car g) '=) (= (length g) 3))
     (list (cons (cadr g) bound) (cons (caddr g) bound)))
    ((and (pair? g) (eq? (car g) 'AND) (= (length g) 3))
     (append (expand--sides (cadr g) bound) (expand--sides (caddr g) bound)))
    ((and (pair? g) (eq? (car g) 'FORSOME) (= (length g) 3))
     (expand--sides (caddr g) (cons (cadr g) bound)))
    (#t '())))

;;; PURE.  (values rewrites reasons): REWRITES the (t . nf) pairs to apply,
;;; REASONS the strings for sides left alone.
(define (expand--plan g)
  (let loop ((ss (expand--sides g '())) (rw '()) (why '()))
    (if (null? ss)
        (values (reverse rw) (reverse why))
        (let* ((t (caar ss)) (r (expand--side-nf t (cdar ss))))
          (cond ((string? r) (loop (cdr ss) rw (if (member r why) why (cons r why))))
                ((and r (not (assoc t rw))) (loop (cdr ss) (cons (cons t r) rw) why))
                (#t (loop (cdr ss) rw why)))))))

;;; Does G contain a power of a sum with a numeral exponent?  -> that power, or #f.
;;; what-now names the binomial theorem as what such an expansion instantiates.
(define (expand--binomial-power g)
  (cond ((not (pair? g)) #f)
        ((and (eq? (car g) 'power) (= (length g) 3)
              (pair? (cadr g)) (memq (car (cadr g)) '(+ binplus -))
              (exact-nonnegative-integer? (caddr g)))
         g)
        (#t (or (expand--binomial-power (car g)) (expand--binomial-power (cdr g))))))

(define (expand--decline! msg)
  (vnb--print-warning (string-append "expand: " msg "; nothing changed"))
  #f)

;;; (expand) -- the surface command.
(define (expand)
  (let ((g (and (proof-state? *ps*) (not (proof-done? *ps*)) (dk-goal))))
    (if (not g)
        (expand--decline! "no open goal")
        (call-with-values (lambda () (expand--plan g))
          (lambda (rw why)
            (if (null? rw)
                (expand--decline!
                 (string-append "no side of an equation in the goal changes under normalisation"
                                (if (null? why) ""
                                    (apply string-append
                                           (map (lambda (r) (string-append " (" r ")")) why)))))
                (if (dk--transaction
                     (lambda ()
                       (for-each (lambda (pr)
                                   (let ((eqn (list '= (car pr) (cdr pr))))
                                     (dk-have! eqn (lambda () (crs)))
                                     (subst eqn)))
                                 rw)
                       (let ((g2 (dk-goal)))
                         (and (not (equal? g2 g))
                              (not (proof-done? *ps*))))))
                    (begin (show) #t)
                    (expand--decline! "the rewriting steps did not go through"))))))))

;;; -----------------------------------------------------------------------
;;; IMAGE membership (2026-09-30).  `image-membership-iff' reads
;;;     w in IMAGE(phi, S)  iff  w in SET and forsome x in S. phi(x) = w
;;; since the repair of that day (docs/image-axiom-inconsistency-2026-09-30.md):
;;; the sethood conjunct is what keeps a class-valued phi from manufacturing a
;;; member.  Every driver that read the membership as the bare existential
;;; meets the conjunction now; these two are the one place that knows its shape.
;;;
;;; (dk-sethood! t)       closes the focus goal (IN t SET): by `ass' when it is in
;;;                       context, else from any typing (IN t C) in context through
;;;                       membership-implies-sethood; errors when there is none.
;;; (dk-image-goal!)      on the goal (IN w (IMAGE phi S)): rewrites by the iff,
;;;                       splits the conjunction, closes the sethood of w, and leaves
;;;                       the EXISTENTIAL focused -- the driver's next step is the
;;;                       `ew' it always was.
;;; (dk-image-hyp! mem)   opens the hypothesis mem = (IN w (IMAGE phi S)) by the iff,
;;;                       splits the conjunction so (IN w SET) lands, and RETURNS the
;;;                       existential as it landed -- what `(dk-landed-1 (lambda ()
;;;                       (mac-h 'image-membership-iff mem)))' used to return.
(define (dk-sethood! t)
  (let ((want (list 'IN t 'SET)))
    (define (in-ctx? f)
      (let loop ((as (dk-asms)))
        (cond ((null? as) #f) ((alpha-equiv? (car as) f) #t) (else (loop (cdr as))))))
    (define (typing-of u)                 ; some (IN u C) in context, C not SET
      (let loop ((as (dk-asms)))
        (cond ((null? as) #f)
              ((and (pair? (car as)) (eq? (caar as) 'IN) (= (length (car as)) 3)
                    (equal? (cadr (car as)) u) (not (eq? (caddr (car as)) 'SET)))
               (car as))
              (else (loop (cdr as))))))
    (define (fun-typing-of f)             ; some (IN f (FUN A B)) in context
      (let loop ((as (dk-asms)))
        (cond ((null? as) #f)
              ((and (pair? (car as)) (eq? (caar as) 'IN) (= (length (car as)) 3)
                    (equal? (cadr (car as)) f)
                    (pair? (caddr (car as))) (eq? (car (caddr (car as))) 'FUN)
                    (= (length (caddr (car as))) 3))
               (car as))
              (else (loop (cdr as))))))
    (if (not (alpha-equiv? (dk-goal) want))
        (error "dk-sethood!: the focus goal is not" (expression->string want)
               "but" (expression->string (dk-goal))))
    (cond
      ;; already there
      ((in-ctx? want) (ass))
      ;; a typing in context: membership-implies-sethood
      ((typing-of t)
       => (lambda (typ) (fact 'membership-implies-sethood t (caddr typ)) (ass)))
      ;; the classes the lam-t closer knows (NN, RR, intervals, products, ...)
      ((and (or (symbol? t) (and (pair? t) (memq (car t) '(INTERVAL CARTESIAN))))
            (dk-close-if! (lambda () (dk-set-close! t)) (lambda () #f)))
       #t)
      ;; a SEP: sep-set, then the sethood of its domain
      ((and (pair? t) (eq? (car t) 'SEP) (= (length t) 4))
       (let ((leaves (dk-opened (lambda () (sep-set)))))
         (for-each (lambda (l) (dk-focus! l) (dk-sethood! (cadr (dk-goal-of l)))) leaves)))
      ;; an IMAGE: replacement, then the sethood of the set it is taken over
      ((and (pair? t) (eq? (car t) 'IMAGE) (= (length t) 3))
       (dk-have! (list 'IN (caddr t) 'SET) (lambda () (dk-sethood! (caddr t))))
       (fact 'image-set (cadr t) (caddr t))
       (ass))
      ;; an application f(a) with f in FUN(A, B) in context: f(a) in B, then sethood
      ((and (pair? t) (= (length t) 2) (fun-typing-of (car t)))
       => (lambda (ft)
            (let ((A (cadr (caddr ft))) (B (caddr (caddr ft))))
              (dk-have! (list 'IN (cadr t) A) (lambda () (ass)))
              (fact 'fun-apply-type-c (car t) A B (cadr t))
              (fact 'membership-implies-sethood t B)
              (ass))))
      ;; an accessor of a structure the context knows (PTS s, CARR r, ...): the typing
      ;; conjunct of IS-X, projected on a lane so the predicate hypothesis survives
      ((and (pair? t) (= (length t) 2) (symbol? (car t))
            (let loop ((as (dk-asms)))
              (cond ((null? as) #f)
                    ((and (pair? (car as)) (= (length (car as)) 2)
                          (symbol? (caar as)) (equal? (cadr (car as)) (cadr t))
                          ;; symbols are folded to lower case (CLAUDE.md, "Case folding"): the
                          ;; predicate reads `is-setoid', the structure `setoid'
                          (let ((nm (string-downcase (symbol->string (caar as)))))
                            (and (> (string-length nm) 3) (string=? (substring nm 0 3) "is-")
                                 (find-shape-structure (string->symbol (substring nm 3 (string-length nm)))))))
                     (car as))
                    (else (loop (cdr as))))))
       => (lambda (pred)
            ;; on THIS leaf, which closes right here: mac-h may consume the predicate
            ;; hypothesis (a lane would prove the claim in place and move the focus to a
            ;; sibling, where a trailing `ass' fires on the wrong goal)
            (mac-h (car pred) pred)
            (dk-split-all!)
            (ass)))
      ;; a binary union: both halves, then union-set-closure (conjunctive antecedent:
      ;; the whole AND must be in context for `fact' to detach it)
      ((and (pair? t) (eq? (car t) 'UNION) (= (length t) 3))
       (dk-have! (list 'AND (list 'IN (cadr t) 'SET) (list 'IN (caddr t) 'SET))
                 (lambda () (dk-each-leaf! (lambda () (di))
                                           (lambda () (dk-sethood! (cadr (dk-goal)))))))
       (fact 'union-set-closure (cadr t) (caddr t))
       (ass))
      ;; a pair: both members, then the pairing axiom
      ((and (pair? t) (eq? (car t) 'PAIR) (= (length t) 3))
       (dk-have! (list 'AND (list 'IN (cadr t) 'SET) (list 'IN (caddr t) 'SET))
                 (lambda () (dk-each-leaf! (lambda () (di))
                                           (lambda () (dk-sethood! (cadr (dk-goal)))))))
       (fact 'pairing (cadr t) (caddr t))
       (ass))
      ;; a relative complement: the sethood of the ambient set
      ((and (pair? t) (eq? (car t) 'COMPLEMENT-IN) (= (length t) 3))
       (dk-have! (list 'IN (cadr t) 'SET) (lambda () (dk-sethood! (cadr t))))
       (fact 'complement-in-set-closure (cadr t) (caddr t))
       (ass))
      ;; a named functoid whose body is a SEP or an IMAGE (BALL, CLASS, COMPLEMENT-IN,
      ;; ...): unfold it in the goal and look again
      ((and (pair? t) (symbol? (car t))
            (hash-table-ref/default *functoid-registry* (car t) #f))
       (let ((g0 (dk-goal)))
         (mac (car t))
         (if (alpha-equiv? (dk-goal) g0)
             (error "dk-sethood!: no route to the sethood of" (expression->string t)))
         (dk-sethood! (cadr (dk-goal)))))
      (else
       (error "dk-sethood!: no typing of the term in context and no route to its sethood"
              (expression->string t))))))

(define (dk-image-goal!)
  (let ((g (dk-goal)))
    (if (not (and (pair? g) (eq? (car g) 'IN) (= (length g) 3)
                  (pair? (caddr g)) (eq? (car (caddr g)) 'IMAGE)))
        (error "dk-image-goal!: the goal is not a membership in an IMAGE"
               (expression->string g)))
    (let* ((w      (cadr g))
           (leaves (dk-opened (lambda () (mac 'image-membership-iff) (di))))
           (seth   (filter (lambda (l) (alpha-equiv? (dk-goal-of l) (list 'IN w 'SET))) leaves))
           (ex     (filter (lambda (l) (let ((x (dk-goal-of l))) (and (pair? x) (eq? (car x) 'FORSOME))))
                           leaves)))
      (if (or (null? seth) (null? ex))
          (error "dk-image-goal!: expected a sethood leaf and an existential leaf, got"
                 (map (lambda (l) (expression->string (dk-goal-of l))) leaves)))
      (dk-focus! (car seth))
      (dk-sethood! w)
      (dk-focus! (car ex)))))

(define (dk-image-hyp! mem)
  (let* ((landed (dk-landed (lambda () (mac-h 'image-membership-iff mem))))
         (conj   (let loop ((ls landed))
                   (cond ((null? ls) #f)
                         ((and (pair? (car ls)) (eq? (caar ls) 'AND)) (car ls))
                         (else (loop (cdr ls)))))))
    (if (not conj)
        (error "dk-image-hyp!: the iff did not land a conjunction; landed"
               (map expression->string landed)))
    (let ((ex (let loop ((ps (dk-split! conj)))
                (cond ((null? ps) #f)
                      ((and (pair? (car ps)) (eq? (caar ps) 'FORSOME)) (car ps))
                      (else (loop (cdr ps)))))))
      (if (not ex) (error "dk-image-hyp!: no existential among the conjuncts of" (expression->string conj)))
      ex)))
