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

;; F15: dk-landed* compares with wff-str=?, wff-member/str, wff-drop-one/str (defined in
;; wff.scm, which is compiled; driver-kit.scm never is).

(define (dk--drop-one s lst)            ; remove ONE occurrence (contexts hold duplicates)
  (cond ((null? lst) '())
        ((string=? s (car lst)) (cdr lst))
        (else (cons (car lst) (dk--drop-one s (cdr lst))))))

;; run `thunk'; return the assumptions it ADDED to the focus context, in context
;; order.  May be empty.
;; F15: assumptions are printed through wff-display-string (cached in the wff, same
;; string object until *accessor-display* changes) instead of expression->string,
;; and compared with eq?-then-string=? (wff-member/str, compiled in wff.scm).  The multiset difference is unchanged and
;; the returned items are still (wff-formula w), the very objects dk-asms returns.
(define (dk-landed* thunk)
  (let ((before (map wff-display-string
                     (sequent-node-assumptions (proof-state-focus *ps*)))))
    (thunk)
    (let loop ((as (sequent-node-assumptions (proof-state-focus *ps*))) (bs before) (acc '()))
      (if (null? as)
          (reverse acc)
          (let ((s (wff-display-string (car as))))
            (if (wff-member/str s bs)
                (loop (cdr as) (wff-drop-one/str s bs) acc)
                (loop (cdr as) bs (cons (wff-formula (car as)) acc))))))))

;;; KIT-9 (2026-10-27; wired 2026-10-27, batch 0): the context without the citation-chain LINKS
;;; (the link table is in interactive.scm, beside `fact'); a file-local finder filters this instead
;;; of (dk-asms).  k9--call-noting runs a citation entry point inside the recorder: every formula it
;;; landed but its result is a link, and the result is unmarked (the driver asked for it).
(define (dk-asms*) (filter (lambda (f) (not (dk-link? f))) (dk-asms)))
(define (k9--call-noting orig args)
  (let* ((r (k9--landed (lambda () (apply orig args)))) (out (car r)))
    (cond ((pair? (cddr r)) (k9--note! (cddr r) (cadr r) (and (pair? out) out) #f))
          ((pair? out) (k9--unmark! out)))
    out))

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

;;; KIT-9 D: citation-chain LINKS are skipped when a non-link also matches; when only links
;;; match, the old behaviour applies (unique match returned).
(define (dk-landed-find thunk pred . opt)     ; the UNIQUE new assumption satisfying `pred'
  (let* ((new (dk-landed thunk))
         (all (filter pred new))
         (hits (if (k9--links-flag? opt) all (filter (lambda (f) (not (dk-link? f))) all))))
    (cond ((and (null? hits) (pair? all))
           ;; only links match: the link IS what the driver asked for (2026-10-28 exam:
           ;; frechet-metric picks an instance landed by a citation) -- old behaviour
           (if (pair? (cdr all))
               (error "dk-landed-find: ambiguous; matched" (map expression->string all))
               (car all)))
          ((null? hits)
           (error "dk-landed-find: no new assumption matches; landed"
                  (map expression->string new)))
          ((pair? (cdr hits))
           (error "dk-landed-find: ambiguous; matched" (map expression->string hits)))
          (else (car hits)))))
(define (k9--links-flag? opt) (and (pair? opt) (eq? (car opt) 'links)))

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

;;; KIT-7 E5 (2026-10-26; wired 2026-10-27): strict as before, but the error says what happened and
;;; names the tolerant form (CA-MONTEL finding 3: helpers that can run twice in one branch).
(define (k9--dkfact-0 . args)            ; dk-fact! before the KIT-9 recorder (KIT-7 E5 body)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler
        (lambda (e)
          (if (and (condition? e)
                   (string-search-forward "landed no assumption" (condition/report-string e) 0))
              (k (error (string-append
                         "dk-fact!: nothing landed -- the instance of " (expression->string (car args))
                         " is most likely ALREADY IN CONTEXT.  dk-fact! is strict; dk-cite! is the tolerant"
                         " form (it returns the instance whether it lands now or was there).  Arguments:")
                        (cdr args)))
              (raise e)))
        (lambda () (dk-deepest (lambda () (apply fact args))))))))
(define (dk-fact! . args) (k9--call-noting k9--dkfact-0 args))    ; KIT-9 C

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
      ;; `ass' only when it can close: on a goal not in context it warned
      ;; "assumption: goal not in context" and left the leaf open, which is what
      ;; it still does -- silently; the CALLER (have!, dk-have!) is what reports an
      ;; unproven side goal, loudly (2026-10-04: 68 such lines in one load log).
      (else (dk-ass!)))))

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
(define (k9--inst*-0 f . terms)          ; inst*! before the KIT-9 recorder
  (let loop ((f f) (ts terms))
    (if (null? ts)
        f
        (loop (dk-deepest (lambda () (inst+ f (car ts)))) (cdr ts)))))
(define (inst*! . args) (k9--call-noting k9--inst*-0 args))      ; KIT-9 C

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
;;; KIT-9 D: prefers an assumption that is not a citation-chain link.
(define (dk-ai-head! head)
  (let ((f (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) head) (not (dk-link? a)))) (dk-asms))
               (any-pred (lambda (a) (and (pair? a) (eq? (car a) head))) (dk-asms)))))
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
;;; KIT-9 D: citation-chain LINKS are skipped unless 'links is passed: (dk-pick PRED WHAT 'links).
;;; When only links match, the first is returned, as before KIT-9.
(define (dk-pick pred what . opt)
  (let* ((all (filter pred (dk-asms)))
         (fs (if (k9--links-flag? opt) all (filter (lambda (f) (not (dk-link? f))) all))))
    (cond ((pair? fs) (car fs))
          ;; only links match: fall back to the old pick (the newest match).  Links are
          ;; skipped only when a non-link also matches (2026-10-28 exam, frechet-metric).
          ((pair? all) (car all))
          (#t (error "dk-pick: nothing matching" what)))))

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
;;;
;;; A PARTIAL INSTANCE ALREADY IN CONTEXT (2026-10-18, the LA-DET2 agent; also the
;;; dk-holomorphic! failure on a + -b of CA-6): after (dk-apply! F i k), a second
;;; (dk-apply! F i l) used to fail -- the instance at i was in context, so `inst+'
;;; landed nothing and the chain errored "landed no assumption".  `dk--reuse-prefix'
;;; walks the instantiation as far as its forms are ALREADY in context (each
;;; instance, each guard detached) and the rest goes through `inst*!' as before; a
;;; call whose first instance is not in context takes exactly the old path.
(define (dk--reuse-prefix f terms)
  ;; -> (FORM . REMAINING-TERMS) for the deepest in-context form reached, or #f
  (let loop ((f f) (ts terms) (best #f))
    (cond ((and (pair? f) (eq? (car f) 'IMPLIES) (dk-asm? (cadr f))
                (dk-ctx-form (caddr f)))
           (let ((c (dk-ctx-form (caddr f))))
             (loop c ts (cons c ts))))
          ((and (pair? ts) (pair? f) (eq? (car f) 'FORALL))
           (let ((have (dk-ctx-form (subst-free (quantifier-var f) (car ts) (quantifier-body f)))))
             (if have (loop have (cdr ts) (cons have (cdr ts))) best)))
          (#t best))))
(define (k9--apply-0 f . terms)          ; dk-apply! before the KIT-9 recorder
  (let* ((f0   (or (dk-ctx-form f) f))
         (pre  (dk--reuse-prefix f0 terms))
         (r0   (cond ((not pre) (apply inst*! f terms))
                     ((null? (cdr pre)) (car pre))
                     (#t (apply inst*! (car pre) (cdr pre))))))
    (let loop ((r r0))
      (if (and (pair? r) (eq? (car r) 'IMPLIES))
          (loop (dk-landed-1 (lambda () (detach! r))))
          r))))
(define (dk-apply! . args) (k9--call-noting k9--apply-0 args))   ; KIT-9 C

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
            ;; a child that hash-consing has GROUNDED by the time we reach it (the
            ;; same sequent as a sibling just closed) is skipped: `dk-focus!' on a
            ;; grounded node is a no-op and the closer would fire on whatever leaf has
            ;; the focus (M-2, 2026-10-04)
            (for-each (lambda (k)
                        (if (not (sequent-node-grounded? k))
                            (begin (dk-focus! k) (walk))))
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
;; land the sethood fact for A (recursively for a CARTESIAN), without closing
;; anything: the old dk-set-close! recursed INTO ITSELF on a CARTESIAN and so fired
;; a bare `ass' on the CARTESIAN goal at every level (M-2, 2026-10-04: one
;; "assumption: goal not in context" per component).
(define (dk--set-fact! A)
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
         (dk--set-fact! (cadr A))
         (dk--set-fact! (caddr A))
         (fact 'cartesian-set-iff (cadr A) (caddr A)))
        (else #f)))
;; A CARTESIAN is closed the way cc-metric-space-proof.scm and c-metric-is-metric.scm
;; do it: `mac' of the iff rewrites the goal into the conjunction of the component
;; sethoods, and each conjunct leaf is closed in turn (recursively, for a nested
;; CARTESIAN).  `fact' of the iff plus `ass' never closed it (suite check, 2026-10-04).
(define (dk-set-close! A)
  (cond ((and (pair? A) (eq? (car A) 'CARTESIAN))
         (mac 'cartesian-set-iff)
         (dk-conj-close! (lambda () (dk-set-close! (cadr (dk-goal))))))
        (#t (dk--set-fact! A) (ass))))

;;; (dk-set-if! THM A B [THUNK]) -- THM is `fun-set-iff' or `cartesian-set-iff', since
;;; 2026-11-20 the IMPLIES (A in SET and B in SET) => HEAD(A, B) in SET (library.scm; the
;;; "only if" halves were false).  Lands HEAD(A, B) in SET and returns it.  The antecedent
;;; conjunction is proved in a have! lane by THUNK, which starts on the goal
;;; (AND (IN A SET) (IN B SET)); the default closes it from context, conjunct by conjunct.
;;; The replacement for the old IFF idiom -- cite, prove the right side, land the left --
;;; at every site that used the IFF value rather than `mac'.
(define (dk-set-if! thm a b . opt)
  (let* ((head (case thm ((fun-set-iff) 'FUN) ((cartesian-set-iff) 'CARTESIAN)
                 (else (error "dk-set-if!: not a sethood axiom" thm))))
         (goal `(IN (,head ,a ,b) SET))
         (thunk (if (pair? opt) (car opt)
                    (lambda () (if (dk-asm? (dk-goal)) (ass) (dk-conj-close! (lambda () (ass))))))))
    (if (not (dk-asm? goal))
        (dk-have! goal (lambda () (mac thm) (thunk))))
    goal))

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

;;; (dk-ass!) -- `ass' only when the goal IS an assumption (up to alpha); returns
;;; whether it closed.  The closer to hand dk-conj-close!, in-sep!, detach-with!
;;; and the like in place of (lambda () (ass)), which warns "assumption: goal not
;;; in context" on every conjunct it cannot close: the load log of 2026-10-04
;;; carried 68 such lines from three new files whose proofs were all fine.
;;; KIT-7 E2 (2026-10-26; wired 2026-10-27): respects the drift marker (interactive.scm) --
;;; returns #f, and does not report a close it did not make.
(define (dk-ass!)
  (cond ((not (and *ps* (not (proof-done? *ps*)))) #f)
        ((vnb--drift-refuse? 'dk-ass!) #f)
        ((dk-asm? (dk-goal)) (ass) #t)
        (#t #f)))

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
;;; THE CLOSER THAT FOLLOWS IT DRIFTS (LA-Z5, LA-Z6, CA-HOPF, 2026-10-25): a
;;; driver that writes `(dk-have! claim thunk) (ass)' -- the claim being a typing
;;; the next step needs -- closes the focus goal in place when the claim IS the
;;; goal, and its `(ass)' then fires on another leaf.  This cannot be cured here
;;; (the leaf is closed; there is nowhere for the focus to stay): capture the node
;;; and close THAT -- `dk-by!', `dk-ass-on!', `dk-close-on!' (KIT-5 section).
(define (dk-have! form0 . opt)
  ;; At most ONE further argument, a procedure (or #f).  A stray argument is a
  ;; closer meant to FOLLOW the call, swallowed by a paren in the wrong place; MIT
  ;; evaluates arguments right to left, so it has already run, before the lane
  ;; (2026-10-18, the CA-6 agent: `prop' printed a countermodel and dk-have! said
  ;; nothing).  `have!' has the same check.
  (if (or (and (pair? opt) (pair? (cdr opt)))
          (and (pair? opt) (car opt) (not (procedure? (car opt)))))
      (error "dk-have!: takes a claim and at most one THUNK; got extra or non-procedure arguments -- a paren in the wrong place swallowed the following form(s), which have ALREADY RUN (right-to-left evaluation)"
             (length opt)))
  (let ((f (->raw-formula form0))
        (thunk (and (pair? opt) (car opt))))
    (if (dk-link? f) (k9--unmark! f))       ; KIT-9 D: a claim the driver states is not a link
    (cond
     ((dk-asm? f) #f)
     ((eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) f))))
      (let ((leaf (proof-state-focus *ps*)))
        (if thunk (thunk) (from-context!))
        (if (not (sequent-node-grounded? leaf))
            (error "dk-have!: the claim is the focus goal, and the lane left it open" f))
        ;; KIT-7 E1: mark the in-place close, so the closer the caller wrote next is
        ;; refused instead of firing on a sibling (interactive.scm, the drift marker).
        (vnb-note-drift! leaf 'dk-have!)
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
;;; The theorem that types a CLOSED term outright: a statement (IN c X), a structure witness
;;; IS-X(c) on the term itself, or for c = (ACC I) the statement (IS-X I) of a structure with that
;;; slot.  #f when there is none.  A scan of the theorem table, cached by term (a miss only
;;; until the table grows).
(define *dk-owed-typing-cache* (make-equal-hash-table))
(define (dk-owed--typing-theorem c)
  (let ((hit (hash-table-ref/default *dk-owed-typing-cache* c #f))   ; a name, (miss . size) or #f
        (n   (hash-table-size *theorem-table*)))
    (if (or (symbol? hit) (and (pair? hit) (= (cdr hit) n)))
        (and (symbol? hit) hit)
        (let ((subj (if (and (pair? c) (= (length c) 2) (symbol? (cadr c))) (cadr c) #f))
              (found #f))
          (hash-table-walk *theorem-table*
            (lambda (name stmt)
              (if (and (not found) (pair? stmt) (symbol? (car stmt)))
                  (cond ((and (eq? (car stmt) 'IN) (= (length stmt) 3) (equal? (cadr stmt) c))
                         (set! found name))
                        ;; a structure witness ON the term itself: IS-X(c) certifies c
                        ((and (pair? c) (= (length stmt) 2) (equal? (cadr stmt) c)
                              (pi--structure-def-for (car stmt)))
                         (set! found name))
                        ((and subj (= (length stmt) 2) (eq? (cadr stmt) subj)
                              (let ((sd (pi--structure-def-for (car stmt))))
                                (and sd (memq (car c) (structure-slot-names sd)))))
                         (set! found name))))))
          ;; a MISS is cached with the size of the theorem table and holds only while the
          ;; table has not grown (2026-10-13, R4-G): a miss cached forever outlived the
          ;; witness -- normed-field-ring-view asked for (CARR RR-NORMED-FIELD) before
          ;; rr-is-normed-field loaded, and rake-inequalities, 1700 entries later,
          ;; inherited the miss
          (hash-table-set! *dk-owed-typing-cache* c (or found (cons 'miss n)))
          found))))
;;; The closed accessor subterms (ACC I) of T, I a registered constant: what the owed-leaf
;;; hook types before `rfl' on a term that is not a list (R4-G, 2026-10-13).  The macete
;;; door owes SUPP(a_, NN-ADD-MONOID, f_) = SUPP(...) for `mac subset-def', and the functoid
;;; walk certifies SUPP's SEP only once CARR(NN-ADD-MONOID) is certified -- by the structure
;;; witness IS-COMM-MONOID(NN-ADD-MONOID), a theorem the context does not hold.
(define (dk-owed--closed-accessors t)
  ;; a functoid application is also searched through its instantiated body (depth 4),
  ;; which is where the certificate's functoid walk looks
  (let walk ((e t) (acc '()) (depth 0))
    (cond ((not (pair? e)) acc)
          ((and (= (length e) 2) (symbol? (car e)) (symbol? (cadr e))
                (constant-head? (cadr e)))
           (if (member e acc) acc (cons e acc)))
          (#t (let* ((acc (let loop ((xs e) (acc acc))
                            (if (pair? xs) (loop (cdr xs) (walk (car xs) acc depth)) acc)))
                     (b (and (< depth 4) (symbol? (car e)) (pi--functoid-instance e))))
                (if b (walk b acc (+ depth 1)) acc))))))
(define (dk-owed--type-closed! c)
  (if (and (or (symbol? c) (pair? c))
           (every constant-head? (free-vars c))      ; closed: every symbol a registered constant
           (not (pi--sets-defined? (sequent-node-assumptions (proof-state-focus *ps*)) (list 'LIST c) 0)))
      (let ((thm (dk-owed--typing-theorem c)))
        (if thm (fact thm)))))
(define (dk-discharge-owed! leaf)
  ;; TRANSACTIONAL (2026-09-18 evening): an attempt that does not close the
  ;; leaf is rolled back -- graph, focus, script, trace, undo stack -- so a
  ;; failed closer leaves no half-cut leaf behind (the recip(0) suite check
  ;; found three leaves where two were owed).
  ;; *proof-mints* is rolled back with the script (2026-10-10, META round 3): the
  ;; record must hold ONE mint entry per recorded step, and a failed attempt's
  ;; `dk-focus!' had left an orphan entry, so every later `name-witness! N' on
  ;; the page addressed the wrong step (five pages failed the audit once the
  ;; macete door began owing t = t leaves this closer cannot discharge).
  (let* ((home  (proof-state-focus *ps*))
         (mark  (vnb--take-mark '(dk-discharge-owed!)))
         (mints *proof-mints*)
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
              ;; a LITERAL LIST (2026-10-12, R4: nth-reduce, length-reduce and
              ;; tuple-equality-decompose owe  L = L  for a list the context does not
              ;; certify; a list denotes when its components are sets).  Each CLOSED
              ;; component the certificate cannot see is typed by the one theorem that
              ;; states it outright -- `c in X' for a constant c, or the structure
              ;; witness IS-X(I) for an accessor (ACC I) of a declared instance I --
              ;; then `rfl'.  A component with a free variable is the driver's business.
              ((and (pair? t) (eq? (car t) 'LIST))
               (for-each dk-owed--type-closed! (cdr t))
               (rfl))
              ;; any other term with closed accessor subterms (ACC I): type those by
              ;; their witness theorems, then `rfl' (R4-G; rolled back if it fails)
              ((and (pair? t) (pair? (dk-owed--closed-accessors t)))
               (for-each dk-owed--type-closed! (dk-owed--closed-accessors t))
               (rfl))
              (#t #f)))))))
    (if (and mark (not (sequent-node-grounded? leaf)))
        (begin                                   ; roll the attempt back
          (dg-rollback! (vnb-undo-mark-dg-mark mark))
          (set-proof-state-focus! *ps* (vnb-undo-mark-focus mark))
          (set! *proof-script* (vnb-undo-mark-script mark))
          (set! *live-trace*   (vnb-undo-mark-trace mark))
          (set! *proof-mints*  mints)
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
;;; ass) -- the second only since 2026-10-25 (KIT-5): `dk-close-if!' used to
;;; read the focus on the REDUCED node as drift and skip the closer (PRODUCT2
;;; finding 1); it now follows the one open leaf below the node it started on.
;;; #f when the reduced goal is open and in focus.  Four files guarded the
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
;;; if N is still OPEN and the focus is on N -- or on the ONE open leaf below N,
;;; the node a rewrite of N created -- and return whether N is grounded.  The
;;; third case -- N open, focus moved anywhere else -- is the drift, and it is
;;; reported rather than papered over: the caller gets #f and a warning naming
;;; both nodes.
;;;
;;; FOLLOWING THE CHILD (2026-10-25, KIT-5 item 2; PRODUCT2 finding 1).  A step
;;; that REWRITES the goal -- lam-b, fact, subst, mac -- does not leave the focus
;;; on N: it justifies N by a new node and focuses that.  The old test (focus
;;; still `eq?' to N) therefore failed on every such thunk, so the idiom the
;;; `dk-lam-b!' comment recommended, (dk-close-if! dk-lam-b! ass), always warned
;;; "moved the focus" and skipped the closer, and the enclosing lane failed.  The
;;; focus on the UNIQUE open leaf below N is not drift: that leaf IS what the
;;; driver means by "the leaf just worked on".  A focus on any other leaf -- a
;;; sibling, as the CONTROL in the 11-D checks shows -- still is.
(define (dk-close-if! thunk closer)
  (let ((node (proof-state-focus *ps*)))
    (thunk)
    (let ((focus (proof-state-focus *ps*)))
      (cond ((sequent-node-grounded? node) #t)
            ((or (eq? node focus)
                 (let ((below (dk--open-below node)))
                   (and (pair? below) (null? (cdr below)) (eq? (car below) focus))))
             (closer)
             (sequent-node-grounded? node))
            (#t
             (display ";VNB warning: dk-close-if!: the thunk left node ")
             (write (sequent-node-number node))
             (display " OPEN and moved the focus to ")
             (write (sequent-node-number focus))
             (display ", which is not the one open leaf below it -- the closer was NOT run.")
             (newline)
             #f)))))

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
;;;
;;; KIT-7 E3 (2026-10-26; wired 2026-10-27): the lane closer takes ITS LANE.  The old
;;; dk--lane-close! read the lane off the focus; an opener that closes the lane itself (M-H: an
;;; opener ending in `(ass)') left the focus on the MAIN leaf, which it then took for the lane and
;;; ran dk-ass! / dk-split-all! / prop on.  Now: grounded lane -> done; else the one open leaf
;;; under the lane is focused (dk--open-below) and closed; no open leaf under a lane that is not
;;; grounded, or several, is an ERROR naming the lane.
;;; dk-ass!, not ass: `ass' on a claim not yet in context warned "goal not in
;;; context" on EVERY lane whose claim needed the split first -- 68 lines in
;;; the load log of 2026-10-04, all from here (dk-project!'s lanes).
(define (dk--lane-close-at! lane)
  (define (still-open?) (not (sequent-node-grounded? lane)))
  (define (on-lane!)
    (if (still-open?)
        (let ((below (dk--open-below lane)))
          (cond ((memq (proof-state-focus *ps*) below) #t)
                ((and (pair? below) (null? (cdr below))) (dk-focus! (car below)) #t)
                ((null? below) (error "dk--lane-close!: the lane has no open leaf but is not grounded, node"
                                      (sequent-node-number lane)))
                (#t (error "dk--lane-close!: several open leaves under the lane, node"
                           (sequent-node-number lane)))))
        #f))
  (if (on-lane!) (vnb-guard (lambda () (dk-ass!))))
  (if (on-lane!) (vnb-guard (lambda () (dk-split-all!))))
  (if (on-lane!) (vnb-guard (lambda () (dk-ass!))))
  (if (on-lane!) (vnb-guard (lambda () (prop))))
  (not (still-open?)))
(define (dk--lane-close!) (dk--lane-close-at! (proof-state-focus *ps*)))

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
;;; KIT-7 E4 (2026-10-26; wired 2026-10-27): the lane is captured BEFORE the opener runs and
;;; closed by dk--lane-close-at!; a claim equal to the focus goal is proved in place (dk-have!)
;;; and returned, where the old code errored "the projection is not in the context after the
;;; lane" (ISOM, 2026-10-26).
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
                                 opener))))
         (in-place #f))
    (if (not (dk-asm? concl))
        (set! in-place
              (eq? #t (dk-have! concl (lambda ()
                                        (let ((lane (proof-state-focus *ps*)))
                                          (open!)
                                          (dk--lane-close-at! lane)))))))
    (cond (in-place concl)                     ; the focus goal itself: proved in place
          ((dk-ctx-form concl))
          (#t (error "dk-project!: the projection is not in the context after the lane"
                     (expression->string concl))))))

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

(define (k9--cite-0 thm . args)          ; dk-cite! before the KIT-9 recorder
  (let* ((terms (map ->raw-formula args))
         (owed0 (vnb--owed-leaves))
         (new   (dk-landed* (lambda () (apply fact thm terms))))
         (owed  (filter (lambda (l) (not (memq l owed0))) (vnb--owed-leaves))))
    ;; 2026-10-07 (WEEK3 kit finding 2): an instantiation at a term the context does not
    ;; certify DEFINED posts a `t = t' leaf; when the owed-leaf hook cannot close it the
    ;; step used to report nothing and the proof died at `qed' ("not complete"), three
    ;; debugging rounds later.  Say so here, naming the term.
    (if (pair? owed)
        (error (string-append "dk-cite!: instantiating " (symbol->string thm)
                              " owes a definedness leaf the context cannot close -- TYPE THE TERM FIRST:")
               (expression->string (dk-goal-of (car owed)))))
    (if (pair? new)
        (dk--deepest-of new)
        (let ((want (dk--fact-instance thm terms)))
          (or (dk-ctx-form want)
              (error (string-append "dk-cite!: " (symbol->string thm)
                                    " landed nothing, and its instance is not in context")
                     (expression->string want)))))))
(define (dk-cite! . args) (k9--call-noting k9--cite-0 args))     ; KIT-9 C

;;; -----------------------------------------------------------------------
;;; THE HYPOTHESIS-SIDE REWRITE (owed since 2026-09-14; built 2026-10-07 from the S-2
;;; agent's `sab-rewrite!' / `ssl-transport!' / `sab-nth!', WEEK3-REPORTS kit finding 1).
;;;
;;;   (dk-rewrite-h! F FROM TO) -- F in context, FROM = TO (or ==, either orientation) in
;;;                                context: land F[FROM := TO] and return it.  F survives.
;;;   (dk-nth-h! F)             -- F in context: land F with every NTH of a literal list
;;;                                reduced and return it (F itself when nothing reduces).
;;;
;;; Both prove F => F\' on a lane -- `subst\' / `nth-r\' act on the GOAL, which is the
;;; implication, so the rewrite reaches both sides and `di\' + `ass\' close it -- and
;;; detach it.  The kernel has no hypothesis-side rewrite; this is the one door.  A
;;; hypothesis not in context, or a FROM that does not occur, is an ERROR (the silent
;;; no-op is the trap CLAUDE.md names).
(define (dk-rewrite-h! f from to)
  (let* ((f  (->raw-formula f))
         (f2 (dk--replace f from to)))
    (cond ((not (dk-asm? f))
           (error "dk-rewrite-h!: the hypothesis is not in context:" (expression->string f)))
          ((equal? f2 f)
           (error "dk-rewrite-h!: FROM does not occur in the hypothesis:" (expression->string from)))
          ((dk-asm? f2) f2)
          (#t (let ((imp (list 'IMPLIES f f2)))
                (dk-have! imp (lambda () (subst (list '= from to)) (di) (ass)))
                (detach! imp)
                f2)))))

(define (dk-nth-h! f)
  (let* ((f  (->raw-formula f))
         (f2 (reduce-nth-in-expr f)))
    (cond ((not (dk-asm? f))
           (error "dk-nth-h!: the hypothesis is not in context:" (expression->string f)))
          ((equal? f2 f) f)
          ((dk-asm? f2) f2)
          (#t (let ((imp (list 'IMPLIES f f2)))
                (dk-have! imp (lambda () (nth-r) (di) (ass)))
                (detach! imp)
                f2)))))

;;; -----------------------------------------------------------------------
;;; THE LITERAL-SUBTERM INVERTER (S-2b's request for S-3, 2026-10-06; built 2026-10-07).
;;;
;;;   (dk-subterm-literal! T K TK M)
;;;
;;; With (IS-SUBTERM T K TK M), (IN TK T), (IS-TOKEN-SET T) and (IN K SET) in context, and
;;; M a LITERAL message -- a token term, (LST (LIST m1 ... mn)) with literal mi, or
;;; (ENCR g y) with literal g -- land the disjunction TK = a1 OR ... OR TK = ak over the
;;; token leaves of M (the one equation when M has one leaf) and return it.  Every token
;;; leaf must be typed (IN a T) in context and every key (IN y K); anything else is an
;;; ERROR naming the missing typing.  The claim is proved on a lane from the laws of
;;; strand-messages-laws.scm: `subterm-of-token\' at a leaf; `token-subterm-of-encr\'
;;; through an encryption (the key is not a subterm, the paper\'s Definition 2.11);
;;; `token-subterm-of-list\' through a list, whose index is enumerated by excluded middle,
;;; one case per position (nn-le-ne-succ, dk-nn!), the hypothesis rewritten at the
;;; position (dk-rewrite-h!) and its NTH reduced (dk-nth-h!).  The memberships the laws
;;; need (a literal in MSG-SET, a literal list in TUPLES(MSG-SET), by `ti\') are landed
;;; on the way.  NSL asks this question at every step of S-3.
(define (dk-stl--lst? m)
  (and (pair? m) (eq? (car m) 'LST) (= (length m) 2) (pair? (cadr m)) (eq? (car (cadr m)) 'LIST)))
(define (dk-stl--encr? m) (and (pair? m) (eq? (car m) 'ENCR) (= (length m) 3)))
(define (dk-stl--leaves m)
  (cond ((dk-stl--lst? m) (apply append (map dk-stl--leaves (cdr (cadr m)))))
        ((dk-stl--encr? m) (dk-stl--leaves (cadr m)))
        (#t (list m))))
(define (dk-stl--or eqs)
  (if (null? (cdr eqs)) (car eqs) (list 'OR (car eqs) (dk-stl--or (cdr eqs)))))
(define (dk-stl--need! f what)
  (if (not (dk-asm? f))
      (error (string-append "dk-subterm-literal!: " what " is not typed in context:") (expression->string f))))

;; land (IN M (MSG-SET T K)) for a literal M
(define (dk-stl--msg! T K m)
  (let ((goal (list 'IN m (list 'MSG-SET T K))))
    (cond ((dk-asm? goal) goal)
          ((dk-stl--lst? m)
           (dk-stl--tuples! T K (cadr m))
           (dk-cite! 'list-in-msgs T K (cadr m))
           goal)
          ((dk-stl--encr? m)
           (dk-stl--msg! T K (cadr m))
           (dk-stl--need! (list 'IN (caddr m) K) "a key")
           (dk-cite! 'encr-in-msgs T K (cadr m) (caddr m))
           goal)
          (#t (dk-stl--need! (list 'IN m T) "a token leaf")
              (dk-cite! 'token-in-msgs T K m)
              goal))))

;; land (IN (LIST m1 ... mn) (TUPLES (MSG-SET T K))) for literal mi
(define (dk-stl--tuples! T K l)
  (let ((goal (list 'IN l (list 'TUPLES (list 'MSG-SET T K)))))
    (if (not (dk-asm? goal))
        (begin
          (for-each (lambda (mi) (dk-stl--msg! T K mi)) (cdr l))
          (dk-have! goal (lambda () (dk-each-leaf! (lambda () (ti)) (lambda () (ass)))))))
    goal))

;; the OR goal built by dk-stl--or over LVS: select the disjunct (= TK A) and close it
(define (dk-stl--select! tk a lvs)
  (let loop ((ls lvs))
    (cond ((null? ls) (error "dk-subterm-literal!: a leaf not among the leaves:" (expression->string a)))
          ((equal? (car ls) a) (if (pair? (cdr ls)) (oi-l)) (ass))
          (#t (oi-r) (loop (cdr ls))))))

;; hypothesis (IS-SUBTERM T K TK M) in context, goal the OR claim: drive it closed
(define (dk-stl--drive! T K tk m lvs)
  (cond
    ((dk-stl--encr? m)
     (let ((g (cadr m)) (y (caddr m)))
       (dk-stl--msg! T K g)
       (dk-stl--need! (list 'IN y K) "a key")
       (dk-cite! 'token-subterm-of-encr T K tk g y)
       (dk-stl--drive! T K tk g lvs)))
    ((dk-stl--lst? m)
     (let* ((l (cadr m)) (ms (cdr l)) (n (length ms)))
       (dk-stl--tuples! T K l)
       (let* ((ex (dk-cite! 'token-subterm-of-list T K tk l))
              (i  (dk-skolem! ex #t))       ; i in NN, 1 <= i, i <= LENGTH l, IS-SUBTERM .. (NTH i l)
              (len (list 'LENGTH l)))
         (dk-have! (list '= len n) (lambda () (len-r) (rfl)))
         ;; i <= LENGTH l  ->  i <= n: a LENGTH term is no atom `ineq' certifies (the first run)
         (dk-rewrite-h! (list '<= i len) len n)
         (let ((at (lambda (j)                ; (= i j) in context
                     (dk-rewrite-h! (list 'IS-SUBTERM T K tk (list 'NTH i l)) i j)
                     (dk-nth-h! (list 'IS-SUBTERM T K tk (list 'NTH j l)))
                     (dk-stl--drive! T K tk (list-ref ms (- j 1)) lvs))))
           (let loop ((j 1))
             (if (= j n)
                 (begin
                   (dk-have! (list '= i n)
                     (lambda () (dk-nn! (list '<= n i) (list '<= i n))))
                   (at n))
                 (use-em (list '= i j)
                   (lambda () (at j))
                   (lambda ()
                     (dk-have! (list 'IN j 'NN) (lambda () (arith)))
                     (dk-cite! 'nn-le-ne-succ j i)          ; j <= i, i /= j  =>  succ j <= i
                     (dk-have! (list '<= (+ j 1) i) (lambda () (dk-nn! (list '<= (list 'succ j) i))))
                     (loop (+ j 1))))))))))
    (#t
     (dk-stl--need! (list 'IN m T) "a token leaf")
     (dk-cite! 'subterm-of-token T K tk m)
     (dk-stl--select! tk m lvs))))

(define (dk-subterm-literal! T K tk m)
  (let* ((hyp   (list 'IS-SUBTERM T K tk m))
         (lvs   (dk-stl--leaves m))
         (claim (dk-stl--or (map (lambda (a) (list '= tk a)) lvs))))
    (if (not (dk-asm? hyp))
        (error "dk-subterm-literal!: the subterm hypothesis is not in context:" (expression->string hyp)))
    (dk-stl--need! (list 'IN tk T) "the token")
    (dk-stl--need! (list 'IS-TOKEN-SET T) "the token set (IS-TOKEN-SET)")
    (dk-stl--need! (list 'IN K 'SET) "the key set")
    (if (not (dk-asm? claim))
        (dk-have! claim (lambda () (dk-stl--drive! T K tk m lvs))))
    claim))

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
;;; SUPERSEDED 2026-10-27 (batch 0): the definition is now KIT-6's, in the KIT-6 section at the
;;; end of this file -- on a non-FALSITY goal it tries dk-ineq! on a transaction, then EX FALSO,
;;; and ERRORS when the goal is still open (the old code returned silently: CA-MONTEL finding 2).

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

;;; THE BARE CALL (2026-10-25, KIT-5 item 3; LA-Z6 finding 5).  (dk-nn!) with
;;; no PREMISE used to pass none to `ineq', so (dk-nn!) could not show 1 <= j
;;; from 2 <= j in context.  Now a bare call first runs exactly as before,
;;; inside a TRANSACTION (`dk--transaction': kept only when it closes the
;;; goal, otherwise undone without a trace), and only if that fails runs again
;;; with the CONTEXT'S NN ORDER ATOMS as premises: every (<= a b), (< a b),
;;; (= a b) in context whose two sides are built from numerals, + - * succ and
;;; terms the context types in NN or RR (so `ineq' can certify every atom and
;;; none poisons the call), connected to the goal's terms through shared terms
;;; (the closure is taken, at most 12 atoms).  A NOT atom is never gathered:
;;; `ineq' cannot use one.  When the context holds no such atom the call is the
;;; old one, run as before.  A call that names its premises is unchanged.
(define (dk--nn-cert? e)
  (cond ((number? e) (and (exact? e) (rational? e)))
        ((and (pair? e) (eq? (car e) 'succ) (= (length e) 2)) (dk--nn-cert? (cadr e)))
        ((and (pair? e) (memq (car e) '(+ - *)) (pair? (cdr e)))
         (every dk--nn-cert? (cdr e)))
        (#t (or (dk-asm? (list 'IN e 'NN)) (dk-asm? (list 'IN e 'RR))))))

(define (dk--nn-context-premises atom)
  (let* ((cands (filter (lambda (f)
                          (and (pair? f) (memq (car f) '(< <= =)) (= (length f) 3)
                               (not (equal? f atom))
                               (dk--nn-cert? (cadr f)) (dk--nn-cert? (caddr f))))
                        (dk-asms)))
         (leaves-of (lambda (f) (filter (lambda (t) (not (number? t))) (dk--nn-leaves f '())))))
    (let loop ((terms (leaves-of atom)) (picked '()) (rest cands))
      (let ((hit (find-first (lambda (f) (any (lambda (t) (member t terms)) (leaves-of f))) rest)))
        (if (or (not hit) (>= (length picked) 12))
            (reverse picked)
            (loop (append (leaves-of hit) terms)
                  (cons hit picked)
                  (filter (lambda (f) (not (eq? f hit))) rest)))))))

(define (dk--nn-run! prems)
  (let* ((g     (dk-goal))
         (neg?  (and (pair? g) (eq? (car g) 'NOT)))
         (atom  (if neg? (cadr g) g))
         (terms (reverse (fold-left (lambda (a f) (dk--nn-leaves f a)) '() (cons atom prems))))
         (extra (delete-duplicates (append-map dk--nn-lift! terms))))
    (if neg?
        (begin
          (dk-landed (lambda () (di)))
          (apply dk-absurd! (append prems extra (list atom))))
        (apply dk-ineq! (append prems extra)))))

(define (dk-nn! . prems0)
  (if (pair? prems0)
      (dk--nn-run! (map ->raw-formula prems0))
      (let* ((g    (dk-goal))
             (atom (if (and (pair? g) (eq? (car g) 'NOT)) (cadr g) g))
             (ctx  (dk--nn-context-premises atom))
             (leaf (proof-state-focus *ps*)))
        (cond ((null? ctx) (dk--nn-run! '()))
              ((dk--transaction (lambda () (dk--nn-run! '()) (sequent-node-grounded? leaf))) #t)
              (#t (dk--nn-run! ctx))))))

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
;;; CONDITION, and the MAIN goal with (= IFT branch) ASSUMED (== when the branch is not
;;; certified defined, since 2026-10-08; `subst' of (= IFT branch) finds either); the goal is NOT
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

;;; UNARY CLOSURE LAWS (2026-10-25, KIT-5 item 6; CA-HOPF finding 1).  A head
;;; with no branch below fell through to the LEAF test, which accepts only a
;;; term the context types or an application f(a) with f in FUN(A, C) in
;;; context -- so conjugate(u2(z)) and magnitude(a) declined ("an atom is not
;;; typed"), and with them every product holding one.  The finding read this as
;;; "type-term declines products of APPLICATIONS"; it does not (u1(z) * u2(z) in
;;; CC with u1 in FUN(CC, CC) closes, and magnitude(u1(z)) * magnitude(u1(z)) in
;;; RR closes once magnitude(u1(z)) in RR is in context): what was missing is a
;;; closure law for the unary heads.  Each row is (HEAD DOMAIN RANGE THEOREM),
;;; THEOREM: forall a. a in DOMAIN => HEAD(a) in RANGE.  A goal class other than
;;; RANGE is reached by the inclusion route RANGE -> C (magnitude(a) in CC: RR,
;;; then rr-subset-cc) -- the `up' plan node.  A row whose theorem is not in the
;;; table yet (early in the load) is simply not offered.
(define *type-term-unary-laws*
  '((conjugate CC CC cc-conjugate-closed)
    (magnitude CC RR cc-magnitude-closed)
    (abs       RR RR rr-abs-closed)
    (real-part CC RR real-part-in-rr)
    (imag-part CC RR imag-part-in-rr)))

(define (type-term--unary-plan t C)
  (let ((row (assq (car t) *type-term-unary-laws*)))
    (and row
         (let ((D (cadr row)) (R (caddr row)) (thm (type-term--thm (cadddr row))))
           (and thm
                (if (eq? R C)
                    (type-term--law-plan t C thm (cdr t) (list D) #f)
                    (let ((route (in-rr--inclusion-route R C))
                          (rplan (if (dk-asm? (list 'IN t R))
                                     (list 'ctx (list 'IN t R))
                                     (type-term--law-plan t R thm (cdr t) (list D) #f))))
                      (and route rplan (every type-term--thm route)
                           (list 'up (list 'IN t C) (list rplan) route)))))))))

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
           ;; a unary head with a closure law (KIT-5), else a leaf or nothing
           ((and (= n 1) (assq h *type-term-unary-laws*))
            (or (type-term--unary-plan t C)
                (and (type-term--leaf-ok? t C) (list 'leaf typ))))
           ;; anything else is a leaf or nothing
           (#t (and (type-term--leaf-ok? t C) (list 'leaf typ)))))))))

;;; Carry out a plan: land its typing in the focus context (on the MAIN branch,
;;; each subterm's typing proved in its own `dk-have!' lane so the lane's
;;; citations stay out of the main context), or, when the typing IS the focus
;;; goal, prove it in place (`dk-have!' does that).  Returns the typing.
;;; `up' (KIT-5): land the typing in the law's own class, then cite the
;;; inclusion route to the goal's class.
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
      ((eq? kind 'up)
       (let ((kids (list-ref p 2)) (route (list-ref p 3)) (t (cadr typ)))
         (for-each type-term--exec! kids)
         (dk-have! typ (dk-lane (lambda ()
                                  (for-each (lambda (thm) (fact thm t)) route)
                                  (dk-lane-if! ass))))
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
    (define (subset-superclass-of u)      ; some X with (SUBSET u X) in context, X not u:
      (let* ((xs (let loop ((as (dk-asms)) (acc '()))   ; one already a set, else a
                   (cond ((null? as) (reverse acc))     ; number class, else the first
                         ((and (pair? (car as)) (eq? (caar as) 'SUBSET) (= (length (car as)) 3)
                               (equal? (cadr (car as)) u) (not (equal? (caddr (car as)) u)))
                          (loop (cdr as) (cons (caddr (car as)) acc)))
                         (else (loop (cdr as) acc)))))
             (known (lambda (x) (in-ctx? (list 'IN x 'SET))))
             (cls   (lambda (x) (memq x '(NN RR ZZ QQ CC)))))
        (cond ((null? xs) #f)
              ((find-first known xs) => (lambda (x) x))
              ((find-first cls xs) => (lambda (x) x))
              (else (car xs)))))
    (if (not (alpha-equiv? (dk-goal) want))
        (error "dk-sethood!: the focus goal is not" (expression->string want)
               "but" (expression->string (dk-goal))))
    (cond
      ;; already there
      ((in-ctx? want) (ass))
      ;; a typing in context: membership-implies-sethood
      ((typing-of t)
       => (lambda (typ) (fact 'membership-implies-sethood t (caddr typ)) (ass)))
      ;; a structure predicate IS-Y(t) in context: the generated is-Y-is-set (W1I)
      ((find-first (lambda (thm) (hash-table-ref/default *theorem-table* thm #f))
                   (filter-map (lambda (a)
                                 (and (pair? a) (= (length a) 2) (symbol? (car a))
                                      (equal? (cadr a) t)
                                      (symbol-append (car a) '-is-set)))
                               (dk-asms)))
       => (lambda (thm) (fact thm t) (ass)))
      ;; a literal LIST (W1I): tuples-intro over its components
      ((and (pair? t) (eq? (car t) 'LIST))
       (dk-list-in-set!))
      ;; a SUBCLASS (R4-W2, 2026-10-13): t a symbol with (SUBSET t X) in context -- the
      ;; sethood of X on a lane, then subclass-of-set-is-set.  What a citer of a read-off
      ;; guarded by `A in SET' (subspace-pts, subspace-dist, ...) holds: an open set or an
      ;; interval U with SUBSET U (PTS m) / (CARR K) / CC / RR.  The first superclass found
      ;; in context is used (its own sethood errors with the reason when it has no route).
      ((and (symbol? t) (not (memq t '(NN RR ZZ QQ CC SET EMPTY-SET ORD)))
            (subset-superclass-of t))
       => (lambda (X)
            (if (not (in-ctx? (list 'IN X 'SET)))
                (dk-have! (list 'IN X 'SET) (lambda () (dk-sethood! X))))
            (fact 'subclass-of-set-is-set t X)
            (ass)))
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

;;; =======================================================================
;;; THE SETHOOD OF A TUPLE AND OF A STRUCTURE (W1I, 2026-11-06; the user's
;;; decision "Go with the s in SET sweep").  build-is-axiom (structures.scm) ends
;;; every IS-X with the conjunct (IN s SET), so a proof that ESTABLISHES IS-X(t) by
;;; unfolding the definition owes t in SET.  t is, or unfolds to, a literal LIST,
;;; and a LIST of sets is a set: (IN L (TUPLES SET)) by tuples-intro, one leaf per
;;; component, then membership-implies-sethood.  `pair-tuple-is-set' is the n = 2
;;; case as a theorem; these are the n-ary route, as tactics.
;;;
;;; (dk-list-in-set! [UNFOLD ...])
;;;     Closes the focus goal (IN t SET).  t is a literal (LIST c1 .. cn), or is
;;;     unfolded to one first: by `mac' of each UNFOLD named, in order; else by the
;;;     def-functoid head of t; else, t a constant, by its defining theorem
;;;     (= t (LIST ..)) (declare-instance! / def-constant).  Each component
;;;     (IN ci SET) is closed by `dk-sethood!': `ass'; a typing (IN ci C) in context,
;;;     through membership-implies-sethood; a structure predicate IS-Y(ci) in
;;;     context, through the generated is-Y-is-set; an accessor of a structure in
;;;     context, an application f(a), a nested LIST, a SEP, an IMAGE, ...
;;;     ERRORS, naming the component and its position, when one stays open: TYPE
;;;     IT IN CONTEXT FIRST.  Surface tactics only (cut, ti, mac, fact, ass), so the
;;;     steps are recorded and the page replays.  Works inside a have! lane.
;;;     Returns #t.  Example, at the goal [a, f, z] in SET with a in RR,
;;;     f in FUN(RR, RR) and z in SET in context:   (dk-list-in-set!)
;;;
;;; (dk-isx-set! [UNFOLD ...])
;;;     THE PRODUCER FORM.  The focus goal is IS-X(t) just unfolded by its
;;;     definition -- `(mac 'IS-X)' and nothing else yet -- i.e. the conjunction
;;;     G = (AND (= (LENGTH t) n) ... (IN t SET)).  It cuts G', G without its last
;;;     conjunct, and on the main branch proves G from G' and t in SET, the latter
;;;     from the COMPONENT TYPINGS G' holds: t == [ACC1(t), .., ACCn(t)] (UNFOLD as
;;;     above, then `slot' / `nth-r' to the fixpoint, `qrfl'), `subst', and
;;;     dk-list-in-set! on the accessor tuple.  The focus is left on G' -- exactly
;;;     the goal the driver's next step met before the conjunct existed -- and that
;;;     leaf is returned.  So a producer gains ONE line after its unfold:
;;;         (mac 'IS-METRIC-SPACE)
;;;         (dk-isx-set!)            ; then the old driver, unchanged
;;;     ERRORS when the focus goal is not an unfolded IS-X of a declared shape
;;;     structure, or when t does not unfold to a literal LIST.
;;;
;;; (dk-is-set-theorem! NAME)
;;;     proves and installs is-NAME-is-set : forall s. IS-NAME(s) => s in SET
;;;     (a shape structure: projection of the last conjunct; a same-shape
;;;     refinement: its parent's theorem), unless it exists.  Called for every
;;;     declared structure through `isx-set--declared!' (structures.scm) and
;;;     structure-library/is-set-laws.scm.  Returns the theorem name.

(define (dk-list--const-def t)
  ;; the name of a theorem (= t (LIST ..)) or (== t (LIST ..)), t a constant
  (let ((hit #f))
    (hash-table-walk *theorem-table*
      (lambda (name f)
        (if (and (not hit) (pair? f) (memq (car f) '(= ==)) (= (length f) 3)
                 (eq? (cadr f) t) (dk-head-is? (caddr f) 'LIST))
            (set! hit name))))
    hit))

(define (dk-list--unfold-name t)
  (cond ((and (pair? t) (symbol? (car t))
              (hash-table-ref/default *functoid-registry* (car t) #f))
         (car t))
        ((symbol? t) (dk-list--const-def t))
        (#t #f)))

(define (dk-list--unfold-names t unfolds who)
  (cond ((pair? unfolds) unfolds)
        ((dk-head-is? t 'LIST) '())
        ((dk-list--unfold-name t) => list)
        (#t (error (string-append who ": the term is not a literal LIST and no unfolding of it is known"
                                  " (name the macete):")
                   (expression->string t)))))

(define (dk-list--component! leaf lst)
  (let* ((c (cadr (dk-goal-of leaf)))
         (i (let loop ((cs (cdr lst)) (k 1))
              (cond ((null? cs) #f) ((equal? (car cs) c) k) (#t (loop (cdr cs) (+ k 1)))))))
    (dk-focus! leaf)
    (let ((why (call-with-current-continuation
                (lambda (k)
                  (with-exception-handler
                   (lambda (e) (k (if (condition? e) (condition/report-string e) e)))
                   (lambda () (dk-sethood! c) #f))))))
      (if (not (sequent-node-grounded? leaf))
          (error (string-append
                  "dk-list-in-set!: component " (if i (number->string i) "?")
                  " of the LIST is not closed: " (expression->string (list 'IN c 'SET))
                  (if (string? why) (string-append " -- " why) "")
                  " -- type it in context first"))))))

(define (dk-list-in-set! . unfolds)
  (let ((g0 (dk-goal)))
    (if (not (and (dk-head-is? g0 'IN) (= (length g0) 3) (eq? (caddr g0) 'SET)))
        (error "dk-list-in-set!: the focus goal is not (IN t SET):" (expression->string g0)))
    (let ((t0 (cadr g0)))
      (if (not (dk-head-is? t0 'LIST))
          (let ((names (dk-list--unfold-names t0 unfolds "dk-list-in-set!")))
            (for-each (lambda (m) (mac m)) names)
            (if (not (and (dk-head-is? (dk-goal) 'IN) (dk-head-is? (cadr (dk-goal)) 'LIST)))
                (error "dk-list-in-set!: after unfolding by" names
                       "the goal is not a literal LIST in SET:" (expression->string (dk-goal))))))
      ;; NB the name: `L' and a leaf binder `l' are ONE folded symbol (CLAUDE.md, case folding)
      (let* ((lst (cadr (dk-goal)))
             (tup (list 'IN lst '(TUPLES SET))))
        (dk-have! tup
          (lambda ()
            ;; the component leaves are found by GOAL and CONTEXT, not by a leaf diff:
            ;; tuples-intro's (IN ci SET) may hash-cons onto a leaf that is already open
            ;; (a nested LIST whose components are also components of the outer one)
            (let* ((leaf0 (proof-state-focus *ps*))
                   (ctx   (dk-asms-of leaf0)))
              (ti)
              (if (not (dk-fired? leaf0))
                  (error "dk-list-in-set!: tuples-intro did not apply to" (expression->string tup)))
              (for-each
               (lambda (c)
                 (let ((lf (find-first (lambda (l) (and (not (sequent-node-grounded? l))
                                                        (equal? (dk-goal-of l) (list 'IN c 'SET))
                                                        (equal? (dk-asms-of l) ctx)))
                                       (proof-leaves))))
                   (if lf (dk-list--component! lf lst))))
               (cdr lst)))))
        (let ((leaf (proof-state-focus *ps*)))
          (fact 'membership-implies-sethood lst '(TUPLES SET))
          (if (not (sequent-node-grounded? leaf)) (ass))
          (if (not (sequent-node-grounded? leaf))
              (error "dk-list-in-set!: membership-implies-sethood did not close" (expression->string g0))))
        #t))))

;; the right spine of a conjunction, and the conjunction without its last conjunct
(define (dk-isx--spine g)
  (if (dk-head-is? g 'AND) (cons (cadr g) (dk-isx--spine (caddr g))) (list g)))
(define (dk-isx--drop-last g)
  (if (dk-head-is? (caddr g) 'AND)
      (list 'AND (cadr g) (dk-isx--drop-last (caddr g)))
      (cadr g)))

;; W1K: the conjuncts of a conjunction, every AND flattened
(define (dk-isx--conj-leaves f)
  (if (dk-head-is? f 'AND)
      (append (dk-isx--conj-leaves (cadr f)) (dk-isx--conj-leaves (caddr f)))
      (list f)))
;; W1K: split the conjunction F (in context) only where a conjunct is missing: `ai' an
;; AND only when one of its two conjuncts is not in context (up to alpha), then descend
;; into each conjunct that is itself an AND (in context now, landed or already there).
(define (dk-isx--split-missing! f)
  (if (dk-head-is? f 'AND)
      (begin
        (if (not (and (dk-asm? (cadr f)) (dk-asm? (caddr f))))
            (dk-landed (lambda () (ai f))))
        (dk-isx--split-missing! (cadr f))
        (dk-isx--split-missing! (caddr f)))))

;; the declared SHAPE structure whose IS-X definiens, instantiated at t, is g
(define (dk-isx--structure-of g t)
  (let ((hit #f))
    (hash-table-walk *structure-table*
      (lambda (name sd)
        (if (not hit)
            (let ((f (hash-table-ref/default *theorem-table* (symbol-append 'IS- name) #f)))
              (if (and (dk-head-is? f 'FORALL) (dk-head-is? (quantifier-body f) 'IFF)
                       (alpha-equiv? (subst-free (quantifier-var f) t (caddr (quantifier-body f))) g))
                  (set! hit sd))))))
    hit))

(define (dk-isx--nth-redex? e)
  (and (pair? e)
       (or (and (eq? (car e) 'NTH) (= (length e) 3) (dk-head-is? (caddr e) 'LIST))
           (any-pred dk-isx--nth-redex? e))))

;; on the focus goal (IN t SET), the component typings in context
(define (dk-isx--sethood! t accs unfolds)
  ;; ACC_i(t) are read off while t is still FOLDED (an instance or functor projection
  ;; gives the slot value; otherwise the outermost (ACC_i t) -> (NTH i t)), then t is
  ;; unfolded and the NTHs of the literal LIST reduced; accessors met inside the
  ;; components are read off on both sides alike, to the fixpoint.
  (let* ((tl (cons 'LIST (map (lambda (a) (list a t)) accs)))
         (e  (list '== t tl)))
    (dk-have! e
      (lambda ()
        (let ((leaf (proof-state-focus *ps*))
              (names (dk-list--unfold-names t unfolds "dk-isx-set!")))
          (define (slots!) (for-each (lambda (a) (if (dk-contains? (dk-goal) a) (slot a))) accs))
          (slots!)
          (for-each (lambda (m) (mac m)) names)
          (let loop ((k 0))
            (if (not (sequent-node-grounded? leaf))
                (let ((g (dk-goal)))
                  (cond ((alpha-equiv? (cadr g) (caddr g))
                         (qrfl)
                         (if (not (sequent-node-grounded? leaf))
                             (error "dk-isx-set!: the tuple read-off left owed leaves (a component that is itself an accessor application of t's structure mixes the read-off: name the unfolding, or prove t in SET by dk-list-in-set! on a lane):"
                                    (map (lambda (l) (expression->string (dk-goal-of l))) (dk-open-leaves)))))
                        ((> k 8) (error "dk-isx-set!: the tuple read-off reached no fixpoint:"
                                        (expression->string g)))
                        ((dk-isx--nth-redex? g) (nth-r) (loop (+ k 1)))
                        (#t (slots!) (loop (+ k 1))))))))))
    (subst (list '= t tl))
    (dk-list-in-set!)))

(define (dk-isx-set! . unfolds)
  (let* ((g  (dk-goal))
         (cs (dk-isx--spine g))
         (sc (car (last-pair cs))))
    (if (not (and (dk-head-is? g 'AND) (dk-head-is? sc 'IN) (= (length sc) 3) (eq? (caddr sc) 'SET)))
        (error "dk-isx-set!: the focus goal is not an unfolded IS-X ending in (IN t SET):"
               (expression->string g)))
    (let* ((t    (cadr sc))
           (sd   (or (dk-isx--structure-of g t)
                     (error "dk-isx-set!: the focus goal is not the definiens of a declared IS-X at"
                            (expression->string t))))
           (accs (map car (structure-def-slots sd)))
           (g1   (dk-isx--drop-last g))
           (new  (dk-opened (lambda () (cut g1))))
           (side (any-pred (lambda (l) (alpha-equiv? (dk-goal-of l) g1)) new))
           (main (any-pred (lambda (l) (not (eq? l side))) new)))
      (if (not (and side main))
          (error "dk-isx-set!: the cut did not open a main and a side leaf for" (expression->string g1)))
      (dk-focus! main)
      ;; W1K: a driver may have landed some or all conjuncts of G' BEFORE the unfold
      ;; (W1J-B s.3, W1J-C s.2a); `dk-split!' then lands nothing at some level and
      ;; errors.  When no conjunct is in context the old split runs unchanged.
      (if (dk-head-is? g1 'AND)
          (if (any-pred dk-asm? (dk-isx--conj-leaves g1))
              (dk-isx--split-missing! g1)
              (dk-split! g1)))
      (dk-have! sc (lambda () (dk-isx--sethood! t accs unfolds)))
      (dk-conj-close!)
      (if (not (sequent-node-grounded? main))
          (error "dk-isx-set!: the conjunction did not close from its parts" (expression->string g)))
      (dk-focus! side)
      side)))

(define (dk-is-set-theorem! name)
  (let* ((is-x   (symbol-append 'IS- name))
         (thm    (symbol-append 'is- name '-is-set))
         (shape? (and (lookup-structure name) #t))
         (parent (and (not shape?)
                      (let ((d (lookup-definitional-structure name)))
                        (and d (definitional-structure-parent d)))))
         (def    (if shape? is-x (symbol-append 'is- name '-def))))
    (cond
      ((hash-table-ref/default *theorem-table* thm #f) thm)
      ((not (or shape? parent))
       (error "dk-is-set-theorem!: not a declared structure" name))
      (#t
       (dk-sp-qed!
        (make-wff `(FORALL s (IMPLIES (,is-x s) (IN s SET))))
        (lambda ()
          (let* ((landed (dk-peel!))
                 (h (or (find-first (lambda (f) (dk-head-is? f is-x)) landed)
                        (error "dk-is-set-theorem!: the peel landed no" is-x)))
                 (v (cadr h))
                 (d (dk-landed-1 (lambda () (mac-h def h)))))
            (if (dk-head-is? d 'AND) (dk-split! d))
            (if (not shape?) (fact (symbol-append 'is- parent '-is-set) v))
            (ass)))
        thm)
       (topic! thm 'plumbing)
       thm))))

;;; =======================================================================
;;; dk-diff! -- IS-DIFF-ON of an EXPLICIT complex expression, with its
;;; derivative (2026-10-04; the kit candidate both week-1 agents named).
;;;
;;;   (dk-diff! U LAM A [L])   land IS-DIFF-ON(CC-NORMED-FIELD, U, LAM, A, L*) in
;;;                            the focus context and return that formula; L* is
;;;                            L when given, else the textbook derivative of
;;;                            LAM's body at A.  LAM is (VNB-LAMBDA x U e).
;;;   (dk-diff!)               the same, read off a focus goal IS-DIFF-ON(...),
;;;                            which it then closes.
;;;   (dk-holomorphic! U LAM)  close the focus goal HOLOMORPHIC-ON(U, LAM).
;;;
;;; THE GRAMMAR of e over the bound variable x: x; a term without x (a
;;; constant); + and * (binary); - (binary and unary); recip; power with a
;;; numeral exponent; CC-EXP, CC-SIN, CC-COS, CC-LOG; and (g s) for a SYMBOL g
;;; with IS-DIFF-ON(CC-NORMED-FIELD, V, g, _, _) or HOLOMORPHIC-ON(V, g) in
;;; context.  Anything else is an error naming the subterm.
;;;
;;; THE PLAN FIRST (as type-term).  A pure pass over e collects the side
;;; conditions the laws will need and the context does not hold -- the
;;; denominators that must not vanish (forall y in U. s(y) /= 0), the
;;; arguments of a log that must lie in the slit plane, the arguments of an
;;; opaque g that must lie in its domain -- and posts each as a `cut' on the
;;; MAIN branch, left OPEN and announced (";; dk-diff!: OWED ..."), so that the
;;; lanes below find them in context.  Nothing is asserted: an owed leaf is
;;; the user's to close, and the proof is not done until it is.
;;;
;;; THE ENGINE drives the library's laws bottom-up over e -- diff-on-identity,
;;; -const, -sum, -product, -chain (with cc-exp-deriv / cc-sin-deriv /
;;; cc-cos-deriv / cc-log-deriv or the opaque g's own fact), diff-on-recip-cc
;;; -- reading the FUNCTION TERM and the DERIVATIVE of every instance off the
;;; formula `dk-cite!' landed, never rebuilding them.  The laws produce a
;;; canonical lambda h over K's own operations ((ADD K), (MUL K)) with the
;;; sub-lambdas applied; the result is carried to the user's LAM by
;;; diff-on-transfer-ptwise-eq, whose pointwise equation is proved by beta to a
;;; fixpoint, the slot read-offs cc-nf-add-apply / cc-nf-mul-apply and the
;;; three de-normalising identities (p + (-1) q = p - q, (-1) p = -p, the
;;; power products), then qrfl -- or, when the two sides still differ, by crs
;;; with the reciprocals named (dk-name!).  The derivative L* is reached from
;;; the laws' K-form value L_K the same way, through the universal
;;;     forall v. v = L_K  =>  IS-DIFF-ON(K, U, LAM, A, v)
;;; instantiated at L* (a `subst' of L* in the goal would also rewrite its
;;; occurrences inside LAM, e.g. the c of c * x).  Every step is a surface
;;; tactic; the page replays without new machinery; no kernel rule is touched.
;;;
;;; K is CC-NORMED-FIELD.  The general-K laws are cited at it; the read-offs,
;;; the exp / log / recip laws and the typing table are CC's.
;;; =======================================================================

(define dkd-K    'CC-NORMED-FIELD)
(define dkd-nfm  '(NF-METRIC-SPACE CC-NORMED-FIELD))
(define dkd-carr '(CARR CC-NORMED-FIELD))
(define dkd-exp-lam '(VNB-LAMBDA dkdev_ CC (CC-EXP dkdev_)))
(define dkd-sin-lam '(VNB-LAMBDA dkdev_ CC (CC-SIN dkdev_)))
(define dkd-cos-lam '(VNB-LAMBDA dkdev_ CC (CC-COS dkdev_)))
(define dkd-slit    '(SEP cxsu_ CC (NOT (AND (= (imag-part cxsu_) 0) (<= (real-part cxsu_) 0)))))
(define dkd-log-lam (list 'VNB-LAMBDA 'dkdlv_ dkd-slit '(CC-LOG dkdlv_)))
(define (dkd-slit-guard t)
  (list 'NOT (list 'AND (list '= (list 'imag-part t) 0) (list '<= (list 'real-part t) 0))))

(define dkd-owed '())                    ; the obligations posted by this run
(define dkd-debug #f)                    ; #t: the derivative equation runs unprotected (errors show)

(define (dkd-str x) (if (string? x) x (expression->string x)))
(define (dkd-warn . xs)
  (vnb--print-warning (apply string-append "dk-diff!: " (map dkd-str xs))))
(define (dkd-error . xs)
  (error (apply string-append "dk-diff!: " (map dkd-str xs))))

;;; ---------------------------------------------------------------- terms
(define (dkd-free-in? x e)
  (cond ((eq? e x) #t)
        ((pair? e)
         (if (and (eq? (car e) 'VNB-LAMBDA) (eq? (cadr e) x))
             #f
             (any (lambda (s) (dkd-free-in? x s)) (cdr e))))
        (#t #f)))
(define (dkd-sub e x t) (subst-free x t e))       ; e[x := t], capture-avoiding
(define (dkd-numeral? t) (and (number? t) (exact? t)))
(define (dkd-nat? t) (and (dkd-numeral? t) (integer? t) (>= t 0)))
(define (dkd-redex? e)
  (and (pair? e) (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA)))
(define (dkd-find e pred)                         ; first subterm satisfying PRED, outermost
  (cond ((pred e) e)
        ((pair? e) (let loop ((xs e)) (cond ((null? xs) #f) ((dkd-find (car xs) pred)) (#t (loop (cdr xs))))))
        (#t #f)))
(define (dkd-has-redex? e) (and (dkd-find e dkd-redex?) #t))
(define (dkd-kop? e)
  (and (pair? e) (= (length e) 3)
       (or (equal? (car e) '(ADD CC-NORMED-FIELD)) (equal? (car e) '(MUL CC-NORMED-FIELD)))))
(define (dkd-kop-find e)                          ; an innermost K-operation
  (cond ((not (pair? e)) #f)
        ((and (dkd-kop? e) (not (dkd-kop-find (cadr e))) (not (dkd-kop-find (caddr e)))) e)
        (#t (let loop ((xs e)) (cond ((null? xs) #f) ((dkd-kop-find (car xs))) (#t (loop (cdr xs))))))))
;; pat[v := w] = term for some w?  Return w, or #f.
(define (dkd-match pat v term)
  (let ((b #f) (ok #t))
    (let walk ((p pat) (t term))
      (cond ((not ok) #f)
            ((eq? p v) (cond ((not b) (set! b t)) ((not (equal? b t)) (set! ok #f))))
            ((and (pair? p) (pair? t) (= (length p) (length t))) (for-each walk p t))
            ((equal? p t) #t)
            (#t (set! ok #f))))
    (and ok b)))

;;; ---------------------------------------------------------- the context
(define (dkd-asms) (dk-asms))
;; the class D with (IN t D) in context, preferring CC
(define (dkd-ctx-class t)
  (let ((hits (filter (lambda (a) (and (pair? a) (eq? (car a) 'IN) (= (length a) 3) (equal? (cadr a) t)))
                      (dkd-asms))))
    (cond ((null? hits) #f)
          ((find-first (lambda (a) (eq? (caddr a) 'CC)) hits) => caddr)
          (#t (caddr (car hits))))))
;; (IN g (FUN D CC)) in context, or derived from IS-DIFF-ON / HOLOMORPHIC-ON of g: D
(define (dkd-fun-dom! g)
  (or (dkd-fun-dom g)
      (let ((d (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IS-DIFF-ON) (= (length a) 6)
                                            (equal? (cadr a) dkd-K) (eq? (cadddr a) g)))
                           (dkd-asms))))
        (and d (begin (dk-cite! 'diff-on-in-fun dkd-K (caddr d) g (list-ref d 4) (list-ref d 5))
                      (dkd-fun-carr->cc! g (caddr d))
                      (caddr d))))
      (let ((h (find-first (lambda (a) (and (pair? a) (eq? (car a) 'HOLOMORPHIC-ON) (= (length a) 3) (eq? (caddr a) g)))
                           (dkd-asms))))
        (and h (begin (dk-have! (list 'IN g (list 'FUN (cadr h) 'CC))
                        (lambda () (mac-h 'HOLOMORPHIC-ON h) (dk-split-all!) (ass)))
                      (cadr h))))))
(define (dkd-fun-dom g)
  (let ((a (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IN) (= (length a) 3) (equal? (cadr a) g)
                                         (pair? (caddr a)) (eq? (car (caddr a)) 'FUN)
                                         (member (caddr (caddr a)) (list 'CC dkd-carr))))
                       (dkd-asms))))
    (and a (cadr (caddr a)))))
;; a universal (FORALL v (IMPLIES (IN v D) BODY)) in context whose BODY matches TARGET
;; at some w with (IN w D) in context: instantiate it and return what landed.
(define (dkd-from-universal! target)
  (let loop ((as (dkd-asms)))
    (cond ((null? as) #f)
          (#t (let ((a (car as)))
                (if (and (pair? a) (eq? (car a) 'FORALL) (= (length a) 3)
                         (pair? (caddr a)) (eq? (car (caddr a)) 'IMPLIES)
                         (pair? (cadr (caddr a))) (eq? (car (cadr (caddr a))) 'IN)
                         (eq? (cadr (cadr (caddr a))) (cadr a)))
                    (let* ((v (cadr a)) (D (caddr (cadr (caddr a)))) (body (caddr (caddr a)))
                           (w (dkd-match body v target)))
                      (if (and w (dk-asm? (list 'IN w D)))
                          (let ((r (dk-apply! a w)))
                            (if (dk-asm? target) target (loop (cdr as))))
                          (loop (cdr as))))
                    (loop (cdr as))))))))

;;; ------------------------------------------------------------- setting up
;; CARR(K) and CC are quasi-equal (cc-nf-carr), but a `subst' of CC -> CARR(K) in a
;; goal rewrites EVERY CC, the lambda domains included; so the two conversions go
;; through universals proved once per proof on a lane and instantiated.
(define dkd-carr->cc-law '(FORALL dkdcv_ (IMPLIES (IN dkdcv_ (CARR CC-NORMED-FIELD)) (IN dkdcv_ CC))))
(define dkd-cc->carr-law '(FORALL dkdcv_ (IMPLIES (IN dkdcv_ CC) (IN dkdcv_ (CARR CC-NORMED-FIELD)))))
(define (dkd-lemma! law thunk)
  (if (not (dk-asm? law)) (dk-have! law thunk))
  (dk-ctx-form law))
(define (dkd-carr->cc! t)                 ; (IN t CC) from (IN t (CARR K)) in context
  (let ((want (list 'IN t 'CC)))
    (if (not (dk-asm? want))
        (dk-apply! (dkd-lemma! dkd-carr->cc-law
                     (lambda () (dk-peel!) (subst (list '== 'CC dkd-carr)) (ass)))
                   t))
    (if (not (dk-asm? want)) (dkd-error "carr->cc did not land " want))
    want))
(define (dkd-cc->carr! t)                 ; (IN t (CARR K)) from (IN t CC) in context
  (let ((want (list 'IN t dkd-carr)))
    (if (not (dk-asm? want))
        (dk-apply! (dkd-lemma! dkd-cc->carr-law
                     (lambda () (dk-peel!) (subst (list '== dkd-carr 'CC)) (ass)))
                   t))
    (if (not (dk-asm? want)) (dkd-error "cc->carr did not land " want))
    want))

(define dkd-fun-carr->cc-law
  '(FORALL dkdfu_ (FORALL dkdfv_ (IMPLIES (IN dkdfv_ (FUN dkdfu_ (CARR CC-NORMED-FIELD)))
                                           (IN dkdfv_ (FUN dkdfu_ CC))))))
(define (dkd-fun-carr->cc! g U)           ; (IN g (FUN U CC)) from (IN g (FUN U (CARR K)))
  (let ((want (list 'IN g (list 'FUN U 'CC))))
    (if (not (dk-asm? want))
        (dk-apply! (dkd-lemma! dkd-fun-carr->cc-law
                     (lambda () (dk-peel!) (subst (list '== 'CC dkd-carr)) (ass)))
                   U g))
    (if (not (dk-asm? want)) (dkd-error "fun carr->cc did not land " want))
    want))

(define (dkd-setup!)
  (if (not (dk-asm? (list 'IS-NORMED-FIELD dkd-K))) (fact 'cc-is-normed-field))
  (if (not (dk-asm? (list '== dkd-carr 'CC))) (fact 'cc-nf-carr)))

;; (IS-OPEN (NF-METRIC-SPACE K) U) in context, or error
(define (dkd-open! U)
  (let ((want (list 'IS-OPEN dkd-nfm U)))
    (cond
      ((dk-asm? want) want)
      ((eq? U 'CC)
       (if (not (dk-asm? (list 'IS-METRIC-SPACE dkd-nfm))) (fact 'nf-cc-is-metric-space))
       (fact 'nf-metric-carrier dkd-K)
       (if (not (dk-asm? (list '== (list 'PTS dkd-nfm) 'CC)))
           (dk-have! (list '== (list 'PTS dkd-nfm) 'CC)
             (lambda () (subst (list '== (list 'PTS dkd-nfm) dkd-carr)) (ass))))
       (fact 'carrier-is-open dkd-nfm)
       (dk-have! want (lambda () (subst (list '== 'CC (list 'PTS dkd-nfm))) (ass)))
       want)
      (#t
       (let ((ms (list 'IS-OPEN 'CC-MS U)))
         (if (not (dk-asm? ms))
             (let ((h (find-first (lambda (a) (and (pair? a) (eq? (car a) 'HOLOMORPHIC-ON) (equal? (cadr a) U)))
                                  (dkd-asms))))
               (if h (fact 'holomorphic-on-open-cc-ms U (caddr h)))))
         (if (not (dk-asm? ms))
             (dkd-error "U is not known to be open: neither " want " nor " ms " is in context"))
         (let ((iff (dk-cite! 'cc-ms-open-iff U)))
           (dk-have! want (lambda () (keep iff ms) (prop))))
         want)))))

;; (IN U SET) as the focus goal
(define (dkd-set-leaf! U)
  (cond ((eq? U 'CC) (fact 'cc-is-set))
        (#t (fact 'nf-open-is-set dkd-K U)))
  (ass))

;;; ------------------------------------------------------------- typing in CC
;; forall y in U. NOT (= s 0): derive or post.  Returns the formula.
(define (dkd-nonzero! s)
  (let ((want (list 'NOT (list '= s 0))))
    (cond ((dk-asm? want) want)
          ((dkd-from-universal! want) want)
          ((and (pair? s) (eq? (car s) '*) (= (length s) 3))
           (dkd-cc! (cadr s)) (dkd-cc! (caddr s))
           (dkd-nonzero! (cadr s)) (dkd-nonzero! (caddr s))
           (dk-cite! 'cc-mul-nonzero (cadr s) (caddr s))
           (if (not (dk-asm? want)) (dkd-error "cc-mul-nonzero did not land " want))
           want)
          (#t (dkd-error "not known: " want " (an owed obligation the plan should have posted)")))))

(define (dkd-slit! t)                      ; the slit-plane guard at t
  (let ((want (dkd-slit-guard t)))
    (cond ((dk-asm? want) want)
          ((dkd-from-universal! want) want)
          (#t (dkd-error "not known: " want)))))

;; land (IN t CC); return it
(define (dkd-cc! t)
  (let ((typ (list 'IN t 'CC)))
    (cond
      ((dk-asm? typ) typ)
      ((eqv? t +i) (fact 'cc-i-in) typ)
      ((number? t) (dk-type! t 'CC) typ)
      ((symbol? t)
       (let ((D (dkd-ctx-class t)))
         (cond ((not D) (dk-type! t 'CC))
               ((eq? D 'CC) #t)
               ((dk-asm? (list 'SUBSET D 'CC)) (fact 'subset-mem-fwd D 'CC t))
               ((dk-asm? (list 'IS-OPEN dkd-nfm D))
                (fact 'cc-open-subset-cc D) (fact 'subset-mem-fwd D 'CC t))
               (#t (dk-type! t 'CC)))
         (if (not (dk-asm? typ)) (dkd-error "could not type " typ))
         typ))
      ((pair? t)
       (let ((h (car t)))
         (cond
           ((and (memq h '(CC-EXP CC-SIN CC-COS)) (= (length t) 2))
            (dkd-cc! (cadr t))
            (let ((c (dk-cite! (cond ((eq? h 'CC-EXP) 'cc-exp-converges)
                                     ((eq? h 'CC-SIN) 'cc-sin-converges)
                                     (#t 'cc-cos-converges))
                               (cadr t))))
              (if (not (dk-asm? typ)) (dk-split! c)))
            typ)
           ((and (eq? h 'CC-LOG) (= (length t) 2))
            (dkd-cc! (cadr t))
            (dkd-slit! (cadr t))
            (let ((c (dk-cite! 'cc-log-in-slit (cadr t))))
              (if (not (dk-asm? typ)) (dk-split! c)))
            typ)
           ((and (eq? h 'recip) (= (length t) 2))
            (dkd-cc! (cadr t))
            (dkd-nonzero! (cadr t))
            (dk-have! (list 'AND (list 'IN (cadr t) 'CC) (list 'NOT (list '= (cadr t) 0)))
              (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
            (dk-cite! 'cc-recip-closed (cadr t))
            typ)
           ((memq h '(+ * -))
            (for-each dkd-cc! (cdr t)) (dk-type! t 'CC) typ)
           ((eq? h 'power)
            (dkd-cc! (cadr t)) (dk-type! t 'CC) typ)
           ((and (symbol? h) (= (length t) 2))
            (let ((D (dkd-fun-dom! h)))
              (if (not D) (dkd-error "no (IN " h " (FUN D CC)), IS-DIFF-ON or HOLOMORPHIC-ON of " h " in context, for " t))
              (dkd-in! (cadr t) D)
              (fact 'fun-apply-type-c h D 'CC (cadr t))
              typ))
           (#t (dk-type! t 'CC) typ))))
      (#t (dkd-error "cannot type " t)))))

;; land (IN t D)
(define (dkd-in! t D)
  (let ((want (list 'IN t D)))
    (cond ((dk-asm? want) want)
          ((eq? D 'CC) (dkd-cc! t))
          ((dkd-from-universal! want) want)
          (#t (dk-type! t D) want))))

;; (IN t (CARR K)) from (IN t CC)
(define (dkd-carr! t)
  (let ((want (list 'IN t dkd-carr)))
    (if (not (dk-asm? want))
        (begin (dkd-cc! t) (dkd-cc->carr! t)))
    want))

;;; ------------------------------------------- the goal, back to user form
;; the three de-normalising identities, proved once per proof on a lane
(define dkd-sub-law
  '(FORALL dkdp_ (IMPLIES (IN dkdp_ CC) (FORALL dkdq_ (IMPLIES (IN dkdq_ CC)
     (= (+ dkdp_ (* -1 dkdq_)) (- dkdp_ dkdq_)))))))
(define dkd-neg-law
  '(FORALL dkdp_ (IMPLIES (IN dkdp_ CC) (= (* -1 dkdp_) (- dkdp_)))))
(define dkd-sub2-law                      ; p + (-q) = p - q (the inner (-1) q may have been rewritten first)
  '(FORALL dkdp_ (IMPLIES (IN dkdp_ CC) (FORALL dkdq_ (IMPLIES (IN dkdq_ CC)
     (= (+ dkdp_ (- dkdq_)) (- dkdp_ dkdq_)))))))
(define (dkd-power-law n)
  (let ((prod (let loop ((k n)) (cond ((= k 1) 'dkdp_) (#t (list '* 'dkdp_ (loop (- k 1))))))))
    (list 'FORALL 'dkdp_ (list 'IMPLIES '(IN dkdp_ CC) (list '= prod (list 'power 'dkdp_ n))))))
(define (dkd-law! law)
  (if (not (dk-asm? law)) (dk-have! law (lambda () (dk-peel!) (crs))))
  (dk-ctx-form law))

(define (dkd-product-of t)               ; t = (* p (* p ... p)) with k factors: (p . k), else #f
  (let loop ((e t) (k 1))
    (cond ((and (pair? e) (eq? (car e) '*) (= (length e) 3) (equal? (cadr e) (cadr t)))
           (loop (caddr e) (+ k 1)))
          ((equal? e (cadr t)) (cons e k))
          (#t #f))))

;; Rewrite the FOCUS GOAL: K's zero / one / operations to the surface ones,
;; p + (-1) q to p - q, (-1) p to -p, repeated products to powers (for the
;; exponents in POWERS).  Loops to a fixpoint.
(define (dkd-user-form! powers)
  (let loop ()
    (let* ((g (dk-goal))
           (zero (dkd-find g (lambda (e) (equal? e '(ZERO CC-NORMED-FIELD)))))
           (one  (and (not zero) (dkd-find g (lambda (e) (equal? e '(ONE CC-NORMED-FIELD))))))
           ;; the surface rewrites come BEFORE the read-off of a K-operation, whose
           ;; arguments must be typed: a denominator still spelled p + (-1) q matches
           ;; no non-vanishing hypothesis
           (sub  (and (not zero) (not one)
                      (dkd-find g (lambda (e) (and (pair? e) (eq? (car e) '+) (= (length e) 3)
                                                   (pair? (caddr e)) (eq? (car (caddr e)) '*)
                                                   (= (length (caddr e)) 3) (eqv? (cadr (caddr e)) -1))))))
           (sub2 (and (not zero) (not one) (not sub)
                      (dkd-find g (lambda (e) (and (pair? e) (eq? (car e) '+) (= (length e) 3)
                                                   (pair? (caddr e)) (eq? (car (caddr e)) '-)
                                                   (= (length (caddr e)) 2))))))
           (neg  (and (not zero) (not one) (not sub) (not sub2)
                      (dkd-find g (lambda (e) (and (pair? e) (eq? (car e) '*) (= (length e) 3)
                                                   (eqv? (cadr e) -1))))))
           (pw   (and (not zero) (not one) (not sub) (not sub2) (not neg) (pair? powers)
                      (dkd-find g (lambda (e) (let ((pk (and (pair? e) (eq? (car e) '*) (dkd-product-of e))))
                                                (and pk (memv (cdr pk) powers)))))))
           (kop  (and (not zero) (not one) (not sub) (not sub2) (not neg) (not pw) (dkd-kop-find g))))
      (cond
        (zero (slot 'ZERO) (loop))
        (one  (slot 'ONE) (loop))
        (kop
         (let ((s (cadr kop)) (t (caddr kop)) (add? (equal? (car kop) '(ADD CC-NORMED-FIELD))))
           (dkd-cc! s) (dkd-cc! t)
           (fact (if add? 'cc-nf-add-apply 'cc-nf-mul-apply) s t)
           (subst (list '== kop (list (if add? '+ '*) s t)))
           (loop)))
        (sub
         (let ((p (cadr sub)) (q (caddr (caddr sub))))
           (dkd-cc! p) (dkd-cc! q)
           (dk-apply! (dkd-law! dkd-sub-law) p q)
           (subst (list '= sub (list '- p q)))
           (loop)))
        (sub2
         (let ((p (cadr sub2)) (q (cadr (caddr sub2))))
           (dkd-cc! p) (dkd-cc! q)
           (dk-apply! (dkd-law! dkd-sub2-law) p q)
           (subst (list '= sub2 (list '- p q)))
           (loop)))
        (neg
         (let ((p (caddr neg)))
           (dkd-cc! p)
           (dk-apply! (dkd-law! dkd-neg-law) p)
           (subst (list '= neg (list '- p)))
           (loop)))
        (pw
         (let* ((pk (dkd-product-of pw)) (p (car pk)) (k (cdr pk)))
           (dkd-cc! p)
           (dk-apply! (dkd-law! (dkd-power-law k)) p)
           (subst (list '= pw (list 'power p k)))
           (loop)))
        (#t g)))))

;; one bottom-up pass of contraction over the redexes PRESENT in e (the kernel's
;; `lam-b' pass; a redex a contraction creates is left standing)
;; A redex sitting under a binder whose argument mentions that binder is left
;; standing (its owed typing would name a bound variable); every other present
;; redex is contracted, licensed or owed.
(define (dkd-reduce1 e . opt)
  (let ((bound (if (pair? opt) (car opt) '())))        ; alist (var . domain) of the enclosing binders
    (cond ((not (pair? e)) e)
          ((and (pair? (car e)) (eq? (caar e) 'VNB-LAMBDA) (= (length e) 2) (= (length (car e)) 4)
                (symbol? (cadr (car e))))
           (let* ((lam (car e)) (v (cadr lam)) (D (dkd-reduce1 (caddr lam) bound))
                  (a (dkd-reduce1 (cadr e) bound))
                  (body (dkd-reduce1 (cadddr lam) (cons (cons v D) bound)))
                  (lam2 (list 'VNB-LAMBDA v D body))
                  (mentions-bound? (any (lambda (b) (dkd-free-in? (car b) a)) bound))
                  (licensed-by-binder? (and (symbol? a) (assq a bound) (alpha-equiv? (cdr (assq a bound)) D))))
             (if (and mentions-bound? (not licensed-by-binder?))
                 (list lam2 a)
                 (subst-free v a body))))
          ((and (eq? (car e) 'VNB-LAMBDA) (= (length e) 4) (symbol? (cadr e)))
           (let ((D (dkd-reduce1 (caddr e) bound)))
             (list 'VNB-LAMBDA (cadr e) D (dkd-reduce1 (cadddr e) (cons (cons (cadr e) D) bound)))))
          ((and (memq (car e) '(FORALL FORSOME SEP BIG-UNION IOTA)) (pair? (cdr e)) (symbol? (cadr e)))
           (cons (car e) (cons (cadr e) (map (lambda (x) (dkd-reduce1 x (cons (cons (cadr e) #f) bound))) (cddr e)))))
          (#t (map (lambda (x) (dkd-reduce1 x bound)) e)))))

;; Beta-reduce the focus goal to a fixpoint.  An unlicensed redex (its argument a
;; K-form term the context does not type) is contracted anyway and its typing
;; posted as a leaf: that leaf is taken, read off to the surface operations, typed
;; and closed, and the loop goes on from the reduced goal.
(define (dkd-close-typ! typer)             ; TYPER lands or closes; `ass' unless the leaf closed
  (let ((home (proof-state-focus *ps*)))
    (typer)
    (if (not (sequent-node-grounded? home)) (ass))))

(define (dkd-beta!)
  (let loop ((n 0))
    (let ((g0 (dk-goal)) (home (proof-state-focus *ps*)))
      (if (and (< n 12) (dkd-has-redex? g0))
          (let* ((predicted (dkd-reduce1 g0))
                 (opened (dk-opened (lambda () (lam-b)))))
            (cond
              ((sequent-node-grounded? home) #t)          ; the reduct was in context: branch closed
              ((null? opened) (dkd-error "lam-b changed nothing on " g0))
              (#t
               (let ((main (find-first (lambda (l) (alpha-equiv? (dk-goal-of l) predicted)) opened)))
                 (if (not main)
                     (dkd-error "beta: no opened leaf matches the predicted reduct " predicted
                                " among " (map dk-goal-of opened)))
                 (for-each
                  (lambda (l)
                    (if (and (not (eq? l main)) (not (sequent-node-grounded? l)))
                        (let ((og (dk-goal-of l)))
                          (if (not (and (pair? og) (eq? (car og) 'IN) (= (length og) 3)))
                              (dkd-error "beta opened a leaf that is not a typing: " og))
                          (dk-focus! l)
                          (dkd-user-form! dkd-powers)
                          (let ((g (dk-goal)))
                            (dkd-close-typ! (lambda () (if (eq? (caddr g) 'CC) (dkd-cc! (cadr g)) (dkd-in! (cadr g) (caddr g))))))
                          (if (not (sequent-node-grounded? l))
                              (dkd-error "beta: the owed typing did not close: " og)))))
                  opened)
                 (dk-focus! main)
                 (loop (+ n 1))))))
          (not (sequent-node-grounded? home))))))

;; Close the focus goal (= s t) or (== s t): qrfl when the sides agree, else
;; crs with the reciprocals named.  Errors when neither closes it.
(define (dkd-crs-here!)                   ; the focus goal is (= s t): type, name recips, crs
  (let loop ((e (dk-goal)) (seen '()))
    (cond ((or (number? e) (member e seen)) seen)
          ((symbol? e) (dkd-cc! e) (cons e seen))
          ((and (pair? e) (memq (car e) '(= + * -))) (fold-left (lambda (acc s) (loop s acc)) seen (cdr e)))
          ((pair? e) (dkd-cc! e) (cons e seen))
          (#t seen)))
  (let name ()
    (let ((r (dkd-find (dk-goal) (lambda (e) (and (pair? e) (eq? (car e) 'recip))))))
      (if r (let ((v (dk-name! r 'CC))) (subst (list '= r v)) (name)))))
  (crs))
(define (dkd-ring-close!)
  (let* ((leaf (proof-state-focus *ps*)) (g (dk-goal)))
    (cond
      ((not (and (pair? g) (memq (car g) '(= ==)) (= (length g) 3)))
       (dkd-error "not an equation: " g))
      ((alpha-equiv? (cadr g) (caddr g))
       (if (eq? (car g) '==) (qrfl) (begin (dkd-cc! (cadr g)) (rfl))))
      ((eq? (car g) '=) (dkd-crs-here!))
      (#t
       (let ((eqn (list '= (cadr g) (caddr g))))
         (dk-have! eqn (lambda () (dkd-crs-here!)))
         (if (not (dk-asm? eqn)) (dkd-error "could not prove " eqn))
         (subst eqn)
         (qrfl))))
    (if (not (sequent-node-grounded? leaf))
        (dkd-error "the equation did not close: " g))))

;;; ---------------------------------------------------------------- the plan
;; A node: (KIND TERM KIDS INFO).  KIND in var const sum product chain recip
;; opaque; INFO: for chain the law name and the outer lambda; for opaque the
;; symbol g and its domain V.  OBLIGATIONS are accumulated in user form.
(define dkd-oblig '())
(define dkd-powers '())
(define (dkd-oblige! f) (if (not (member f dkd-oblig)) (set! dkd-oblig (cons f dkd-oblig))))

(define (dkd-plan e x U)
  (let ((univ (lambda (body-of)           ; forall y in U. body-of(y)
                (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) (body-of (dkd-sub e x 'dkdoy_)))))))
    (cond
      ((eq? e x) (list 'var e '()))
      ((not (dkd-free-in? x e)) (list 'const e '()))
      ((not (pair? e)) (dkd-error "a bound variable other than " x " in " e))
      (#t
       (let ((h (car e)) (n (length (cdr e))))
         (cond
           ((and (eq? h '+) (= n 2)) (list 'sum e (list (dkd-plan (cadr e) x U) (dkd-plan (caddr e) x U))))
           ((and (eq? h '*) (= n 2)) (list 'product e (list (dkd-plan (cadr e) x U) (dkd-plan (caddr e) x U))))
           ((and (eq? h '-) (= n 2))
            (list 'sum e (list (dkd-plan (cadr e) x U)
                               (list 'product (list '* -1 (caddr e)) (list (list 'const -1 '()) (dkd-plan (caddr e) x U))))))
           ((and (eq? h '-) (= n 1))
            (list 'product (list '* -1 (cadr e)) (list (list 'const -1 '()) (dkd-plan (cadr e) x U))))
           ((and (eq? h 'power) (= n 2) (dkd-nat? (caddr e)) (>= (caddr e) 1))
            (let ((k (caddr e)) (b (cadr e)))
              (if (not (memv k dkd-powers)) (set! dkd-powers (cons k dkd-powers)))
              (let loop ((j k))
                (if (= j 1) (dkd-plan b x U)
                    (list 'product (list '* b (let p ((i (- j 1))) (if (= i 1) b (list '* b (p (- i 1))))))
                          (list (dkd-plan b x U) (loop (- j 1))))))))
           ((and (eq? h 'recip) (= n 1))
            (let ((s (cadr e)))
              (dkd-oblige! ((lambda (body) (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) body)))
                            (list 'NOT (list '= (dkd-sub s x 'dkdoy_) 0))))
              (list 'recip e (list (dkd-plan s x U)))))
           ((and (memq h '(CC-EXP CC-SIN CC-COS)) (= n 1))
            (list 'chain e (list (dkd-plan (cadr e) x U))
                  (cond ((eq? h 'CC-EXP) (list 'cc-exp-deriv dkd-exp-lam 'CC))
                        ((eq? h 'CC-SIN) (list 'cc-sin-deriv dkd-sin-lam 'CC))
                        (#t (list 'cc-cos-deriv dkd-cos-lam 'CC)))))
           ((and (eq? h 'CC-LOG) (= n 1))
            (let ((s (cadr e)))
              (dkd-oblige! (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) (list 'IN (dkd-sub s x 'dkdoy_) dkd-slit))))
              (dkd-oblige! (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) (dkd-slit-guard (dkd-sub s x 'dkdoy_)))))
              (dkd-oblige! (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) (list 'NOT (list '= (dkd-sub s x 'dkdoy_) 0)))))
              (list 'chain e (list (dkd-plan s x U)) (list 'cc-log-deriv dkd-log-lam dkd-slit))))
           ((and (symbol? h) (= n 1))
            (let* ((s (cadr e))
                   (V (dkd-opaque-domain h)))
              (if (not V) (dkd-error "no IS-DIFF-ON or HOLOMORPHIC-ON of " h " in context, for " e))
              (if (not (and (eq? s x) (equal? V U)))
                  (dkd-oblige! (list 'FORALL 'dkdoy_ (list 'IMPLIES (list 'IN 'dkdoy_ U) (list 'IN (dkd-sub s x 'dkdoy_) V)))))
              (list 'opaque e (list (dkd-plan s x U)) (list h V))))
           (#t (dkd-error "outside the grammar: " e))))))))

(define (dkd-opaque-domain g)
  (let ((a (find-first (lambda (a) (and (pair? a)
                                        (or (and (eq? (car a) 'IS-DIFF-ON) (= (length a) 6) (equal? (cadr a) dkd-K) (eq? (cadddr a) g))
                                            (and (eq? (car a) 'HOLOMORPHIC-ON) (= (length a) 3) (eq? (caddr a) g)))))
                       (dkd-asms))))
    (and a (if (eq? (car a) 'IS-DIFF-ON) (caddr a) (cadr a)))))

;; post P as an open side leaf on the main branch (unless the context has it)
(define (dkd-owe! P)
  (if (not (dk-asm? P))
      (let ((g0 (dk-goal)) (home (proof-state-focus *ps*)))
        (cut P)
        (let ((main (find-first (lambda (l) (and (not (eq? l home))
                                                 (alpha-equiv? (dk-goal-of l) g0)
                                                 (any (lambda (a) (alpha-equiv? a P)) (dk-asms-of l))))
                                (dk-open-leaves))))
          (if (not main) (dkd-error "cut left no main branch for " P))
          (dk-focus! main)
          (set! dkd-owed (cons P dkd-owed))
          (dkd-warn "OWED, left open for you: " P)))))

;;; -------------------------------------------------------------- the engine
;; the function term and the derivative of a landed IS-DIFF-ON
(define (dkd-fn r) (list-ref r 3))
(define (dkd-L r)  (list-ref r 5))
;; (IN L CC) for the derivative L of a landed IS-DIFF-ON(K, V, g, p, L): the
;; definition types L in CARR(K); without it an instantiation at L owes `L = L'
(define (dkd-deriv-cc! r)
  (let ((want (list 'IN (dkd-L r) 'CC)) (L (dkd-L r)))
    (if (not (dk-asm? want))
        (if (symbol? L)                    ; a skolem symbol: certified as a variable, read off
            (begin
              (dk-cite! 'diff-on-deriv-in-carr dkd-K (list-ref r 2) (list-ref r 3) (list-ref r 4) L)
              (dkd-carr->cc! L))
            (dkd-cc! L)))                  ; an application: type it (the read-off would owe L = L)
    want))

;; (IN (f A) CC) from IS-DIFF-ON(K, U, f, A, L); the carr universal lands too
(define (dkd-value-cc! U f A L)
  (let ((want (list 'IN (list f A) 'CC)))
    (if (not (dk-asm? want))
        (begin
          (dk-cite! 'diff-on-value-in-carr dkd-K U f A L)
          (let ((u (dk-ctx-form (list 'FORALL 'dfx_ (list 'IMPLIES (list 'IN 'dfx_ U) (list 'IN (list f 'dfx_) dkd-carr))))))
            (if (not u) (dkd-error "diff-on-value-in-carr did not land its universal"))
            (dk-apply! u A))
          (dkd-carr->cc! (list f A))))
    want))

;; forall y in U. (f y) in D, on a lane; D is CC, or a set the plan's owed
;; universal covers, or U itself when f is the identity
(define (dkd-values-in! U f D s x)
  (let ((want (list 'FORALL 'dkdvy_ (list 'IMPLIES (list 'IN 'dkdvy_ U) (list 'IN (list f 'dkdvy_) D)))))
    (if (not (dk-asm? want))
        (dk-have! want
          (lambda ()
            (let ((y (dk-di-var!)))
              (cond
                ((eq? D 'CC)
                 (let ((u (dk-ctx-form (list 'FORALL 'dfx_ (list 'IMPLIES (list 'IN 'dfx_ U) (list 'IN (list f 'dfx_) dkd-carr))))))
                   (if (not u) (dkd-error "no carr universal for " f))
                   (dk-apply! u y)
                   (dkd-carr->cc! (list f y))
                   (ass)))
                (#t
                 (dkd-beta!)
                 (dkd-user-form! dkd-powers)
                 (let ((g (dk-goal)))
                   (cond ((dk-asm? g) (ass))
                         ((dkd-from-universal! g) (ass))
                         (#t (dkd-in! (cadr g) D) (ass))))))))))
    want))

;; the law's REDEX-form antecedent from the user-form fact: forall y in U. NOT (= (f y) 0)
(define (dkd-nonzero-univ! U f)
  (let ((want (list 'FORALL 'cry_ (list 'IMPLIES (list 'IN 'cry_ U) (list 'NOT (list '= (list f 'cry_) 0))))))
    (if (not (dk-asm? want))
        (dk-have! want
          (lambda ()
            (let ((y (dk-di-var!)))
              (dkd-beta!)
              (dkd-user-form! dkd-powers)
              (let ((g (dk-goal)))
                (cond ((dk-asm? g) (ass))
                      ((dkd-from-universal! g) (ass))
                      (#t (dkd-nonzero! (cadr (cadr g))) (ass))))))))
    want))

;; the same bridge for ONE formula about (f A): prove WANT whose user form is in context
(define (dkd-at-point! want)
  (if (not (dk-asm? want))
      (dk-have! want
        (lambda ()
          (dkd-beta!)
          (dkd-user-form! dkd-powers)
          (let ((g (dk-goal)))
            (cond ((dk-asm? g) (ass))
                  ((dkd-from-universal! g) (ass))
                  (#t (dkd-error "the point obligation is not in context: " g)))))))
  want)

;; the symbolic derivative, simplified a little
(define (dkd-simp e)
  (cond ((not (pair? e)) e)
        ((and (eq? (car e) '*) (= (length e) 3))
         (let ((a (cadr e)) (b (caddr e)))
           (cond ((or (eqv? a 0) (eqv? b 0)) 0)
                 ((eqv? a 1) b) ((eqv? b 1) a)
                 ((and (dkd-numeral? a) (dkd-numeral? b)) (* a b))
                 (#t e))))
        ((and (eq? (car e) '+) (= (length e) 3))
         (let ((a (cadr e)) (b (caddr e)))
           (cond ((eqv? a 0) b) ((eqv? b 0) a)
                 ((and (dkd-numeral? a) (dkd-numeral? b)) (+ a b))
                 (#t e))))
        ((and (eq? (car e) '-) (= (length e) 3))
         (let ((a (cadr e)) (b (caddr e)))
           (cond ((eqv? b 0) a) ((eqv? a 0) (dkd-simp (list '- b)))
                 ((and (dkd-numeral? a) (dkd-numeral? b)) (- a b))
                 (#t e))))
        ((and (eq? (car e) '-) (= (length e) 2))
         (let ((a (cadr e)))
           (cond ((eqv? a 0) 0) ((dkd-numeral? a) (- a)) (#t e))))
        (#t e)))
(define (dkd-mul a b) (dkd-simp (list '* a b)))
(define (dkd-add a b) (dkd-simp (list '+ a b)))

;; Run PLAN at the point A: return (FORMULA . L*), FORMULA the landed IS-DIFF-ON
;; of the canonical lambda, L* the user-form derivative at A.  X is the bound
;; variable of the user's lambda (for the symbolic derivative).
(define (dkd-exec! plan U A x)
  (let ((kind (car plan)) (e (cadr plan)) (kids (caddr plan)))
    (cond
      ((eq? kind 'var)
       (cons (dk-cite! 'diff-on-identity dkd-K U A) 1))
      ((eq? kind 'const)
       (dkd-carr! e)
       (cons (dk-cite! 'diff-on-const dkd-K U e A) 0))
      ((eq? kind 'sum)
       (let* ((r1 (dkd-exec! (car kids) U A x)) (r2 (dkd-exec! (cadr kids) U A x))
              (f1 (car r1)) (f2 (car r2)))
         (cons (dk-cite! 'diff-on-sum dkd-K U (dkd-fn f1) (dkd-fn f2) A (dkd-L f1) (dkd-L f2))
               (dkd-add (cdr r1) (cdr r2)))))
      ((eq? kind 'product)
       (let* ((r1 (dkd-exec! (car kids) U A x)) (r2 (dkd-exec! (cadr kids) U A x))
              (f1 (car r1)) (f2 (car r2))
              (e1 (cadr (car kids))) (e2 (cadr (cadr kids))))
         (cons (dk-cite! 'diff-on-product dkd-K U (dkd-fn f1) (dkd-fn f2) A (dkd-L f1) (dkd-L f2))
               (dkd-add (dkd-mul (cdr r1) (dkd-sub e2 x A)) (dkd-mul (dkd-sub e1 x A) (cdr r2))))))
      ((eq? kind 'chain)
       (let* ((r1 (dkd-exec! (car kids) U A x)) (f1 (car r1))
              (info (cadddr plan)) (law (car info)) (lam (cadr info)) (V (caddr info))
              (s (cadr (car kids))) (sA (dkd-sub s x A))
              (fn1 (dkd-fn f1)) (pt (list fn1 A)))
         (dkd-value-cc! U fn1 A (dkd-L f1))
         (if (eq? law 'cc-log-deriv)
             (begin (dkd-at-point! (dkd-slit-guard pt))         ; the law's guard, at the redex
                    (dkd-at-point! (list 'NOT (list '= pt 0))))) ; for the typing of recip(pt)
         (let ((m (dk-cite! law pt)))
           (dkd-deriv-cc! m)
           (dkd-values-in! U fn1 V s x)
           (let ((r (dk-cite! 'diff-on-chain dkd-K U V fn1 lam A (dkd-L f1) (dkd-L m))))
             (cons r
                   (dkd-mul (cond ((eq? law 'cc-exp-deriv) (list 'CC-EXP sA))
                                  ((eq? law 'cc-sin-deriv) (list 'CC-COS sA))
                                  ((eq? law 'cc-cos-deriv) (list '- (list 'CC-SIN sA)))
                                  (#t (list 'recip sA)))
                            (cdr r1)))))))
      ((eq? kind 'opaque)
       (let* ((r1 (dkd-exec! (car kids) U A x)) (f1 (car r1))
              (info (cadddr plan)) (g (car info)) (V (cadr info))
              (s (cadr (car kids))) (sA (dkd-sub s x A))
              (fn1 (dkd-fn f1)) (pt (list fn1 A)))
         (dkd-value-cc! U fn1 A (dkd-L f1))
         (dkd-in! sA V)
         ;; IS-DIFF-ON(K, V, g, sA, M) in user form
         (let ((have (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IS-DIFF-ON) (= (length a) 6)
                                                  (equal? (cadr a) dkd-K) (equal? (caddr a) V)
                                                  (eq? (cadddr a) g) (alpha-equiv? (list-ref a 4) sA)))
                                 (dkd-asms))))
           (if (not have)
               (let ((h (find-first (lambda (a) (and (pair? a) (eq? (car a) 'HOLOMORPHIC-ON) (equal? (cadr a) V) (eq? (caddr a) g)))
                                    (dkd-asms))))
                 (if (not h) (dkd-error "no IS-DIFF-ON of " g " at " sA " and no HOLOMORPHIC-ON(" V ", " g ")"))
                 (let ((ex (dk-apply! (dk-cite! 'holomorphic-on-diff V g) sA)))
                   (dk-skolem! ex)
                   (set! have (find-first (lambda (a) (and (pair? a) (eq? (car a) 'IS-DIFF-ON) (= (length a) 6)
                                                            (eq? (cadddr a) g) (alpha-equiv? (list-ref a 4) sA)))
                                          (dkd-asms)))
                   (if (not have) (dkd-error "holomorphic-on-diff did not land IS-DIFF-ON of " g)))))
           (let* ((M (dkd-L have))
                  (redex-form (list 'IS-DIFF-ON dkd-K V g pt M)))
             (if (not (dk-asm? redex-form))
                 (begin
                   (dkd-cc! sA)
                   (dk-have! (list '= pt sA) (lambda () (dkd-beta!) (dkd-user-form! dkd-powers) (dkd-ring-close!)))
                   (dk-have! redex-form (lambda () (subst (list '= pt sA)) (ass)))))
             (dkd-values-in! U fn1 V s x)
             (dkd-deriv-cc! have)
             (cons (dk-cite! 'diff-on-chain dkd-K U V fn1 g A (dkd-L f1) M)
                   (dkd-mul M (cdr r1)))))))
      ((eq? kind 'recip)
       (let* ((r1 (dkd-exec! (car kids) U A x)) (f1 (car r1)) (fn1 (dkd-fn f1))
              (s (cadr (car kids))) (sA (dkd-sub s x A))
              (q (list 'VNB-LAMBDA 'dkdqv_ U (list 'recip (list fn1 'dkdqv_)))))
         (dkd-nonzero-univ! U fn1)
         (dk-have! (list 'IN q (list 'FUN U 'CC))
           (lambda ()
             (dk-lam-type!
              (lambda ()
                (let ((y (dk-di-var!)))
                  (dkd-beta!)
                  (dkd-user-form! dkd-powers)
                  (dkd-close-typ! (lambda () (dkd-cc! (cadr (dk-goal)))))))
              (lambda () (dkd-set-leaf! U)))))
         (dk-have! (list 'FORALL 'cry_ (list 'IMPLIES (list 'IN 'cry_ U) (list '== (list q 'cry_) (list 'recip (list fn1 'cry_)))))
           (lambda () (let ((y (dk-di-var!))) (dkd-beta!) (qrfl))))
         (cons (dk-cite! 'diff-on-recip-cc U fn1 A (dkd-L f1) q)
               (dkd-simp (list '- (dkd-mul (cdr r1) (list 'recip (list '* sA sA))))))))
      (#t (dkd-error "unknown plan node " kind)))))

;;; ------------------------------------------------------------ the surface
(define (dk-diff! . args)
  (let* ((goal (and (null? args) (dk-goal)))
         (U   (if goal (caddr goal) (car args)))
         (LAM (->raw-formula (if goal (cadddr goal) (cadr args))))
         (A   (->raw-formula (if goal (list-ref goal 4) (caddr args))))
         (Lu  (cond (goal (list-ref goal 5))
                    ((> (length args) 3) (->raw-formula (cadddr args)))
                    (#t #f))))
    (if goal
        (if (not (and (pair? goal) (eq? (car goal) 'IS-DIFF-ON) (= (length goal) 6) (equal? (cadr goal) dkd-K)))
            (dkd-error "the focus goal is not IS-DIFF-ON(CC-NORMED-FIELD, ...): " goal)))
    (if (not (and (pair? LAM) (eq? (car LAM) 'VNB-LAMBDA) (= (length LAM) 4) (equal? (caddr LAM) U)))
        (dkd-error "the function must be (VNB-LAMBDA x U e) over the given U: " LAM))
    (let* ((x (cadr LAM)) (e (cadddr LAM))
           (home (proof-state-focus *ps*)))
      (set! dkd-owed '()) (set! dkd-oblig '()) (set! dkd-powers '())
      ;; the plan, then the obligations on the main branch
      (let ((plan (dkd-plan e x U)))
        (dkd-setup!)
        (dkd-open! U)
        (if (not (dk-asm? (list 'IN A U))) (dkd-error "the point is not typed in U: " (list 'IN A U)))
        (for-each dkd-owe! (reverse dkd-oblig))
        ;; the laws
        (let* ((r (dkd-exec! plan U A x))
               (T (car r)) (Lstar (or Lu (cdr r)))
               (h (dkd-fn T)) (LK (dkd-L T)))
          ;; LAM in FUN(U, CARR K)
          (dk-have! (list 'IN LAM (list 'FUN U dkd-carr))
            (lambda ()
              (subst (list '== dkd-carr 'CC))
              (dk-lam-type!
               (lambda () (let ((y (dk-di-var!))) (dkd-close-typ! (lambda () (dkd-cc! (cadr (dk-goal)))))))
               (lambda () (dkd-set-leaf! U)))))
          ;; the pointwise equation
          (dk-have! (list 'FORALL 'hbx_ (list 'IMPLIES (list 'IN 'hbx_ U) (list '== (list LAM 'hbx_) (list h 'hbx_))))
            (lambda ()
              (let ((y (dk-di-var!)))
                (dkd-beta!)
                (dkd-user-form! dkd-powers)
                (dkd-ring-close!))))
          (let ((TL (dk-cite! 'diff-on-transfer-ptwise-eq dkd-K U LAM h A LK)))
            ;; the derivative in user form
            (let ((final
                   (if (alpha-equiv? LK Lstar)
                       TL
                       (let ((G (list 'FORALL 'dkdlv_ (list 'IMPLIES (list '= 'dkdlv_ LK)
                                                             (list 'IS-DIFF-ON dkd-K U LAM A 'dkdlv_))))
                             (eqn (list '= Lstar LK)))
                         (dkd-cc! Lstar)
                         (dk-have! G
                           (lambda ()
                             (dk-di-var! (lambda (g) (cadr (cadr g))))
                             (di)
                             (let ((hyp (find-first (lambda (a) (and (pair? a) (eq? (car a) '=) (equal? (caddr a) LK)
                                                                      (symbol? (cadr a))))
                                                    (dkd-asms))))
                               (subst hyp)
                               (ass))))
                         (let ((ok (let ((work (lambda ()
                                                 (dk-have! eqn
                                                   (lambda () (dkd-beta!) (dkd-user-form! dkd-powers) (dkd-ring-close!)))
                                                 (dk-asm? eqn))))
                                     (if dkd-debug (work) (dk--transaction work)))))
                           (if ok
                               (dk-apply! (dk-ctx-form G) Lstar)
                               (begin
                                 (dkd-warn "the derivative could not be brought to " Lstar
                                           "; landed with the laws' value " LK)
                                 TL)))))))
              (if (pair? dkd-owed)
                  (dkd-warn (number->string (length dkd-owed)) " obligation(s) left open: "
                            (apply string-append (map (lambda (p) (string-append " | " (dkd-str p))) (reverse dkd-owed)))))
              (if goal (dk-ass!))
              final)))))))

;;; (dk-holomorphic! U LAM) -- close the focus goal HOLOMORPHIC-ON(U, LAM)
(define (dk-holomorphic! U LAM0)
  (let ((LAM (->raw-formula LAM0)) (leaf (proof-state-focus *ps*)))
    (if (not (alpha-equiv? (dk-goal) (list 'HOLOMORPHIC-ON U LAM)))
        (dkd-error "the focus goal is not " (list 'HOLOMORPHIC-ON U LAM)))
    (dkd-setup!)
    (dkd-open! U)
    (mac 'HOLOMORPHIC-ON)
    (dk-conj-close!
     (lambda ()
       (let ((g (dk-goal)))
         (cond ((dk-asm? g) (ass))
               ((and (pair? g) (eq? (car g) 'IN))
                (dk-lam-type!
                 (lambda () (let ((y (dk-di-var!))) (dkd-close-typ! (lambda () (dkd-cc! (cadr (dk-goal)))))))
                 (lambda () (dkd-set-leaf! U))))
               ((and (pair? g) (eq? (car g) 'FORALL))
                (let ((a (dk-di-var!)))
                  (let ((r (dk-diff! U LAM a)))
                    (ew (dkd-L r))
                    (ass))))
               (#t (dkd-error "unexpected conjunct of HOLOMORPHIC-ON: " g))))))
    (sequent-node-grounded? leaf)))


;;; =======================================================================
;;; META: the shared helpers of the K2 meta files (agent META-KIT, 2026-10-08; the user's decision
;;; of the same day).  docs/meta-k2-admissibility-2026-10-08.md, sections 10-11.
;;; =======================================================================
;;;
;;; The meta laws files theorem-library/meta-syntax-laws.scm (phase 1, the locally nameless
;;; expressions) and theorem-library/meta-core-laws.scm (phase 2, the core, DERIVABLE) drove their
;;; proofs with the same staged-class helpers: phase 2 had copied 59 of phase 1's top-level definitions;
;;; 56 are here (the other three are term constants spelled with a statement's own variables, which
;;; stay local).  By the rule at the head of this file a helper two files need lives
;;; here, so each is here ONCE, under the prefix dk-meta-; the copies are deleted from both files.
;;; Binders a helper builds are spelled dkm*_ (dkmw_, dkmx_, dkmi3_), names no statement and no
;;; predicate body uses.  A helper only one file uses stays in that file.
;;;
;;; A. THE SHARED HELPERS, as phase 1 wrote them (dk-meta-cond-transfer! is phase 2's version, which
;;;    adds one clause: a conjunct both conditions share closes by `ass').  By group:
;;;    - the openers of tags, lists, unions and products: dk-meta-keep-prop!, -tag-absurd!,
;;;      -component(s)!, -num-set!, -unpack!, -cart-chain, -cart-open!, -union-open!, -or-each!,
;;;      -fits?, -close-in!, -ex-fill!;
;;;    - stages and rank: -stage-eq, -stage-open!, -step-case?, -ni-cases!, -type-stages!, -nth-in!,
;;;      -set-of!, -and!, -set-open!, -incl!, -tuples-lift!, -lift-to-expr!, -has-le?, -rank!,
;;;      -rank-min, -unfold-cite!, -absurd-eq!, -eq-of, -disjunct-kind, -ind-hyps;
;;;    - THE STRUCTURAL-RECURSION DRIVER: dk-meta-struct-laws! (the STEP / COH / AT triple of a
;;;      per-stage map with the keep clause), with -wrap, -but-last, -lit-nth?, -nth-r!, -cond-close!,
;;;      -if-left!, -ifs!, -val-ex, -val0!, -val-succ!, -new-at!;
;;;    - binder congruence by extensionality: -bu-eq!, -sep-eq!, -cond-transfer!;
;;;    - lists and maps: -makeset-set!, -in-makeset!, -len-nn!, -app-type!, -app2-type!, -mapl!,
;;;      -maplk!; and -finsub (the formula "a finite subset of NN").
;;;
;;; B. dk-derive! -- a derivation in the core, given as a TREE, proved as a membership in
;;;    DERIVABLE(T); its planner for the side conditions (dk-meta--plan-*, with the tables
;;;    dk-meta-wf-intros / -wf-elims / -wf-atoms of meta-core-laws.scm's laws); and the phase-2
;;;    helpers it calls, moved here from meta-core-laws.scm: dk-meta-iff!, -iff-r!, -iff-l!
;;;    (IFF projections without `prop'), -seq!, -ctx+!, -law-name.  See its own header below.
;;;    dk-meta-trace (#f) prints each node and side condition as dk-derive! discharges it.
;;;
;;; The section names theorems of the meta laws files (derivable-<rule>, seq-iff, ctx-add-ctx,
;;; ctx-mem, ctx-add-has / -keeps, ctx-sub-cons / -snoc, the clf- laws, hyps-in-0/1/2): they are
;;; cited when a helper RUNS, so the section loads before those files, with the rest of this file.

;;; -----------------------------------------------------------------------
;;; A. The shared helpers.

(define (dk-meta-keep-prop! . fs)
  (let ((node (proof-state-focus *ps*)))
    (apply dk-only! fs)
    (if (not (sequent-node-grounded? node)) (prop))))

;; (= L1 L2) in context, L1, L2 literal lists whose first entries are two DIFFERENT numerals:
;; close the goal (whatever it is) by FALSITY.
(define (dk-meta-tag-absurd! l1 l2)
  (let ((t1 (cadr l1)) (t2 (cadr l2)))
    (dk-have! `(= (NTH 1 ,l2) ,t2) (lambda () (nth-r) (rfl)))
    (dk-have! `(= ,t1 (NTH 1 ,l2)) (lambda () (subst `(= ,l2 ,l1)) (nth-r) (rfl)))
    (dk-have! `(= ,t1 ,t2) (lambda () (subst `(= ,t2 (NTH 1 ,l2))) (ass)))
    (dk-have! `(NOT (= ,t1 ,t2)) (lambda () (arith)))
    (ai `(NOT (= ,t1 ,t2)))))

;; (= L1 L2) in context, literal lists of one length; the goal (= x y), x the I-th entry of L1
;; and y the I-th entry of L2.
(define (dk-meta-component! l1 l2 i)
  (let* ((x (list-ref l1 i)) (y (list-ref l2 i)))
    (dk-have! `(= (NTH ,i ,l2) ,y) (lambda () (nth-r) (rfl)))
    (subst `(= ,y (NTH ,i ,l2)))
    (subst `(= ,l2 ,l1))
    (nth-r)
    (rfl)))

(define (dk-meta-components! l1 l2)
  (dk-each-leaf! (lambda () (di))
    (lambda ()
      (if (dk-head-is? (dk-goal) 'AND)
          (dk-meta-components! l1 l2)
          (let* ((g (dk-goal))
                 (i (let loop ((k 1))
                      (cond ((> k (- (length l1) 1)) (error "dk-meta-components!: no index for" g))
                            ((and (equal? (list-ref l1 k) (cadr g))
                                  (equal? (list-ref l2 k) (caddr g))) k)
                            (#t (loop (+ k 1)))))))
            (dk-meta-component! l1 l2 i))))))

;; (IN n SET) for a numeral n, through n in NN.
(define (dk-meta-num-set! n)
  (dk-have! `(IN ,n SET)
    (lambda ()
      (dk-have! `(IN ,n NN) (lambda () (arith)))
      (fact 'membership-implies-sethood n 'NN)
      (ass))))

;; Skolemise the FORSOME EX and every FORSOME that lands from it; return the eigenvariables.  A
;; tag membership (IN v (PAIR n n)) that lands becomes (= v n).
(define (dk-meta-unpack! ex)
  (let loop ((ex ex) (acc '()))
    (let* ((before (dk-asms))
           (v (dk-skolem! ex))
           (new (filter (lambda (f) (not (member f before))) (dk-asms)))
           (tag (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) v)
                                             (dk-head-is? (caddr f) 'PAIR)))
                            new))
           (next (find-first (lambda (f) (dk-head-is? f 'FORSOME)) new)))
      (if tag
          (let ((n (cadr (caddr tag))))
            (dk-meta-num-set! n)
            (fact 'pair-self-eq n v)))
      (if next (loop next (cons v acc)) (reverse (cons v acc))))))

;; (IN x (CARTESIAN C1 ... Cn)) in context: land and return the existential chain of the
;; primitive `cartesian-decompose', with FIXED binders cdv1_ ...
(define (dk-meta-cart-chain x classes)
  (let nest ((i 1) (cs classes) (vars '()))
    (if (null? cs)
        `(= ,x (LIST ,@(reverse vars)))
        (let ((v (string->symbol (string-append "cdv" (number->string i) "_"))))
          `(FORSOME ,v (AND (IN ,v ,(car cs)) ,(nest (+ i 1) (cdr cs) (cons v vars))))))))

(define (dk-meta-cart-open! mem)
  (let* ((ex  (dk-meta-cart-chain (cadr mem) (cdr (caddr mem))))
         (imp `(IMPLIES ,mem ,ex)))
    (dk-have! imp (lambda () (mac 'cartesian-decompose) (di) (ass)))
    (detach! imp)
    (or (dk-ctx-form ex) (error "dk-meta-cart-open!: the chain did not land" (expression->string ex)))))

;; (IN x (UNION A B)) in context: land and return (OR (IN x A) (IN x B)).
(define (dk-meta-union-open! mem)
  (let* ((x (cadr mem)) (a (cadr (caddr mem))) (b (caddr (caddr mem)))
         (o `(OR (IN ,x ,a) (IN ,x ,b))))
    (dk-have! o (lambda () (fact 'union-membership a b x) (dk-meta-keep-prop! (iff-for mem) mem)))
    o))

;; An OR in context, split to its leaves (right-nested); HANDLER gets each leaf's disjunct.
(define (dk-meta-or-each! o handler)
  (dk-each-leaf! (lambda () (ai o))
    (lambda ()
      (cond ((dk-asm? (cadr o)) (handler (cadr o)))
            ((dk-head-is? (caddr o) 'OR) (dk-meta-or-each! (caddr o) handler))
            (#t (handler (caddr o)))))))

;; Close the goal (IN x C), C built from UNION, CARTESIAN and PAIR(n, n) around classes x's
;; pieces are typed in, in context.
(define (dk-meta-fits? x c)
  (cond ((dk-asm? `(IN ,x ,c)) #t)
        ((and (pair? c) (eq? (car c) 'PAIR)) (equal? x (cadr c)))
        ((and (pair? c) (eq? (car c) 'UNION)) (or (dk-meta-fits? x (cadr c)) (dk-meta-fits? x (caddr c))))
        ((and (pair? c) (eq? (car c) 'CARTESIAN) (pair? x) (eq? (car x) 'LIST)
              (= (length x) (length c)))
         (let loop ((xs (cdr x)) (cs (cdr c)))
           (or (null? xs) (and (dk-meta-fits? (car xs) (car cs)) (loop (cdr xs) (cdr cs))))))
        (#t #f)))

(define (dk-meta-close-in!)
  (let* ((g (dk-goal)) (x (cadr g)) (c (caddr g)))
    (cond
      ((dk-asm? g) (ass))
      ((and (pair? c) (eq? (car c) 'PAIR))
       (dk-meta-num-set! x)
       (fact 'pair-self-member x)
       (ass))
      ((and (pair? c) (eq? (car c) 'UNION))
       (let ((left? (dk-meta-fits? x (cadr c))))
         (if (not (or left? (dk-meta-fits? x (caddr c))))
             (error "dk-meta-close-in!: neither side of the union fits" (expression->string g)))
         (dk-have! `(IN ,x ,(if left? (cadr c) (caddr c))) (lambda () (dk-meta-close-in!)))
         (fact 'union-membership (cadr c) (caddr c) x)
         (dk-meta-keep-prop! (iff-for g) `(IN ,x ,(if left? (cadr c) (caddr c))))))
      ((and (pair? c) (eq? (car c) 'CARTESIAN))
       (mac 'cartesian-decompose)
       (let loop ((xs (cdr x)))
         (if (null? xs)
             (rfl)
             (begin
               (ew (car xs))
               (dk-each-leaf! (lambda () (di))
                 (lambda ()
                   (if (dk-head-is? (dk-goal) 'FORSOME) (loop (cdr xs))
                       (if (dk-head-is? (dk-goal) '=) (rfl) (dk-meta-close-in!)))))))))
      (#t (error "dk-meta-close-in!: no route" (expression->string g))))))

;; Close FORSOME x1 ... (AND ...) with the witnesses WS, each conjunct by rfl or the context.
(define (dk-meta-ex-fill! ws)
  (ew (car ws))
  (dk-conj-close!
    (lambda ()
      (cond ((dk-head-is? (dk-goal) 'FORSOME) (dk-meta-ex-fill! (cdr ws)))
            ((dk-asm? (dk-goal)) (ass))
            ((dk-head-is? (dk-goal) '=) (rfl))
            (#t (ass))))))

;; The stage equation at n (0, or (succ j) with j in NN in context), landed and returned.
(define (dk-meta-stage-eq n)
  (if (equal? n 0)
      (dk-cite! 'expr-stage-zero)
      (dk-cite! 'expr-stage-succ (cadr n))))

;; (IN m (EXPR-STAGE n)) in context: land and return (IN m BODY).
(define (dk-meta-stage-open! m n)
  (let* ((eqn (dk-meta-stage-eq n))
         (body (caddr eqn))
         (claim `(IN ,m ,body)))
    (dk-have! claim (lambda () (subst `(= ,body (EXPR-STAGE ,n))) (ass)))
    claim))

;; Is G the step case of an `ni' on a guarded NN universal?
(define (dk-meta-step-case? g)
  (and (dk-head-is? g 'FORALL) (dk-head-is? (caddr g) 'IMPLIES)
       (dk-head-is? (cadr (caddr g)) 'IN) (eq? (caddr (cadr (caddr g))) 'NN)))

(define (dk-meta-ni-cases!)
  (dk-meta-ni-cases--pick (dk-opened (lambda () (ni)))))
;; W1G-B (2026-11-06; META item 1): the same, with the parameters HOIST fixed by dk-ni-fixed!
;; (defined further down), so that the induction body is predicative (NBG) when a parameter
;; ranges over classes.  Used by dk-meta-struct-laws! when its PARAMS are not empty, and (W1N,
;; 2026-11-07) by meta-core-laws and meta-ind-laws, whose file-local twins it replaces.
;; (dk-meta-ni-cases-fixed! HOIST) -> (BASE-LEAF STEP-LEAF), the leaves of the induction that
;; dk-ni-fixed! opens on its lemma branch; the step leaf is the one of shape
;; forall n. n in NN => ...; HOIST is the list of prefix binders to fix (non-empty).
(define (dk-meta-ni-cases-fixed! hoist)
  (dk-meta-ni-cases--pick (cdr (assq 'cases (dk-ni-fixed! hoist)))))
(define (dk-meta-ni-cases--pick cases)
  (let ()
    (list (or (find-first (lambda (l) (not (dk-meta-step-case? (dk-goal-of l)))) cases)
              (error "dk-meta-ni-cases!: no base case"))
          (or (find-first (lambda (l) (dk-meta-step-case? (dk-goal-of l))) cases)
              (error "dk-meta-ni-cases!: no step case")))))

;; TYPE THE TERM BEFORE YOU INSTANTIATE AT IT: (IN (EXPR-STAGE n) SET) for every stage term in T
;; (n typed in NN in context), so that an instantiation at T owes nothing.
(define (dk-meta-type-stages! t)
  (cond ((and (pair? t) (eq? (car t) 'EXPR-STAGE))
         (if (not (dk-asm? `(IN ,t SET)))
             (begin
               (if (not (dk-asm? `(IN ,(cadr t) NN)))
                   (cond ((equal? (cadr t) 0) (fact 'nn-zero-in))
                         ((and (pair? (cadr t)) (eq? (car (cadr t)) 'succ))
                          (fact 'nn-succ-closed (cadr (cadr t))))))
               (fact 'expr-stage-set (cadr t)))))
        ((pair? t) (for-each dk-meta-type-stages! (cdr t)))))

;; (IN (NTH i l) C) from i in NN, l in TUPLES(C), 1 <= i, i <= LENGTH(l) in context.
(define (dk-meta-nth-in! cc i l)
  (let ((goal `(IN (NTH ,i ,l) ,cc)))
    (if (not (dk-asm? goal))
        (begin
          (dk-meta-type-stages! cc)
          (dk-have! `(AND (IN ,i NN) (AND (IN ,l (TUPLES ,cc)) (AND (<= 1 ,i) (<= ,i (LENGTH ,l)))))
            (lambda () (dk-conj-close! dk-ass!)))
          (fact 'nth-in-range cc i l)))
    goal))

;; (IN x SET) from (IN x C) in context.
(define (dk-meta-set-of! x c)
  (if (not (dk-asm? `(IN ,x SET))) (fact 'membership-implies-sethood x c))
  `(IN ,x SET))

(define (dk-meta-and! . fs)                        ; the conjunction of formulas in context
  (let ((f (fold-right (lambda (a b) (if b `(AND ,a ,b) a)) #f fs)))
    (dk-have! f (lambda () (dk-conj-close! (lambda () (ass)))))
    f))

;; (IN x EXPR-SET) in context: land a stage index and the stage membership; return the index.
(define (dk-meta-set-open! x)
  (dk-skolem! (dk-cite! 'expr-set-elim x)))

;; "C1 inside C2" as tuples-mono wants it, proved by THUNK on the peeled leaf.
(define (dk-meta-incl! c1 c2 thunk)
  (let ((incl `(FORALL dkmw_ (IMPLIES (IN dkmw_ ,c1) (IN dkmw_ ,c2)))))
    (dk-have! incl (lambda () (dk-peel!) (thunk (cadr (dk-goal)))))
    incl))

(define (dk-meta-tuples-lift! l c1 c2 thunk)
  (if (not (dk-asm? `(IN ,l (TUPLES ,c2))))
      (begin
        (dk-meta-type-stages! c1)
        (dk-meta-type-stages! c2)
        (dk-meta-incl! c1 c2 thunk)
        (dk-apply! (dk-cite! 'tuples-mono c1 c2) l))))

;; l in TUPLES(S_n) in context: land l in TUPLES(EXPR-SET).
(define (dk-meta-lift-to-expr! l n)
  (dk-meta-tuples-lift! l `(EXPR-STAGE ,n) 'EXPR-SET
    (lambda (w) (fact 'expr-set-intro n w) (ass))))

;; The five hypotheses of expr-induction at the class CC (read off the theorem).
(define (dk-meta-ind-hyps cc)
  (let* ((th (lookup-theorem 'expr-induction))
         (b (subst-free (quantifier-var th) cc (quantifier-body th))))
    (let loop ((f b) (acc '()))
      (if (and (dk-head-is? f 'IMPLIES) (dk-head-is? (caddr f) 'IMPLIES))
          (loop (caddr f) (cons (cadr f) acc))
          (reverse (cons (cadr f) acc))))))

(define (dk-meta-has-le? f x)
  (and (pair? f)
       (or (and (eq? (car f) '<=) (pair? (cdr f)) (equal? (cadr f) x))
           (any-pred (lambda (g) (dk-meta-has-le? g x)) f))))

;; rank-prop at the TYPED expression x: land (IN rank NN), (IN x stage(rank)), the minimality.
(define (dk-meta-rank! x)
  (fact 'expr-rank-prop x)
  (dk-split-all!)
  `(EXPR-RANK ,x))

(define (dk-meta-rank-min x)
  (or (find-first (lambda (f) (and (dk-head-is? f 'FORALL) (dk-meta-has-le? f `(EXPR-RANK ,x)))) (dk-asms))
      (error "dk-meta-rank-min: no minimality for" x)))

;; The literal list a constructor term stands for, and its unfolding equation (landed).
(define (dk-meta-unfold-cite! t)
  (case (car t)
    ((EFVAR) (dk-cite! 'efvar-unfold (cadr t)))
    ((EBVAR) (dk-cite! 'ebvar-unfold (cadr t)))
    ((ECONST) (dk-cite! 'econst-unfold (cadr t)))
    ((EAPP) (apply dk-cite! 'eapp-unfold (cdr t)))
    ((EBIND) (apply dk-cite! 'ebind-unfold (cdr t)))
    (else (error "dk-meta-unfold-cite!: not a constructor term" t))))

;; (= X Y) in context, X and Y constructor terms or literal lists with DIFFERENT tags: close the
;; goal by FALSITY.
(define (dk-meta-absurd-eq! eqn)
  (let* ((x (cadr eqn)) (y (caddr eqn))
         (lx (if (eq? (car x) 'LIST) x (caddr (dk-meta-unfold-cite! x))))
         (ly (if (eq? (car y) 'LIST) y (caddr (dk-meta-unfold-cite! y)))))
    (dk-have! `(= ,lx ,ly)
      (lambda ()
        (if (not (eq? (car x) 'LIST)) (subst `(= ,lx ,x)))
        (if (not (eq? (car y) 'LIST)) (subst `(= ,ly ,y)))
        (ass)))
    (dk-meta-tag-absurd! lx ly)))

;; the (= m X) equation in context with m on the left.
(define (dk-meta-eq-of m)
  (or (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) m))) (dk-asms))
      (error "dk-meta-eq-of: no equation for" m)))

;; The constructor heading the right-hand side of the innermost equation of an existential
;; disjunct (FORSOME .. (AND .. (= m (CTOR ..)))).
(define (dk-meta-disjunct-kind d)
  (cond ((dk-head-is? d 'FORSOME) (dk-meta-disjunct-kind (caddr d)))
        ((dk-head-is? d 'AND) (dk-meta-disjunct-kind (caddr d)))
        ((dk-head-is? d '=) (dk-head (caddr d)))
        (#t #f)))

(define (dk-meta-wrap params f) (fold-right (lambda (p g) `(FORALL ,p ,g)) f params))

(define (dk-meta-but-last l) (reverse (cdr (reverse l))))

;; the literal NTH redexes (NTH i (LIST ...)) with i a numeral in range
(define (dk-meta-lit-nth? e)
  (and (pair? e)
       (or (and (eq? (car e) 'NTH) (= (length e) 3) (number? (cadr e))
                (pair? (caddr e)) (eq? (car (caddr e)) 'LIST)
                (<= 1 (cadr e) (- (length (caddr e)) 1)))
           (any-pred dk-meta-lit-nth? (cdr e)))))

(define (dk-meta-nth-r!)
  (let loop ((k 0))
    (if (and (< k 12) (dk-meta-lit-nth? (dk-goal))) (begin (nth-r) (loop (+ k 1))))))

;; Close the condition leaf of an IF on a tag or an equation of literal lists.
(define (dk-meta-cond-close!)
  (cond ((dk-asm? (dk-goal)) (ass))
        (#t (dk-meta-nth-r!)
            (cond ((dk-asm? (dk-goal)) (ass))
                  ((dk-head-is? (dk-goal) 'NOT) (arith))
                  (#t (rfl))))))

;; Resolve the IF heading the LEFT side of the goal (== (IF ..) R) on the side TRUE?, the
;; condition closed by CLOSE (default dk-meta-cond-close!), then K on the main leaf.
(define (dk-meta-if-left! true? k . close)
  (let ((ift (cadr (dk-goal))))
    (dk-if-branch! true? ift (if (pair? close) (car close) dk-meta-cond-close!) k)))

;;; ONE PROOF OPENED AND CLOSED BY A KIT HELPER, so the certified loader can skip it
;;; (META-FALLBACK, 2026-10-20).  The loader's body rewrite (certificates.scm, cert-rewrite)
;;; sees only the `sp' / `qed' forms written in the proof FILE; a helper here that opens
;;; several proofs is invisible to it, so under VNB_CERTIFIED=on the first certified `sp'
;;; inside the helper escaped the whole top-level form and the helper's later theorems were
;;; never installed (the file then fell back to off mode).  This procedure does by hand what
;;; the rewrite does for a body: the `sp' runs as cert-sp/body (it installs a certified
;;; theorem and does NOT escape), the steps run only while (cert-proof-running?), and the
;;; `qed' always runs (for a skipped proof the qed hook takes it).  Outside a certified load
;;; cert-proof-running? is #t and this is (sp STMT) (STEPS!) (qed NAME).  A kit helper that
;;; opens more than one proof must open each through this procedure.
(define (dk-sp-qed! stmt steps! name)
  (cert-sp/body stmt)
  (if (cert-proof-running?) (steps!))
  (qed name))

(define (dk-meta-struct-laws! F-of G-of params zero-name succ-name step-name coh-name at-name . extra)
  ;; EXTRA, optional: (ARGS GUARDS) -- further arguments of the stage map after e (OPEN's
  ;; index), quantified inside e, with their guards.  Each of the three proofs is opened and
  ;; closed by dk-sp-qed! (above), so a certified load installs all three.
  (let* ((ghead (car (G-of 'e)))
         (ex  (if (pair? extra) (car extra) '()))
         (exg (if (pair? extra) (cadr extra) '()))
         (guard (lambda (f) (fold-right (lambda (g f) `(IMPLIES ,g ,f)) f exg))))
    ;; STEP
    (dk-sp-qed!
     (make-wff (dk-meta-wrap params
       `(FORALL k (FORALL e ,(dk-meta-wrap ex `(IMPLIES (IN k NN) (IMPLIES (IN e (EXPR-STAGE k))
           ,(guard `(== (,(F-of '(succ k)) e ,@ex) (,(F-of 'k) e ,@ex))))))))))
     (lambda ()
       (dk-peel!)
       (let* ((lhs (cadr (dk-goal))) (ft (car lhs)) (pv (dk-meta-but-last (cdr ft))))
         (fact 'expr-stage-keep 'k 'e)
         (subst (apply dk-cite! succ-name (append pv '(k))))
         (dk-lam-b!)
         (dk-meta-if-left! #t (lambda () (qrfl)))))
     step-name)
    ;; COH
    (dk-sp-qed!
     (make-wff `(FORALL d (IMPLIES (IN d NN)
       ,(dk-meta-wrap params `(FORALL j (FORALL e ,(dk-meta-wrap ex `(IMPLIES (IN j NN) (IMPLIES (IN e (EXPR-STAGE j))
           ,(guard `(== (,(F-of '(+ j d)) e ,@ex) (,(F-of 'j) e ,@ex))))))))))))
     (lambda ()
       ;; W1G-B: the parameters are fixed (dk-ni-fixed!), so the IH is used at the same ones.
       (let ((cs (if (null? params) (dk-meta-ni-cases!) (dk-meta-ni-cases-fixed! params))))
         (dk-focus! (car cs))
         (dk-peel!)
         (let ((j (last (cdr (car (caddr (dk-goal)))))))
           (subst (dk-cite! 'nn-add-zero j))
           (qrfl))
         (dk-focus! (cadr cs))
         (let* ((landed (dk-peel!))
                (ih (or (find-first (lambda (f) (dk-head-is? f 'FORALL)) landed)
                        (error "coh: no induction hypothesis")))
                (lhs (cadr (dk-goal))) (ft (car lhs)) (e (cadr lhs))
                (pv (dk-meta-but-last (cdr ft)))
                (sum (last ft)) (j (cadr sum)) (n (cadr (caddr sum))))
           (subst (dk-cite! 'nn-add-succ j n))
           (dk-meta-and! `(IN ,j NN) `(IN ,n NN))
           (fact 'nn-add-closed j n)
           (fact 'expr-stage-add n j e)
           ;; let*, s2 FIRST: the order the interpreter took when these two recording calls
           ;; shared one let (operands right to left); never bind two recording calls in one let.
           (let* ((s2 (apply dk-apply! ih (append (if (null? params) pv '()) (list j e) (cddr lhs))))   ; W1G-B: params fixed
                  (s1 (apply dk-cite! step-name (append pv (list `(+ ,j ,n) e) (cddr lhs)))))
             (subst s1)
             (subst s2)
             (qrfl)))))
     coh-name)
    ;; AT
    (dk-sp-qed!
     (make-wff (dk-meta-wrap params
       `(FORALL j (FORALL e ,(dk-meta-wrap ex `(IMPLIES (IN j NN) (IMPLIES (IN e (EXPR-STAGE j))
           ,(guard `(== ,(G-of 'e) (,(F-of 'j) e ,@ex))))))))))
     (lambda ()
       (dk-peel!)
       (let* ((rhs (caddr (dk-goal))) (ft (car rhs)) (pv (dk-meta-but-last (cdr ft))))
         (fact 'expr-set-intro 'j 'e)
         (let* ((r (dk-meta-rank! 'e)))
           (dk-apply! (dk-meta-rank-min 'e) 'j)
           (let* ((d (dk-skolem! (dk-cite! 'nn-le-gap 'j r))))
             (dk-split-all!)
             (let ((c (apply dk-cite! coh-name d (append pv (list r 'e) (cddr rhs)))))
               (mac ghead)
               (subst `(= j (+ ,r ,d)))
               (subst c)
               (qrfl))))))
     at-name)))

;;; The node-value drivers.  X a constructor term; AT the read-off law of the operation; ZS the
;;; zero / succ recursion law of its map; PV its parameter values; TRUTHS the sides of the IFs
;;; after the beta (the keep test excluded); FINISH closes the residual (== branch rhs).
(define (dk-meta-ifs! truths finish)
  (if (null? truths)
      (finish)
      (dk-meta-if-left! (car truths) (lambda () (dk-meta-ifs! (cdr truths) finish)))))

(define dk-meta-val-ex (make-parameter '()))     ; extra arguments of the stage map (OPEN's index)

(define (dk-meta-val0! x stage-law at zero pv truths finish)
  (fact stage-law (cadr x))
  (fact 'nn-zero-in)
  (subst (apply dk-cite! at (append pv (list 0 x) (dk-meta-val-ex))))
  (subst (apply dk-cite! zero pv))
  (dk-lam-b!)
  (mac (car x))
  (dk-meta-ifs! truths finish))

;; X new at stage (succ k), (IN x (EXPR-STAGE (succ k))) and (NOT (IN x (EXPR-STAGE k))) in context.
(define (dk-meta-val-succ! x k at succ pv truths finish)
  (fact 'nn-succ-closed k)
  (subst (apply dk-cite! at (append pv (list `(succ ,k) x) (dk-meta-val-ex))))
  (subst (apply dk-cite! succ (append pv (list k))))
  (dk-lam-b!)
  (dk-meta-if-left! #f (lambda () (mac (car x)) (dk-meta-ifs! truths finish))))

;; Unpack the "new at its rank" law for the node X: return k, with the conjuncts in context and
;; X typed in S_(succ k).
(define (dk-meta-new-at! x)
  (let* ((k (case (car x)
              ((EAPP) (dk-skolem! (apply dk-cite! 'expr-rank-app (cdr x))))
              ((EBIND) (dk-skolem! (apply dk-cite! 'expr-rank-bind (cdr x))))
              (else (error "dk-meta-new-at!: not an APP / BIND term" x)))))
    (dk-split-all!)
    (case (car x)
      ((EAPP) (fact 'expr-stage-app k (cadr x) (caddr x)))
      ((EBIND) (apply fact 'expr-stage-bind k (cdr x))))
    k))

;; (= A B) for A, B BIG-UNIONs over one domain D: by class-extensionality, at the element
;; level, where (ELEM! w) lands (== FA[w] FB[w]) with (IN w D) in context.  Returns the claim.
(define (dk-meta-bu-eq! a b elem!)
  (let* ((claim `(= ,a ,b))
         (dom (caddr a))
         (fa (lambda (w) (subst-free (cadr a) w (cadddr a))))
         (fb (lambda (w) (subst-free (cadr b) w (cadddr b))))
         (dir! (lambda (from to fx fy)        ; (IN x from) assumed, goal (IN x to)
                 (let* ((x (cadr (dk-goal)))
                        (landed (dk-landed (lambda () (bu-me `(IN ,x ,from)))))
                        (wm (or (find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (caddr f) dom)))
                                            landed)
                                (error "dk-meta-bu-eq!: no index landed")))
                        (w (cadr wm)))
                   (elem! w)
                   (dk-each-leaf! (lambda () (bu-mi w))
                     (lambda ()
                       (if (dk-asm? (dk-goal))
                           (ass)
                           (begin (subst `(= ,(fy w) ,(fx w))) (ass)))))))))
    (dk-have! claim
      (lambda ()
        (let ((univ `(FORALL dkmx_ (IFF (IN dkmx_ ,a) (IN dkmx_ ,b)))))
          (dk-have! univ
            (lambda ()
              (dk-peel!)
              ;; `di' of the IFF opens two leaves, each with its antecedent assumed
              (dk-iff! (lambda (g) (equal? (caddr g) b))
                (lambda () (dir! a b fa fb))
                (lambda () (dir! b a fb fa)))))
          (fact 'class-extensionality a b)
          (ass))))
    claim))

;; (IN (MAKE-SET l) SET) for l in TUPLES(EXPR-SET) in context.
(define (dk-meta-makeset-set! l)
  (if (not (dk-asm? `(IN (MAKE-SET ,l) SET)))
      (begin
        (if (not (dk-asm? '(IN EXPR-SET SET))) (fact 'expr-set-is-set))
        (dk-meta-and! `(IN ,l (TUPLES EXPR-SET)) '(IN EXPR-SET SET))
        (fact 'make-set-sethood 'EXPR-SET l))))

(define (dk-meta-finsub x) `(AND (IN ,x SET) (AND (SUBSET ,x NN) (IN (CARD ,x) NN))))

;; (IN (LENGTH l) NN) for l in TUPLES(C) in context (C typed first if it is a stage).
(define (dk-meta-len-nn! l c)
  (if (not (dk-asm? `(IN (LENGTH ,l) NN)))
      (begin (dk-meta-type-stages! c) (fact 'length-in-nn c l))))

;; (IN (,f (NTH i l)) B) from f in FUN(A, B), l in TUPLES(A), i in range, all in context.
(define (dk-meta-app-type! f a b x)
  (dk-meta-and! `(IN ,f (FUN ,a ,b)) `(IN ,x ,a))
  (fact 'fun-apply-type f a b x))

;; MAPL(f, l) in TUPLES(B), with its length and entries, for f in FUN(S, B) and l in TUPLES(S)
;; in context (VALUE-TYPE! i lands (IN (f (NTH i l)) B) on the leaf; default fun-apply-type).
(define (dk-meta-mapl! f l s b . value-type!)
  (dk-meta-len-nn! l s)
  (let ((hv `(FORALL dkmi3_ (IMPLIES (IN dkmi3_ NN) (IMPLIES (<= 1 dkmi3_) (IMPLIES (<= dkmi3_ (LENGTH ,l))
               (IN (,f (NTH dkmi3_ ,l)) ,b)))))))
    (dk-have! hv
      (lambda ()
        (dk-peel!)
        (let ((i (cadr (cadr (cadr (dk-goal))))))
          (dk-meta-nth-in! s i l)
          (if (pair? value-type!)
              ((car value-type!) i)
              (let ((leaf (proof-state-focus *ps*)))
                (dk-meta-app-type! f s b `(NTH ,i ,l))
                (if (not (sequent-node-grounded? leaf)) (ass)))))))
    (fact 'mapl-prop b f l)
    (dk-split-all!)
    `(MAPL ,f ,l)))

;; the goal (IN (NTH i l) (MAKE-SET l)), i in range and l in TUPLES(C) in context.
(define (dk-meta-in-makeset! i l c)
  (let ((w `(NTH ,i ,l)))
    (dk-meta-nth-in! c i l)
    (fact 'make-set-membership w l)
    (let* ((iff (iff-for `(IN ,w (MAKE-SET ,l)))) (rhs (caddr iff)))
      (dk-have! rhs
        (lambda ()
          (dk-conj-close!
            (lambda ()
              (cond ((dk-head-is? (dk-goal) 'FORSOME)
                     (ew i)
                     (dk-conj-close! (lambda () (if (dk-asm? (dk-goal)) (ass) (rfl)))))
                    (#t (dk-meta-set-of! w c) (ass)))))))
      (dk-meta-keep-prop! iff rhs))))

;; (IN (f x y) B) from f in FUN(S x NN, B), x in S, y in NN in context (apply-tupling-2).
(define (dk-meta-app2-type! f s b x y)
  (let ((goal `(IN (,f ,x ,y) ,b)))
    (if (not (dk-asm? goal))
        (begin
          (dk-meta-type-stages! s)
          (dk-have! `(IN (LIST ,x ,y) (CARTESIAN ,s NN)) (lambda () (dk-meta-close-in!)))
          (dk-meta-app-type! f `(CARTESIAN ,s NN) b `(LIST ,x ,y))
          (let ((eqn (dk-cite! 'apply-tupling-2 f x y)))
            (dk-have! goal (lambda () (subst eqn) (ass))))))
    goal))

;; MAPLK(f, l, y) in TUPLES(B), with length and entries; VALUE-TYPE! as in dk-meta-mapl!.
(define (dk-meta-maplk! f l y s b . value-type!)
  (dk-meta-len-nn! l s)
  (let ((hv `(FORALL dkmi3_ (IMPLIES (IN dkmi3_ NN) (IMPLIES (<= 1 dkmi3_) (IMPLIES (<= dkmi3_ (LENGTH ,l))
               (IN (,f (NTH dkmi3_ ,l) ,y) ,b)))))))
    (dk-have! hv
      (lambda ()
        (dk-peel!)
        (let ((i (cadr (cadr (cadr (dk-goal))))))
          (dk-meta-nth-in! s i l)
          (if (pair? value-type!)
              ((car value-type!) i)
              (let ((leaf (proof-state-focus *ps*)))
                (dk-meta-app2-type! f s b `(NTH ,i ,l) y)
                (if (not (sequent-node-grounded? leaf)) (ass)))))))
    (fact 'maplk-prop b f l y)
    (dk-split-all!)
    `(MAPLK ,f ,l ,y)))

;; Transfer a SEP condition: prove the goal TO from FROM (in context), the two differing only by
;; the applications FAPP[t] (in FROM) and GAPP[t] (in TO); shapes: a guarded universal
;; (FORALL w (IMPLIES (IN w D) (IN x APP[w]))), a membership (IN y APP[t]), or an AND of them.
;; (ELEM! t) lands the equation between FAPP[t] and GAPP[t].
(define (dk-meta-cond-transfer! from gapp fapp elem!)
  (let ((to (dk-goal)))
    (cond
      ((dk-asm? to) (ass))                    ; a conjunct both conditions share (META-2)
      ((dk-head-is? to 'AND)
       (let ((parts (dk-split! from)))
         (dk-conj-close!
           (lambda ()
             (let* ((g (dk-goal))
                    (src (find-first (lambda (f) (and (pair? f) (eq? (car f) (car g))
                                                      (or (not (eq? (car g) 'IN)) (equal? (cadr f) (cadr g)))))
                                     parts)))
               (dk-meta-cond-transfer! src gapp fapp elem!))))))
      ((dk-head-is? to 'FORALL)
       (dk-peel!)
       (let* ((g (dk-goal)) (w (cadr (caddr g))))
         (dk-apply! from w)
         (elem! w)
         (subst `(= ,(gapp w) ,(fapp w)))
         (ass)))
      ((dk-head-is? to 'IN)
       (let ((t (cadr (caddr to))))
         (elem! t)
         (subst `(= ,(gapp t) ,(fapp t)))
         (ass)))
      (#t (error "dk-meta-cond-transfer!: no route" (expression->string to))))))

;; (= A B) for A, B SEPs over one domain whose conditions differ by FAPP / GAPP (A has FAPP).
(define (dk-meta-sep-eq! a b fapp gapp elem!)
  (let* ((claim `(= ,a ,b))
         (dir! (lambda (from to fa ga)
                 (let* ((x (cadr (dk-goal)))
                        (landed (dk-landed (lambda () (sep-me `(IN ,x ,from)))))
                        (c (find-first (lambda (f) (not (and (dk-head-is? f 'IN) (equal? (cadr f) x)
                                                             (equal? (caddr f) (caddr from)))))
                                       landed)))
                   (in-sep! (lambda () (ass))
                            (lambda () (dk-meta-cond-transfer! c ga fa elem!)))))))
    (dk-have! claim
      (lambda ()
        (let ((univ `(FORALL dkmx_ (IFF (IN dkmx_ ,a) (IN dkmx_ ,b)))))
          (dk-have! univ
            (lambda ()
              (dk-peel!)
              (dk-iff! (lambda (g) (equal? (caddr g) b))
                (lambda () (dir! a b fapp gapp))
                (lambda () (dir! b a gapp fapp)))))
          (fact 'class-extensionality a b)
          (ass))))
    claim))

;;; -----------------------------------------------------------------------
;;; B. dk-derive! -- a derivation in the core, given as a tree, proved as a membership in DERIVABLE.
;;;
;;;   (dk-derive! TT TREE)  lands (IN (LIST G F) (DERIVABLE TT)) for the root sequent G ==> F of
;;;                         TREE and returns that formula.  The focus stays where it was.
;;;
;;; THE TREE.  A node is written as the paper writes a step of a sequent derivation, conclusion
;;; first, premises below it, in the order of the rule's hypothesis list (structure-library/
;;; meta-core.scm, section 4):
;;;
;;;     (RULE (G ==> F) [(v := TERM) ...] PREMISE ...)     a core rule
;;;     (given (G ==> F))                                   a premise of the whole derivation:
;;;                                                         (IN (LIST G F) (DERIVABLE TT)) is
;;;                                                         already in context
;;;
;;; RULE is the core relation's name without CR- (cut, backchain, assumption, weakening, not-elim,
;;; iff-elim, union-mem, intersection-mem, forall-intro, ...: the 42 of mc--core-names).  G is a
;;; context TERM (a variable or CTX-ADD terms over one) and F an encoded formula.  The witnesses
;;; of the relation are read off by MATCHING the relation's conclusion and hypothesis patterns
;;; against the node's sequent and its premises' sequents; a witness neither pattern determines
;;; (not-elim's a, which no premise shows) is given as (a := TERM), named as in meta-core.scm
;;; without the mc prefix and the underscore (g f a b d p q x l k y tm ...).
;;;
;;; WHAT IT DISCHARGES, for each node, bottom up, before it cites the closure law
;;; derivable-<rule> (meta-core-laws.scm, section G):
;;;   - the node's SEQ-SET membership: G in CTX-SET (CTX-ADD by ctx-add-ctx), F in CLF;
;;;   - the relation's side conditions, instantiated: (IN a G) for a context G (CTX-ADD by
;;;     ctx-add-has / ctx-add-keeps down to a membership in context), (SUBSET D G) (subset-refl,
;;;     ctx-sub-cons, ctx-sub-snoc down to a SUBSET in context), (IN t CLF) / (IN t CLT) (below),
;;;     and any other condition (an index bound, the eigenvariable condition (NOT (IN y ...)),
;;;     (<= 1 (LENGTH l))) only from the context, or by `arith' when ground;
;;;   - well-formedness (IN t CLF), (IN t CLT): from the context; from a SEQ-SET membership in
;;;     context (seq-iff); by the constructor's intro law (dk-meta-wf-intros); as a member of a
;;;     context in CTX-SET (ctx-mem); or by elimination from a larger formula known well formed
;;;     (dk-meta-wf-elims).  A list entry, an n-ary ENC-ORL / ENC-ANDL / ENC-ANDE or a MAKE-SET
;;;     universal is NOT reached: the driver lands such facts before calling dk-derive!.
;;; A side condition that does not close is an ERROR naming the node (its path from the root,
;;; its rule and its sequent) and the unmet condition; nothing is cited for that node.
;;;
;;; Example (adm-detach, meta-core-laws.scm): from [g + q, f] derivable, (p => q) and p in g:
;;;     (dk-derive! 'tt
;;;       `(cut (,g ==> ,f)
;;;          (backchain (,g ==> ,q) (assumption (,g ==> ,p)))
;;;          (given ((CTX-ADD ,g ,q) ==> ,f))))
;;;
;;; The planner (dk-meta--plan-*) only INSPECTS the context and returns a thunk or #f; nothing is
;;; cited until a whole plan exists, so a failed attempt leaves no step behind.

;;; IFF projections without `prop' (phase 2, mc-iff! / mc-iff-r! / mc-iff-l!).
(define (dk-meta-iff! thm . args)          ; cite THM at ARGS, detach to its IFF, return it
  (let ((f (apply dk-cite! thm args)))
    (if (dk-head-is? f 'IFF) f
        (error "dk-meta-iff!: the citation did not detach to an IFF" thm (expression->string f)))))
(define (dk-meta-iff-r! iff)               ; IFF and its left side in context: land the right side
  (let ((l (cadr iff)) (r (caddr iff)))
    (if (not (dk-asm? r))
        (begin (if (dk-asm? iff) (ai iff)) (detach! `(IMPLIES ,l ,r))))
    r))
(define (dk-meta-iff-l! iff)               ; IFF and its right side in context: land the left side
  (let ((l (cadr iff)) (r (caddr iff)))
    (if (not (dk-asm? l))
        (begin (if (dk-asm? iff) (ai iff)) (detach! `(IMPLIES ,r ,l))))
    l))

;; (IN (LIST g f) SEQ-SET) from g in CTX-SET and f in CLF in context.
(define (dk-meta-seq! g f)
  (let ((goal `(IN (LIST ,g ,f) SEQ-SET)))
    (if (not (dk-asm? goal))
        (let ((iff (dk-meta-iff! 'seq-iff g f)))
          (dk-meta-and! `(IN ,g CTX-SET) `(IN ,f CLF))
          (dk-meta-iff-l! iff)))
    goal))
;; CTX-ADD g a in CTX-SET, a in SET, from g in CTX-SET and a in CLF.
(define (dk-meta-ctx+! g a)
  (dk-meta-set-of! a 'CLF)
  (dk-cite! 'ctx-add-ctx g a)
  `(CTX-ADD ,g ,a))
;; the closure law of a core relation: CR-CUT -> derivable-cut
(define (dk-meta-law-name cr)
  (string->symbol (string-append "derivable-" (string-downcase (string-tail (symbol->string cr) 3)))))

;;; The well-formedness tables: constructor -> argument classes and the law.
(define dk-meta-wf-intros
  '((ENC-IMP (CLF CLF) clf-imp-intro) (ENC-OR (CLF CLF) clf-or-intro) (ENC-IFF (CLF CLF) clf-iff-intro)
    (ENC-AND (CLF CLF) clf-and-intro) (ENC-NOT (CLF) clf-not-intro) (ENC-IN (CLT CLT) clf-in-intro)))
(define dk-meta-wf-atoms '((ENC-FALSITY clf-falsity) (ENC-TRUTH clf-truth)))
(define dk-meta-wf-elims                   ; each law: (IN (C a ..) CLF) => the AND of the arguments'
  '((ENC-IMP (CLF CLF) clf-imp-elim) (ENC-OR (CLF CLF) clf-or-elim) (ENC-IFF (CLF CLF) clf-iff-elim)
    (ENC-AND (CLF CLF) clf-and-elim) (ENC-NOT (CLF) clf-not-elim) (ENC-IN (CLT CLT) clf-in-elim)))
(define dk-meta--classes '(CLF CLT CTX-SET SEQ-SET EXPR-SET SET NN))

(define (dk-meta--ctx-term? g) (not (memq g dk-meta--classes)))
(define (dk-meta--add? t) (and (pair? t) (eq? (car t) 'CTX-ADD) (= (length t) 3)))
(define (dk-meta--same? a b) (or (equal? a b) (eq? #t (vnb-guard (lambda () (alpha-equiv? a b))))))
(define (dk-meta--seq-of node) (cadr node))            ; (G ==> F)
(define (dk-meta--seq-term s)
  (if (and (list? s) (= (length s) 3) (eq? (cadr s) '==>))
      `(LIST ,(car s) ,(caddr s))
      (error "dk-derive!: a sequent is written (G ==> F), not" s)))

;;; ---- the planner: each returns a thunk that establishes the fact, or #f.  VISIT is the stack
;;; of (term . class) pairs being planned, so that no plan loops.

(define (dk-meta--once fact thunk)          ; a plan step re-checks its fact when it runs: an
  (and thunk (lambda () (if (not (dk-asm? fact)) (thunk)))))   ; earlier step may have landed it
(define (dk-meta--plan-wf t cls visit)
  (dk-meta--once `(IN ,t ,cls) (dk-meta--plan-wf0 t cls visit)))
(define (dk-meta--plan-wf0 t cls visit)
  (cond
    ((dk-asm? `(IN ,t ,cls)) (lambda () #t))
    ((member (cons t cls) visit) #f)
    (#t
     (let ((visit (cons (cons t cls) visit)))
       (or (dk-meta--plan-wf-seq t cls)
           (and (eq? cls 'CTX-SET) (dk-meta--add? t)
                (let ((p1 (dk-meta--plan-wf (cadr t) 'CTX-SET visit))
                      (p2 (dk-meta--plan-wf (caddr t) 'CLF visit)))
                  (and p1 p2 (lambda () (p1) (p2) (dk-meta-ctx+! (cadr t) (caddr t))))))
           (and (eq? cls 'CLF) (symbol? t) (assq t dk-meta-wf-atoms)
                (let ((law (cadr (assq t dk-meta-wf-atoms)))) (lambda () (fact law))))
           (and (memq cls '(CLF CLT)) (pair? t) (assq (car t) dk-meta-wf-intros)
                (let ((row (assq (car t) dk-meta-wf-intros)))
                  (and (eq? cls 'CLF) (= (length (cadr row)) (length (cdr t)))
                       (let ((ps (map (lambda (a c) (dk-meta--plan-wf a c visit)) (cdr t) (cadr row))))
                         (and (every (lambda (p) p) ps)
                              (lambda () (for-each (lambda (p) (p)) ps)
                                         (apply dk-cite! (caddr row) (cdr t))))))))
           (and (eq? cls 'CLF) (dk-meta--plan-wf-member t visit))
           (dk-meta--plan-wf-elim t cls visit))))))

;; a SEQ-SET membership in context names t as a context or a formula
(define (dk-meta--plan-wf-seq t cls)
  (let ((s (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'SEQ-SET)
                                        (dk-head-is? (cadr f) 'LIST) (= (length (cadr f)) 3)
                                        (equal? (if (eq? cls 'CTX-SET) (cadr (cadr f)) (caddr (cadr f))) t)))
                       (if (memq cls '(CLF CTX-SET)) (dk-asms) '()))))
    (and s (lambda ()
             (dk-split! (dk-meta-iff-r! (dk-meta-iff! 'seq-iff (cadr (cadr s)) (caddr (cadr s)))))))))

;; t a member of a context in CTX-SET: ctx-mem
(define (dk-meta--plan-wf-member t visit)
  (let loop ((as (dk-asms)))
    (and (pair? as)
         (let ((f (car as)))
           (or (and (dk-head-is? f 'IN) (equal? (cadr f) t) (dk-meta--ctx-term? (caddr f))
                    (let ((p (dk-meta--plan-wf (caddr f) 'CTX-SET visit)))
                      (and p (lambda () (p) (dk-cite! 'ctx-mem (caddr f) t)))))
               (loop (cdr as)))))))

;; the path of argument positions from U down to an occurrence of T through eliminable heads
(define (dk-meta--elim-path u t)
  (cond ((equal? u t) '())
        ((and (pair? u) (assq (car u) dk-meta-wf-elims)
              (= (length (cadr (assq (car u) dk-meta-wf-elims))) (length (cdr u))))
         (let loop ((as (cdr u)) (i 0))
           (and (pair? as)
                (let ((p (dk-meta--elim-path (car as) t)))
                  (if p (cons i p) (loop (cdr as) (+ i 1)))))))
        (#t #f)))
(define (dk-meta--elim-class u path cls)     ; the class the path ends in, starting from U in CLS
  (if (null? path) cls
      (let ((row (assq (car u) dk-meta-wf-elims)))
        (and (eq? cls 'CLF)
             (dk-meta--elim-class (list-ref (cdr u) (car path)) (cdr path) (list-ref (cadr row) (car path)))))))
(define (dk-meta--plan-wf-elim t cls visit)
  (let loop ((as (dk-asms)))
    (and (pair? as)
         (let* ((f (car as))
                (u (and (dk-head-is? f 'IN) (pair? (cadr f)) (cadr f)))
                (path (and u (not (equal? u t)) (dk-meta--elim-path u t))))
           (or (and path (pair? path) (eq? (dk-meta--elim-class u path 'CLF) cls)
                    (let ((p (dk-meta--plan-wf u 'CLF visit)))
                      (and p (lambda ()
                               (p)
                               (let walk ((u u) (path path))
                                 (if (pair? path)
                                     (let ((row (assq (car u) dk-meta-wf-elims)))
                                       (if (not (dk-asm? `(IN ,(list-ref (cdr u) (car path)) ,(list-ref (cadr row) (car path)))))
                                           (let ((r (apply dk-cite! (caddr row) (cdr u))))
                                             (if (dk-head-is? r 'AND) (dk-split! r))))
                                       (walk (list-ref (cdr u) (car path)) (cdr path)))))))))
               (loop (cdr as)))))))

;; (IN a G), G a context term
(define (dk-meta--plan-mem a g visit)
  (dk-meta--once `(IN ,a ,g) (dk-meta--plan-mem0 a g visit)))
(define (dk-meta--plan-mem0 a g visit)
  (cond ((dk-asm? `(IN ,a ,g)) (lambda () #t))
        ((dk-meta--add? g)
         (let ((g0 (cadr g)) (b (caddr g)))
           (if (dk-meta--same? a b)
               (let ((p (dk-meta--plan-wf b 'CLF visit)))
                 (and p (lambda () (p) (dk-meta-set-of! b 'CLF) (dk-cite! 'ctx-add-has g0 b))))
               (let ((p1 (dk-meta--plan-mem a g0 visit)) (p2 (dk-meta--plan-wf b 'CLF visit)))
                 (and p1 p2 (lambda () (p1) (p2) (dk-meta-set-of! b 'CLF) (dk-cite! 'ctx-add-keeps g0 b a)))))))
        (#t #f)))
;; (SUBSET D G), contexts
(define (dk-meta--plan-sub d g visit)
  (dk-meta--once `(SUBSET ,d ,g) (dk-meta--plan-sub0 d g visit)))
(define (dk-meta--plan-sub0 d g visit)
  (cond ((dk-asm? `(SUBSET ,d ,g)) (lambda () #t))
        ((equal? d g) (lambda () (fact 'subset-refl d)))
        ((dk-meta--add? d)
         (let ((p1 (dk-meta--plan-sub (cadr d) g visit)) (p2 (dk-meta--plan-mem (caddr d) g visit))
               (p3 (dk-meta--plan-wf (caddr d) 'CLF visit)))
           (and p1 p2 p3 (lambda () (p1) (p2) (p3) (dk-meta-set-of! (caddr d) 'CLF)
                                    (dk-cite! 'ctx-sub-cons (cadr d) g (caddr d))))))
        ((dk-meta--add? g)
         (let ((p1 (dk-meta--plan-sub d (cadr g) visit)) (p2 (dk-meta--plan-wf (caddr g) 'CLF visit)))
           (and p1 p2 (lambda () (p1) (p2) (dk-meta-set-of! (caddr g) 'CLF)
                                 (dk-cite! 'ctx-sub-snoc d (cadr g) (caddr g))))))
        (#t #f)))
;; a side condition of a relation
(define (dk-meta--plan-side c)
  (dk-meta--once c (dk-meta--plan-side0 c)))
(define (dk-meta--plan-side0 c)
  (cond ((dk-asm? c) (lambda () #t))
        ((and (dk-head-is? c 'IN) (memq (caddr c) '(CLF CLT CTX-SET))) (dk-meta--plan-wf (cadr c) (caddr c) '()))
        ((and (dk-head-is? c 'IN) (dk-meta--ctx-term? (caddr c))) (dk-meta--plan-mem (cadr c) (caddr c) '()))
        ((dk-head-is? c 'SUBSET) (dk-meta--plan-sub (cadr c) (caddr c) '()))
        ((and (memq (dk-head c) '(<= = IN NOT)) (eq? #t (vnb-guard (lambda () (arith-eval-formula c)))))
         (lambda () (dk-have! c (lambda () (arith)))))
        (#t #f)))

;;; ---- the relation, read off its definition

(define (dk-meta--cr-name rule)          ; cut -> cr-cut (MIT folds: every symbol is lower case)
  (let ((nm (string->symbol (string-append "cr-" (string-downcase (symbol->string rule))))))
    (if (not (hash-table-ref/default *theorem-table* nm #f)) (error "dk-derive!: no core rule named" rule))
    nm))
;; the defining IFF of CR-X, its FORSOME variables and its conjuncts, with T, hs, c substituted
(define (dk-meta--cr-parts cr tt hs c)
  (let* ((f (lookup-theorem cr))
         (body (let peel ((f f) (k 3)) (if (> k 0) (peel (caddr f) (- k 1)) (caddr f))))
         (body (dk-meta--subst-syms body `((mct_ . ,tt) (mchs_ . ,hs) (mcc_ . ,c)))))
    (let strip ((b body) (vars '()))
      (if (dk-head-is? b 'FORSOME)
          (strip (caddr b) (cons (cadr b) vars))
          (values (reverse vars)
                  (let flat ((b b)) (if (dk-head-is? b 'AND) (append (flat (cadr b)) (flat (caddr b))) (list b))))))))
(define (dk-meta--subst-syms e al)
  (cond ((symbol? e) (let ((p (assq e al))) (if p (cdr p) e)))
        ((pair? e) (map (lambda (x) (dk-meta--subst-syms x al)) e))
        (#t e)))
;; first-order matching of PAT (holes VARS) against TERM, extending the alist AL; #f on a clash
(define (dk-meta--match vars pat term al)
  (cond ((not al) #f)
        ((and (symbol? pat) (memq pat vars))
         (let ((p (assq pat al)))
           (cond ((not p) (cons (cons pat term) al))
                 ((equal? (cdr p) term) al)
                 (#t #f))))
        ((pair? pat)
         (and (pair? term) (= (length pat) (length term))
              (let loop ((ps pat) (ts term) (al al))
                (if (null? ps) al (loop (cdr ps) (cdr ts) (dk-meta--match vars (car ps) (car ts) al))))))
        (#t (and (equal? pat term) al))))
(define (dk-meta--wname v)                 ; mca_ -> a
  (let ((s (symbol->string v)))
    (string->symbol (substring s 2 (- (string-length s) 1)))))

;;; ---- the driver

(define dk-meta-trace #f)                  ; #t: print each node and side condition as it is discharged

(define (dk-derive! tt tree)
  (dk-meta--derive tt tree "root"))

(define (dk-meta--describe tree path)
  (string-append "node " path " (" (symbol->string (car tree)) " "
                 (expression->string (dk-meta--seq-term (dk-meta--seq-of tree))) ")"))

(define (dk-meta--derive tt tree path)
  (if (not (and (pair? tree) (symbol? (car tree)) (pair? (cdr tree))))
      (error "dk-derive!: a node is (RULE (G ==> F) ...), not" tree))
  (let* ((rule (car tree)) (c (dk-meta--seq-term (dk-meta--seq-of tree)))
         (goal `(IN ,c (DERIVABLE ,tt))))
    (cond
      ((eq? rule 'given)
        (if (dk-asm? goal) goal
            (error (string-append "dk-derive!: " (dk-meta--describe tree path)
                                  ": the given sequent is not derivable in context")
                   (expression->string goal))))
      ((dk-asm? goal) goal)
      (#t
        (let* ((cr (dk-meta--cr-name rule))
               (items (cddr tree))
               (withs (filter (lambda (i) (and (list? i) (= (length i) 3) (eq? (cadr i) ':=))) items))
               (kids (filter (lambda (i) (not (memq i withs))) items))
               (kid-seqs
                 (let loop ((ks kids) (i 1) (acc '()))
                   (if (null? ks) (reverse acc)
                       (begin (dk-meta--derive tt (car ks) (string-append path "/" (number->string i)))
                              (loop (cdr ks) (+ i 1) (cons (dk-meta--seq-term (dk-meta--seq-of (car ks))) acc))))))
               (hs `(LIST ,@kid-seqs))
               (what (lambda () (dk-meta--describe tree path))))
          (call-with-values (lambda () (dk-meta--cr-parts cr tt hs c))
            (lambda (vars conjs)
              (let* ((ceq (find-first (lambda (k) (and (dk-head-is? k '=) (equal? (cadr k) c))) conjs))
                     (heq (find-first (lambda (k) (and (dk-head-is? k '=) (equal? (cadr k) hs))) conjs))
                     (sides (filter (lambda (k) (not (or (eq? k ceq) (eq? k heq)))) conjs))
                     (al0 (dk-meta--match vars (caddr ceq) c '()))
                     (chk0 (if (not al0) (error (string-append "dk-derive!: " (what) ": the sequent is not a conclusion of the rule")
                                             (expression->string (caddr ceq)))))
                     (hpats (cdr (caddr heq)))
                     (chk1 (if (not (= (length hpats) (length kid-seqs)))
                            (error (string-append "dk-derive!: " (what) ": the rule takes "
                                                  (number->string (length hpats)) " premise(s), the node has "
                                                  (number->string (length kid-seqs))))))
                     (al1 (let loop ((ps hpats) (ss kid-seqs) (al al0) (i 1))
                            (cond ((null? ps) al)
                                  (#t (let ((al2 (dk-meta--match vars (car ps) (car ss) al)))
                                        (if (not al2)
                                            (error (string-append "dk-derive!: " (what) ": premise " (number->string i)
                                                                  " does not have the rule's shape")
                                                   (expression->string (car ps))))
                                        (loop (cdr ps) (cdr ss) al2 (+ i 1)))))))
                     (al (fold-left (lambda (al w)
                                      (let ((v (symbol-append 'mc (car w) '_)))
                                        (if (not (memq v vars))
                                            (error (string-append "dk-derive!: " (what) ": the rule has no witness") (car w)))
                                        (dk-meta--match vars v (caddr w) al)))
                                    al1 withs))
                     (chk2 (if (not al) (error (string-append "dk-derive!: " (what) ": a given witness clashes with the match"))))
                     (ws (map (lambda (v)
                                (let ((p (assq v al)))
                                  (if p (cdr p)
                                      (error (string-append "dk-derive!: " (what) ": the witness " (symbol->string (dk-meta--wname v))
                                                            " is not determined; give (" (symbol->string (dk-meta--wname v))
                                                            " := TERM)")))))
                              vars))
                     (sides (map (lambda (k) (dk-meta--subst-syms k al)) sides))
                     (g (cadr c)) (f (caddr c))
                     (plans (map (lambda (k)
                                   (or (dk-meta--plan-side k)
                                       (error (string-append "dk-derive!: " (what) ": the side condition does not close")
                                              (expression->string k))))
                                 (append sides (list `(IN ,g CTX-SET) `(IN ,f CLF))))))
                (if dk-meta-trace
                    (begin (display ";; dk-derive! ") (display (what)) (newline)))
                (for-each (lambda (k p)
                            (if dk-meta-trace (begin (display ";;   side ") (display (expression->string k)) (newline)))
                            (p))
                          (append sides (list `(IN ,g CTX-SET) `(IN ,f CLF))) plans)
                (dk-meta-seq! g f)
                (dk-have! `(,cr ,tt ,hs ,c) (lambda () (mac cr) (dk-meta-ex-fill! ws)))
                (dk-have! `(HYPS-IN ,hs (DERIVABLE ,tt))
                  (lambda ()
                    (case (length kid-seqs)
                      ((0) (fact 'hyps-in-0 `(DERIVABLE ,tt)))
                      ((1) (fact 'hyps-in-1 (car kid-seqs) `(DERIVABLE ,tt)))
                      ((2) (fact 'hyps-in-2 (car kid-seqs) (cadr kid-seqs) `(DERIVABLE ,tt)))
                      ;; K1FIX (2026-11-19): lambda-type has three premises (the codomain's definedness)
                      ((3) (fact 'hyps-in-3 (car kid-seqs) (cadr kid-seqs) (caddr kid-seqs) `(DERIVABLE ,tt))))
                    (ass)))
                (if (not (dk-asm? goal)) (dk-cite! (dk-meta-law-name cr) tt hs c))
                (if (not (dk-asm? goal))
                    (error (string-append "dk-derive!: " (what) ": the closure law did not land") (expression->string goal)))
                goal))))))))

;;; ---- dk-meta-derive!: lemma nodes, one node at a time, the context pruned between nodes

;;; (dk-meta-derive! TT TREE) -- dk-derive! with two additions (agent META-3, 2026-10-09; spliced here
;;; from scratchpad/meta3/driver-kit-meta3.scm by META-W1, 2026-10-16, since three files use it:
;;; meta-cr-laws, meta-ind-laws, meta-def-laws).
;;;
;;;  1. LEMMA NODES:  (lemma (G ==> F) NAME (ARG ...) CHILD ...)  derives each CHILD, then cites NAME
;;;     at TT ARG ... (dk-cite!, which detaches the children's derivabilities and whatever typings are
;;;     in context) and demands that (IN [G, F] (DERIVABLE TT)) landed.  A derived rule proven once
;;;     (der-iff-r: (g ==> b) from (g ==> a IFF b) and (g ==> a)) replaces its expansion at every use.
;;;
;;;  2. ONE NODE AT A TIME, THE CONTEXT PRUNED BETWEEN NODES.  dk-derive! lands, at every node, the
;;;     node's CR instance, its HYPS-IN, its SEQ-SET membership and the typing of every context and
;;;     formula the planner touched, all in the one sequent the driver works in; the rule checkers
;;;     compare contexts as sets up to alpha, so every later step pays for every earlier node.  Here
;;;     each core node is handed to dk-derive! with its premises as (given ...) leaves, and after it
;;;     the context is cut back by ONE `keep' to the formulas present at entry plus every
;;;     derivability (IN (LIST g f) (DERIVABLE TT)) landed since.  A typing the next node needs is
;;;     planned again.  CONSEQUENCE FOR THE CALLER: a formula that landed during the call and is not
;;;     a derivability is GONE afterwards; land it after the call, or before it (then it is kept).
;;;
;;; Returns the root's derivability formula.  Suite: two "kit: dk-meta-derive!" checks.

(define (dk-meta-derive! tt tree)
  (let ((base (dk-asms)))
    (define (with? i) (and (list? i) (= (length i) 3) (eq? (cadr i) ':=)))
    (define (der-fact? f)
      (and (dk-head-is? f 'IN) (dk-head-is? (caddr f) 'DERIVABLE) (equal? (cadr (caddr f)) tt)))
    (define (prune!)
      (let* ((keepers (filter (lambda (f) (or (member f base) (der-fact? f))) (dk-asms))))
        (if (< (length keepers) (length (dk-asms)))
            (apply keep keepers))))
    (define (goal-of seq) `(IN ,(dk-meta--seq-term seq) (DERIVABLE ,tt)))
    (define (der t)
      (if (not (and (pair? t) (symbol? (car t)) (pair? (cdr t))))
          (error "dk-meta-derive!: a node is (RULE (G ==> F) ...), not" t))
      (let ((seq (cadr t)))
        (cond
          ((eq? (car t) 'given)
           (if (not (dk-asm? (goal-of seq)))
               (error "dk-meta-derive!: the given sequent is not derivable in context"
                      (expression->string (goal-of seq)))))
          ((dk-asm? (goal-of seq)) #t)
          ((eq? (car t) 'lemma)
           (let ((name (caddr t)) (args (cadddr t)) (kids (cddddr t)))
             (for-each der kids)
             (apply dk-cite! name tt args)
             (if (not (dk-asm? (goal-of seq)))
                 (error "dk-meta-derive!: the lemma did not land its sequent" name (expression->string (goal-of seq))))
             (prune!)))
          (#t
           (let* ((items (cddr t))
                  (withs (filter with? items))
                  (kids (filter (lambda (i) (not (with? i))) items)))
             (for-each der kids)
             (dk-derive! tt `(,(car t) ,seq ,@withs ,@(map (lambda (k) `(given ,(cadr k))) kids)))
             (prune!))))
        (goal-of seq)))
    (der tree)))

;;; =======================================================================
;;; KIT-5 (2026-10-25) -- the kit fixes owed by the LA-Z5, LA-Z6, PRODUCT2 and
;;; CA-HOPF sessions.  Each item has suite checks (test-suite.scm, "driver kit
;;; (KIT-5)"), with a CONTROL that fails on the code before this section.
;;; Changed in place elsewhere in this file: dk-close-if! (follows the leaf its
;;; thunk created), dk-nn! (a bare call gathers the context's NN order atoms),
;;; type-term--plan / type-term--exec! (unary closure laws: conjugate,
;;; magnitude, abs, real-part, imag-part).
;;; =======================================================================

;;; -----------------------------------------------------------------------
;;; THE LEAF A NODE BECAME.  A step that rewrites the goal -- lam-b, mac, subst,
;;; fact, a cut -- does not close the node it ran on: it justifies it by a NEW
;;; node, and the focus moves there.  The node the driver captured is then an
;;; ungrounded INNER node, and what the driver means by "that leaf" is the open
;;; leaf below it.  (dk--open-below NODE): the open leaves reachable from NODE
;;; through the rules that justify it -- NODE itself when it is still a leaf,
;;; () when it is grounded.  Hash-consing makes the graph a DAG, so the walk
;;; keeps a visited list.
(define (dk--open-below node)
  (let ((leaves (dk-open-leaves)) (seen '()) (acc '()))
    (let walk ((n node))
      (if (not (memq n seen))
          (begin
            (set! seen (cons n seen))
            (cond ((sequent-node-grounded? n) #f)
                  ((memq n leaves) (set! acc (cons n acc)))
                  (#t (for-each (lambda (inf) (for-each walk (inference-node-hypotheses inf)))
                                (sequent-node-in-arrows n)))))))
    (reverse acc)))

;;; -----------------------------------------------------------------------
;;; (dk-close-on! NODE CLOSER) / (dk-ass-on! NODE) / (dk-by! THUNK [CLOSER])
;;; -- THE GUARDED CLOSER (KIT-5 items 1 and 4; LA-Z5 finding 4, LA-Z6 finding
;;; 3, CA-HOPF finding 2).
;;;
;;; The drift: a step that CLOSES the focus leaf -- `dk-have!' of a claim equal
;;; to the focus goal (proved in place), a `dk-cite!' / `detach-with!' /
;;; `dk-lam-b!' whose result was already in context -- moves the focus to
;;; another leaf, and the `(ass)' the driver wrote next, as the closer of the
;;; leaf just worked on, fires THERE ("assumption: goal not in context: I in
;;; set" was a lam-t sethood leaf).  `dk-have!' cannot be fixed to prevent it:
;;; once its claim was the focus goal, the leaf is CLOSED and there is no place
;;; left for the focus to stay; `dk-have!' says so by returning #t, and a caller
;;; that reads the value can tell.  What can be fixed is the closer: capture the
;;; node BEFORE the step, and close THAT, wherever it now is.
;;;
;;;   (dk-close-on! NODE CLOSER) -- NODE grounded: nothing, #t.  NODE still has
;;;       ONE open leaf below it (itself, or the node a rewrite of it created):
;;;       focus it if the focus is elsewhere, run CLOSER, and ERROR unless NODE
;;;       is then grounded.  Several open leaves below NODE: an ERROR naming
;;;       them, since which one the closer was meant for cannot be decided.
;;;   (dk-ass-on! NODE) -- the same with `ass', which ERRORS, naming the goal,
;;;       when the goal is not in context (the bare `ass' only warns).
;;;   (dk-by! THUNK [CLOSER]) -- capture the focus, run THUNK, close the
;;;       captured node with CLOSER (default `ass') if it is still open.
;;;
;;; Replaces: lz5c- / lz5d- / lz5q- / lz5z-ass-if!, lz5d- / lz5q- / lz5z-ass-ctx!,
;;; lz5d- / lz5q-by! (la-z5-*.scm), lz6p-ass-on! (la-z6-pullback.scm).  The
;;; -ass-if! copies tested the goal by SHAPE (`equal?' to the captured goal),
;;; which a sibling with the same goal passes; these test the NODE.
(define (dk-close-on! node closer)
  (if (sequent-node-grounded? node)
      #t
      (let ((below (dk--open-below node)))
        (cond
          ((null? below)
           (error "dk-close-on!: the node is open but has no open leaf below it"
                  (expression->string (dk-goal-of node))))
          ((pair? (cdr below))
           (error "dk-close-on!: the node has several open leaves below it; which one the closer is for is not decidable"
                  (map (lambda (l) (expression->string (dk-goal-of l))) below)))
          (#t
           (let ((leaf (car below)))
             (if (not (eq? leaf (proof-state-focus *ps*))) (dk-focus! leaf))
             (closer)
             (if (not (sequent-node-grounded? node))
                 (error "dk-close-on!: the closer left the node open"
                        (expression->string (dk-goal-of leaf))))
             #t))))))

(define (dk-ass-on! node)
  (dk-close-on! node
    (lambda ()
      (if (not (dk-asm? (dk-goal)))
          (error "dk-ass-on!: the goal is not in context" (expression->string (dk-goal))))
      (ass))))

(define (dk-by! thunk . opt)
  (let ((node (proof-state-focus *ps*)))
    (thunk)
    (if (pair? opt) (dk-close-on! node (car opt)) (dk-ass-on! node))))

;;; -----------------------------------------------------------------------
;;; (dk-have-cases! CLAIM P THEN ELSE) -- LAND A FACT BY CASES (KIT-5 item 4;
;;; LA-Z5 finding 3).  A helper meant to LAND a fact that splits on cases with a
;;; bare `use-em' leaves both branches open on the CALLER's goal; the cure is to
;;; run the split inside a `dk-have!' lane whose claim is the fact.  This is that
;;; lane: CLAIM is proved by `use-em' on P, THEN on the P branch and ELSE on the
;;; NOT-P branch.  A branch that leaves its leaf open with the goal in context is
;;; closed by `ass' (on the branch's own node, `dk-ass-on!'); one that leaves it
;;; open otherwise is an ERROR.  When the context ALREADY DECIDES P -- where
;;; `use-em' errors, rightly, as a split there is vacuous -- only the matching
;;; branch runs, with no split.  CLAIM equal to the focus goal is proved in place,
;;; as by `dk-have!'.  Returns CLAIM as a raw formula.  MODEL: lz5d-val!
;;; (la-z5-dsumcard.scm).
(define (dk--case-lane body)
  (lambda ()
    (let ((node (proof-state-focus *ps*)))
      (body)
      (if (not (sequent-node-grounded? node))
          (let ((below (dk--open-below node)))
            (if (and (pair? below) (null? (cdr below)) (dk-asm? (dk-goal-of (car below))))
                (dk-ass-on! node)
                (error "dk-have-cases!: a branch left its leaf open"
                       (map (lambda (l) (expression->string (dk-goal-of l))) below))))))))

(define (dk-have-cases! claim p then-body else-body)
  (let ((P (->raw-formula p)))
    (dk-have! claim
      (lambda ()
        (let ((dec (use-em--decided P)))
          (cond ((not dec) (use-em P (dk--case-lane then-body) (dk--case-lane else-body)))
                ((eq? (car dec) 'P) ((dk--case-lane then-body)))
                (#t ((dk--case-lane else-body)))))))
    (->raw-formula claim)))

;;; -----------------------------------------------------------------------
;;; READING EIGENVARIABLES OFF A LANDING (KIT-5 item 5; PRODUCT2 finding 2).
;;; `dk-peel!' returns what it landed.  The eps of an unfolded continuity or
;;; convergence goal is the variable of the POS-RR the peel landed, and the
;;; point is the variable the peel typed in the space; reading them off the
;;; CONTEXT instead (`msc-eps' in ms-continuity-algebra.scm: the first POS-RR in
;;; context) picks the wrong one as soon as a second POS-RR is there -- a delta
;;; already obtained, a hypothesis's own eps.
;;;
;;;   (dk-landed-vars LANDED CLASS)  -- every t with (IN t CLASS) among LANDED,
;;;                                     in landing order (CLASS compared by equal?)
;;;   (dk-landed-var LANDED CLASS)   -- the ONE such t; ERRORS on none and when
;;;                                     ambiguous (two variables typed in CLASS:
;;;                                     pass K)
;;;   (dk-landed-var LANDED CLASS K) -- the K-th (1-based)
;;;   (dk-landed-eps LANDED)         -- the ONE e with (POS-RR e) among LANDED, else
;;;                                     the one with (< 0 e); ERRORS on none or two
;;;
;;; Replaces p2-landed-eps / p2-landed-var (product2-laws.scm), p2c-landed-eps /
;;; p2c-landed-var (product2-cc.scm), which took the FIRST match silently.
(define (dk-landed-vars landed cls)
  (map cadr (filter (lambda (f) (and (dk-head-is? f 'IN) (= (length f) 3) (equal? (caddr f) cls)))
                    landed)))

(define (dk-landed-var landed cls . opt)
  (let ((vs (dk-landed-vars landed cls)))
    (cond ((null? vs)
           (error "dk-landed-var: nothing typed in the class among the landed formulas"
                  (expression->string cls) (map expression->string landed)))
          ((pair? opt)
           (if (and (exact-nonnegative-integer? (car opt)) (<= 1 (car opt) (length vs)))
               (list-ref vs (- (car opt) 1))
               (error "dk-landed-var: no such index; typed in the class:" (car opt) vs)))
          ((pair? (cdr vs))
           (error "dk-landed-var: ambiguous -- several variables typed in the class (pass the index):"
                  (expression->string cls) vs))
          (#t (car vs)))))

(define (dk-landed-eps landed)
  (let* ((pos (filter (lambda (f) (and (dk-head-is? f 'POS-RR) (= (length f) 2))) landed))
         (lt0 (filter (lambda (f) (and (dk-head-is? f '<) (= (length f) 3) (eqv? (cadr f) 0)))
                      landed))
         (hits (if (pair? pos) pos lt0)))
    (cond ((null? hits)
           (error "dk-landed-eps: no POS-RR (nor 0 < e) among the landed formulas"
                  (map expression->string landed)))
          ((pair? (cdr hits))
           (error "dk-landed-eps: ambiguous -- several positive reals landed"
                  (map expression->string hits)))
          (#t (if (dk-head-is? (car hits) 'POS-RR) (cadr (car hits)) (caddr (car hits)))))))

;;; =======================================================================
;;; KIT-6 (agent RA-BASICS, 2026-10-26; wired 2026-10-27, batch 0): scratchpad/kit6/kit6.scm,
;;; verbatim but for the integration fix: the first (chain) dk-vs-eq! is named dk-vs-eq-chain! in its
;;; own define (the probe file defined dk-vs-eq! twice and aliased the first).  Report:
;;; scratchpad/triage/KIT-6-REPORT.md.
;;; =======================================================================
;;; kit6.scm -- KIT-6: the tactics behind the 2026-10-26 grinds (agent RA-BASICS).
;;; An ADDITION to driver-kit.scm (paste at its end).  Every helper drives SURFACE tactics only
;;; (fact / subst / crs / ineq / cut / dk-*), moves focus through dk-focus!, and ERRORS on a miss.
;;;
;;;   (dk-undiv!)                 rewrite every `/' of the focus goal by binary-divide-def,
;;;                               typing each inner quotient first (F3 of RA-BASICS)
;;;   (dk-absurd! P ...)          FIXED: closes ANY goal from contradictory linear premises, and
;;;                               ERRORS when it does not close (the CA-MONTEL finding)
;;;   (dk-use-cases-open! DISJ BODY ...)   use-cases that runs a body only on a branch that is
;;;                               still OPEN (a branch hash-consing grounded is skipped)
;;;   (dk-vs-eq!)                 THE MODULE NORMALISER: decides a vector identity
;;;                               sum c_i . v_i = sum d_j . w_j in a normed vector space m
;;;   (dk-field-eq! [FIELD])      FIELD SIMPLIFICATION: decides an identity with recip / `/'
;;;                               over RR (default) or CC, posting missing d /= 0 as OWED leaves

;;; ===========================================================================
;;; (3) dk-undiv!
;;; One `mac binary-divide-def' pass rewrites the OUTERMOST quotients only, and under META-10 a
;;; matched value that is not certified defined (an inner quotient) is owed `t = t'.  So: type
;;; every quotient, innermost first, on a lane (the lane rewrites it, types the product and
;;; closes), then rewrite the goal to a fixpoint.  TYPER (optional) types a non-quotient
;;; subterm in the number class CLS (default RR); a denominator must be typed and nonzero in
;;; context, else ERROR naming it.
(define (dk--quotients t)                  ; innermost first
  (if (not (pair? t)) '()
      (let ((inner (apply append (map dk--quotients (cdr t)))))
        (if (and (eq? (car t) '/) (= (length t) 3)) (append inner (list t)) inner))))
(define (dk--nested-quotients t)           ; quotients that sit inside another quotient, innermost first
  (let ((all (dk--quotients t)))
    (filter (lambda (q) (any (lambda (o) (and (not (eq? o q)) (not (equal? o q)) (dk-contains? o q))) all)) all)))
(define (dk--undiv-term t)
  (cond ((not (pair? t)) t)
        ((and (eq? (car t) '/) (= (length t) 3))
         (list '* (dk--undiv-term (cadr t)) (list 'recip (dk--undiv-term (caddr t)))))
        (#t (map dk--undiv-term t))))
(define (dk--num-type! t cls)
  (let ((goal (list 'IN t cls)))
    (cond
     ((dk-asm? goal) #t)
     ((and (eqv? t 0) (eq? cls 'RR)) (fact 'rr-zero-in) #t)
     ((and (eqv? t 1) (eq? cls 'RR)) (fact 'rr-one-in) #t)
     ((number? t) (vnb-guard (lambda () (dk-have! goal))) (dk-asm? goal))
     ((and (pair? t) (eq? (car t) 'recip) (= (length t) 2))
      (let ((d (cadr t)))
        (and (dk--num-type! d cls)
             (or (dk-asm? (list 'NOT (list '= d 0)))
                 (error "dk--num-type!: recip of a term not known nonzero:" (expression->string d)))
             (begin
               (dk-have! (list 'AND (list 'IN d cls) (list 'NOT (list '= d 0))))
               (fact (if (eq? cls 'CC) 'cc-recip-closed 'rr-recip-closed) d)
               (dk-asm? goal)))))
     (#t
      (if (and (pair? t) (memq (car t) '(+ * - abs)))
          (for-each (lambda (a) (dk--num-type! a cls)) (cdr t)))
      (if (and (eq? cls 'RR) (pair? t) (every (lambda (a) (dk-asm? (list 'IN a 'RR))) (cdr t)))
          (let ((n (length t)))
            (cond ((and (eq? (car t) '+) (= n 3))
                   (dk-have! (list 'AND (list 'IN (cadr t) 'RR) (list 'IN (caddr t) 'RR)))
                   (fact 'rr-add-closed (cadr t) (caddr t)))
                  ((and (eq? (car t) '*) (= n 3))
                   (dk-have! (list 'AND (list 'IN (cadr t) 'RR) (list 'IN (caddr t) 'RR)))
                   (fact 'rr-mul-closed (cadr t) (caddr t)))
                  ((and (eq? (car t) '-) (= n 3)) (fact 'rr-sub-in-rr (cadr t) (caddr t)))
                  ((and (eq? (car t) '-) (= n 2)) (fact 'rr-neg-closed (cadr t)))
                  ((and (eq? (car t) 'abs) (= n 2)) (fact 'rr-abs-closed (cadr t))))))
      (if (not (dk-asm? goal)) (vnb-guard (lambda () (dk-type! t cls))))
      (dk-asm? goal)))))
(define (dk-undiv! . opt)
  (let ((cls (if (pair? opt) (car opt) 'RR)))
    (for-each
     (lambda (q)
       (let ((num (cadr q)) (den (caddr q)))
         (if (not (dk-asm? (list 'IN q cls)))
             (begin
               (if (not (dk-asm? (list 'NOT (list '= den 0))))
                   (if (not (dk-asm? (list 'NOT (list '= (dk--undiv-term den) 0))))
                       (error "dk-undiv!: the denominator is not known nonzero:" (expression->string den))))
               (dk-have! (list 'IN q cls)
                 (lambda ()
                   (let loop ((n 0))
                     (if (and (dk-contains? (dk-goal) '/) (< n 8))
                         (begin (mac 'binary-divide-def) (loop (+ n 1)))))
                   (let ((g (cadr (dk-goal))))
                     (if (not (dk--num-type! g cls))
                         (error "dk-undiv!: cannot type the quotient" (expression->string g))))
                   (if (dk-asm? (dk-goal)) (ass))))))))
     (dk--nested-quotients (dk-goal)))
    (let loop ((n 0))
      (if (and (dk-contains? (dk-goal) '/) (< n 8))
          (begin (mac 'binary-divide-def) (loop (+ n 1)))))
    (if (dk-contains? (dk-goal) '/)
        (error "dk-undiv!: a quotient survived" (expression->string (dk-goal))))))

;;; ===========================================================================
;;; (4a) dk-absurd!, fixed.  On FALSITY: as before.  On any other goal: `ineq' first (the old
;;; behaviour, kept: callers use it as dk-ineq!), on a transaction; if that does not close,
;;; EX FALSO -- refute (< 0 0) from the premises and close the goal propositionally.  ERRORS
;;; when the goal is still open (the old code returned silently: CA-MONTEL finding 2).
(define (dk-absurd! . prems)
  (let ((leaf (proof-state-focus *ps*)))
    (define (ex-falso!)
      (dk-have! '(< 0 0) (lambda () (apply dk-ineq! prems)))
      (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
      (let ((neg (dk-cite! 'rr-lt-irrefl 0)))
        (if (eq? (dk-goal) 'FALSITY)
            (ai neg)
            (if (dk-only! '(< 0 0) neg) (prop)))))
    (cond ((eq? (dk-goal) 'FALSITY) (ex-falso!))
          ((dk--transaction (lambda () (apply dk-ineq! prems) (sequent-node-grounded? leaf))) #t)
          (#t (ex-falso!)))
    (if (not (sequent-node-grounded? leaf))
        (error "dk-absurd!: the goal is still open -- the premises are not contradictory"
               (map expression->string (map ->raw-formula prems))))
    #t))

;;; ===========================================================================
;;; (4b) dk-use-cases-open!  use-cases, but a branch whose node is ALREADY GROUNDED (hash-
;;; consing put the case's sequent on a proven node -- a sibling case closed the same sequent)
;;; is skipped: positional `use-cases' focuses it, `dk-focus!' refuses to move, and the body
;;; runs on whatever leaf the focus fell back to (RA-BASICS rb2-use-cases!).  Returns the
;;; obligation node (#f when the disjunction was in context), as use-cases does.
(define (dk-use-cases-open! disjuncts . bodies)
  (let* ((result (use-cases disjuncts))
         (ob     (cases-obligation result))
         (cs     (cdr (assq 'cases result))))
    (if (not (= (length cs) (length bodies)))
        (error "dk-use-cases-open!: the split produced" (length cs) "cases, bodies:" (length bodies)))
    (for-each (lambda (mc body)
                (if (not (sequent-node-grounded? (cdr mc)))
                    (begin (dk-focus! (cdr mc)) (body))))
              cs bodies)
    ob))

;;; ===========================================================================
;;; (1) dk-vs-eq! -- THE MODULE NORMALISER ("crs for modules").
;;;
;;; Goal (= L R), L and R built from (VADD m), (ACT m), (VNEG m) over vector ATOMS (any other
;;; term, typed (IN v (VEC m)) in context), with IS-NORMED-VECTOR-SPACE(m) in context and the
;;; scalars real.  Each side is brought, by a chain of CITED law instances, to the canonical
;;; linear combination
;;;      c1.v1 + (c2.v2 + ( ... + ck.vk))      atoms sorted, each once,
;;; landing (= side canonical).  An atom present on one side only is padded on the other with
;;; coefficient 0 (nvs-act-zero).  The coefficients are then matched one by one by `crs' (a
;;; coefficient pair crs refuses is an ERROR: the identity is not a module identity), the
;;; canonical forms are joined by congruence, and eq-sym / eq-trans close the goal.
;;; Laws: nvs-vadd-assoc, nvs-vadd-comm, nvs-act-distrib-vec-rr, nvs-act-scale-assoc,
;;; nvs-act-add-scalars, nvs-one-act, nvs-neg-one-act, nvs-act-zero, eq-sym, eq-trans; the
;;; congruences go through dk-congr!.  Each equation is an exact law instance, so no `subst'
;;; ever rewrites an unintended occurrence.
;;; Not handled (ERROR): VZERO, scalars outside RR (a general module's carr(scal)).
(define dkv-m #f)
(define (dkv-add x y) (list (list 'VADD dkv-m) x y))
(define (dkv-act c v) (list (list 'ACT dkv-m) c v))
(define (dkv-op? t op n) (and (pair? t) (pair? (car t)) (eq? (caar t) op) (equal? (cadar t) dkv-m) (= (length t) n)))
(define (dkv-key v) (expression->string v))
(define (dkv-term L)                       ; L: list of (coef . atom), non-empty
  (if (null? (cdr L))
      (dkv-act (caar L) (cdar L))
      (dkv-add (dkv-act (caar L) (cdar L)) (dkv-term (cdr L)))))
(define (dkv-rr! c)
  (if (not (dk--num-type! c 'RR)) (error "dk-vs-eq!: a scalar is not typed in RR:" (expression->string c))))
(define (dkv-vec! t)
  (let ((g (list 'IN t (list 'VEC dkv-m))))
    (cond ((dk-asm? g) #t)
          ((dkv-op? t 'VADD 3) (dkv-vec! (cadr t)) (dkv-vec! (caddr t)) (dk-cite! 'nvs-vadd-in-vec dkv-m (cadr t) (caddr t)))
          ((dkv-op? t 'ACT 3) (dkv-rr! (cadr t)) (dkv-vec! (caddr t)) (dk-cite! 'nvs-act-in-vec dkv-m (cadr t) (caddr t)))
          ((dkv-op? t 'VNEG 2) (dkv-vec! (cadr t)) (dk-cite! 'nvs-vneg-in-vec dkv-m (cadr t)))
          (#t (error "dk-vs-eq!: a vector atom is not typed in VEC:" (expression->string t))))))
;;; a chain from ORIG: (vector orig cur); STEP! moves cur to NEW with PROVER! landing (= cur new)
(define (dkv-chain t) (vector t t))
(define (dkv-step! ch new prover!)
  (let ((orig (vector-ref ch 0)) (cur (vector-ref ch 1)))
    (if (not (equal? cur new))
        (begin
          (dkv-vec! new)
          (prover!)
          (if (not (dk-asm? (list '= cur new)))
              (error "dk-vs-eq!: a step did not land" (expression->string (list '= cur new))))
          (if (not (equal? orig cur)) (dk-cite! 'eq-trans orig cur new))
          (vector-set! ch 1 new)))))
(define (dkv-sym! a b)                     ; (= a b) in context: land (= b a)
  (if (not (dk-asm? (list '= b a))) (dk-cite! 'eq-sym a b)))
;;; congruence: (= s s2) in context, TEMPLATE z -> the term with s replaced by z
(define (dkv-congr! s s2 template)
  (if (not (equal? s s2)) (dk-congr! (list '= s s2) template)))

;;; t -> canonical list; lands (= t (term L)) unless equal
(define (dkv-norm! t)
  (dkv-vec! t)
  (cond
   ((dkv-op? t 'VADD 3)
    (let* ((x (cadr t)) (y (caddr t))
           (Lx (dkv-norm! x)) (Ly (dkv-norm! y))
           (Cx (dkv-term Lx)) (Cy (dkv-term Ly))
           (ch (dkv-chain t)))
      (dkv-step! ch (dkv-add Cx y) (lambda () (dkv-congr! x Cx (lambda (z) (dkv-add z y)))))
      (dkv-step! ch (dkv-add Cx Cy) (lambda () (dkv-congr! y Cy (lambda (z) (dkv-add Cx z)))))
      (let ((M (dkv-merge! Lx Ly)))
        (dkv-step! ch (dkv-term M) (lambda () #t))
        M)))
   ((dkv-op? t 'ACT 3)
    (let* ((c (cadr t)) (x (caddr t))
           (Lx (dkv-norm! x)) (Cx (dkv-term Lx))
           (ch (dkv-chain t)))
      (dkv-step! ch (dkv-act c Cx) (lambda () (dkv-congr! x Cx (lambda (z) (dkv-act c z)))))
      (let ((S (dkv-scale! c Lx)))
        (dkv-step! ch (dkv-term S) (lambda () #t))
        S)))
   ((dkv-op? t 'VNEG 2)
    (let* ((x (cadr t))
           (inst (dk-cite! 'nvs-neg-one-act dkv-m x))       ; (= (act K x) (vneg x))
           (a (cadr inst))
           (ch (dkv-chain t)))
      (dkv-step! ch a (lambda () (dkv-sym! a t)))
      (let* ((La (dkv-norm! a)))
        (dkv-step! ch (dkv-term La) (lambda () #t))
        La)))
   (#t
    (let ((one (dkv-act 1 t)) (ch (dkv-chain t)))
      (dkv-step! ch one (lambda () (dk-cite! 'nvs-one-act dkv-m t) (dkv-sym! one t)))
      (list (cons 1 t))))))
;;; (= (vadd (term A) (term B)) (term M)) landed (unless equal); returns M
(define (dkv-merge! A B)
  (if (null? (cdr A))
      (dkv-insert! (car A) B)
      (let* ((t1 (dkv-act (caar A) (cdar A))) (Ap (cdr A))
             (CAp (dkv-term Ap)) (CB (dkv-term B))
             (cur0 (dkv-add (dkv-add t1 CAp) CB))
             (ch (dkv-chain cur0)))
        (dkv-step! ch (dkv-add t1 (dkv-add CAp CB))
                   (lambda () (dk-cite! 'nvs-vadd-assoc dkv-m t1 CAp CB)))
        (let* ((Mp (dkv-merge! Ap B)) (CMp (dkv-term Mp)))
          (dkv-step! ch (dkv-add t1 CMp)
                     (lambda () (dkv-congr! (dkv-add CAp CB) CMp (lambda (z) (dkv-add t1 z)))))
          (let ((M (dkv-insert! (car A) Mp)))
            (dkv-step! ch (dkv-term M) (lambda () #t))
            M)))))
;;; p = (a . v): (= (vadd a.v (term M)) (term result)) landed; returns the result
(define (dkv-insert! p M)
  (let* ((a (car p)) (v (cdr p)) (tp (dkv-act a v))
         (q (car M)) (b (car q)) (w (cdr q)) (tq (dkv-act b w))
         (kv (dkv-key v)) (kw (dkv-key w))
         (cur0 (dkv-add tp (dkv-term M)))
         (ch (dkv-chain cur0)))
    (cond
     ((string<? kv kw) (cons p M))
     ((string=? kv kw)
      (let ((ab (list '+ a b)))
        (dkv-rr! ab)
        (if (null? (cdr M))
            (begin
              (dkv-step! ch (dkv-act ab v) (lambda () (dk-cite! 'nvs-act-add-scalars dkv-m a b v)))
              (list (cons ab v)))
            (let ((CR (dkv-term (cdr M))))
              (dkv-step! ch (dkv-add (dkv-add tp tq) CR)
                         (lambda () (dk-cite! 'nvs-vadd-assoc dkv-m tp tq CR)
                                    (dkv-sym! (dkv-add (dkv-add tp tq) CR) cur0)))
              (dkv-step! ch (dkv-add (dkv-act ab v) CR)
                         (lambda () (dk-cite! 'nvs-act-add-scalars dkv-m a b v)
                                    (dkv-congr! (dkv-add tp tq) (dkv-act ab v) (lambda (z) (dkv-add z CR)))))
              (cons (cons ab v) (cdr M))))))
     (#t
      (if (null? (cdr M))
          (begin
            (dkv-step! ch (dkv-add tq tp) (lambda () (dk-cite! 'nvs-vadd-comm dkv-m tp tq)))
            (list q p))
          (let* ((R (cdr M)) (CR (dkv-term R)))
            (dkv-step! ch (dkv-add (dkv-add tp tq) CR)
                       (lambda () (dk-cite! 'nvs-vadd-assoc dkv-m tp tq CR)
                                  (dkv-sym! (dkv-add (dkv-add tp tq) CR) cur0)))
            (dkv-step! ch (dkv-add (dkv-add tq tp) CR)
                       (lambda () (dk-cite! 'nvs-vadd-comm dkv-m tp tq)
                                  (dkv-congr! (dkv-add tp tq) (dkv-add tq tp) (lambda (z) (dkv-add z CR)))))
            (dkv-step! ch (dkv-add tq (dkv-add tp CR))
                       (lambda () (dk-cite! 'nvs-vadd-assoc dkv-m tq tp CR)))
            (let* ((R2 (dkv-insert! p R)) (CR2 (dkv-term R2)))
              (dkv-step! ch (dkv-add tq CR2)
                         (lambda () (dkv-congr! (dkv-add tp CR) CR2 (lambda (z) (dkv-add tq z)))))
              (cons q R2))))))))
;;; (= (act c (term L)) (term S)) landed; returns S
(define (dkv-scale! c L)
  (dkv-rr! c)
  (let* ((a (caar L)) (v (cdar L)) (ca (list '* c a)))
    (dkv-rr! ca)
    (if (null? (cdr L))
        (let ((ch (dkv-chain (dkv-act c (dkv-act a v)))))
          (dkv-step! ch (dkv-act ca v) (lambda () (dk-cite! 'nvs-act-scale-assoc dkv-m c a v)))
          (list (cons ca v)))
        (let* ((t1 (dkv-act a v)) (R (cdr L)) (CR (dkv-term R))
               (ch (dkv-chain (dkv-act c (dkv-add t1 CR)))))
          (dkv-step! ch (dkv-add (dkv-act c t1) (dkv-act c CR))
                     (lambda () (dk-cite! 'nvs-act-distrib-vec-rr dkv-m c t1 CR)))
          (dkv-step! ch (dkv-add (dkv-act ca v) (dkv-act c CR))
                     (lambda () (dk-cite! 'nvs-act-scale-assoc dkv-m c a v)
                                (dkv-congr! (dkv-act c t1) (dkv-act ca v) (lambda (z) (dkv-add z (dkv-act c CR))))))
          (let* ((S (dkv-scale! c R)) (CS (dkv-term S)))
            (dkv-step! ch (dkv-add (dkv-act ca v) CS)
                       (lambda () (dkv-congr! (dkv-act c CR) CS (lambda (z) (dkv-add (dkv-act ca v) z)))))
            (cons (cons ca v) S))))))
;;; pad L (chain CH) with atom v at coefficient 0
(define (dkv-pad! ch L v)
  (let* ((C (dkv-term L)) (z (dkv-act 0 v)) (padded (dkv-add C z)))
    (dkv-rr! 0)
    (dkv-step! ch padded (lambda () (dk-cite! 'nvs-act-zero dkv-m v C) (dkv-sym! padded C)))
    (let ((M (dkv-merge! L (list (cons 0 v)))))
      (dkv-step! ch (dkv-term M) (lambda () #t))
      M)))
(define (dkv-find-m t)
  (cond ((not (pair? t)) #f)
        ((and (pair? (car t)) (memq (caar t) '(VADD ACT VNEG)) (pair? (cdar t))) (cadar t))
        (#t (let loop ((l t)) (cond ((null? l) #f) ((dkv-find-m (car l)) => (lambda (x) x)) (#t (loop (cdr l))))))))
(define (dk-vs-eq-chain!)
  (let* ((g (dk-goal))
         (ignore (if (not (and (pair? g) (eq? (car g) '=))) (error "dk-vs-eq!: the goal is not an equation" g)))
         (m (dkv-find-m g))
         (L (cadr g)) (R (caddr g)))
    (if (not m) (error "dk-vs-eq!: no VADD / ACT / VNEG in the goal" (expression->string g)))
    (if (not (dk-asm? (list 'IS-NORMED-VECTOR-SPACE m)))
        (error "dk-vs-eq!: IS-NORMED-VECTOR-SPACE not in context for" m))
    (set! dkv-m m)
    (let* ((chL (dkv-chain L)) (chR (dkv-chain R))
           (LL (dkv-norm! L)) (LR (dkv-norm! R)))
      (vector-set! chL 1 (dkv-term LL)) (vector-set! chR 1 (dkv-term LR))
      ;; pad the atoms missing on either side
      (for-each (lambda (q) (if (not (assoc-cdr (cdr q) LL)) (set! LL (dkv-pad! chL LL (cdr q))))) LR)
      (for-each (lambda (q) (if (not (assoc-cdr (cdr q) LR)) (set! LR (dkv-pad! chR LR (cdr q))))) LL)
      (if (not (equal? (map cdr LL) (map cdr LR)))
          (error "dk-vs-eq!: the atoms do not line up" (map cdr LL) (map cdr LR)))
      ;; the coefficients, one by one
      (let loop ((i 0) (cur LL))
        (if (< i (length cur))
            (let* ((a (car (list-ref cur i))) (b (car (list-ref LR i))))
              (if (equal? a b)
                  (loop (+ i 1) cur)
                  (let* ((eq (list '= a b))
                         (new (list-set-copy cur i (cons b (cdr (list-ref cur i))))))
                    (dkv-rr! a) (dkv-rr! b)
                    (dk-have! eq (lambda ()
                                   (let ((leaf (proof-state-focus *ps*)))
                                     (crs)
                                     (if (not (sequent-node-grounded? leaf))
                                         (error "dk-vs-eq!: the coefficients differ (crs refuses):" (expression->string eq))))))
                    (dkv-step! chL (dkv-term new)
                               (lambda () (dkv-congr! a b (lambda (z) (dkv-term (list-set-copy cur i (cons z (cdr (list-ref cur i))))))))) 
                    (loop (+ i 1) new))))))
      ;; L = C, R = C  ==>  L = R
      (let ((C (vector-ref chL 1)))
        (if (not (equal? C (vector-ref chR 1))) (error "dk-vs-eq!: the canonical forms differ" C (vector-ref chR 1)))
        (cond ((and (equal? L C) (equal? R C)) (rfl))
              ((equal? R C) #t)
              ((equal? L C) (dkv-sym! R C))
              (#t (dkv-sym! R C) (dk-cite! 'eq-trans L C R)))
        (if (not (sequent-node-grounded? (proof-state-focus *ps*)))
            (if (dk-asm? (dk-goal)) (ass)
                (error "dk-vs-eq!: the equation did not land" (expression->string g))))))))
(define (assoc-cdr v L) (find-first (lambda (q) (equal? (cdr q) v)) L))
(define (list-set-copy lst i x)
  (let loop ((l lst) (k 0)) (if (null? l) '() (cons (if (= k i) x (car l)) (loop (cdr l) (+ k 1))))))

;;; ---------------------------------------------------------------------------
;;; dk-vs-eq! v2 -- IN-PLACE REWRITING.  The chain version above (kept as dk-vs-eq-chain!)
;;; lands every intermediate equation and joins them by eq-trans / dk-congr!; this one rewrites
;;; the GOAL with `subst' of exact law instances, so congruence is free and a step is a citation
;;; and a rewrite.  A rewrite that also hits the same subterm elsewhere in the goal is sound
;;; and harmless: the sides are re-read from the goal after every step.
;; (the chain version is defined above under its own name, dk-vs-eq-chain!; integration fix 2026-10-27)
(define (dkw-atom? t) (not (or (dkv-op? t 'VADD 3) (dkv-op? t 'ACT 3) (dkv-op? t 'VNEG 2))))
;;; the first redex of the normalising rules in T, as a thunk that rewrites it; #f if none
(define (dkw-redex t)
  (cond
   ((not (pair? t)) #f)
   ((dkv-op? t 'VNEG 2)
    (or (dkw-redex (cadr t))
        (lambda ()
          (dkv-vec! t)
          (let* ((inst (dk-cite! 'nvs-neg-one-act dkv-m (cadr t))))
            (subst (list '= t (cadr inst)))))))
   ((dkv-op? t 'ACT 3)
    (let ((c (cadr t)) (x (caddr t)))
      (cond ((dkv-op? x 'VADD 3)
             (lambda () (dkv-vec! t)
                     (subst (dk-cite! 'nvs-act-distrib-vec-rr dkv-m c (cadr x) (caddr x)))))
            ((dkv-op? x 'ACT 3)
             (lambda () (dkv-vec! t) (dkv-rr! (list '* c (cadr x)))
                     (subst (dk-cite! 'nvs-act-scale-assoc dkv-m c (cadr x) (caddr x)))))
            (#t (dkw-redex x)))))
   ((dkv-op? t 'VADD 3)
    (let ((x (cadr t)) (y (caddr t)))
      (cond ((dkv-op? x 'VADD 3)
             (lambda () (dkv-vec! t)
                     (subst (dk-cite! 'nvs-vadd-assoc dkv-m (cadr x) (caddr x) y))))
            ((dkw-redex x) => (lambda (r) r))
            ((dkw-redex y) => (lambda (r) r))
            (#t (dkw-sort-redex t)))))
   (#t #f)))
;;; sorting / collecting on a right-nested sum of acts
(define (dkw-left-comm! p q r)      ; rewrite p + (q + r) to q + (p + r)
  (let* ((lhs (dkv-add p (dkv-add q r))) (rhs (dkv-add q (dkv-add p r))) (claim (list '= lhs rhs)))
    (dkv-vec! lhs) (dkv-vec! rhs) (dkv-vec! (dkv-add p q)) (dkv-vec! (dkv-add q p))
    (dk-have! claim
      (lambda ()
        (let ((leaf (proof-state-focus *ps*)))
          (dk-cite! 'nvs-vadd-assoc dkv-m p q r)
          (subst (list '= lhs (dkv-add (dkv-add p q) r)))
          (subst (dk-cite! 'nvs-vadd-comm dkv-m p q))
          (subst (dk-cite! 'nvs-vadd-assoc dkv-m q p r))
          (if (not (sequent-node-grounded? leaf)) (rfl)))))
    (subst claim)))
(define (dkw-sort-redex t)
  (let ((p (cadr t)) (s (caddr t)))
    (and (dkv-op? p 'ACT 3)
         (let* ((v (caddr p)) (kv (dkv-key v)))
           (cond
            ((dkv-op? s 'ACT 3)
             (let* ((w (caddr s)) (kw (dkv-key w)))
               (cond ((string>? kv kw)
                      (lambda () (dkv-vec! t) (subst (dk-cite! 'nvs-vadd-comm dkv-m p s))))
                     ((string=? kv kw)
                      (lambda () (dkv-vec! t) (dkv-rr! (list '+ (cadr p) (cadr s)))
                              (subst (dk-cite! 'nvs-act-add-scalars dkv-m (cadr p) (cadr s) v))))
                     (#t #f))))
            ((and (dkv-op? s 'VADD 3) (dkv-op? (cadr s) 'ACT 3))
             (let* ((q (cadr s)) (r (caddr s)) (w (caddr q)) (kw (dkv-key w)))
               (cond ((string>? kv kw) (lambda () (dkv-vec! t) (dkw-left-comm! p q r)))
                     ((string=? kv kw)
                      (lambda ()
                        (dkv-vec! t) (dkv-vec! (dkv-add p q))
                        (dk-cite! 'nvs-vadd-assoc dkv-m p q r)
                        (subst (list '= t (dkv-add (dkv-add p q) r)))
                        (dkv-rr! (list '+ (cadr p) (cadr q)))
                        (subst (dk-cite! 'nvs-act-add-scalars dkv-m (cadr p) (cadr q) v))))
                     (#t #f))))
            (#t #f))))))
(define (dkw-atoms t)
  (cond ((dkv-op? t 'VADD 3) (append (dkw-atoms (cadr t)) (dkw-atoms (caddr t))))
        ((dkv-op? t 'ACT 3) (dkw-atoms (caddr t)))
        ((dkv-op? t 'VNEG 2) (dkw-atoms (cadr t)))
        (#t (list t))))
(define (dkw-canon->list t)          ; canonical sum -> ((coef . atom) ...) or #f
  (cond ((and (dkv-op? t 'ACT 3) (dkw-atom? (caddr t))) (list (cons (cadr t) (caddr t))))
        ((and (dkv-op? t 'VADD 3) (dkv-op? (cadr t) 'ACT 3) (dkw-atom? (caddr (cadr t))))
         (let ((r (dkw-canon->list (caddr t)))) (and r (cons (cons (cadr (cadr t)) (caddr (cadr t))) r))))
        (#t #f)))
(define (dk-vs-eq!)
  (let* ((g (dk-goal))
         (m (and (pair? g) (eq? (car g) '=) (dkv-find-m g))))
    (if (not m) (error "dk-vs-eq!: the goal is not a vector equation" (expression->string g)))
    (if (not (dk-asm? (list 'IS-NORMED-VECTOR-SPACE m)))
        (error "dk-vs-eq!: IS-NORMED-VECTOR-SPACE not in context for" m))
    (set! dkv-m m)
    (dkv-vec! (cadr g)) (dkv-vec! (caddr g))
    ;; every atom becomes 1.atom (one global rewrite each; scale-assoc then folds 1.(c.v))
    (for-each
     (lambda (v)
       (if (or (dkw-bare-somewhere? (cadr (dk-goal)) v #t) (dkw-bare-somewhere? (caddr (dk-goal)) v #t))
           (let ((one (dkv-act 1 v)))
             (dkv-vec! one)
             (dk-cite! 'nvs-one-act dkv-m v)
             (subst (list '= v one)))))
     (delete-duplicates (append (dkw-atoms (cadr g)) (dkw-atoms (caddr g)))))
    ;; rewrite to the canonical forms
    (let loop ((n 0))
      (let* ((g2 (dk-goal))
             (r (or (dkw-redex (cadr g2)) (dkw-redex (caddr g2)))))
        (if r
            (if (> n 400) (error "dk-vs-eq!: no normal form after 400 rewrites")
                (begin (r) (loop (+ n 1)))))))
    ;; pad, align the coefficients, close
    (let* ((g3 (dk-goal)) (LL (dkw-canon->list (cadr g3))) (LR (dkw-canon->list (caddr g3))))
      (if (not (and LL LR)) (error "dk-vs-eq!: a side is not a canonical combination" (expression->string g3)))
      (for-each (lambda (q) (if (not (assoc-cdr (cdr q) LL)) (dkw-pad! #t (cdr q)))) LR)
      (for-each (lambda (q) (if (not (assoc-cdr (cdr q) LR)) (dkw-pad! #f (cdr q)))) LL)
      (let loop ((n 0))
        (let* ((g4 (dk-goal)) (r (or (dkw-redex (cadr g4)) (dkw-redex (caddr g4)))))
          (if r (begin (r) (loop (+ n 1))))))
      (let* ((g5 (dk-goal)) (LL (dkw-canon->list (cadr g5))) (LR (dkw-canon->list (caddr g5))))
        (if (not (equal? (map cdr LL) (map cdr LR)))
            (error "dk-vs-eq!: the atoms do not line up" (expression->string g5)))
        (for-each
         (lambda (pl pr)
           (let ((a (car pl)) (b (car pr)))
             (if (not (equal? a b))
                 (let ((eq (list '= a b)))
                   (dkv-rr! a) (dkv-rr! b)
                   (dk-have! eq (lambda ()
                                  (let ((leaf (proof-state-focus *ps*)))
                                    (crs)
                                    (if (not (sequent-node-grounded? leaf))
                                        (error "dk-vs-eq!: the coefficients differ (crs refuses):" (expression->string eq))))))
                   (subst eq)))))
         LL LR)
        (let ((g6 (dk-goal)) (leaf (proof-state-focus *ps*)))
          (if (not (equal? (cadr g6) (caddr g6)))
              (error "dk-vs-eq!: the sides differ after normalising" (expression->string g6)))
          (dkv-vec! (cadr g6))
          (rfl)
          (if (not (sequent-node-grounded? leaf)) (error "dk-vs-eq!: rfl did not close" (expression->string g6))))))))
(define (dkw-bare-somewhere? t v top?)       ; v occurs as a summand or as the whole side
  (cond ((equal? t v) top?)
        ((dkv-op? t 'VADD 3) (or (dkw-bare-somewhere? (cadr t) v #t) (dkw-bare-somewhere? (caddr t) v #t)))
        ((dkv-op? t 'ACT 3) (dkw-bare-somewhere? (caddr t) v #f))
        ((dkv-op? t 'VNEG 2) (dkw-bare-somewhere? (cadr t) v #t))
        (#t #f)))
(define (dkw-pad! left? v)                   ; side := side + 0.v
  (let* ((g (dk-goal)) (side (if left? (cadr g) (caddr g)))
         (z (dkv-act 0 v)) (padded (dkv-add side z)))
    (dkv-vec! padded)
    (dk-cite! 'nvs-act-zero dkv-m v side)                  ; (= (vadd side 0.v) side)
    (subst (list '= side padded))))

;;; ===========================================================================
;;; (2) dk-field-eq! -- FIELD SIMPLIFICATION BY A DENOMINATOR CERTIFICATE.
;;;
;;; Goal (= L R) over RR (default) or CC (pass 'CC), with recip and `/' (rewritten first by
;;; dk-undiv!).  Every (recip d) is a generator r with the relation d.r = 1.  Scheme computes,
;;; recip by recip (outermost first), the PSEUDO-DIVISION of E = L - R by d.r - 1 in r:
;;;      E . d^k  =  Q . (d.r - 1)  +  E'          (k = the degree of r in E; E' free of r)
;;; [E = sum_j c_j r^j gives E' = sum_j c_j d^(k-j) and Q = sum_j c_j d^(k-j) sum_(l<j) (d r)^l],
;;; until no recip is left; the last E' must be the ZERO polynomial (else ERROR: the identity is
;;; false).  The proof: each displayed identity is a commutative-ring identity with the recips
;;; opaque (dk-crs-opaque!); d.r = 1 (rr-/cc-recip-inverse) turns it into E.d^k = E'; from the
;;; last E' = 0 back up, E.d^k = 0 and d^k /= 0 give E = 0 (rr-no-zero-divisors /
;;; cc-mul-zero-left); L - R = 0 gives L = R.  A denominator not known nonzero is posted as an
;;; OWED leaf on the main branch (cut) and announced.  Every inference is a citation, a crs or
;;; an ineq: nothing new is trusted.
(define dkf-cls 'RR)
(define dkf-owed '())
(define (dkf-recips t)                     ; every (recip d) subterm, all depths
  (if (not (pair? t)) '()
      (let ((inner (apply append (map dkf-recips (cdr t)))))
        (if (and (eq? (car t) 'recip) (= (length t) 2)) (cons t inner) inner))))
(define (dkf-size t) (string-length (expression->string t)))
(define (dkf-owe! P)
  (if (not (dk-asm? P))
      (let ((g0 (dk-goal)) (home (proof-state-focus *ps*)))
        (cut P)
        (let ((main (find-first (lambda (l) (and (not (eq? l home))
                                                 (alpha-equiv? (dk-goal-of l) g0)
                                                 (any (lambda (a) (alpha-equiv? a P)) (dk-asms-of l))))
                                (dk-open-leaves))))
          (if (not main) (error "dk-field-eq!: cut left no main branch for" (expression->string P)))
          (dk-focus! main)
          (set! dkf-owed (cons P dkf-owed))
          (display ";; dk-field-eq!: OWED, left open for you: ") (display (expression->string P)) (newline)))))
;;; polynomial helpers over the comm-ring-simplify representation ((sorted-gens . coeff) ...)
(define (dkf-poly t)
  (let ((p (cvnb->poly t)))
    (if (not (list? p)) (error "dk-field-eq!: not a polynomial in its generators:" (expression->string t)))
    p))
(define (dkf-pow p k) (if (= k 0) (list (cons '() 1)) (cpoly-mul p (dkf-pow p (- k 1)))))
(define (dkf-deg-in p r)
  (fold-left max 0 (map (lambda (tm) (length (filter (lambda (g) (equal? g r)) (car tm)))) p)))
(define (dkf-coeff-of p r j)                ; the part of p of degree j in r, with r^j removed
  (cpoly-normalize
   (map (lambda (tm) (cons (filter (lambda (g) (not (equal? g r))) (car tm)) (cdr tm)))
        (filter (lambda (tm) (= j (length (filter (lambda (g) (equal? g r)) (car tm))))) p))))
(define (dkf-sum ps) (fold-left poly-add '() ps))
(define (dkf-mono->term gens)
  (cond ((null? gens) 1)
        ((null? (cdr gens)) (car gens))
        (#t (list '* (car gens) (dkf-mono->term (cdr gens))))))
(define (dkf-term->term c gens)
  (cond ((null? gens) c)
        ((= c 1) (dkf-mono->term gens))
        (#t (list '* c (dkf-mono->term gens)))))
(define (dkf-poly->term p)
  (let* ((pos (filter (lambda (tm) (> (cdr tm) 0)) p))
         (neg (filter (lambda (tm) (< (cdr tm) 0)) p))
         (pt (map (lambda (tm) (dkf-term->term (cdr tm) (car tm))) pos))
         (nt (map (lambda (tm) (dkf-term->term (- (cdr tm)) (car tm))) neg)))
    (cond ((and (null? pt) (null? nt)) 0)
          ((null? pt) (fold-left (lambda (acc x) (list '- acc x)) (list '- (car nt)) (cdr nt)))
          (#t (fold-left (lambda (acc x) (list '- acc x))
                         (fold-left (lambda (acc x) (list '+ acc x)) (car pt) (cdr pt))
                         nt)))))
(define (dkf-dpow d k) (if (= k 1) d (list '* d (dkf-dpow d (- k 1)))))
;;; the elimination: a list of steps (r d k Qpoly Epoly-next)
(define (dkf-eliminate E0)
  (let loop ((E E0) (steps '()))
    (let ((rs (sort (delete-duplicates
                     (filter (lambda (g) (and (pair? g) (eq? (car g) 'recip)))
                             (apply append (map car E))))
                    (lambda (a b) (> (dkf-size a) (dkf-size b))))))
      (if (null? rs)
          (values (reverse steps) E)
          (let* ((r (car rs)) (d (cadr r)) (Dp (dkf-poly d)) (k (dkf-deg-in E r))
                 (Dr (cpoly-mul Dp (list (cons (list r) 1))))
                 (cj (lambda (j) (dkf-coeff-of E r j)))
                 (Enext (dkf-sum (map (lambda (j) (cpoly-mul (cj j) (dkf-pow Dp (- k j)))) (iota (+ k 1)))))
                 (Q (dkf-sum (map (lambda (j)
                                    (cpoly-mul (cpoly-mul (cj j) (dkf-pow Dp (- k j)))
                                               (dkf-sum (map (lambda (l) (dkf-pow Dr l)) (iota j)))))
                                  (iota (+ k 1))))))
            (loop Enext (cons (list r d k Q Enext) steps)))))))
(define (dkf-type! t)
  (if (not (dk--num-type! t dkf-cls)) (error "dk-field-eq!: cannot type" (expression->string t))))
(define (dkf-nonzero-prod! d k)            ; (NOT (= d^k 0)) landed
  (let ((Dk (dkf-dpow d k)))
    (if (and (> k 1) (not (dk-asm? (list 'NOT (list '= Dk 0)))))
        (begin
          (dkf-nonzero-prod! d (- k 1))
          (let ((rest (dkf-dpow d (- k 1))))
            (dkf-type! Dk)
            (if (eq? dkf-cls 'CC)
                (dk-cite! 'cc-mul-nonzero d rest)
                (dk-have! (list 'NOT (list '= Dk 0))
                  (lambda ()
                    (di)
                    (let ((o (dk-cite! 'rr-no-zero-divisors d rest)))
                      (if (dk-only! o (list '= Dk 0) (list 'NOT (list '= d 0)) (list 'NOT (list '= rest 0))) (prop)))))))))))
;;; (NOT (= (f1 * (f2 * ...)) 0)) for the factor list FS (each a d^k)
(define (dkf-nonzero-all! fs ss)
  (for-each (lambda (s) (dkf-nonzero-prod! (list-ref s 1) (list-ref s 2))) ss)
  (let build ((fs fs))
    (if (pair? (cdr fs))
        (let* ((rest (fold-right (lambda (f acc) (if (equal? acc 1) f (list '* f acc))) 1 (cdr fs)))
               (whole (list '* (car fs) rest)))
          (build (cdr fs))
          (dkf-type! (car fs)) (dkf-type! rest) (dkf-type! whole)
          (if (not (dk-asm? (list 'NOT (list '= whole 0))))
              (if (eq? dkf-cls 'CC)
                  (dk-cite! 'cc-mul-nonzero (car fs) rest)
                  (dk-have! (list 'NOT (list '= whole 0))
                    (lambda ()
                      (di)
                      (let ((o (dk-cite! 'rr-no-zero-divisors (car fs) rest)))
                        (if (dk-only! o (list '= whole 0) (list 'NOT (list '= (car fs) 0)) (list 'NOT (list '= rest 0))) (prop)))))))))))
(define (dkf-zero-factor! E Dk)            ; (= (* E Dk) 0), Dk /= 0 in context: land (= E 0)
  (if (eq? dkf-cls 'CC)
      (dk-cite! 'cc-mul-zero-left E Dk)
      (dk-have! (list '= E 0)
        (lambda ()
          (let ((o (dk-cite! 'rr-no-zero-divisors E Dk)))
            (if (dk-only! o (list '= (list '* E Dk) 0) (list 'NOT (list '= Dk 0))) (prop)))))))
;;; crs with EVERY recip subterm generalised (outermost first), proved on a lane and
;;; instantiated back: dk-crs-opaque! leaves a recip whose argument held another recip.
(define (dkf-replace t from to)
  (cond ((equal? t from) to)
        ((pair? t) (map (lambda (x) (dkf-replace x from to)) t))
        (#t t)))
(define (dkf-crs! eqn)
  (let* ((rs (sort (delete-duplicates (dkf-recips eqn)) (lambda (a b) (> (dkf-size a) (dkf-size b)))))
         (pool '(dkfa_ dkfb_ dkfc_ dkfd_ dkfe_ dkff_ dkfg_ dkfh_ dkfi_ dkfj_ dkfk_ dkfl_))
         (vs (let loop ((n (length rs)) (p pool) (acc '()))
               (if (= n 0) (reverse acc)
                   (if (null? p) (error "dk-field-eq!: too many recips to generalise" n)
                       (loop (- n 1) (cdr p) (cons (car p) acc))))))
         (gen (fold-left (lambda (acc pr) (dkf-replace acc (car pr) (cdr pr))) eqn (map cons rs vs)))
         (claim (fold-right (lambda (v acc) (list 'FORALL v (list 'IMPLIES (list 'IN v dkf-cls) acc))) gen vs)))
    (if (null? rs)
        (dk-have! eqn (lambda () (let ((leaf (proof-state-focus *ps*))) (crs)
                                   (if (not (sequent-node-grounded? leaf)) (error "dk-field-eq!: crs refused" (expression->string eqn))))))
        (begin
          (for-each dkf-type! rs)
          (dk-have! claim (lambda () (let ((leaf (proof-state-focus *ps*))) (dk-peel!) (crs)
                                       (if (not (sequent-node-grounded? leaf)) (error "dk-field-eq!: crs refused" (expression->string gen))))))
          (apply dk-apply! claim rs)
          (if (not (dk-asm? eqn)) (error "dk-field-eq!: the instance did not land" (expression->string eqn)))
          (if (eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) eqn)))) (ass))))))
(define (dk-field-eq! . opt)
  (set! dkf-cls (if (pair? opt) (car opt) 'RR))
  (set! dkf-owed '())
  (if (dk-contains? (dk-goal) '/) (dk-undiv! dkf-cls))
  (let* ((g (dk-goal))
         (ignore (if (not (and (pair? g) (eq? (car g) '=))) (error "dk-field-eq!: the goal is not an equation" g)))
         (L (cadr g)) (R (caddr g))
         (home (proof-state-focus *ps*)))
    ;; denominators: typed, nonzero (owed if not in context), and d.r = 1
    (for-each (lambda (r)
                (let ((d (cadr r)))
                  (dkf-type! d)
                  (dkf-owe! (list 'NOT (list '= d 0)))))
              (sort (delete-duplicates (dkf-recips g)) (lambda (a b) (< (dkf-size a) (dkf-size b)))))
    (dkf-type! L) (dkf-type! R)
    (let ((E1 (list '- L R)))
      (dkf-type! E1)
      (call-with-values (lambda () (dkf-eliminate (dkf-poly E1)))
        (lambda (steps Efinal)
          (if (not (null? Efinal))
              (error "dk-field-eq!: not an identity -- after clearing denominators the remainder is"
                     (expression->string (dkf-poly->term Efinal))))
          ;; ONE certificate: E1 * PI = sum_i Q'_i (d_i r_i - 1),  PI = prod_i d_i^k_i,
          ;; Q'_i = Q_i * prod_(j>i) d_j^k_j  (E_(n+1) = 0)
          (let* ((ss (filter (lambda (s) (> (list-ref s 2) 0)) steps))
                 (facs (map (lambda (s) (dkf-dpow (list-ref s 1) (list-ref s 2))) ss))
                 (PI (if (null? facs) 1 (fold-right (lambda (f acc) (if (equal? acc 1) f (list '* f acc))) 1 facs)))
                 (later (lambda (idx) (fold-left cpoly-mul (list (cons '() 1))
                                                 (map (lambda (s) (dkf-pow (dkf-poly (list-ref s 1)) (list-ref s 2)))
                                                      (list-tail ss (+ idx 1))))))
                 (zs (map (lambda (s) (list '- (list '* (list-ref s 1) (list-ref s 0)) 1)) ss))
                 (qs (let loop ((k 0) (l ss) (acc '()))
                       (if (null? l) (reverse acc)
                           (loop (+ k 1) (cdr l) (cons (dkf-poly->term (cpoly-mul (list-ref (car l) 3) (later k))) acc)))))
                 (rhs (if (null? ss) 0
                          (fold-right (lambda (q z acc) (if (equal? acc 0) (list '* q z) (list '+ (list '* q z) acc))) 0 qs zs)))
                 (lhs (if (equal? PI 1) E1 (list '* E1 PI))))
            (for-each (lambda (s)
                        (let ((d (list-ref s 1)) (r (list-ref s 0)))
                          (if (not (dk-asm? (list '= (list '* d r) 1)))
                              (begin (dk-have! (list 'AND (list 'IN d dkf-cls) (list 'NOT (list '= d 0))))
                                     (fact (if (eq? dkf-cls 'CC) 'cc-recip-inverse 'rr-recip-inverse) d)))))
                      ss)
            (if (null? ss)
                (dkf-crs! (list '= E1 0))
                (let ((C (list '= lhs rhs)))
                  (dkf-crs! C)
                  (dk-have! (list '= lhs 0)
                    (lambda ()
                      (subst C)
                      (for-each (lambda (s) (subst (list '= (list '* (list-ref s 1) (list-ref s 0)) 1))) ss)
                      (dkf-crs! (dk-goal))))
                  ;; PI /= 0, then E1 = 0
                  (dkf-type! PI)
                  (dkf-nonzero-all! facs ss)
                  (dkf-zero-factor! E1 PI))))
          ;; L - R = 0  ==>  L = R
          (if (eq? dkf-cls 'CC)
              (dk-cite! 'cc-sub-zero-eq L R)
              (dk-ineq! (list '= E1 0)))
          (if (not (sequent-node-grounded? (proof-state-focus *ps*)))
              (if (dk-asm? (dk-goal)) (ass)))
          (if (pair? dkf-owed)
              (begin (display ";; dk-field-eq!: ") (display (length dkf-owed)) (display " owed side condition(s)") (newline)))
          dkf-owed)))))

;;; =======================================================================
;;; KIT-8 (2026-10-26; wired 2026-10-27, batch 0): scratchpad/kitlem/kit8.scm, verbatim.  The local
;;; copies each helper retires: scratchpad/triage/KIT-8-REPORT.md.
;;; =======================================================================
;;; kit8.scm -- PROPOSED DRIVER-KIT ADDITION (KIT-8): the generic helpers that today's proof agents copied
;;; into their files under local prefixes.  Agent KIT-8, 2026-10-26.  To adopt: append to driver-kit.scm.
;;; Until then a probe loads this file INTO *driver-kit-env* (as sb3-helpers.scm is loaded).
;;; Every helper drives surface tactics only; a helper that cannot do its job ERRORS (no silent #f).
;;; The local copies each helper would retire are listed in scratchpad/triage/KIT-8-REPORT.md; the
;;; suite checks (one or more per helper) are scratchpad/kitlem/kit8-check.scm.
;;;
;;; FORMULA BUILDERS
;;;   (dk-and FS)                    right-nested AND of the list FS (one element: itself)
;;;   (dk-curry FS BODY)             FS1 => (FS2 => ... BODY)
;;;   (dk-foralls VS BODY)           FORALL v1 ... FORALL vn BODY
;;; CONTEXT
;;;   (dk-have-and! . FS)            land (AND F1 ... Fn) from its conjuncts in context; return it (idempotent)
;;;   (dk-or-each! OR HANDLER)       split a right-nested OR in context; HANDLER runs on each disjunct's leaf
;;;   (dk-iff-fwd! IFF) (dk-iff-bwd! IFF)   IFF in context, its left (right) side in context: land the other
;;;   (dk-iff-parts! IFF)            IFF in context, its left side in context: land every conjunct of the
;;;                                  right side, the one equal to the focus goal LAST (focus-drift safe)
;;;   (dk-project-safe! CLAIM OPENER) dk-project!, but CLAIM may be the focus goal (then proved in place)
;;;   (dk-fact-split! THM . ARGS)    cite; split a conjunction that landed; return the citation
;;;   (dk-chain-ass! CH)             walk an implication chain: detach antecedents in context, prove the
;;;                                  others (conjunctions of context formulas) by detach-with!; return the end
;;;   (dk-nn-absurd! . PREMS)        contradictory NN premises close the focus goal (FALSITY or anything)
;;; GOAL CLOSERS
;;;   (dk-subst-ass! E) (dk-subst-rfl! E)   rewrite the goal by E, then ass / rfl; ERROR if that fails
;;;   (dk-and-close! CLOSER)         split AND goals recursively, CLOSER on each atom
;;;   (dk-close-if-asm!)             `ass' when the focus goal is in context (no warning otherwise)
;;;   (dk-select! J N)               pick the J-th of N right-nested disjuncts of the goal
;;;   (dk-index-cases! X N BODY)     X in NN, 1 <= X <= N (numeral): BODY on each j with X = j in context
;;; LOOKUP
;;;   (dk-find TAG PRED LST)         find-first that ERRORS with TAG on a miss
;;;   (dk-map-ordered F L)           map with left-to-right evaluation (recording calls in order)
;;;   (dk-eq-for LHS)                the context equation LHS = (literal right side), or #f
;;;   (dk-nth-all!)                  reduce the NTHs of literal lists in every context equation
;;; SETS
;;;   (dk-class-ext! LHS RHS FWD BWD) LHS = RHS by class extensionality; FWD/BWD prove the two membership
;;;                                  directions for the fresh point w
;;;   (dk-bu-open! W BU)             W in a BIG-UNION over NN in context: return (k . the membership landed)
;;;   (dk-bu-close! K)               the goal W in a BIG-UNION: witness index K, close the leaves by ass
;;;   (dk-sep-parts! M)              M = (IN w (SEP v D p)) in context: land w in D and p[v:=w], keep M
;;; NUMBERS
;;;   (dk-ne! A B LT)                (NOT (= A B)) from the strict inequality LT in context
;;;   (dk-recip-succ! K)             K in NN: recip(K + 1) typed in RR and POS-RR (idempotent); return it
;;;   (dk-rr-mul! P Q)               P, Q in RR in context: land (IN (* P Q) RR)
;;;   (dk-ni-leaves)                 run `ni'; return (BASE STEP), the step being the leaf with succ

;;; ---- formula builders ----
(define (dk-and fs) (if (null? (cdr fs)) (car fs) (list 'AND (car fs) (dk-and (cdr fs)))))
(define (dk-curry fs body) (fold-right (lambda (p acc) (list 'IMPLIES p acc)) body fs))
(define (dk-foralls vs body) (fold-right (lambda (v acc) (list 'FORALL v acc)) body vs))

;;; ---- context ----
(define (dk-have-and! . fs)
  (let ((c (dk-and fs)))
    (if (not (dk-asm? c)) (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!))))))
    c))

(define (dk-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
      (dk-each-leaf! (lambda () (ai o))
        (lambda ()
          (cond ((dk-asm? (cadr o)) (handler (cadr o)))
                ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (dk-or-each! (caddr o) handler))
                (#t (handler (caddr o))))))))

(define (dk-iff-fwd! iff) (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!))
(define (dk-iff-bwd! iff) (ai iff) (detach! (list 'IMPLIES (caddr iff) (cadr iff))) (dk-split-all!))

(define (dk-project-safe! claim opener)
  (if (eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) claim))))
      (let ((leaf (proof-state-focus *ps*)))
        (opener)
        (if (not (sequent-node-grounded? leaf)) (vnb-guard (lambda () (dk-split-all!))))
        (if (not (sequent-node-grounded? leaf)) (ass))
        claim)
      (dk-project! claim opener)))

(define (dk-iff-parts! iff)
  (let* ((rhs (caddr iff))
         (cs (let loop ((r rhs) (acc '()))
               (if (and (pair? r) (eq? (car r) 'AND))
                   (loop (caddr r) (cons (cadr r) acc))
                   (reverse (cons r acc)))))
         (goal? (lambda (c) (eq? #t (vnb-guard (lambda () (alpha-equiv? (dk-goal) c))))))
         (opener (lambda () (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!)))
         (rest (filter (lambda (c) (not (goal? c))) cs))
         (last (filter goal? cs)))
    (append (dk-map-ordered (lambda (c) (dk-project-safe! c opener)) rest)
            (dk-map-ordered (lambda (c) (dk-project-safe! c opener)) last))))

(define (dk-fact-split! thm . args)
  (let ((f (apply dk-cite! thm args)))
    (if (and (pair? f) (eq? (car f) 'AND)) (dk-split-all!))
    f))

(define (dk-chain-ass! ch)
  (let loop ((c ch))
    (cond ((not (dk-head-is? c 'IMPLIES)) c)
          ((dk-asm? (cadr c))
           (let ((new (dk-landed* (lambda () (detach! c)))))
             (loop (if (pair? new) (car new) (caddr c)))))
          (#t (loop (detach-with! c (lambda () (dk-conj-close! (lambda () (ass))))))))))

(define (dk-nn-absurd! . prems)
  (dk-have! '(< 0 0) (lambda () (apply dk-nn! prems)))
  (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
  (ai (dk-cite! 'rr-lt-irrefl 0)))

;;; ---- goal closers ----
(define (dk-subst-ass! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (if (not (dk-ass!)) (error "dk-subst-ass!: the rewritten goal is not in context" (dk-goal))))))

(define (dk-subst-rfl! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (let ((g (dk-goal)))
          (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
              (rfl)
              (error "dk-subst-rfl!: not reflexive after the rewrite" g))))))

(define (dk-and-close! closer)
  (if (dk-head-is? (dk-goal) 'AND)
      (for-each (lambda (k) (dk-focus! k) (dk-and-close! closer)) (dk-opened (lambda () (di))))
      (closer)))

(define (dk-close-if-asm!) (if (and (pair? (dk-open-leaves)) (dk-asm? (dk-goal))) (ass)))

(define (dk-select! j n)
  (cond ((= n 1) #t)
        ((= j 1) (oi-l))
        (#t (oi-r) (dk-select! (- j 1) (- n 1)))))

(define (dk-index-cases! x n body)
  (let loop ((j 1))
    (if (= j n)
        (begin
          (dk-have! (list '= x n) (lambda () (dk-nn! (list '<= n x) (list '<= x n))))
          (body n))
        (use-em (list '= x j)
          (lambda () (body j))
          (lambda ()
            (dk-have! (list 'IN j 'NN) (lambda () (arith)))
            (dk-cite! 'nn-le-ne-succ j x)
            (dk-have! (list '<= (+ j 1) x) (lambda () (dk-nn! (list '<= (list 'succ j) x))))
            (loop (+ j 1)))))))

;;; ---- lookup ----
(define (dk-find tag pred lst)
  (or (find-first pred lst) (error "dk-find: nothing matches at" tag (map expression->string lst))))
(define (dk-map-ordered f l)
  (let loop ((l l) (acc '())) (if (null? l) (reverse acc) (loop (cdr l) (cons (f (car l)) acc)))))
(define (dk-eq-for lhs)
  (find-first (lambda (f) (and (pair? f) (memq (car f) '(= ==)) (equal? (cadr f) lhs)
                               (equal? (reduce-nth-in-expr (caddr f)) (caddr f))))
              (dk-asms)))
(define (dk-nth-all!)
  (for-each (lambda (f) (if (and (pair? f) (memq (car f) '(= ==)) (dk-contains? f 'NTH)) (dk-nth-h! f)))
            (dk-asms)))

;;; ---- sets ----
(define (dk-class-ext! lhs rhs fwd bwd)
  (dk-have! (list 'FORALL 'w_ (list 'IFF (list 'IN 'w_ lhs) (list 'IN 'w_ rhs)))
    (lambda ()
      (let ((wv (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (dk-iff! (lambda (g) (equal? g (list 'IN wv rhs)))
          (lambda () (fwd wv))
          (lambda () (bwd wv))))))
  (fact 'class-extensionality lhs rhs))

(define (dk-bu-open! w bu)
  (let* ((landed (dk-landed (lambda () (bu-me (list 'IN w bu)))))
         (ein (find-first (lambda (f) (and (dk-head-is? f 'IN) (eq? (caddr f) 'NN))) landed))
         (app (find-first (lambda (f) (not (eq? f ein))) landed)))
    (if (not ein) (error "dk-bu-open!: no index landed" landed))
    (cons (cadr ein) app)))
(define (dk-bu-close! k)
  (for-each (lambda (n) (if (not (sequent-node-grounded? n)) (begin (dk-focus! n) (ass))))
            (dk-opened (lambda () (bu-mi k)))))

(define (dk-sep-parts! m0)
  (let* ((m (->raw-formula m0))
         (w (cadr m)) (s0 (caddr m)) (v (cadr s0)) (dom (caddr s0))
         (d (list 'IN w dom))
         (p (subst-free v w (cadddr s0)))
         (conj (list 'AND d p)))
    (if (not (dk-asm? m)) (error "dk-sep-parts!: not in context" (expression->string m)))
    (if (not (and (dk-asm? d) (dk-asm? p)))
        (begin
          (if (not (dk-asm? conj))
              (dk-have! conj (lambda () (sep-me (dk-ctx-form m)) (vnb-guard (lambda () (dk-split-all!)))
                                        (dk-conj-close! dk-ass!))))
          (ai (dk-ctx-form conj))))
    p))

;;; ---- numbers ----
(define (dk-ne! a b lt)
  (dk-have! (list 'NOT (list '= a b))
    (lambda ()
      (di)
      (dk-have! '(< 0 0) (lambda () (dk-ineq! lt (list '= a b))))
      (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
      (ai (dk-cite! 'rr-lt-irrefl 0)))))

(define (dk-recip-succ! k)
  (let* ((k1 (list '+ k 1)) (rq (list 'RECIP k1)))
    (if (dk-asm? (list 'POS-RR rq))
        rq
        (begin
          (dk-cite! 'nn-in-rr k) (dk-type! k1 'RR)
          (dk-have! (list '< 0 k1) (lambda () (dk-cite! 'nn-zero-le k) (dk-ineq! (list '<= 0 k))))
          (dk-ne! k1 0 (list '< 0 k1))
          (dk-chain-ass! (dk-fact! 'rr-recip-closed k1))
          (dk-cite! 'rr-recip-pos k1)
          (dk-cite! 'rr-pos-rr-of-lt rq)
          rq))))

(define (dk-rr-mul! p q)
  (dk-have-and! (list 'IN p 'RR) (list 'IN q 'RR))
  (dk-cite! 'rr-mul-closed p q))

(define (dk-ni-leaves)
  (let ((leaves (dk-opened (lambda () (ni)))))
    (list (dk-find "dk-ni-leaves base" (lambda (l) (not (dk-contains? (dk-goal-of l) 'succ))) leaves)
          (dk-find "dk-ni-leaves step" (lambda (l) (dk-contains? (dk-goal-of l) 'succ)) leaves))))

;;; ==================================================================================================
;;; SB-3 (2026-10-26), wired 2026-10-27: the dks- strand-space kit, scratchpad/sb3/sb3-helpers.scm, appended
;;; verbatim below.  Used by theorem-library/otway-rees-laws.scm and or-missing-guarantee.scm.
;;; ==================================================================================================

;;; sb3-helpers.scm -- PROPOSED DRIVER-KIT ADDITION: strand-space trace reading and literal messages.
;;; Agent SB-3, wave MAP-1026, 2026-10-26.  These are the helpers nsl.scm (S-3), SB-2's honesty and instance
;;; files and SB-3's Otway-Rees file each needed; SB-2 had copied them three times.  Written here ONCE, over
;;; a CURRENT SPACE set by (dks-use! SPACE-TERM), so they no longer hard-wire nsp / isp.  To adopt: append to
;;; driver-kit.scm (prefix dks- = "driver kit, strands"); until then a probe loads this file INTO
;;; *driver-kit-env* (not a child environment), so every later file sees it as if it were the kit.
;;; Every helper drives surface tactics only and errors rather than returning #f on a miss.
;;;
;;;   (dks-use! SP)                 set the current strand space term; dks-sp, dks-T, dks-K, dks-A
;;;   (dks-or-each! OR HANDLER)     split a right-nested OR in context; HANDLER gets each disjunct
;;;   (dks-project! PRED HYP CLAIM) land CLAIM, a projection of the predicate HYP, keeping HYP
;;;   (dks-fact-split! THM . ARGS)  cite, split a conjunction that landed
;;;   (dks-subst-ass! E) (dks-subst-rfl! E) (dks-eq-for LHS) (dks-nth-all!)
;;;   (dks-index-cases! X N BODY)   X in NN, 1 <= X <= N (numeral): BODY on each j with X = j in context
;;;   (dks-select! J N)             select the J-th of N right-nested disjuncts of the goal
;;;   (dks-nn-absurd! . PREMS)      contradictory NN premises close the goal
;;;   (dks-set! T)                  (IN T SET) from a typing, through LST / ENCR
;;;   (dks-msg! M)                  a literal message typed in A (dk-stl--msg!)
;;;   (dks-sub-fwd! A M)            land A @ M for a literal M in which A occurs
;;;   (dks-sub-cases! W M)          W @ M in context, M a literal: land and return the OR over M's subterm
;;;                                 atoms (W = each LST / ENCR sub-literal, W = each token leaf, W @ each
;;;                                 message-variable leaf)
;;;   (dks-lit-neq! A B)            (= A B) in context, A, B literal and known to differ: close the goal
;;;   (dks-sg N) (dks-lit-facts! M LIT) (dks-entry! N K D M) (dks-earlier! J M . PREMS) (dks-num-index! J M)
;;;   (dks-recv-absurd! N)          the node-level readers of nsl.scm, over the current space
;;;   (dks-lit-node-cases! N LIT H) N a node of a strand whose trace is the literal LIT (any length):
;;;                                 H gets each index j with N's reduced content and direction in context
;;;   (dks-trace-witnesses! D COUNT) skolemise a predicate's existentials in order

(define dks-sp #f) (define dks-T #f) (define dks-K #f) (define dks-A #f)
(define (dks-use! sp)
  (set! dks-sp sp)
  (set! dks-T `(TOKENS ,sp))
  (set! dks-K `(KEYS ,sp))
  (set! dks-A `(MSG-SET (TOKENS ,sp) (KEYS ,sp))))

(define (dks-and fs) (if (null? (cdr fs)) (car fs) `(AND ,(car fs) ,(dks-and (cdr fs)))))
(define (dks-curry fs body) (fold-right (lambda (p acc) `(IMPLIES ,p ,acc)) body fs))
(define (dks-foralls vs body) (fold-right (lambda (v acc) `(FORALL ,v ,acc)) body vs))

(define (dks-have-and! . fs)
  (let ((c (dks-and fs)))
    (dk-have! c (lambda () (dk-conj-close! (lambda () (dk-ass!)))))
    c))

(define (dks-or-each! o handler)
  (if (not (dk-head-is? o 'OR))
      (handler o)
      (dk-each-leaf! (lambda () (ai o))
        (lambda ()
          (cond ((dk-asm? (cadr o)) (handler (cadr o)))
                ((and (pair? (caddr o)) (eq? (car (caddr o)) 'OR)) (dks-or-each! (caddr o) handler))
                (#t (handler (caddr o))))))))

(define (dks-project! pred hyp claim)
  (dk-have! claim
    (lambda ()
      (mac-h pred hyp)
      (if (not (dk-ass!))
          (begin
            (dk-split-all!)
            (dk-conj-close! (lambda () (if (not (dk-ass!)) (error "dks-project!: not a projection" claim))))))))
  claim)

(define (dks-fact-split! thm . args)
  (let ((f (apply dk-cite! thm args)))
    (if (and (pair? f) (eq? (car f) 'AND)) (dk-split-all!))
    f))

(define (dks-subst-ass! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (if (not (dk-ass!)) (error "dks-subst-ass!: the rewritten goal is not in context" (dk-goal))))))

(define (dks-subst-rfl! e)
  (let ((leaf (proof-state-focus *ps*)))
    (subst e)
    (if (not (sequent-node-grounded? leaf))
        (let ((g (dk-goal)))
          (if (and (pair? g) (memq (car g) '(= ==)) (equal? (cadr g) (caddr g)))
              (rfl)
              (error "dks-subst-rfl!: not reflexive after the rewrite" g))))))

(define (dks-eq-for lhs)
  (find-first (lambda (f) (and (pair? f) (memq (car f) '(= ==)) (equal? (cadr f) lhs)
                               (equal? (reduce-nth-in-expr (caddr f)) (caddr f))))
              (dk-asms)))

(define (dks-nth-all!)
  (for-each (lambda (f) (if (and (pair? f) (memq (car f) '(= ==)) (dk-contains? f 'NTH)) (dk-nth-h! f)))
            (dk-asms)))

(define (dks-index-cases! x n body)
  (let loop ((j 1))
    (if (= j n)
        (begin
          (dk-have! `(= ,x ,n) (lambda () (dk-nn! `(<= ,n ,x) `(<= ,x ,n))))
          (body n))
        (use-em `(= ,x ,j)
          (lambda () (body j))
          (lambda ()
            (dk-have! `(IN ,j NN) (lambda () (arith)))
            (dk-cite! 'nn-le-ne-succ j x)
            (dk-have! `(<= ,(+ j 1) ,x) (lambda () (dk-nn! `(<= (succ ,j) ,x))))
            (loop (+ j 1)))))))

(define (dks-select! j n)
  (cond ((= n 1) #t)
        ((= j 1) (oi-l))
        (#t (oi-r) (dks-select! (- j 1) (- n 1)))))

(define (dks-nn-absurd! . prems)
  (dk-have! '(< 0 0) (lambda () (apply dk-nn! prems)))
  (if (not (dk-asm? '(IN 0 RR))) (fact 'rr-zero-in))
  (ai (dk-cite! 'rr-lt-irrefl 0)))

(define (dks-set! t)
  (let ((goal `(IN ,t SET)))
    (cond ((dk-asm? goal) goal)
          ((find-first (lambda (f) (and (dk-head-is? f 'IN) (equal? (cadr f) t) (not (eq? (caddr f) 'SET)))) (dk-asms))
           => (lambda (ty) (fact 'membership-implies-sethood t (caddr ty)) goal))
          ((dk-head-is? t 'LST)
           (dks-set! (cadr t))
           (fact 'lst-in-tuples-set (cadr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          ((dk-head-is? t 'ENCR)
           (dks-set! (cadr t)) (dks-set! (caddr t))
           (fact 'encr-in-tuples-set (cadr t) (caddr t))
           (fact 'membership-implies-sethood t '(TUPLES SET))
           goal)
          (#t (error "dks-set!: no typing for" t)))))

(define (dks-msg! m) (dk-stl--msg! dks-T dks-K m))

;; a leaf of a literal message: a token (typed in T) or a message variable (typed in A)
(define (dks-token? x) (dk-asm? `(IN ,x ,dks-T)))

(define (dks-occurs? a m)
  (cond ((equal? a m) #t)
        ((dk-stl--encr? m) (dks-occurs? a (cadr m)))
        ((dk-stl--lst? m) (any-pred (lambda (mi) (dks-occurs? a mi)) (cdr (cadr m))))
        (#t #f)))

(define (dks-sub-fwd! a m)
  (let ((goal `(IS-SUBTERM ,dks-T ,dks-K ,a ,m)))
    (cond ((dk-asm? goal) goal)
          ((equal? a m)
           (dks-msg! m)
           (dk-cite! 'subterm-refl dks-T dks-K m)
           goal)
          ((dk-stl--encr? m)
           (dks-sub-fwd! a (cadr m))
           (dks-msg! (cadr m))
           (dk-cite! 'subterm-encr dks-T dks-K a (cadr m) (caddr m))
           goal)
          ((dk-stl--lst? m)
           (let* ((l (cadr m)) (ms (cdr l))
                  (i (let loop ((ms ms) (i 1))
                       (cond ((null? ms) (error "dks-sub-fwd!: does not occur" a m))
                             ((dks-occurs? a (car ms)) i)
                             (#t (loop (cdr ms) (+ i 1))))))
                  (mi (list-ref ms (- i 1))))
             (dks-sub-fwd! a mi)
             (dk-stl--tuples! dks-T dks-K l)
             (dk-have! `(IS-SUBTERM ,dks-T ,dks-K ,a (NTH ,i ,l)) (lambda () (nth-r) (dk-ass!)))
             (dk-have! `(IN ,i NN) (lambda () (arith)))
             (dk-have! `(<= 1 ,i) (lambda () (dk-nn!)))
             (dk-have! `(<= ,i (LENGTH ,l)) (lambda () (len-r) (arith)))
             (dk-cite! 'subterm-component dks-T dks-K a l i)
             goal))
          (#t (error "dks-sub-fwd!: not a literal message" m)))))

;;; ---- the subterm inverter for any W ----

(define (dks-sub-atoms w m)
  (let ((self `(= ,w ,m)))
    (cond ((dk-stl--encr? m) (cons self (dks-sub-atoms w (cadr m))))
          ((dk-stl--lst? m) (cons self (append-map (lambda (mi) (dks-sub-atoms w mi)) (cdr (cadr m)))))
          ((dks-token? m) (list self))
          (#t (list `(IS-SUBTERM ,dks-T ,dks-K ,w ,m))))))

(define (dks-dedup xs)
  (let loop ((xs xs) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((member (car xs) acc) (loop (cdr xs) acc))
          (#t (loop (cdr xs) (cons (car xs) acc))))))

;; the goal an OR over ATOMS (right-nested), the disjunct D in context: select it and close
(define (dks-select-atom! d atoms)
  (let loop ((as atoms))
    (cond ((null? as) (error "dks-sub-cases!: not among the atoms" d))
          ((equal? (car as) d) (if (pair? (cdr as)) (oi-l)) (dk-ass!))
          (#t (oi-r) (loop (cdr as))))))

(define (dks-sub-drive! w m atoms)
  (cond
    ((dk-stl--encr? m)
     (let ((g (cadr m)) (y (caddr m)))
       (dks-msg! g)
       (dks-or-each! (dk-cite! 'subterm-of-encr dks-T dks-K w g y)
         (lambda (e)
           (if (dk-head-is? e '=)
               (dks-select-atom! `(= ,w ,m) atoms)
               (dks-sub-drive! w g atoms))))))
    ((dk-stl--lst? m)
     (let* ((l (cadr m)) (ms (cdr l)) (n (length ms)))
       (dk-stl--tuples! dks-T dks-K l)
       (dks-or-each! (dk-cite! 'subterm-of-list dks-T dks-K w l)
         (lambda (e)
           (if (dk-head-is? e '=)
               (dks-select-atom! `(= ,w ,m) atoms)
               (let* ((i (dk-skolem! e #t))
                      (len `(LENGTH ,l)))
                 (dk-have! `(= ,len ,n) (lambda () (len-r) (rfl)))
                 (dk-rewrite-h! `(<= ,i ,len) len n)
                 (dks-index-cases! i n
                   (lambda (j)
                     (dk-rewrite-h! `(IS-SUBTERM ,dks-T ,dks-K ,w (NTH ,i ,l)) i j)
                     (dk-nth-h! `(IS-SUBTERM ,dks-T ,dks-K ,w (NTH ,j ,l)))
                     (dks-sub-drive! w (list-ref ms (- j 1)) atoms)))))))))
    ((dks-token? m)
     (dk-cite! 'subterm-of-token dks-T dks-K w m)
     (dks-select-atom! `(= ,w ,m) atoms))
    (#t (dks-select-atom! `(IS-SUBTERM ,dks-T ,dks-K ,w ,m) atoms))))

(define (dks-sub-cases! w m)
  (let* ((hyp `(IS-SUBTERM ,dks-T ,dks-K ,w ,m))
         (atoms (dks-dedup (dks-sub-atoms w m)))
         (claim (dk-stl--or atoms)))
    (if (not (dk-asm? hyp)) (error "dks-sub-cases!: the hypothesis is not in context" hyp))
    (if (not (dk-asm? claim)) (dk-have! claim (lambda () (dks-sub-drive! w m atoms))))
    claim))

;;; ---- literal disequalities ----

(define (dks-raw-list? x) (and (pair? x) (eq? (car x) 'LIST)))

(define (dks-distinct? a b)
  (cond ((and (dks-raw-list? a) (dks-raw-list? b))
         (or (not (= (length a) (length b)))
             (let loop ((as (cdr a)) (bs (cdr b)))
               (and (pair? as) (or (dks-distinct? (car as) (car bs)) (loop (cdr as) (cdr bs)))))))
        ((and (dk-stl--encr? a) (dk-stl--encr? b))
         (or (dks-distinct? (cadr a) (cadr b)) (dks-distinct? (caddr a) (caddr b))))
        ((and (dk-stl--lst? a) (dk-stl--lst? b)) (dks-distinct? (cadr a) (cadr b)))
        ((and (dk-stl--encr? a) (dk-stl--lst? b)) #t)
        ((and (dk-stl--lst? a) (dk-stl--encr? b)) #t)
        ((and (or (dk-stl--encr? a) (dk-stl--lst? a)) (dks-token? b)) #t)
        ((and (or (dk-stl--encr? b) (dk-stl--lst? b)) (dks-token? a)) #t)
        (#t (or (dk-asm? `(NOT (= ,a ,b))) (dk-asm? `(NOT (= ,b ,a)))))))

(define (dks-token-eq-absurd! w term)
  (if (not (dk-asm? `(= ,w ,term))) (dk-have! `(= ,w ,term) (lambda () (dks-subst-rfl! `(= ,term ,w)))))
  (cond ((dk-head-is? term 'ENCR)
         (dks-set! (cadr term)) (dks-set! (caddr term))
         (ai (dk-cite! 'encr-ne-token dks-T w (cadr term) (caddr term))))
        (#t
         (dks-set! (cadr term))
         (ai (dk-cite! 'token-ne-list dks-T w (cadr term))))))

(define (dks-lit-neq! a b)
  (cond
    ((dk-asm? `(= ,a ,b)) (dks-lit-neq-1! a b))
    ((dk-asm? `(= ,b ,a)) (dks-lit-neq-1! b a))
    ((or (dk-asm? `(== ,a ,b)) (dk-asm? `(== ,b ,a)))
     (dk-have! `(= ,a ,b) (lambda () (subst `(== ,a ,b)) (rfl)))
     (dks-lit-neq-1! a b))
    (#t (error "dks-lit-neq!: no equation in context" a b))))

(define (dks-lit-neq-1! a b)
  (cond
    ((and (dks-raw-list? a) (dks-raw-list? b))
     (if (not (= (length a) (length b)))
         (let ((na0 (- (length a) 1)) (nb0 (- (length b) 1)))
           (dk-congr! `(= ,a ,b) (lambda (t) `(LENGTH ,t)) '==)
           (dk-have! `(= (LENGTH ,b) ,na0) (lambda () (subst `(== (LENGTH ,b) (LENGTH ,a))) (len-r) (rfl)))
           (dk-have! `(= (LENGTH ,b) ,nb0) (lambda () (len-r) (rfl)))
           (dk-rewrite-h! `(= (LENGTH ,b) ,na0) `(LENGTH ,b) nb0)
           (dks-nn-absurd! `(= ,nb0 ,na0)))
         (let loop ((i 1) (as (cdr a)) (bs (cdr b)))
           (cond ((null? as) (error "dks-lit-neq!: the lists do not differ" a b))
                 ((dks-distinct? (car as) (car bs))
                  (dk-congr! `(= ,a ,b) (lambda (t) `(NTH ,i ,t)) '==)
                  (dk-nth-h! `(== (NTH ,i ,a) (NTH ,i ,b)))
                  (dks-lit-neq! (car as) (car bs)))
                 (#t (loop (+ i 1) (cdr as) (cdr bs)))))))
    ((and (dk-stl--lst? a) (dk-stl--lst? b))
     (dk-cite! 'lst-injective (cadr a) (cadr b))
     (dks-lit-neq! (cadr a) (cadr b)))
    ((and (dk-stl--encr? a) (dk-stl--encr? b))
     (dks-fact-split! 'encr-injective (cadr a) (caddr a) (cadr b) (caddr b))
     (if (dks-distinct? (cadr a) (cadr b))
         (dks-lit-neq! (cadr a) (cadr b))
         (dks-lit-neq! (caddr a) (caddr b))))
    ((and (dk-stl--encr? a) (dk-stl--lst? b)) (ai (dk-cite! 'encr-ne-list (cadr a) (caddr a) (cadr b))))
    ((and (dk-stl--lst? a) (dk-stl--encr? b)) (ai (dk-cite! 'lst-ne-encr (cadr a) (cadr b) (caddr b))))
    ((and (dks-token? a) (or (dk-stl--encr? b) (dk-stl--lst? b))) (dks-token-eq-absurd! a b))
    ((and (dks-token? b) (or (dk-stl--encr? a) (dk-stl--lst? a)))
     (dk-have! `(= ,b ,a) (lambda () (dks-subst-rfl! `(= ,a ,b))))
     (dks-token-eq-absurd! b a))
    ((dk-asm? `(NOT (= ,a ,b))) (ai `(NOT (= ,a ,b))))
    ((dk-asm? `(NOT (= ,b ,a)))
     (dk-have! `(= ,b ,a) (lambda () (dks-subst-rfl! `(= ,a ,b))))
     (ai `(NOT (= ,b ,a))))
    (#t (error "dks-lit-neq!: cannot tell apart" a b))))

;;; ---- nodes of literal strands ----

(define (dks-sg n) `((STRAND-MAP ,dks-sp) (NTH 2 ,n)))

(define (dks-lit-facts! m lit)
  (let ((sg (dks-sg m)) (n (length (cdr lit))))
    (dk-have! `(= (LENGTH ,sg) ,n) (lambda () (subst `(= ,sg ,lit)) (len-r) (rfl)))
    (let loop ((j 1))
      (if (<= j n)
          (begin
            (dk-have! `(= (NTH ,j ,sg) ,(list-ref lit j)) (lambda () (subst `(= ,sg ,lit)) (nth-r) (rfl)))
            (loop (+ j 1)))))))

(define (dks-content n) (caddr (dks-eq-for `(NODE-CONTENT ,dks-sp ,n))))

;; with (= (NTH k sigma(NTH 2 m)) d) in context: land N's content and direction (N = M, a literal
;; [k, NTH 2 m], or N with (= (NTH 2 N) (NTH 2 M)) and (= (NTH 1 N) K) in context); return the content
(define (dks-entry! n k d m)
  (let ((mver `(= (NTH ,k ,(dks-sg m)) ,d))
        (nver `(= (NTH ,k ,(dks-sg n)) ,d)))
    (if (not (dk-asm? mver)) (error "dks-entry!: the entry is not in context" mver))
    (cond ((dk-asm? nver) #t)
          ((and (pair? n) (eq? (car n) 'LIST)) (dk-have! nver (lambda () (nth-r) (dk-ass!))))
          (#t (dk-rewrite-h! mver `(NTH 2 ,m) `(NTH 2 ,n))))
    (if (not (dk-asm? `(= (NTH 1 ,n) ,k)))
        (dk-have! `(= (NTH 1 ,n) ,k) (lambda () (if (not (equal? k `(NTH 1 ,n))) (nth-r)) (rfl))))
    (fact 'node-content-eq dks-sp n k d)
    (dk-split-all!)
    (dks-nth-all!)
    (dks-content n)))

;; the node [J, NTH(2, M)] and J ==> M, given J < NTH 1 M provable by dk-nn! from PREMS
(define (dks-earlier! j m . prems)
  (let ((n `(LIST ,j (NTH 2 ,m))))
    (fact 'node-intro dks-sp j `(NTH 2 ,m))
    (dk-have! `(SAME-STRAND-BEFORE ,dks-sp ,n ,m)
      (lambda ()
        (mac 'same-strand-before)
        (nth-r)
        (dk-conj-close!
          (lambda ()
            (cond ((dk-ass!) #t)
                  ((dk-head-is? (dk-goal) '=) (rfl))
                  (#t (apply dk-nn! prems)))))))
    n))

(define (dks-num-index! j m)
  (let* ((sg (dks-sg m))
         (leq (find-first (lambda (f) (and (dk-head-is? f '=) (equal? (cadr f) `(LENGTH ,sg)) (number? (caddr f)))) (dk-asms))))
    (dk-have! `(IN ,j NN) (lambda () (arith)))
    (dk-have! `(<= 1 ,j) (lambda () (dk-nn!)))
    (dk-have! `(<= ,j (LENGTH ,sg)) (lambda () (subst leq) (arith)))))

(define (dks-recv-absurd! n)
  (dk-have! `(= (NODE-DIR ,dks-sp ,n) SENT) (lambda () (mac-h 'is-sent `(IS-SENT ,dks-sp ,n)) (dk-ass!)))
  (dk-have! '(= SENT RECEIVED)
    (lambda () (subst `(= SENT (NODE-DIR ,dks-sp ,n))) (dks-subst-rfl! `(= (NODE-DIR ,dks-sp ,n) RECEIVED))))
  (ai (dk-cite! 'sent-ne-received)))

;; N in NODES, (= sigma(NTH 2 N) LIT) in context (any length): HANDLER gets each index j, with
;; (= (NTH 1 N) j) and N's reduced content and direction in context
(define (dks-lit-node-cases! n lit handler)
  (let* ((sg (dks-sg n)) (len (length (cdr lit))))
    (dks-fact-split! 'node-parts dks-sp n)
    (dks-lit-facts! n lit)
    (dk-rewrite-h! `(<= (NTH 1 ,n) (LENGTH ,sg)) `(LENGTH ,sg) len)
    (dks-index-cases! `(NTH 1 ,n) len
      (lambda (j)
        (fact 'node-content-eq dks-sp n j (list-ref lit j))
        (dk-split-all!)
        (dks-nth-all!)
        (handler j)))))

(define (dks-trace-witnesses! d count)
  (let loop ((i 0) (ex d) (acc '()))
    (if (= i count)
        (reverse acc)
        (let* ((v (dk-skolem! ex))
               (nx (if (< (+ i 1) count)
                       (dk-pick (lambda (f) (and (dk-head-is? f 'FORSOME) (dk-contains? f v))) "the next witness")
                       #f)))
          (loop (+ i 1) nx (cons v acc))))))

;;; (dks-lit-path! EQ PATH) -- EQ = (= A B) or (== A B) in context, A and B literals; PATH a list of
;;; steps: an integer i (the i-th entry of a raw LIST), LST (unwrap a list message), BODY / KEY (the
;;; plaintext / key of an encryption).  Land and return the equation between the two sub-literals PATH
;;; reaches (strict at the end, the last sub-literals typed).
(define (dks-lit-path! eq path)
  (let ((a (cadr eq)) (b (caddr eq)))
    (cond
      ((null? path)
       (if (eq? (car eq) '=) eq
           (let ((e `(= ,a ,b))) (dk-have! e (lambda () (subst eq) (rfl))) e)))
      ((number? (car path))
       (let* ((i (car path))
              (c (dk-congr! eq (lambda (t) `(NTH ,i ,t)) '==))
              (r (dk-nth-h! (if (eq? c #t) `(== (NTH ,i ,a) (NTH ,i ,b)) c))))
         (dks-lit-path! r (cdr path))))
      (#t
       (let ((se (if (eq? (car eq) '=) eq (let ((e `(= ,a ,b))) (dk-have! e (lambda () (subst eq) (rfl))) e))))
         (case (car path)
           ((LST) (dks-lit-path! (dk-cite! 'lst-injective (cadr a) (cadr b)) (cdr path)))
           ((BODY KEY)
            (dks-fact-split! 'encr-injective (cadr a) (caddr a) (cadr b) (caddr b))
            (dks-lit-path! (if (eq? (car path) 'BODY) `(= ,(cadr a) ,(cadr b)) `(= ,(caddr a) ,(caddr b))) (cdr path)))
           (else (error "dks-lit-path!: unknown step" (car path)))))))))

;;; ===========================================================================
;;; W1B (2026-11-05; META item 1, W1-CENSUS-REPORT.md s.3b): INDUCTION WITH THE PARAMETERS FIXED.
;;;
;;;   (dk-ni-fixed! [HOIST])    on a focus goal   forall n in NN. B
;;;   (dk-tfi3-fixed! [HOIST])  on a focus goal   forall n in ORD. B
;;;
;;; B = forall p1. ... A1 => ... R  has PARAMETERS in its prefix.  Since METACORE finding 2 the
;;; induction checkers test the body for predicativity (NBG has {n | B} only when every quantifier
;;; of B is confined to sets), and a parameter that ranges over classes -- a "function" typed only
;;; pointwise, a carrier, an unguarded universal -- makes B impredicative.  The theorem itself is
;;; still provable by a PREDICATIVE induction when the proof uses the induction hypothesis only at
;;; the same parameters: fix them first, and induct on  forall n. R  with the parameters FREE.
;;;
;;; What it does, as surface steps (so the page replays them):
;;;   1. `di' on the goal until the prefix is peeled through the last HOISTED item (n, its typing,
;;;      every item before and including the last hoisted one; `di' is greedy and may peel further,
;;;      which is tolerated).  The eigenvariables are read off the result and VERIFIED: the goal
;;;      must be the peeled subformula of the old goal under them, up to alpha, or it errors.
;;;   2. `cut' the lemma  T = forall n in CLS. B'  where B' is B with the hoisted items removed and
;;;      the hoisted parameters replaced by their eigenvariables (the kept binders stay quantified,
;;;      so the induction hypothesis may still vary them).
;;;   3. Close the main branch from T: `inst' at the eigenvariables, `detach!' the antecedents the
;;;      peel landed, `ass'.
;;;   4. On T's branch: `keep' the context without the formulas that mention the eigenvariables of
;;;      n and of the kept binders (their names are then free again for the step's `di'), and run
;;;      `ni' / `tfi3'.
;;; HOIST: a list of the binder names to fix; default every prefix binder of B that NO later
;;; prefix guard confines by an (IN p _), alone or as a conjunct (a binder so guarded ranges over
;;; a set and may stay inside, where the induction hypothesis may vary it).  A guard is hoisted with its binders when it mentions neither n nor a kept binder.
;;; Returns an alist: (base . NODE) (step . NODE) for `ni'; (cases . NODES) for both (the leaves
;;; the induction opened); (params . ((p . eigenvariable) ...)); (lemma . T).  Focus is left on the
;;; base case (for tfi3, the first case opened).  A proof that used the induction hypothesis at
;;; OTHER values of a hoisted parameter fails afterwards in its own step: such a theorem needs a
;;; guard confining that parameter, which is a statement change and not this helper's to make.
(define (dkf--spine f)                 ; (ITEMS . REM), items (forall x) / (implies A), top first
  (let loop ((f f) (acc '()))
    (cond ((and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3) (symbol? (cadr f)))
           (loop (caddr f) (cons (list 'forall (cadr f)) acc)))
          ((and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3))
           (loop (caddr f) (cons (list 'implies (cadr f)) acc)))
          (#t (cons (reverse acc) f)))))
(define (dkf--build items rem)
  (fold-right (lambda (it b) (if (eq? (car it) 'forall)
                                 (list 'FORALL (cadr it) b)
                                 (list 'IMPLIES (cadr it) b)))
              rem items))
(define (dkf--drop k lst) (if (or (= k 0) (null? lst)) lst (dkf--drop (- k 1) (cdr lst))))
(define (dkf--subst-all sigma f)
  (fold-left (lambda (acc p) (if (eq? (car p) (cdr p)) acc (subst-free (car p) (cdr p) acc))) f sigma))
(define (dkf--eigen-candidates x new)
  (let ((pre (string-append (symbol->string x) "_")))
    (filter (lambda (s)
              (let ((str (symbol->string s)))
                (and (> (string-length str) (string-length pre))
                     (string=? (substring str 0 (string-length pre)) pre)
                     (string->number (substring str (string-length pre) (string-length str))))))
            new)))

(define (dkf--induct-fixed! who cls induct! hoist)
  (let* ((leaf0 (proof-state-focus *ps*))
         (g     (dk-goal)))
    (if (not (and (dk-head-is? g 'FORALL) (symbol? (cadr g)) (dk-head-is? (caddr g) 'IMPLIES)
                  (equal? (cadr (caddr g)) (list 'IN (cadr g) cls))))
        (error (string-append who ": goal is not  forall n in " (symbol->string cls) ". B")
               (expression->string g)))
    (let* ((n      (cadr g))
           (spB    (dkf--spine (caddr (caddr g))))
           (items  (car spB))
           (R      (cdr spB))
           ;; a binder is CONFINED when a later prefix guard has (IN x _) as itself or as a conjunct
           (guarded-in? (lambda (x rest)
                          (let ((in-x? (lambda (a) (and (dk-head-is? a 'IN) (eq? (cadr a) x)))))
                            (any (lambda (it)
                                   (and (eq? (car it) 'implies)
                                        (let conj ((a (cadr it)))
                                          (if (dk-head-is? a 'AND) (or (conj (cadr a)) (conj (caddr a))) (in-x? a)))))
                                 rest))))
           ;; classify the prefix items: hoisted (#t) or kept (#f), in order
           (marks
            (let loop ((its items) (kept '()) (acc '()))
              (if (null? its) (reverse acc)
                  (let ((it (car its)))
                    (if (eq? (car it) 'forall)
                        (let ((h (if (eq? hoist 'default)
                                     (not (guarded-in? (cadr it) (cdr its)))
                                     (and (memq (cadr it) hoist) #t))))
                          (loop (cdr its) (if h kept (cons (cadr it) kept)) (cons h acc)))
                        (let* ((fv (free-vars (cadr it)))
                               (h  (and (not (memq n fv))
                                        (not (any (lambda (k) (memq k fv)) kept)))))
                          (loop (cdr its) kept (cons h acc))))))))
           (hoisted-binders (let loop ((its items) (ms marks) (acc '()))
                              (if (null? its) (reverse acc)
                                  (loop (cdr its) (cdr ms)
                                        (if (and (car ms) (eq? (car (car its)) 'forall))
                                            (cons (cadr (car its)) acc) acc)))))
           (last-h (let loop ((ms marks) (i 0) (last #f))
                     (if (null? ms) last (loop (cdr ms) (+ i 1) (if (car ms) i last)))))
           (kept-items (let loop ((its items) (ms marks) (acc '()))
                         (if (null? its) (reverse acc)
                             (loop (cdr its) (cdr ms) (if (car ms) acc (cons (car its) acc))))))
           (spG    (dkf--spine g))
           (lenG   (length (car spG)))
           (d      (+ 2 (+ last-h 1)))
           (ctx0   (dk-asms)))
      (if (null? hoisted-binders)
          (error (string-append who ": no parameter to fix in") (expression->string g)))
      ;; 1. peel through the last hoisted item
      (let loop ()
        (let ((e (- lenG (length (car (dkf--spine (dk-goal)))))))
          (if (< e d)
              (let ((before (dk-goal)))
                (di)
                (if (equal? (dk-goal) before)
                    (error (string-append who ": di made no progress on") (expression->string before)))
                (loop)))))
      (let* ((gc     (dk-goal))
             (main   (proof-state-focus *ps*))
             (e      (- lenG (length (car (dkf--spine gc)))))
             (peeled (list-head (car spG) e))
             (pbind  (filter-map (lambda (it) (and (eq? (car it) 'forall) (cadr it))) peeled))
             (old-fv (apply append (map free-vars (cons g ctx0))))
             (landed (filter (lambda (a) (not (any (lambda (b) (alpha-equiv? a b)) ctx0))) (dk-asms)))
             (new    (filter (lambda (s) (not (memq s old-fv)))
                             (delete-duplicates (apply append (map free-vars (cons gc landed))))))
             (sigma  (map (lambda (x)
                            (cond ((memq x new) (cons x x))
                                  (#t (let ((c (dkf--eigen-candidates x new)))
                                        (if (and (pair? c) (null? (cdr c))) (cons x (car c))
                                            (cons x x))))))
                          pbind))
             (pat    (dkf--build (dkf--drop e (car spG)) (cdr spG))))
        (if (not (alpha-equiv? (dkf--subst-all sigma pat) gc))
            (error (string-append who ": could not read the eigenvariables off the peeled goal")
                   (expression->string gc)))
        (let* ((hsig   (filter (lambda (p) (memq (car p) hoisted-binders)) sigma))
               (drop-vars (map cdr (filter (lambda (p) (not (memq (car p) hoisted-binders))) sigma)))
               (lemma  (list 'FORALL n (list 'IMPLIES (list 'IN n cls)
                                             (dkf--subst-all hsig (dkf--build kept-items R)))))
               (opened (dk-opened (lambda () (cut lemma))))
               (tleaf  (or (find-first (lambda (l) (alpha-equiv? (dk-goal-of l) lemma)) opened)
                           (error (string-append who ": cut opened no branch for the lemma"))))
               (mleaf  (or (find-first (lambda (l) (not (eq? l tleaf))) opened)
                           (error (string-append who ": cut opened no main branch")))))
          ;; 3. the main branch from the lemma
          (dk-focus! mleaf)
          (let loop ((f (or (dk-ctx-form lemma) lemma)))
            (cond ((alpha-equiv? f (dk-goal)) (ass))
                  ((dk-head-is? f 'FORALL)
                   (let* ((x (cadr f))
                          (t (cond ((assq x sigma) => cdr) (#t x)))
                          (f1 (subst-free x t (caddr f))))
                     (if (not (dk-asm? f1)) (inst f t))
                     (loop (or (dk-ctx-form f1)
                               (error (string-append who ": inst landed nothing for") (expression->string f1))))))
                  ((dk-head-is? f 'IMPLIES)
                   (if (not (dk-asm? (caddr f))) (detach! f))
                   (loop (or (dk-ctx-form (caddr f))
                             (error (string-append who ": detach! landed nothing for")
                                    (expression->string f)))))
                  (#t (error (string-append who ": cannot reach the peeled goal from the lemma")
                             (expression->string f)))))
          (if (not (sequent-node-grounded? mleaf))
              (error (string-append who ": the main branch was not closed from the lemma")))
          ;; 4. the induction, on the lemma's branch
          (dk-focus! tleaf)
          (let* ((ctx (dk-asms))
                 (keepers (filter (lambda (a) (not (any (lambda (v) (memq v (free-vars a))) drop-vars)))
                                  ctx)))
            (if (< (length keepers) (length ctx)) (apply keep keepers)))
          (let* ((cases (dk-opened induct!))
                 ;; the step is the leaf whose goal IS the step formula of the lemma (up to alpha):
                 ;; a base case may have the same outer shape (a kept binder guarded in NN)
                 (bodyT (caddr (caddr lemma)))
                 (step-goal (list 'FORALL n (list 'IMPLIES (list 'IN n 'NN)
                                                  (list 'IMPLIES bodyT (subst-free n (list 'succ n) bodyT)))))
                 (step  (and (eq? cls 'NN)
                             (find-first (lambda (l) (alpha-equiv? (dk-goal-of l) step-goal)) cases)))
                 (base  (and (eq? cls 'NN) (find-first (lambda (l) (not (eq? l step))) cases))))
            (if (null? cases) (error (string-append who ": the induction opened no case")))
            (if (and (eq? cls 'NN) (not (and step base)))
                (error (string-append who ": ni did not open a base and a step case")))
            (dk-focus! (or base (car cases)))
            (list (cons 'base base) (cons 'step step) (cons 'cases cases)
                  (cons 'params hsig) (cons 'lemma lemma))))))))

(define (dk-ni-fixed! . opt)
  (dkf--induct-fixed! "dk-ni-fixed!" 'NN (lambda () (ni)) (if (pair? opt) (car opt) 'default)))
;;; (dk-use-induction-fixed! [HOIST]) -- `use-induction' (above) on top of dk-ni-fixed!: the same
;;; alist (base step ih var), the step peeled and the IH captured, plus (params . ...).
(define (dk-use-induction-fixed! . opt)
  (let* ((r (apply dk-ni-fixed! opt))
         (step (cdr (assq 'step r)))
         (v (cadr (dk-goal-of step))))
    (dk-focus! step)
    (di)
    (let ((ih (dk-landed-1 (lambda () (di)))))
      (list (cons 'base (cdr (assq 'base r)))
            (cons 'step (proof-state-focus *ps*))
            (cons 'ih ih) (cons 'var v)
            (cons 'params (cdr (assq 'params r)))))))
(define (dk-tfi3-fixed! . opt)
  (dkf--induct-fixed! "dk-tfi3-fixed!" 'ORD (lambda () (tfi3)) (if (pair? opt) (car opt) 'default)))

;;; ==================================================================
;;; KIT-ALG (2026-11-09/10), hoisted 2026-11-10 from scratchpad/kitalg-1109/kit-alg.scm, verbatim:
;;; the algebra normaliser dk-alg-norm!.  Its law sets are proven in theorem-library/kal-laws.
;;; ==================================================================

;;; kit-alg.scm -- THE ALGEBRA NORMALISER: (dk-alg-norm! PREFIX A), an UNTRUSTED driver helper
;;; that proves an equation between terms of a complex (star-)algebra by rewriting both sides to a
;;; normal form with CITED LAWS of the structure.  Agent KIT-ALG, 2026-11-09/10.  Written as kit
;;; code (prefix dk-alg- / dk--alg-) for the integrator to hoist into driver-kit.scm; it defines no
;;; theorem.  Until hoisted it is loaded INTO *driver-kit-env* (not a fresh frame) so that later
;;; files see it: (load ".../kit-alg.scm" *driver-kit-env*).
;;;
;;; WHAT IT PROVES.  The focus goal (= L R), L and R terms built from
;;;     (VADD A) (VNEG A) (VZERO A) (ACT A) (VMUL A) (VONE A) (VSTAR A)
;;; of one algebra A, over ATOMS: vector atoms typed (IN x (VEC A)) in context, scalar atoms typed
;;; (IN c CC) or (IN c RR) in context, numerals (exact, complex allowed: +i), and the scalar
;;; operations + * - conjugate.  It decides whether L = R holds in EVERY associative complex
;;; (star-)algebra -- VMUL is NOT assumed commutative, monomials are WORDS -- and if so proves it;
;;; if not it REFUSES, naming the word whose coefficients differ, with nothing changed.
;;;
;;; HOW.  Nothing is trusted but what is cited.  Every step is a `dk-cite!' of a law of the
;;; structure followed by `subst' in the goal; the scalar coefficients are compared by `crs' (a
;;; standing oracle) on lanes; conjugates are pushed inward by the CC axioms of the fixed base.
;;;   0. DECIDE (Scheme, no proof step): both sides are put in the abstract normal form
;;;      sum_w p_w . w (w a word of letters, p_w a polynomial in the scalar atoms with exact
;;;      complex coefficients); the identity holds iff p_w(L) - p_w(R) = 0 for every word.
;;;   1. EXPAND to a fixpoint, innermost redex first: -x -> (-1)x; star pushed to the letters;
;;;      c(x+y), c(dx) -> (cd)x, c0, 0x, 1x; products distributed, scalars pulled out of
;;;      products, 0 and 1 absorbed, products right-associated; sums right-associated, 0 dropped;
;;;      conjugates of scalars pushed to the scalar atoms.
;;;   2. WRAP every bare word on a sum spine as 1.w (the act-one law, by congruence).
;;;   3. SORT the summands of each side by word (commutativity of VADD, through associativity)
;;;      and COLLECT equal words: c.w + d.w -> (c + d).w.
;;;   4. COMPARE word by word: equal coefficients made syntactically equal (crs on a lane),
;;;      a word on one side only has a zero coefficient and is rewritten to 0 (then back to 1).
;;;   5. rfl.
;;;
;;; THE LAW TABLE.  PREFIX names the law set: the law ROLE is the theorem PREFIX-ROLE, stated
;;; forall A. PRED(A) => forall <args>. <equation>, the args in the order of the signature below.
;;; theorem-library kal-laws.scm proves the sets kal-cna (IS-COMPLEX-NORMED-ALGEBRA), kal-uba
;;; (IS-UNITAL-BANACH-ALGEBRA) and kal-uiba (IS-UNITAL-INVOLUTIVE-BANACH-ALGEBRA).  A set without
;;; the one / star roles serves terms without VONE / VSTAR.  (dk-alg-law-statement ROLE PRED) is
;;; the statement template, so a new structure gets its set by proving those statements.
;;;
;;; OPTIONS (keyword list after A):
;;;   'hints (EQ ...)  -- equations (= U V) in context; a subterm equal to U is rewritten to V
;;;                       wherever it occurs (e.g. (= (VSTAR A) h) h) for h self-adjoint).
;;;   'trace #t        -- print each step.
;;; Errors: an untyped atom, an unknown head, a refused identity (before any step), a law that
;;; does not land, a step that changes nothing, or a lane that does not close.
;;;
;;; THE OTHER ENTRY POINTS.
;;;   (dk-alg-have! PREFIX A CLAIM . OPTS) -- land the equation CLAIM, proved by dk-alg-norm!.
;;;   (dk-alg-identity? PREFIX A L R . OPTS) -- the decision alone: #t, or the differing words.
;;;   (dk-alg-type! PREFIX A T)  -- land (IN T (VEC A)) by the typing roles.
;;;   (dk-cc-type! T)            -- land (IN T CC) for a scalar term (+ * - conjugate, numerals).
;;;   (dk-cc-norm! . OPTS)       -- THE SCALAR FINISHER: the focus goal an equation over CC;
;;;                                 conjugates pushed in by the CC axioms (a conjugate of an atom
;;;                                 typed in RR, or of a real numeral, is dropped), then `crs'.
;;; WHAT IT CANNOT DO: commutativity (refused: VMUL is a word product), a hypothesis other than a
;;; hint equation, inverses, norms or any inequality, a scalar atom under a conjugate that is not
;;; known real (it stays an opaque atom, so conj(u) = u is not proved), division by a non-numeral.

;;; ------------------------------------------------------------------------------------------
;;; the law roles: (ROLE ARG-KINDS), v = a vector, c = a scalar in CC
(define dk--alg-roles
  '((vadd-in (v v)) (vneg-in (v)) (act-in (c v)) (vmul-in (v v)) (vzero-in ()) (vone-in ())
    (vstar-in (v))
    (add-assoc (v v v)) (add-comm (v v)) (add-zero-l (v)) (add-zero-r (v))
    (vneg-act (v)) (act-vadd (c v v)) (act-add (c c v)) (act-mul (c c v)) (act-one (v))
    (act-zero (v)) (act-vzero (c))
    (mul-assoc (v v v)) (mul-dist-l (v v v)) (mul-dist-r (v v v)) (mul-act-l (c v v))
    (mul-act-r (c v v)) (mul-zero-l (v)) (mul-zero-r (v)) (mul-one-l (v)) (mul-one-r (v))
    (star-vadd (v v)) (star-act (c v)) (star-star (v)) (star-mul (v v)) (star-one ()) (star-zero ())))

;;; the statement of ROLE for the structure predicate PRED, instance variable a
(define (dk-alg-law-statement role pred)
  (let* ((A 'a)
         (ad (lambda (x y) (list (list 'VADD A) x y))) (ng (lambda (x) (list (list 'VNEG A) x)))
         (ac (lambda (c x) (list (list 'ACT A) c x))) (mu (lambda (x y) (list (list 'VMUL A) x y)))
         (st (lambda (x) (list (list 'VSTAR A) x)))
         (z (list 'VZERO A)) (o (list 'VONE A)) (V (list 'VEC A))
         (sig (cadr (or (assq role dk--alg-roles) (error "dk-alg-law-statement: unknown role" role))))
         (vars (let loop ((ks sig) (vs '(kax_ kay_ kaz_)) (cs '(kar_ kas_)) (acc '()))
                 (cond ((null? ks) (reverse acc))
                       ((eq? (car ks) 'v) (loop (cdr ks) (cdr vs) cs (cons (car vs) acc)))
                       (#t (loop (cdr ks) vs (cdr cs) (cons (car cs) acc))))))
         (x (if (pair? vars) (car vars) #f)) (y (and (pair? vars) (pair? (cdr vars)) (cadr vars)))
         (w (and (pair? vars) (pair? (cdr vars)) (pair? (cddr vars)) (caddr vars)))
         (body
          (case role
            ((vadd-in) (list 'IN (ad x y) V)) ((vneg-in) (list 'IN (ng x) V))
            ((act-in) (list 'IN (ac x y) V)) ((vmul-in) (list 'IN (mu x y) V))
            ((vzero-in) (list 'IN z V)) ((vone-in) (list 'IN o V)) ((vstar-in) (list 'IN (st x) V))
            ((add-assoc) (list '= (ad (ad x y) w) (ad x (ad y w))))
            ((add-comm) (list '= (ad x y) (ad y x)))
            ((add-zero-l) (list '= (ad z x) x)) ((add-zero-r) (list '= (ad x z) x))
            ((vneg-act) (list '= (ng x) (ac -1 x)))
            ((act-vadd) (list '= (ac x (ad y w)) (ad (ac x y) (ac x w))))
            ((act-add) (list '= (ac (list '+ x y) w) (ad (ac x w) (ac y w))))
            ((act-mul) (list '= (ac (list '* x y) w) (ac x (ac y w))))
            ((act-one) (list '= (ac 1 x) x)) ((act-zero) (list '= (ac 0 x) z))
            ((act-vzero) (list '= (ac x z) z))
            ((mul-assoc) (list '= (mu (mu x y) w) (mu x (mu y w))))
            ((mul-dist-l) (list '= (mu x (ad y w)) (ad (mu x y) (mu x w))))
            ((mul-dist-r) (list '= (mu (ad x y) w) (ad (mu x w) (mu y w))))
            ((mul-act-l) (list '= (mu (ac x y) w) (ac x (mu y w))))
            ((mul-act-r) (list '= (mu y (ac x w)) (ac x (mu y w))))
            ((mul-zero-l) (list '= (mu z x) z)) ((mul-zero-r) (list '= (mu x z) z))
            ((mul-one-l) (list '= (mu o x) x)) ((mul-one-r) (list '= (mu x o) x))
            ((star-vadd) (list '= (st (ad x y)) (ad (st x) (st y))))
            ((star-act) (list '= (st (ac x y)) (ac (list 'conjugate x) (st y))))
            ((star-star) (list '= (st (st x)) x))
            ((star-mul) (list '= (st (mu x y)) (mu (st y) (st x))))
            ((star-one) (list '= (st o) o)) ((star-zero) (list '= (st z) z))
            (else (error "dk-alg-law-statement: no template" role)))))
    (list 'FORALL A
          (list 'IMPLIES (list pred A)
                (let wrap ((vs vars) (ks sig))
                  (if (null? vs) body
                      (list 'FORALL (car vs)
                            (list 'IMPLIES (list 'IN (car vs) (if (eq? (car ks) 'v) V 'CC))
                                  (wrap (cdr vs) (cdr ks))))))))))

;;; ------------------------------------------------------------------------------------------
;;; the structure record: (A PREFIX HINTS TRACE)
(define (dk--alg-A krec) (car krec))
(define (dk--alg-prefix krec) (cadr krec))
(define (dk--alg-hints krec) (caddr krec))
(define (dk--alg-trace? krec) (cadddr krec))
(define (dk--alg-head krec acc) (list acc (dk--alg-A krec)))
(define (dk--alg-op? krec t acc n)          ; t = ((ACC A) arg1 .. argn)
  (and (pair? t) (equal? (car t) (dk--alg-head krec acc)) (= (length (cdr t)) n)))
(define (dk--alg-const? krec t acc) (equal? t (dk--alg-head krec acc)))
(define (dk--alg-vec krec) (list 'VEC (dk--alg-A krec)))
(define (dk--alg-law krec role) (symbol-append (dk--alg-prefix krec) '- role))
(define (dk--alg-has? krec role)
  (eq? #t (vnb-guard (lambda () (and (lookup-theorem (dk--alg-law krec role)) #t)))))
(define (dk--alg-say krec . xs)
  (if (dk--alg-trace? krec)
      (begin (display ";; dk-alg-norm! ")
             (for-each (lambda (x) (display (if (string? x) x (expression->string x))) (display " ")) xs)
             (newline))))
(define (dk--alg-vecop? krec t)
  (and (pair? t) (pair? (car t)) (memq (caar t) '(VADD VNEG ACT VMUL VSTAR))
       (pair? (cdar t)) (equal? (cadar t) (dk--alg-A krec))))

;;; ------------------------------------------------------------------------------------------
;;; TYPING.  Scalars in CC, bottom-up by the CC closure laws; vectors in (VEC A) by the typing
;;; roles.  Each lands its typing and returns the term; an atom not typed is an ERROR.
(define (dk--alg-cite2! . args)          ; dk-cite!, detaching conjunctive antecedents from context
  (let loop ((ch (apply dk-cite! args)) (n 0))
    (if (and (dk-head-is? ch 'IMPLIES) (< n 6))
        (loop (detach-with! ch (lambda () (dk-conj-close! (lambda () (dk-ass!))))) (+ n 1))
        ch)))
(define (dk--alg-ct! t)
  (let ((want (list 'IN t 'CC)))
    (cond ((dk-asm? want) t)
          ((number? t) (dk-have! want (lambda () (arith))) t)
          ((dk-asm? (list 'IN t 'RR)) (dk-cite! 'rr-subset-cc t) t)
          ((and (pair? t) (memq (car t) '(+ *)) (= (length t) 3))
           (dk--alg-ct! (cadr t)) (dk--alg-ct! (caddr t))
           (dk--alg-cite2! (if (eq? (car t) '+) 'cc-add-closed 'cc-mul-closed) (cadr t) (caddr t)) t)
          ((and (pair? t) (eq? (car t) '-) (= (length t) 2))
           (dk--alg-ct! (cadr t)) (dk-cite! 'cc-neg-closed (cadr t)) t)
          ((and (pair? t) (eq? (car t) '-) (= (length t) 3))
           (dk--alg-ct! (cadr t)) (dk--alg-ct! (caddr t))
           (dk-have! want (lambda () (type-term))) t)
          ((and (pair? t) (eq? (car t) 'conjugate) (= (length t) 2))
           (dk--alg-ct! (cadr t)) (dk-cite! 'cc-conjugate-closed (cadr t)) t)
          (#t (error "dk-alg-norm!: a scalar atom is not typed in CC or RR:" (expression->string t))))))
(define (dk--alg-vt! krec t)
  (let ((want (list 'IN t (dk--alg-vec krec))) (A (dk--alg-A krec)))
    (cond ((dk-asm? want) t)
          ((dk--alg-const? krec t 'VZERO) (dk-cite! (dk--alg-law krec 'vzero-in) A) t)
          ((dk--alg-const? krec t 'VONE) (dk-cite! (dk--alg-law krec 'vone-in) A) t)
          ((dk--alg-op? krec t 'VADD 2)
           (dk--alg-vt! krec (cadr t)) (dk--alg-vt! krec (caddr t))
           (dk-cite! (dk--alg-law krec 'vadd-in) A (cadr t) (caddr t)) t)
          ((dk--alg-op? krec t 'VMUL 2)
           (dk--alg-vt! krec (cadr t)) (dk--alg-vt! krec (caddr t))
           (dk-cite! (dk--alg-law krec 'vmul-in) A (cadr t) (caddr t)) t)
          ((dk--alg-op? krec t 'VNEG 1)
           (dk--alg-vt! krec (cadr t)) (dk-cite! (dk--alg-law krec 'vneg-in) A (cadr t)) t)
          ((dk--alg-op? krec t 'VSTAR 1)
           (dk--alg-vt! krec (cadr t)) (dk-cite! (dk--alg-law krec 'vstar-in) A (cadr t)) t)
          ((dk--alg-op? krec t 'ACT 2)
           (dk--alg-ct! (cadr t)) (dk--alg-vt! krec (caddr t))
           (dk-cite! (dk--alg-law krec 'act-in) A (cadr t) (caddr t)) t)
          (#t (error "dk-alg-norm!: a vector atom is not typed in (VEC A):" (expression->string t))))))

;;; ------------------------------------------------------------------------------------------
;;; THE STEP: cite ROLE at ARGS (typed first), check the instance is an equation between FROM and
;;; TO (either orientation), and rewrite FROM -> TO in the goal.  Errors when nothing changes.
(define (dk--alg-step! krec role args from to)
  (let ((sig (cadr (assq role dk--alg-roles))))
    (for-each (lambda (k a) (if (eq? k 'v) (dk--alg-vt! krec a) (dk--alg-ct! a))) sig args))
  (let ((inst (apply dk-cite! (dk--alg-law krec role) (dk--alg-A krec) args)))
    (if (not (and (pair? inst) (eq? (car inst) '=)
                  (or (and (equal? (cadr inst) from) (equal? (caddr inst) to))
                      (and (equal? (cadr inst) to) (equal? (caddr inst) from)))))
        (error "dk-alg-norm!: the law did not land as the expected equation:" role
               (expression->string inst) (expression->string (list '= from to))))
    (dk--alg-say krec role ":" from "->" to)
    (dk--alg-subst! (list '= from to))))
(define (dk--alg-subst! eq)
  (let ((g (dk-goal)))
    (subst eq)
    (if (equal? g (dk-goal))
        (error "dk-alg-norm!: the rewrite changed nothing:" (expression->string eq)))))
;;; a step justified by a scalar-law citation (the CC axioms): cite THM at TERMS (conjunctive
;;; antecedents detached from context), rewrite FROM -> TO
(define (dk--alg-cc-step! krec thm terms from to)
  (for-each dk--alg-ct! terms)
  (let ((inst (apply dk--alg-cite2! thm terms)))
    (if (not (and (pair? inst) (eq? (car inst) '=)))
        (error "dk-alg-norm!: the scalar law did not land:" thm (expression->string inst)))
    (dk--alg-say krec thm ":" from "->" to)
    (dk--alg-subst! (list '= from to))))

;;; ------------------------------------------------------------------------------------------
;;; PHASE 1: the expansion redexes.  (dk--alg-redex S t) is #f or a thunk performing the step.
(define (dk--alg-real-number? t) (and (number? t) (exact? t) (real? t)))
(define (dk--alg-letter? krec t)            ; an atom or the star of an atom
  (and (not (dk--alg-vecop? krec t)) (not (dk--alg-const? krec t 'VZERO))))
;;; the conjugate-pushing redex (the CC axioms), shared by dk-alg-norm! and dk-cc-norm!
(define (dk--alg-conj-redex krec t)
  (and (pair? t) (eq? (car t) 'conjugate) (= (length t) 2)
      (let ((u (cadr t)))
        (cond ((and (pair? u) (memq (car u) '(+ *)) (= (length u) 3))
               (let ((to (list (car u) (list 'conjugate (cadr u)) (list 'conjugate (caddr u)))))
                 (lambda () (dk--alg-cc-step! krec (if (eq? (car u) '+) 'cc-conjugate-add 'cc-conjugate-mul)
                                              (cdr u) t to))))
              ((and (pair? u) (eq? (car u) '-) (= (length u) 2))
               (lambda () (dk--alg-cc-step! krec 'cc-conjugate-neg (cdr u) t (list '- (list 'conjugate (cadr u))))))
              ((and (pair? u) (eq? (car u) '-) (= (length u) 3))
               (lambda () (dk--alg-cc-step! krec 'cc-conjugate-sub (cdr u) t
                                            (list '- (list 'conjugate (cadr u)) (list 'conjugate (caddr u))))))
              ((and (pair? u) (eq? (car u) 'conjugate) (= (length u) 2))
               (lambda () (dk--alg-cc-step! krec 'cc-conjugate-involution (cdr u) t (cadr u))))
              ((equal? u +i)
               (lambda () (dk--alg-say krec "cc-conjugate-i") (dk-cite! 'cc-conjugate-i)
                          (dk--alg-subst! (list '= t (list '- +i)))))
              ((or (dk--alg-real-number? u) (dk-asm? (list 'IN u 'RR)))
               (lambda ()
                 (if (not (dk-asm? (list 'IN u 'RR))) (dk-have! (list 'IN u 'RR) (lambda () (arith))))
                 (dk--alg-say krec "cc-conjugate-fixes-rr" u)
                 (dk-cite! 'cc-conjugate-fixes-rr u)
                 (dk--alg-subst! (list '= t u))))
              (#t #f)))))
(define (dk--alg-redex krec t)
  (let* ((A (dk--alg-A krec))
         (hint (find-first (lambda (h) (equal? (cadr h) t)) (dk--alg-hints krec)))
         (V? (lambda (u acc) (dk--alg-const? krec u acc)))
         (O? (lambda (u acc n) (dk--alg-op? krec u acc n)))
         (ad (lambda (x y) (list (dk--alg-head krec 'VADD) x y)))
         (ac (lambda (c x) (list (dk--alg-head krec 'ACT) c x)))
         (mu (lambda (x y) (list (dk--alg-head krec 'VMUL) x y)))
         (st (lambda (x) (list (dk--alg-head krec 'VSTAR) x)))
         (Z (dk--alg-head krec 'VZERO)) (One (dk--alg-head krec 'VONE))
         (step (lambda (role args to) (lambda () (dk--alg-step! krec role args t to)))))
    (cond
     (hint (lambda () (dk--alg-say krec "hint:" hint) (dk--alg-subst! hint)))
     ;; scalars: conjugates pushed in
     ((dk--alg-conj-redex krec t))
     ((O? t 'VNEG 1) (step 'vneg-act (list (cadr t)) (ac -1 (cadr t))))
     ((O? t 'VSTAR 1)
      (let ((u (cadr t)))
        (cond ((O? u 'VADD 2) (step 'star-vadd (cdr u) (ad (st (cadr u)) (st (caddr u)))))
              ((O? u 'ACT 2) (step 'star-act (cdr u) (ac (list 'conjugate (cadr u)) (st (caddr u)))))
              ((O? u 'VSTAR 1) (step 'star-star (cdr u) (cadr u)))
              ((O? u 'VMUL 2) (step 'star-mul (cdr u) (mu (st (caddr u)) (st (cadr u)))))
              ((V? u 'VONE) (step 'star-one '() One))
              ((V? u 'VZERO) (step 'star-zero '() Z))
              (#t #f))))
     ((O? t 'ACT 2)
      (let ((c (cadr t)) (u (caddr t)))
        (cond ((O? u 'VADD 2) (step 'act-vadd (list c (cadr u) (caddr u)) (ad (ac c (cadr u)) (ac c (caddr u)))))
              ((O? u 'ACT 2) (step 'act-mul (list c (cadr u) (caddr u)) (ac (list '* c (cadr u)) (caddr u))))
              ((V? u 'VZERO) (step 'act-vzero (list c) Z))
              ((equal? c 0) (step 'act-zero (list u) Z))
              ((equal? c 1) (step 'act-one (list u) u))
              (#t #f))))
     ((O? t 'VMUL 2)
      (let ((p (cadr t)) (q (caddr t)))
        (cond ((V? p 'VZERO) (step 'mul-zero-l (list q) Z))
              ((V? q 'VZERO) (step 'mul-zero-r (list p) Z))
              ((O? p 'VADD 2) (step 'mul-dist-r (list (cadr p) (caddr p) q) (ad (mu (cadr p) q) (mu (caddr p) q))))
              ((O? q 'VADD 2) (step 'mul-dist-l (list p (cadr q) (caddr q)) (ad (mu p (cadr q)) (mu p (caddr q)))))
              ((O? p 'ACT 2) (step 'mul-act-l (list (cadr p) (caddr p) q) (ac (cadr p) (mu (caddr p) q))))
              ((O? q 'ACT 2) (step 'mul-act-r (list (cadr q) p (caddr q)) (ac (cadr q) (mu p (caddr q)))))
              ((V? p 'VONE) (step 'mul-one-l (list q) q))
              ((V? q 'VONE) (step 'mul-one-r (list p) p))
              ((O? p 'VMUL 2) (step 'mul-assoc (list (cadr p) (caddr p) q) (mu (cadr p) (mu (caddr p) q))))
              (#t #f))))
     ((O? t 'VADD 2)
      (let ((p (cadr t)) (q (caddr t)))
        (cond ((V? p 'VZERO) (step 'add-zero-l (list q) q))
              ((V? q 'VZERO) (step 'add-zero-r (list p) p))
              ((O? p 'VADD 2) (step 'add-assoc (list (cadr p) (caddr p) q) (ad (cadr p) (ad (caddr p) q))))
              (#t #f))))
     (#t #f))))
;;; the first redex, innermost (post-order), left to right
(define (dk--alg-find krec t)
  (or (and (pair? t) (let loop ((ts (cdr t)))
                       (and (pair? ts) (or (dk--alg-find krec (car ts)) (loop (cdr ts))))))
      (dk--alg-redex krec t)))
(define (dk--alg-expand! krec)
  (let loop ((n 0))
    (if (> n 3000) (error "dk-alg-norm!: expansion did not terminate"))
    (let ((r (dk--alg-find krec (dk-goal))))
      (if r (begin (r) (loop (+ n 1)))))))

;;; ------------------------------------------------------------------------------------------
;;; the summand spine of a side in phase-1 normal form
(define (dk--alg-spine krec t)              ; list of summands; () for VZERO
  (cond ((dk--alg-const? krec t 'VZERO) '())
        ((dk--alg-op? krec t 'VADD 2) (cons (cadr t) (dk--alg-spine krec (caddr t))))
        (#t (list t))))
(define (dk--alg-word krec s) (if (dk--alg-op? krec s 'ACT 2) (caddr s) s))
(define (dk--alg-coef krec s) (if (dk--alg-op? krec s 'ACT 2) (cadr s) #f))
(define (dk--alg-key krec s) (expression->string (dk--alg-word krec s)))

;;; PHASE 2: wrap the bare words of a spine of two or more summands
(define (dk--alg-wrap! krec)
  (let ((ad (lambda (x y) (list (dk--alg-head krec 'VADD) x y)))
        (ac (lambda (c x) (list (dk--alg-head krec 'ACT) c x))))
    (let loop ()
      (let ((node
             (let scan ((sides (cdr (dk-goal))))
               (and (pair? sides)
                    (or (let walk ((t (car sides)))
                          (and (dk--alg-op? krec t 'VADD 2)
                               (cond ((not (dk--alg-coef krec (cadr t))) (cons t 'left))
                                     ((and (not (dk--alg-op? krec (caddr t) 'VADD 2))
                                           (not (dk--alg-coef krec (caddr t)))) (cons t 'right))
                                     (#t (walk (caddr t))))))
                        (scan (cdr sides)))))))
        (if node
            (let* ((t (car node)) (left? (eq? (cdr node) 'left))
                   (m (if left? (cadr t) (caddr t)))
                   (new (if left? (ad (ac 1 m) (caddr t)) (ad (cadr t) (ac 1 m))))
                   (e1 (dk--alg-law-eq! krec 'act-one (list m))))
              (dk--alg-vt! krec t) (dk--alg-vt! krec new)
              (dk--alg-say krec "wrap" m)
              (dk-congr! e1 (lambda (h) (if left? (ad h (caddr t)) (ad (cadr t) h))))
              (dk--alg-subst! (list '= t new))
              (loop)))))))
(define (dk--alg-law-eq! krec role args)    ; cite ROLE at ARGS (typed), return the instance
  (let ((sig (cadr (assq role dk--alg-roles))))
    (for-each (lambda (k a) (if (eq? k 'v) (dk--alg-vt! krec a) (dk--alg-ct! a))) sig args))
  (apply dk-cite! (dk--alg-law krec role) (dk--alg-A krec) args))

;;; PHASE 3: sort the spine by word, collect equal words
(define (dk--alg-sort! krec)
  (let ((ad (lambda (x y) (list (dk--alg-head krec 'VADD) x y)))
        (ac (lambda (c x) (list (dk--alg-head krec 'ACT) c x))))
    (let loop ((fuel 4000))
      (if (< fuel 0) (error "dk-alg-norm!: sorting did not terminate"))
      ;; find, on either side, the first spine node VADD(si, rest) with key(si) >= key(s_{i+1})
      (let ((hit
             (let scan ((sides (cdr (dk-goal))))
               (and (pair? sides)
                    (or (let walk ((t (car sides)))
                          (and (dk--alg-op? krec t 'VADD 2)
                               (let* ((si (cadr t)) (rest (caddr t))
                                      (tail? (not (dk--alg-op? krec rest 'VADD 2)))
                                      (sj (if tail? rest (cadr rest))))
                                 (if (string<? (dk--alg-key krec si) (dk--alg-key krec sj))
                                     (walk rest)
                                     (list t si sj tail? (if tail? #f (caddr rest)))))))
                        (scan (cdr sides)))))))
        (if hit
            (let ((t (car hit)) (si (cadr hit)) (sj (caddr hit)) (tail? (cadddr hit)) (rest (car (cddddr hit))))
              (if (string=? (dk--alg-key krec si) (dk--alg-key krec sj))
                  ;; collect: c.w + d.w -> (c + d).w
                  (let ((m (dk--alg-word krec si)) (c (dk--alg-coef krec si)) (d (dk--alg-coef krec sj)))
                    (if tail?
                        (dk--alg-step! krec 'act-add (list c d m) t (ac (list '+ c d) m))
                        (let ((t2 (ad (ad si sj) rest)))
                          (dk--alg-step! krec 'add-assoc (list si sj rest) t t2)
                          (dk--alg-step! krec 'act-add (list c d m) (ad si sj) (ac (list '+ c d) m)))))
                  ;; swap
                  (if tail?
                      (dk--alg-step! krec 'add-comm (list si sj) t (ad sj si))
                      (begin
                        (dk--alg-step! krec 'add-assoc (list si sj rest) t (ad (ad si sj) rest))
                        (dk--alg-step! krec 'add-comm (list si sj) (ad si sj) (ad sj si))
                        (dk--alg-step! krec 'add-assoc (list sj si rest) (ad (ad sj si) rest) (ad sj (ad si rest))))))
              (loop (- fuel 1))))))))

;;; ------------------------------------------------------------------------------------------
;;; SCALAR equalities, on a lane: c = d by crs once every atom is typed in CC
(define (dk--alg-scalar-have! krec c d)
  (let ((claim (list '= c d)))
    (dk--alg-ct! c) (dk--alg-ct! d)
    (dk--alg-say krec "scalar:" claim)
    (dk-have! claim (lambda () (crs)))
    claim))
;;; land (= s1 s2) for two summands of word m, coefficient #f meaning 1
(define (dk--alg-coef-subst! c1 c2)     ; rewrite coefficient c1 into c2 in the goal, oriented by containment
  (if (not (equal? c1 c2))
      (subst (if (dk--occurs? c1 c2) (list '= c2 c1) (list '= c1 c2)))))
(define (dk--alg-summand-eq! krec s1 s2)
  (let* ((m (dk--alg-word krec s1))
         (ac (lambda (c x) (list (dk--alg-head krec 'ACT) c x)))
         (k1 (dk--alg-coef krec s1)) (k2 (dk--alg-coef krec s2))
         (c1 (or k1 1)) (c2 (or k2 1)))
    (dk--alg-vt! krec s1) (dk--alg-vt! krec s2)
    (dk-have! (list '= s1 s2)
      (lambda ()
        ;; the scalar equation first, then the rewrite ON THE GOAL (no nested congruence lane:
        ;; a lane inside this lane drifted focus, kalt-04 of probe 1).  The coefficient that is
        ;; rewritten is always one that OCCURS in the goal, so a bare side never is the FROM.
        (if (not (equal? c1 c2)) (dk--alg-scalar-have! krec c1 c2))
        (cond ((and k1 k2) (dk--alg-coef-subst! c1 c2))
              (k1 (if (not (equal? c1 1)) (subst (list '= c1 1)))      ; s2 = m bare: c1 -> 1
                  (dk--alg-law-eq! krec 'act-one (list m))
                  (subst (list '= (ac 1 m) m)))
              (k2 (if (not (equal? c2 1)) (subst (list '= c2 1)))      ; s1 = m bare
                  (dk--alg-law-eq! krec 'act-one (list m))
                  (subst (list '= (ac 1 m) m))))
        (dk--alg-vt! krec m)
        (rfl)))))
(define (dk--alg-zero-eq! krec s)           ; land (= s VZERO) for a summand with zero coefficient
  (let* ((m (dk--alg-word krec s)) (c (dk--alg-coef krec s))
         (ac (lambda (c x) (list (dk--alg-head krec 'ACT) c x)))
         (Z (dk--alg-head krec 'VZERO)))
    (if (not c) (error "dk-alg-norm!: internal: a bare word with coefficient 1 cannot be zero" (expression->string s)))
    (dk--alg-vt! krec s)
    (dk-have! (list '= s Z)
      (lambda ()
        (dk--alg-scalar-have! krec c 0)
        (subst (list '= c 0))
        (dk--alg-law-eq! krec 'act-zero (list m))
        (subst (list '= (ac 0 m) Z))
        (dk--alg-vt! krec Z)
        (rfl)))))
(define (dk--alg-compare! krec leaf)
  (call-with-current-continuation (lambda (done) (dk--alg-compare-1! krec leaf done))))
(define (dk--alg-compare-1! krec leaf done)
  ;; a landed summand claim may BE the goal: dk-have! then proves it in place and the leaf
  ;; is grounded (kalt-05, kalt-09 of probe 2) -- stop there, reporting 'closed
  (define (closed?) (if (sequent-node-grounded? leaf) (done 'closed)))
  (let* ((g (dk-goal)) (Ls (dk--alg-spine krec (cadr g))) (Rs (dk--alg-spine krec (caddr g)))
         (find (lambda (k ss) (find-first (lambda (s) (string=? (dk--alg-key krec s) k)) ss)))
         (zeroed #f))
    ;; words of one side only: coefficient zero
    (for-each (lambda (pr)
                (for-each (lambda (s)
                            (if (not (find (dk--alg-key krec s) (cdr pr)))
                                (begin (dk--alg-zero-eq! krec s)
                                       (closed?)
                                       (dk--alg-say krec "zero:" s)
                                       (dk--alg-subst! (list '= s (dk--alg-head krec 'VZERO)))
                                       (set! zeroed #t))))
                          (car pr)))
              (list (cons Ls Rs) (cons Rs Ls)))
    (if zeroed #t
        (begin
          (for-each (lambda (s1)
                      (let ((s2 (find (dk--alg-key krec s1) Rs)))
                        (if (not (equal? s1 s2))
                            (begin (dk--alg-summand-eq! krec s1 s2)
                                   (closed?)
                                   (dk--alg-say krec "match:" s1 "->" s2)
                                   (dk--alg-subst! (list '= s1 s2))))))
                    Ls)
          #f))))

;;; ------------------------------------------------------------------------------------------
;;; PHASE 0: the decision, in Scheme.  A polynomial is an alist ((MONO . COEF) ...), MONO a
;;; sorted list of atom strings; the atom terms are kept in a table for conjugation.
(define (dk--alg-cconj z) (if (real? z) z (make-rectangular (real-part z) (- (imag-part z)))))
(define (dk--alg-p-norm p)
  (let loop ((p p) (acc '()))
    (if (null? p)
        (filter (lambda (e) (not (= 0 (cdr e)))) acc)
        (let ((hit (assoc (caar p) acc)))
          (if hit (begin (set-cdr! hit (+ (cdr hit) (cdar p))) (loop (cdr p) acc))
              (loop (cdr p) (cons (cons (caar p) (cdar p)) acc)))))))
(define (dk--alg-p-add p q) (dk--alg-p-norm (append (map (lambda (e) (cons (car e) (cdr e))) p)
                                                  (map (lambda (e) (cons (car e) (cdr e))) q))))
(define (dk--alg-p-mul p q)
  (dk--alg-p-norm
   (append-map (lambda (a) (map (lambda (b) (cons (sort (append (car a) (car b)) string<?) (* (cdr a) (cdr b)))) q)) p)))
(define (dk--alg-p-const k) (if (= k 0) '() (list (cons '() k))))
(define (dk--alg-p-zero? p) (null? (dk--alg-p-norm p)))
(define (dk--alg-p-conj atoms p)         ; atoms: alist string -> term
  (dk--alg-p-norm
   (map (lambda (e)
          (cons (sort (map (lambda (s) (car (dk--alg-atom-conj atoms s))) (car e)) string<?)
                (dk--alg-cconj (cdr e))))
        p)))
(define (dk--alg-atom-conj atoms s)      ; returns (string . term), registering the new atom
  (let* ((t (cdr (assoc s (car atoms))))
         (u (cond ((and (pair? t) (eq? (car t) 'conjugate)) (cadr t))
                  ((dk-asm? (list 'IN t 'RR)) t)
                  (#t (list 'conjugate t))))
         (k (expression->string u)))
    (if (not (assoc k (car atoms))) (set-car! atoms (cons (cons k u) (car atoms))))
    (cons k u)))
(define (dk--alg-scalar-poly atoms t)
  (cond ((number? t) (dk--alg-p-const t))
        ((and (pair? t) (eq? (car t) '+) (= (length t) 3))
         (dk--alg-p-add (dk--alg-scalar-poly atoms (cadr t)) (dk--alg-scalar-poly atoms (caddr t))))
        ((and (pair? t) (eq? (car t) '*) (= (length t) 3))
         (dk--alg-p-mul (dk--alg-scalar-poly atoms (cadr t)) (dk--alg-scalar-poly atoms (caddr t))))
        ((and (pair? t) (eq? (car t) '-) (= (length t) 2))
         (dk--alg-p-mul (dk--alg-p-const -1) (dk--alg-scalar-poly atoms (cadr t))))
        ((and (pair? t) (eq? (car t) '-) (= (length t) 3))
         (dk--alg-p-add (dk--alg-scalar-poly atoms (cadr t))
                        (dk--alg-p-mul (dk--alg-p-const -1) (dk--alg-scalar-poly atoms (caddr t)))))
        ((and (pair? t) (eq? (car t) 'conjugate) (= (length t) 2))
         (dk--alg-p-conj atoms (dk--alg-scalar-poly atoms (cadr t))))
        (#t (if (not (or (dk-asm? (list 'IN t 'CC)) (dk-asm? (list 'IN t 'RR))))
                (error "dk-alg-norm!: a scalar atom is not typed in CC or RR:" (expression->string t)))
            (let ((k (expression->string t)))
              (if (not (assoc k (car atoms))) (set-car! atoms (cons (cons k t) (car atoms))))
              (list (cons (list k) 1))))))
;;; a vector normal form: alist ((WORD . POLY) ...), WORD a list of letter terms
(define (dk--alg-v-norm nf)
  (let loop ((nf nf) (acc '()))
    (if (null? nf)
        (filter (lambda (e) (not (dk--alg-p-zero? (cdr e)))) (reverse acc))
        (let ((hit (assoc (caar nf) acc)))
          (if hit (begin (set-cdr! hit (dk--alg-p-add (cdr hit) (cdar nf))) (loop (cdr nf) acc))
              (loop (cdr nf) (cons (cons (caar nf) (cdar nf)) acc)))))))
(define (dk--alg-vnf krec atoms t)
  (let ((hint (find-first (lambda (h) (equal? (cadr h) t)) (dk--alg-hints krec)))
        (scale (lambda (p nf) (map (lambda (e) (cons (car e) (dk--alg-p-mul p (cdr e)))) nf))))
    (cond (hint (dk--alg-vnf krec atoms (caddr hint)))
          ((dk--alg-const? krec t 'VZERO) '())
          ((dk--alg-const? krec t 'VONE) (list (cons '() (dk--alg-p-const 1))))
          ((dk--alg-op? krec t 'VADD 2) (dk--alg-v-norm (append (dk--alg-vnf krec atoms (cadr t)) (dk--alg-vnf krec atoms (caddr t)))))
          ((dk--alg-op? krec t 'VNEG 1) (scale (dk--alg-p-const -1) (dk--alg-vnf krec atoms (cadr t))))
          ((dk--alg-op? krec t 'ACT 2) (dk--alg-v-norm (scale (dk--alg-scalar-poly atoms (cadr t)) (dk--alg-vnf krec atoms (caddr t)))))
          ((dk--alg-op? krec t 'VMUL 2)
           (let ((p (dk--alg-vnf krec atoms (cadr t))) (q (dk--alg-vnf krec atoms (caddr t))))
             (dk--alg-v-norm (append-map (lambda (a) (map (lambda (b) (cons (append (car a) (car b))
                                                                            (dk--alg-p-mul (cdr a) (cdr b)))) q)) p))))
          ((dk--alg-op? krec t 'VSTAR 1)
           (let ((p (dk--alg-vnf krec atoms (cadr t))))
             (dk--alg-v-norm
              (append-map (lambda (e)
                            (let ((pc (dk--alg-p-conj atoms (cdr e))))
                              ;; star of a word: reversed, each letter starred (and re-normalised by hints)
                              (let loop ((ls (reverse (car e))) (acc (list (cons '() pc))))
                                (if (null? ls) acc
                                    (let* ((l (car ls))
                                           (sl (if (dk--alg-op? krec l 'VSTAR 1) (cadr l) (list (dk--alg-head krec 'VSTAR) l)))
                                           (sh (find-first (lambda (h) (equal? (cadr h) sl)) (dk--alg-hints krec)))
                                           ;; a starred letter is a letter: re-entering vnf on (VSTAR x)
                                           ;; would star x again, forever (kalt-12, probe 2)
                                           (lnf (if sh (dk--alg-vnf krec atoms (caddr sh))
                                                    (list (cons (list sl) (dk--alg-p-const 1))))))
                                      (loop (cdr ls)
                                            (dk--alg-v-norm
                                             (append-map (lambda (a) (map (lambda (b) (cons (append (car a) (car b))
                                                                                            (dk--alg-p-mul (cdr a) (cdr b)))) lnf)) acc))))))))
                          p))))
          ((dk--alg-vecop? krec t) (error "dk-alg-norm!: an operation of A with the wrong arity:" (expression->string t)))
          (#t (if (not (dk-asm? (list 'IN t (dk--alg-vec krec))))
                  (error "dk-alg-norm!: a vector atom is not typed in (VEC A):" (expression->string t)))
              (list (cons (list t) (dk--alg-p-const 1)))))))
;;; #t, or the list of words whose coefficients differ (each with the two polynomials)
(define (dk--alg-decide krec l r)
  (let* ((atoms (list '()))
         (nl (dk--alg-vnf krec atoms l)) (nr (dk--alg-vnf krec atoms r))
         (words (let loop ((ws (append (map car nl) (map car nr))) (acc '()))
                  (cond ((null? ws) (reverse acc)) ((member (car ws) acc) (loop (cdr ws) acc))
                        (#t (loop (cdr ws) (cons (car ws) acc))))))
         (bad (filter (lambda (w)
                        (let ((pl (let ((h (assoc w nl))) (if h (cdr h) '())))
                              (pr (let ((h (assoc w nr))) (if h (cdr h) '()))))
                          (not (dk--alg-p-zero? (dk--alg-p-add pl (dk--alg-p-mul (dk--alg-p-const -1) pr))))))
                      words)))
    (if (null? bad) #t
        (map (lambda (w) (list w (let ((h (assoc w nl))) (if h (cdr h) '()))
                               (let ((h (assoc w nr))) (if h (cdr h) '()))))
             bad))))

;;; ------------------------------------------------------------------------------------------
;;; THE ENTRY POINTS
(define (dk--alg-make prefix A opts)
  (let loop ((o opts) (hints '()) (trace #f))
    (cond ((null? o) (list A prefix (map ->raw-formula hints) trace))
          ((and (eq? (car o) 'hints) (pair? (cdr o))) (loop (cddr o) (cadr o) trace))
          ((and (eq? (car o) 'trace) (pair? (cdr o))) (loop (cddr o) hints (cadr o)))
          (#t (error "dk-alg-norm!: unknown option" (car o))))))
;;; (dk-alg-identity? PREFIX A L R . OPTS) -- the decision alone: #t or the differing words
(define (dk-alg-identity? prefix A l r . opts)
  (dk--alg-decide (dk--alg-make prefix A opts) (->raw-formula l) (->raw-formula r)))
;;; (dk-alg-norm! PREFIX A . OPTS) -- prove the focus goal (= L R); returns #t
(define (dk-alg-norm! prefix A . opts)
  (let* ((krec (dk--alg-make prefix A opts))
         (g (dk-goal))
         (leaf (proof-state-focus *ps*)))
    (if (not (and (pair? g) (eq? (car g) '=) (= (length g) 3)))
        (error "dk-alg-norm!: the goal is not an equation" (expression->string g)))
    (for-each (lambda (h) (if (not (dk-asm? h)) (error "dk-alg-norm!: a hint is not in context:" (expression->string h))))
              (dk--alg-hints krec))
    (let ((verdict (dk--alg-decide krec (cadr g) (caddr g))))
      (if (not (eq? verdict #t))
          (error "dk-alg-norm!: REFUSED -- not an identity of the algebra; the coefficients differ at the word(s):"
                 (map (lambda (b) (list (expression->string (car b)) (cadr b) (caddr b))) verdict))))
    (let loop ((round 0))
      (if (> round 50) (error "dk-alg-norm!: the compare loop did not terminate"))
      (dk--alg-expand! krec)
      (dk--alg-wrap! krec)
      (dk--alg-sort! krec)
      (let ((r (dk--alg-compare! krec leaf)))
        (cond ((eq? r 'closed) 'closed)
              (r (loop (+ round 1)))
              (#t (let ((g2 (dk-goal)))
      (if (not (equal? (cadr g2) (caddr g2)))
          (error "dk-alg-norm!: internal: the normal forms differ after the compare" (expression->string g2)))
                    (dk--alg-vt! krec (cadr g2))
                    (rfl))))))
    (if (not (sequent-node-grounded? leaf))
        (error "dk-alg-norm!: the goal did not close" (expression->string g)))
    #t))
;;; (dk-alg-have! PREFIX A CLAIM . OPTS) -- land the equation CLAIM, proved by dk-alg-norm!
(define (dk-alg-have! prefix A claim . opts)
  (dk-have! claim (lambda () (apply dk-alg-norm! prefix A opts)))
  (->raw-formula claim))

;;; ------------------------------------------------------------------------------------------
;;; (dk-cc-norm! . OPTS) -- THE SCALAR FINISHER.  The focus goal is an equation over CC whose
;;; atoms are typed in CC or RR in context.  Conjugates are pushed in by the CC axioms
;;; (cc-conjugate-add / -mul / -neg / -sub / -involution / -i, cc-conjugate-fixes-rr at a real
;;; number or an atom typed in RR), both sides are typed in CC, and `crs' closes the
;;; commutative-ring identity (i*i = -1 is native to it).  Errors when the goal does not close.
;;; OPTS: 'trace #t.  An atom left under a conjugate (conjugate(u), u not known real) stays an
;;; opaque atom of crs: the identity must hold with it as an independent variable.
(define (dk--cc-find krec t)
  (or (and (pair? t) (let loop ((ts (cdr t)))
                       (and (pair? ts) (or (dk--cc-find krec (car ts)) (loop (cdr ts))))))
      (dk--alg-conj-redex krec t)))
(define (dk-cc-norm! . opts)
  (let ((krec (dk--alg-make #f #f opts))
        (g (dk-goal))
        (leaf (proof-state-focus *ps*)))
    (if (not (and (pair? g) (eq? (car g) '=) (= (length g) 3)))
        (error "dk-cc-norm!: the goal is not an equation" (expression->string g)))
    (let loop ((n 0))
      (if (> n 500) (error "dk-cc-norm!: conjugate pushing did not terminate"))
      (let ((r (dk--cc-find krec (dk-goal))))
        (if r (begin (r) (loop (+ n 1))))))
    (if (not (sequent-node-grounded? leaf))
        (let ((g2 (dk-goal)))
          (dk--alg-ct! (cadr g2)) (dk--alg-ct! (caddr g2))
          (crs)))
    (if (not (sequent-node-grounded? leaf))
        (error "dk-cc-norm!: crs did not close" (expression->string (dk-goal))))
    #t))
;;; (dk-alg-type! PREFIX A T) -- land (IN T (VEC A)) for a term of the algebra built from typed
;;; atoms, by the typing laws PREFIX-vadd-in ... (a scalar coefficient typed in CC on the way)
(define (dk-alg-type! prefix A t . opts)
  (dk--alg-vt! (dk--alg-make prefix A opts) (->raw-formula t))
  (list 'IN (->raw-formula t) (list 'VEC A)))
;;; (dk-cc-type! T) -- land (IN T CC) for a scalar built by + * - conjugate from typed atoms
(define (dk-cc-type! t) (dk--alg-ct! (->raw-formula t)) (list 'IN (->raw-formula t) 'CC))

;;; =======================================================================
;;; THE VIEW TYPING DRIVER (D8, 2026-11-15; the user's decision "Prove views").
;;;
;;; def-functor (structures.scm) no longer installs its typing axiom
;;;     V-is-T :  forall r. IS-S(r) => IS-T(V r)
;;; as a `definitional' fact; it POSTS it, and this driver PROVES it.
;;;
;;; (dk-view-typing! V)       open, drive and close V's typing obligation through
;;;                           dk-sp-qed!, then hand the new theorem to the views
;;;                           declared after V (view-typing-installed!).  Errors when
;;;                           the generic driver leaves a leaf open.  Returns the name.
;;; (dk-view-close! V [T])    on a focus goal IS-T(V x) with IS-S(x) in context
;;;                           (T defaults to V's target; an ANCESTOR of it may be
;;;                           named), drive the goal and return the leaves left open
;;;                           (empty: closed).  A hand proof of a deferred obligation
;;;                           calls this and closes what it returns.
;;;
;;; THE METHOD, in order:
;;;  1. the SOURCE is expanded: every conjunct of IS-S(x) is landed by a lane
;;;     (dk-project!: IS-S(x) survives), recursively into a parent conjunct and into
;;;     a structure predicate of a literal LIST (UBA's is-cba([scal(s), ...])), and
;;;     every def-predicate hypothesis (is-measure, ...) is opened the same way;
;;;  2. COMPOSITION: for a source conjunct IS-X(t) and a view W : X -> T whose
;;;     typing is installed, W's typing is cited at t;
;;;  3. the goal is MATCHED against a hypothesis equal to it up to NORMALISATION
;;;     (accessors read off literal lists, views unfolded): the differing closed
;;;     subterm pairs are proved equal on lanes (dk-vt--eq-lane!) and the
;;;     HYPOTHESIS is rewritten (dk-rewrite-h!) -- never the goal, whose terms are
;;;     the smaller ones -- and `ass' closes;
;;;  4. else the target is unfolded to its shape level (refinements through their
;;;     parent), dk-isx-set! takes the sethood conjunct, and each conjunct is read
;;;     off (slot / view unfold / nth-r) and closed by `ass', the LENGTH by len-r,
;;;     a symmetric `not(a = b)' by neq-sym, a match (3), a property or predicate
;;;     unfolded, or -- for a universal -- peeled, split and closed piecewise by a
;;;     universal hypothesis instantiated where its body MATCHES the piece.
;;; Nothing is asserted; every step is a recorded surface tactic.  The read-off of
;;; an accessor applied to a literal list goes through an equation proved by `slot'
;;; to its fixpoint, then `subst': a global `slot' would also rewrite the accessor
;;; inside the list's own components, and nth-r would then owe the denotation of a
;;; list of NTHs, which the certificate does not see.

(define (dk-vt--try thunk)
  (call-with-current-continuation
    (lambda (k) (with-exception-handler
                  (lambda (e) (k (if (condition? e) (condition/report-string e) (list 'raised e))))
                  (lambda () (thunk) #f)))))
(define (dk-vt--loud what thunk)        ; dk-vt--try, saying what failed
  (let ((why (dk-vt--try thunk)))
    (if why (begin (display ";; dk-view: ") (display what) (display " did not go through: ")
                   (display why) (newline)))
    why))
(define (dk-vt--def-name x)
  (if (lookup-structure x) (symbol-append 'IS- x) (symbol-append 'is- x '-def)))
(define (dk-vt--parent x)
  (let ((d (lookup-definitional-structure x))) (and d (definitional-structure-parent d))))
(define (dk-vt--struct-of-pred h)        ; an IS-X head -> X, when X is a declared structure
  (and (symbol? h)
       (let ((s (symbol->string h)))
         (and (> (string-length s) 3) (string=? (substring s 0 3) "is-")
              (let ((x (string->symbol (substring s 3 (string-length s)))))
                (and (or (lookup-structure x) (lookup-definitional-structure x)) x))))))
(define (dk-vt--definiens x t)
  (let ((f (hash-table-ref/default *theorem-table* (dk-vt--def-name x) #f)))
    (subst-free (quantifier-var f) t (caddr (quantifier-body f)))))
(define (dk-vt--conjs f)
  (if (dk-head-is? f 'AND) (append (dk-vt--conjs (cadr f)) (dk-vt--conjs (caddr f))) (list f)))
;; the definiens of a def-predicate application (P a1 .. an), or #f
(define (dk-vt--pred-def f)
  (and (pair? f) (symbol? (car f)) (not (dk-vt--struct-of-pred (car f)))
       (let ((d (hash-table-ref/default *theorem-table* (car f) #f)))
         (and d (let loop ((d d) (args (cdr f)))
                  (cond ((and (dk-head-is? d 'FORALL) (pair? args))
                         (loop (subst-free (quantifier-var d) (car args) (quantifier-body d)) (cdr args)))
                        ((and (null? args) (dk-head-is? d 'IFF) (dk-head-is? (cadr d) (car f))) (caddr d))
                        (#t #f)))))))
;; THE EXPANSION IN ONE PASS (D8b, 2026-11-15; finding V1).  The definiens of a
;; predicate hypothesis H is landed WHOLE by one lane (dk-project!: mac-h, then
;; `ass' on the lane) and split ONCE on the main branch; H survives.  The first
;; version projected each conjunct by its own lane, and every lane's closer
;; (dk--lane-close-at!) split EVERY conjunction in the lane's context -- a cubic
;; number of `ai' steps, each scanning the context: in a load, with a context of
;; some hundred formulas, one expansion of IS-INTEGRAL-DOMAIN took 64 s and one
;; view typing ten minutes.  A definiens that is not a conjunction keeps the
;; one-conjunct lane.
(define (dk-vt--land-definiens! d opener h)
  (let ((cs (dk-vt--conjs d)))
    (if (any-pred (lambda (c) (not (dk-asm? c))) cs)
        (begin
          (if (dk-head-is? d 'AND)
              (dk-vt--try (lambda ()
                            (let ((f (dk-project! d opener h)))
                              (if (and (pair? f) (dk-asm? f)) (dk-split-all! (list f)))))))
          ;; a conjunct the whole lane did not land (or a definiens that is not a
          ;; conjunction): its own lane, as before
          (for-each (lambda (c) (if (not (dk-asm? c)) (dk-vt--try (lambda () (dk-project! c opener h)))))
                    cs)))
    cs))
(define (dk-vt--expand! x t depth)
  (let ((h (list (symbol-append 'IS- x) t)))
    (for-each
      (lambda (c)
        (let ((y (and (pair? c) (= (length c) 2) (dk-vt--struct-of-pred (car c)))))
          (if (and y (dk-asm? c) (< depth 3)
                   (or (equal? (cadr c) t) (dk-head-is? (cadr c) 'LIST)))
              (dk-vt--expand! y (cadr c) (+ depth 1)))))
      (dk-vt--land-definiens! (dk-vt--definiens x t) (dk-vt--def-name x) h))))
(define (dk-vt--expand-preds!)
  (for-each (lambda (f)
              (let ((b (dk-vt--pred-def f)))
                (if b (dk-vt--land-definiens! b (car f) f))))
            (dk-asms)))
;;; ---- the symbolic normal form: accessors to NTH, views unfolded, NTH of a LIST reduced
(define (dk-vt--view-unfold e)
  (let ((v (and (pair? e) (symbol? (car e)) (= (length e) 2) (lookup-view-as (car e)))))
    (and v (cons 'LIST (map (lambda (c) (view-as-comp-at c (cadr e))) (view-as-source-comps v))))))
(define (dk-vt--accessor? a)
  (and (symbol? a) (eq? (constant-head? a) 'accessor) (hash-table-ref/default *accessor-index* a #f)))
(define (dk-vt--norm e)
  (cond ((not (pair? e)) e)
        (#t (let ((e (map dk-vt--norm e)))
              (cond ((and (= (length e) 2) (dk-vt--accessor? (car e)))
                     (let ((k (car (dk-vt--accessor? (car e)))) (x (cadr e)))
                       (if (and (dk-head-is? x 'LIST) (<= k (length (cdr x)))) (list-ref x k) (list 'NTH k x))))
                    ((dk-vt--view-unfold e) => dk-vt--norm)
                    (#t e))))))
(define (dk-vt--views-in e)
  (let ((acc '()))
    (let walk ((e e))
      (if (pair? e)
          (begin (if (and (symbol? (car e)) (lookup-view-as (car e)) (not (memq (car e) acc)))
                     (set! acc (cons (car e) acc)))
                 (for-each walk e))))
    acc))
(define (dk-vt--nth-redex? e)
  (and (pair? e) (or (and (eq? (car e) 'NTH) (= (length e) 3) (dk-head-is? (caddr e) 'LIST))
                     (any-pred dk-vt--nth-redex? e))))
(define (dk-vt--acc-on-list e)           ; the first subterm (ACC (LIST ..)), or #f
  (cond ((not (pair? e)) #f)
        ((and (= (length e) 2) (dk-vt--accessor? (car e)) (dk-head-is? (cadr e) 'LIST)) e)
        (#t (let loop ((xs e))
              (cond ((null? xs) #f)
                    ((dk-vt--acc-on-list (car xs)) => (lambda (x) x))
                    (#t (loop (cdr xs))))))))
;; slot ACC to the fixpoint of an (== A B) goal, then qrfl
(define (dk-vt--slot-fix! acc)
  (let loop ((k 0))
    (let ((g (dk-goal)))
      (cond ((alpha-equiv? (cadr g) (caddr g)) (qrfl))
            ((> k 5) (error "dk-vt--slot-fix!: no fixpoint" (expression->string g)))
            (#t (slot acc)
                (if (equal? g (dk-goal)) (error "dk-vt--slot-fix!: slot changed nothing" (expression->string g)))
                (loop (+ k 1)))))))
;; on a lane whose goal is (== A B), A and B equal up to normalisation
(define (dk-vt--eq-lane!)
  (let ((leaf (proof-state-focus *ps*)))
    (let loop ((k 0))
      (if (not (sequent-node-grounded? leaf))
          (let ((g (dk-goal)))
            (cond ((alpha-equiv? (cadr g) (caddr g)) (qrfl))
                  ((> k 40) (error "dk-vt--eq-lane!: no fixpoint" (expression->string g)))
                  ((dk-vt--nth-redex? g) (nth-r) (loop (+ k 1)))
                  ((pair? (dk-vt--views-in g)) (for-each (lambda (v) (mac v)) (dk-vt--views-in g)) (loop (+ k 1)))
                  ((dk-vt--acc-on-list g)
                   => (lambda (t)
                        (let* ((kx (car (dk-vt--accessor? (car t))))
                               (nt (list 'NTH kx (cadr t)))
                               (e  (list '== t nt)))
                          (if (not (dk-asm? e)) (dk-have! e (lambda () (dk-vt--slot-fix! (car t)))))
                          (subst (list '= t nt))
                          (loop (+ k 1)))))
                  (#t (error "dk-vt--eq-lane!: stuck" (expression->string g)))))))
    (if (not (sequent-node-grounded? leaf))
        (error "dk-vt--eq-lane!: open" (map (lambda (l) (expression->string (dk-goal-of l))) (dk-open-leaves))))))
;;; ---- the parallel diff of a goal G against a hypothesis H
(define *dk-vt--connectives* '(AND OR IMPLIES IFF NOT))
(define *dk-vt--term-binders* '(SEP IOTA VNB-LAMBDA BIG-UNION COMP))
(define (dk-vt--mentions-any? e vs)
  (cond ((symbol? e) (memq e vs)) ((pair? e) (any-pred (lambda (x) (dk-vt--mentions-any? x vs)) e)) (#t #f)))
(define (dk-vt--rename-binder g v)
  (if (eq? (cadr g) v) g (cons (car g) (cons v (map (lambda (x) (subst-free (cadr g) v x)) (cddr g))))))
(define (dk-vt--all ds) (and (every (lambda (x) x) ds) (apply append ds)))
(define (dk-vt--diff g h bound)          ; formula position: a list of (g-term . h-term), or #f
  (cond ((equal? g h) '())
        ((not (and (pair? g) (pair? h) (eq? (car g) (car h)) (= (length g) (length h)))) #f)
        ((memq (car g) *dk-vt--connectives*)
         (dk-vt--all (map (lambda (a b) (dk-vt--diff a b bound)) (cdr g) (cdr h))))
        ((memq (car g) '(FORALL FORSOME))
         (and (symbol? (cadr g)) (symbol? (cadr h))
              (let ((g2 (dk-vt--rename-binder g (cadr h))))
                (dk-vt--diff (caddr g2) (caddr h) (cons (cadr h) bound)))))
        (#t (dk-vt--all (map (lambda (a b) (dk-vt--diff-t a b bound)) (cdr g) (cdr h))))))
(define (dk-vt--diff-t g h bound)        ; term position
  (cond ((equal? g h) '())
        ((and (not (dk-vt--mentions-any? g bound)) (not (dk-vt--mentions-any? h bound))
              (equal? (dk-vt--norm g) (dk-vt--norm h)))
         (list (cons g h)))
        ((not (and (pair? g) (pair? h) (= (length g) (length h)))) #f)
        ((and (memq (car g) '(SEP IOTA)) (eq? (car g) (car h)) (symbol? (cadr g)) (symbol? (cadr h)))
         (let ((g2 (dk-vt--rename-binder g (cadr h))) (b2 (cons (cadr h) bound)))
           (if (= (length g) 4)
               (dk-vt--all (list (dk-vt--diff-t (caddr g2) (caddr h) bound) (dk-vt--diff (cadddr g2) (cadddr h) b2)))
               (dk-vt--diff (caddr g2) (caddr h) b2))))
        ((and (memq (car g) '(VNB-LAMBDA BIG-UNION)) (eq? (car g) (car h)) (= (length g) 4)
              (symbol? (cadr g)) (symbol? (cadr h)))
         (let ((g2 (dk-vt--rename-binder g (cadr h))) (b2 (cons (cadr h) bound)))
           (dk-vt--all (list (dk-vt--diff-t (caddr g2) (caddr h) bound) (dk-vt--diff-t (cadddr g2) (cadddr h) b2)))))
        ((and (symbol? (car g)) (memq (car g) *dk-vt--term-binders*)) #f)
        (#t (dk-vt--all (map (lambda (a b) (dk-vt--diff-t a b bound)) g h)))))
;; close the focus goal from the hypothesis that differs from it least (up to
;; normalisation); #t when the start leaf is grounded
(define (dk-vt--match!)
  (let* ((leaf (proof-state-focus *ps*)) (g (dk-goal))
         (cands (filter (lambda (c) (cdr c))
                        (map (lambda (h) (cons h (and (pair? h) (pair? g) (eq? (car h) (car g)) (dk-vt--diff g h '()))))
                             (dk-asms))))
         (best (and (pair? cands)
                    (fold-left (lambda (b c) (if (< (length (cdr c)) (length (cdr b))) c b)) (car cands) (cdr cands)))))
    (if best
        (let ((why (dk-vt--try
                    (lambda ()
                      ;; each pair is rewritten toward its SMALLER side: the goal's term
                      ;; when the goal's term contains the hypothesis' (the hypothesis is
                      ;; then rewritten), else the goal (subst): a rewrite whose result
                      ;; contains the term it replaces would rewrite its own result
                      (let loop ((ps (cdr best)) (hh (car best)))
                        (if (pair? ps)
                            (let* ((p (car ps)) (g1 (car p)) (h1 (cdr p)) (e (list '== g1 h1)))
                              (if (not (dk-asm? e)) (dk-have! e dk-vt--eq-lane!))
                              (cond ((dk-contains? g1 h1)
                                     (if (dk-contains? (dk-goal) g1) (subst (list '= g1 h1)))
                                     (loop (cdr ps) hh))
                                    (#t (loop (cdr ps) (if (dk-contains? hh h1) (dk-rewrite-h! hh h1 g1) hh)))))))
                      (if (not (sequent-node-grounded? leaf)) (ass))))))
          (if why (begin (display ";; dk-view: a match did not go through: ") (display why) (newline)))))
    (sequent-node-grounded? leaf)))
;;; ---- a universal hypothesis whose body matches the goal
(define (dk-vt--univ-parts h)
  (let loop ((h h) (vs '()))
    (cond ((dk-head-is? h 'FORALL) (loop (caddr h) (cons (cadr h) vs)))
          ((and (dk-head-is? h 'IMPLIES) (pair? vs) (dk-head-is? (cadr h) 'IN) (memq (cadr (cadr h)) vs))
           (loop (caddr h) vs))
          (#t (cons (reverse vs) h)))))
(define (dk-vt--inst-guards h ts)       ; the (IN t D) guards of h instantiated at ts
  (let loop ((h h) (ts ts) (acc '()))
    (cond ((and (dk-head-is? h 'FORALL) (pair? ts))
           (loop (subst-free (cadr h) (car ts) (caddr h)) (cdr ts) acc))
          ((and (dk-head-is? h 'IMPLIES) (dk-head-is? (cadr h) 'IN))
           (loop (caddr h) ts (cons (cadr h) acc)))
          (#t (reverse acc)))))
(define (dk-vt--pmatch p e vs binds)
  (cond ((not binds) #f)
        ((and (symbol? p) (memq p vs))
         (let ((b (assq p binds)))
           (cond ((not b) (cons (cons p e) binds)) ((equal? (cdr b) e) binds) (#t #f))))
        ((and (pair? p) (pair? e) (= (length p) (length e)))
         (let loop ((ps p) (es e) (bs binds))
           (if (null? ps) bs (loop (cdr ps) (cdr es) (dk-vt--pmatch (car ps) (car es) vs bs)))))
        ((equal? p e) binds)
        (#t #f)))
(define (dk-vt--univ!)
  (let* ((leaf (proof-state-focus *ps*)) (g (dk-goal)) (ng (dk-vt--norm g))
         (hit (let loop ((hs (dk-asms)))
                (if (null? hs) #f
                    (let* ((h (car hs)) (pp (and (dk-head-is? h 'FORALL) (dk-vt--univ-parts h)))
                           (bs (and pp (pair? (car pp)) (dk-vt--pmatch (dk-vt--norm (cdr pp)) ng (car pp) '()))))
                      (if (and bs (= (length bs) (length (car pp)))) (cons h (map (lambda (v) (cdr (assq v bs))) (car pp)))
                          (loop (cdr hs))))))))
    (if hit
        (begin
          ;; the guards of the instance, typed in the hypothesis' own spelling (a
          ;; universal read off a literal list guards on vec([..]), the goal's
          ;; eigenvariable is typed on vec(r)): each one not in context is MATCHED first
          (for-each (lambda (gd)
                      (if (not (dk-asm? gd))
                          (dk-vt--try (lambda () (dk-have! gd (lambda () (dk-vt--match!)))))))
                    (dk-vt--inst-guards (car hit) (cdr hit)))
          (dk-vt--try (lambda () (apply dk-apply! hit)))
          (if (not (sequent-node-grounded? leaf))
              (if (dk-asm? (dk-goal)) (ass) (dk-vt--match!)))))
    (sequent-node-grounded? leaf)))
(define (dk-vt--goal-leaves!)            ; split an AND focus goal to its non-AND leaves
  (let ((leaf (proof-state-focus *ps*)))
    (if (dk-head-is? (dk-goal) 'AND)
        (let ((ls (dk-opened (lambda () (di)))))
          (append-map (lambda (l) (dk-focus! l) (dk-vt--goal-leaves!)) ls))
        (list leaf))))
(define (dk-vt--deep! . depth0)           ; peel, split, close each piece (pieces recursively)
  (let ((depth (if (pair? depth0) (car depth0) 0)))
    (dk-vt--loud "a piece" (lambda ()
      (if (memq (car (dk-goal)) '(FORALL IMPLIES)) (dk-peel!))
      (for-each (lambda (l)
                  (if (not (sequent-node-grounded? l))
                      (begin (dk-focus! l)
                             (cond ((dk-asm? (dk-goal)) (ass))
                                   ((dk-vt--match!) #t)
                                   ((dk-vt--univ!) #t)
                                   ((and (< depth 3) (pair? (dk-goal)) (memq (car (dk-goal)) '(FORALL IMPLIES AND)))
                                    (dk-vt--deep! (+ depth 1)))
                                   (#t #f)))))
                (dk-vt--goal-leaves!))))))
(define (dk-vt--close-leaf! leaf view accs)
  (define (done?) (sequent-node-grounded? leaf))
  (dk-focus! leaf)
  (for-each (lambda (a) (if (dk-contains? (dk-goal) a) (slot a))) accs)
  (if (dk-contains? (dk-goal) view) (mac view))
  (let loop ((k 0)) (if (and (< k 6) (dk-vt--nth-redex? (dk-goal))) (begin (nth-r) (loop (+ k 1)))))
  (if (not (done?))
      (let ((g (dk-goal)))
        (cond ((dk-asm? g) (ass))
              ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'LENGTH)) (len-r) (if (not (done?)) (rfl)))
              ((and (dk-head-is? g 'NOT) (dk-head-is? (cadr g) '=)
                    (dk-asm? (list 'NOT (list '= (caddr (cadr g)) (cadr (cadr g))))))
               (fact 'neq-sym (caddr (cadr g)) (cadr (cadr g))) (ass))
              (#t (dk-vt--match!)))))
  (if (and (not (done?)) (dk-vt--pred-def (dk-goal)))
      (begin (dk-vt--try (lambda () (mac (car (dk-goal)))))
             (if (not (done?)) (if (dk-asm? (dk-goal)) (ass) (dk-vt--match!)))))
  (if (and (not (done?)) (pair? (dk-goal)) (memq (car (dk-goal)) '(FORALL IMPLIES AND)))
      (dk-vt--deep!))
  (done?))
(define (dk-vt--compose! view tgt)
  (for-each
    (lambda (h)
      (let ((x (and (pair? h) (= (length h) 2) (dk-vt--struct-of-pred (car h)))))
        (if x
            (for-each
              (lambda (w)
                (let ((wv (lookup-view-as w)))
                  (if (and (not (eq? w view)) (eq? (view-as-source-struct wv) x)
                           (eq? (view-as-target-struct wv) tgt))
                      (let ((thm (view-typing-name w)))
                        (if (hash-table-ref/default *theorem-table* thm #f)
                            (dk-vt--try (lambda () (dk-cite! thm (cadr h)))))))))
              *view-as-order*))))
    (dk-asms)))
(define (dk-view-close! view . opt)
  (let* ((v   (or (lookup-view-as view) (error "dk-view-close!: not a view" view)))
         (src (view-as-source-struct v))
         (tgt (if (pair? opt) (car opt) (view-as-target-struct v)))
         (accs (map car (structure-def-slots (find-shape-structure tgt))))
         (g0  (dk-goal))
         (x   (if (and (pair? g0) (= (length g0) 2) (dk-head-is? (cadr g0) view)) (cadr (cadr g0))
                  (error "dk-view-close!: the focus goal is not IS-T(V x) for" view (expression->string g0))))
         (top (proof-state-focus *ps*)))
    (if (not (dk-asm? (list (symbol-append 'IS- src) x)))
        (error "dk-view-close!: the source predicate is not in context" (list (symbol-append 'IS- src) x)))
    (let ((opened
           (dk-opened
            (lambda ()
              (dk-vt--expand! src x 0)
              (dk-vt--expand-preds!)
              (dk-vt--compose! view tgt)
              ;; the lanes above moved the main branch to a NEW leaf: stay on it
              (if (not (dk-vt--match!))
                  (let unfold ((y tgt))
                    (mac (dk-vt--def-name y))
                    (if (not (lookup-structure y))
                        (for-each (lambda (l)
                                    (if (dk-head-is? (dk-goal-of l) (symbol-append 'IS- (dk-vt--parent y)))
                                        (begin (dk-focus! l)
                                               (if (not (dk-vt--match!)) (unfold (dk-vt--parent y))))
                                        (dk-vt--close-leaf! l view accs)))
                                  (dk-vt--goal-leaves!))
                        (begin (dk-isx-set!)
                               (for-each (lambda (l) (dk-vt--close-leaf! l view accs)) (dk-vt--goal-leaves!))))))))))
      (let ((left (filter (lambda (l) (not (sequent-node-grounded? l))) opened)))
        (cond ((sequent-node-grounded? top) '())
              ((pair? left) (dk-focus! (car left)) left)
              (#t (list (proof-state-focus *ps*))))))))
(define (dk-view-typing! view)
  (let ((name (or (view-typing-name view) (error "dk-view-typing!: not a view" view))))
    (if (not (hash-table-ref/default *theorem-table* name #f))
        (dk-sp-qed! (view-obligation view)
          (lambda ()
            (dk-peel!)
            (let ((left (dk-view-close! view)))
              (if (pair? left)
                  (error "dk-view-typing!: the generic driver left open:" view
                         (map (lambda (l) (expression->string (dk-goal-of l))) left)))))
          name))
    (view-typing-installed! view)
    name))
