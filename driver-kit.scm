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

(define (proof-leaves)
  (filter (lambda (sqn) (and (not (sequent-node-grounded? sqn))
                             (null? (sequent-node-in-arrows sqn))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))

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
(define (dk-focus! node) (set-proof-state-focus! *ps* node) node)
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
(define (have! form . opt)
  (let* ((thunk (and (pair? opt) (car opt)))
         (new  (dk-opened (lambda () (cut form))))
         (side (or (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) form)) new)
                   (error "have!: no side goal for" form)))
         (main (or (any-pred (lambda (s) (not (eq? s side))) new)
                   (error "have!: no main branch (CLAIM already in context up to alpha?)" form))))
    (dk-focus! side) (if thunk (thunk) (from-context!)) (dk-focus! main) main))

;;; -----------------------------------------------------------------------
;;; Arm the containment.  From here on prover-load gives every theorem-library/
;;; and calculus/ file its own top-level environment (load.scm).
(define *driver-kit-env* (the-environment))
(set! *contain-proof-files?* #t)
(display ";; driver-kit: proof files from here on load in private environments")
(newline)
