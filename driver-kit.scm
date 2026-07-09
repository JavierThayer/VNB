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
;;; Arm the containment.  From here on prover-load gives every theorem-library/
;;; and calculus/ file its own top-level environment (load.scm).
(define *driver-kit-env* (the-environment))
(set! *contain-proof-files?* #t)
(display ";; driver-kit: proof files from here on load in private environments")
(newline)
