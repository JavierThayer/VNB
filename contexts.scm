;;; contexts.scm -- make-wff, the interactive entry point for building a <wff>
;;;
;;; This file used to carry a LOCAL CONTEXT facility as well: declare-local-
;;; context conjured a named instance of a structure into the session,
;;; make-wff snapshotted the active stack into the <wff>, start-proof turned
;;; those bindings into root assumptions of the proof, and `unravel' folded
;;; them back into destructuring FORALLs.  It was removed on 2026-07-29.
;;;
;;; The reason was not that it was broken -- it worked, and the manual
;;; documented it at section length.  It was that NOTHING USED IT.  `unravel'
;;; had no callers at all, not even a test; declare-local-context had callers
;;; only in test-suite.scm, where it served as a convenient way to get an
;;; assumption into a root sequent.  Every proof in structure-library/ and
;;; theorem-library/ states its hypotheses explicitly instead.  The manual
;;; sections that described it were also wrong in three particulars (a base
;;; theory named `normal-math', which does not exist -- it is VNB-SET-THEORY;
;;; an `extend-theory' that does not exist; and a get-context returning a
;;; qualified name when it returned a binding), which is what a facility with
;;; no users looks like after a few years.
;;;
;;; What survives here is make-wff itself, which never needed the stack.
;;; ====================================================================

;;; When #t, make-wff REJECTS a formula that binds a variable whose case-folded
;;; name is a registered constant (accessor / operator / functoid / predicate)
;;; -- the interactive counterpart of the load-time constant-binder-audit.
;;;
;;; It used to shout and hand the wff back anyway.  That made the rule a
;;; discouragement you could walk past: `(FORALL carr (FORALL add ...))', with
;;; add(mul(q,b),r) in its body, would sail through make-wff and be accepted by
;;; theory-add-axiom!.  In head position (add ...) reads as the CONSTANT, not
;;; the bound variable -- the binder is scope-blind, and the formula does not
;;; mean what it looks like.  There is no legitimate use, so it is now an error
;;; and such a wff cannot be built at all.  constant-binder-audit reports the
;;; library clean, so nothing real was relying on the old leniency.
;;;
;;; Left #f during the library load (set #t at the end of load.scm) so it fires
;;; only for user-constructed wffs, and so it never runs before
;;; wff-constant-binders (macetes.scm) is defined.
(define *reject-constant-binders?* #f)

(define (make-wff formula)
  (vnb-guard
    (lambda ()
      (if (string? formula)
          (make-wff (parse-string formula))
          (let* ((expanded (expand-destructuring-quantifiers formula)))
            (validate-wff! expanded)
            (when *reject-constant-binders?*
              (let ((hits (wff-constant-binders expanded)))
                (when (pair? hits)
                  (warn-constant-binders! hits)          ; the loud diagnosis, then:
                  (error (string-append
                          "make-wff: bound variable named like a registered constant: "
                          (symbol->string (cadr (car hits)))
                          " (a " (symbol->string (caddr (car hits)))
                          ").  In head position it reads as the constant, not your"
                          " binder.  Rename it (trailing underscore).")))))
            (%make-concrete-wff expanded (theory-name *current-theory*)))))))

;;; display-contents: print a wff with its formula, theory, and kind.
;;; Convenience alias for browsing wffs at the REPL.
(define (display-contents w)
  (cond
    ((wff? w)
     (display "kind:    concrete")
     (newline)
     (display "theory:  ")
     (display (wff-theory w))
     (newline)
     (display "formula: ")
     (write (wff-formula w))
     (newline))
    (else
     (display "(not a wff) ")
     (write w)
     (newline))))

