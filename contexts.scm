;;; contexts.scm -- local context management and make-wff
;;;
;;; A local context asserts the existence of a named instance of some class.
;;; The binding form is (IN x A) or (IN (LIST n1...nk) A).  Declaring a
;;; context adds it to the active stack; make-wff snapshots the stack into
;;; a <wff>.  The <wff> record type itself lives in wff.scm.

;;; -----------------------------------------------------------------------
;;; Local context record

(define-record-type <local-context>
  (%make-local-context name binding)
  local-context?
  (name    local-context-name)
  (binding local-context-binding))

;;; Global registry: all ever-declared contexts (name -> <local-context>)
(define *context-registry* '())

;;; Active stack: contexts currently in scope, outermost first
(define *active-local-contexts* '())

;;; -----------------------------------------------------------------------
;;; declare-local-context / undeclare-local-context

(define (declare-local-context binding name)
  (vnb-guard
    (lambda ()
      (let ((ctx (%make-local-context name binding)))
        (set! *context-registry* (cons (cons name ctx) *context-registry*))
        (set! *active-local-contexts*
              (append *active-local-contexts* (list ctx)))
        (list 'CONTEXT name)))))

(define (undeclare-local-context name)
  (vnb-guard
    (lambda ()
      (set! *active-local-contexts*
            (filter (lambda (ctx)
                      (not (eq? (local-context-name ctx) name)))
                    *active-local-contexts*))
      (list 'UNDECLARED name))))

(define (get-context name)
  (let ((entry (assq name *context-registry*)))
    (if entry
        (local-context-binding (cdr entry))
        (error "get-context: unknown context name" name))))

;;; -----------------------------------------------------------------------
;;; make-wff: snapshot current theory + active context stack into a <wff>

;;; When #t, make-wff warns (loudly, non-fatally) if the formula binds a
;;; variable whose case-folded name is a registered constant (accessor /
;;; operator / functoid / predicate) -- the interactive counterpart of the
;;; load-time constant-binder-audit.  Left #f during the library load (set #t
;;; at the end of load.scm) so it fires only for user-constructed wffs, and so
;;; it never runs before wff-constant-binders (macetes.scm) is defined.
(define *warn-constant-binders?* #f)

(define (make-wff formula)
  (vnb-guard
    (lambda ()
      (if (string? formula)
          (make-wff (parse-string formula))
          (let* ((expanded (expand-destructuring-quantifiers formula)))
            (validate-wff! expanded)
            (when *warn-constant-binders?*
              (let ((hits (wff-constant-binders expanded)))
                (when (pair? hits) (warn-constant-binders! hits))))
            (%make-concrete-wff expanded
                                (theory-name *current-theory*)
                                (list-copy *active-local-contexts*)))))))

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
     (newline)
     (when (not (null? (wff-contexts w)))
       (display "context: ")
       (display (wff-context-name w))
       (newline)))
    (else
     (display "(not a wff) ")
     (write w)
     (newline))))

;;; -----------------------------------------------------------------------
;;; Display helpers

(define (wff-context-name wic)
  (let ((base (wff-theory wic))
        (ctxs (map local-context-name (wff-contexts wic))))
    (if (null? ctxs)
        base
        (cons base ctxs))))

;;; -----------------------------------------------------------------------
;;; free-vars for a wff (context-bound names don't count as free)

(define (wff-free-vars wic)
  (let* ((raw   (free-vars (wff-formula wic)))
         (bound (contexts-bound-names (wff-contexts wic))))
    (filter (lambda (v) (not (memq v bound))) raw)))

(define (contexts-bound-names ctx-list)
  (apply append
    (map (lambda (ctx)
           (let ((binding (local-context-binding ctx)))
             (cond
               ((and (pair? binding)
                     (eq? (car binding) 'IN)
                     (pair? (cadr binding))
                     (eq? (car (cadr binding)) 'LIST))
                (cdr (cadr binding)))
               ((and (pair? binding) (eq? (car binding) 'IN))
                (list (cadr binding)))
               (else '()))))
         ctx-list)))

;;; -----------------------------------------------------------------------
;;; unravel: wrap formula with FORALL quantifiers for each context layer,
;;; outermost first, producing a self-contained wff in the base theory.

(define (unravel wic)
  (vnb-guard
    (lambda ()
      (let ((ctxs    (wff-contexts wic))
            (formula (wff-formula wic))
            (base    (wff-theory wic)))
        (wff-in-theory (fold-right-contexts ctxs formula) base)))))

(define (fold-right-contexts ctx-list formula)
  (if (null? ctx-list)
      formula
      (let ((binding (local-context-binding (car ctx-list)))
            (inner   (fold-right-contexts (cdr ctx-list) formula)))
        `(FORALL ,binding ,inner))))

;;; -----------------------------------------------------------------------
;;; Display

(define (print-wff wic)
  (display "(wff ")
  (write (wff-formula wic))
  (display " IN ")
  (write (wff-context-name wic))
  (display ")"))

(define (wff-in-context->string wic)
  (call-with-output-string
    (lambda (port)
      (display "(wff " port)
      (write (wff-formula wic) port)
      (display " IN " port)
      (write (wff-context-name wic) port)
      (display ")" port))))
