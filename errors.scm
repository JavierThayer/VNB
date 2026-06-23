;;; errors.scm -- VNB error value and guard wrapper
;;;
;;; User-facing VNB functions wrap their bodies in vnb-guard.  If a Scheme
;;; error is signalled, the outermost active guard catches it, prints a
;;; one-line message, and returns a <vnb-error> value instead of dropping
;;; into the debugger.
;;;
;;; Nested guards are transparent: when *vnb-guard-active* is already #t,
;;; vnb-guard just calls the thunk directly so errors propagate outward and
;;; only the outermost guard catches and displays them.

;;; -----------------------------------------------------------------------
;;; Error value

(define-record-type <vnb-error>
  (%make-vnb-error message)
  vnb-error?
  (message vnb-error-message))

(define (vnb-error-display err)
  (display ";; VNB error: " (current-output-port))
  (display (vnb-error-message err) (current-output-port))
  (newline (current-output-port)))

;;; -----------------------------------------------------------------------
;;; Guard

(define *vnb-guard-active* #f)

;;; When #t, vnb-guard catches errors SILENTLY (no auto one-line print).  Bound
;;; by `quietly' so speculative drivers (scout, cheap-mac, bplus, proof-tex
;;; replay) that EXPECT branches to fail don't spray "VNB error: ..." per prune.
;;; The <vnb-error> is still returned, so callers detect the failure as usual.
(define *vnb-guard-quiet* #f)

;;; Run THUNK inside an error-catching boundary.
;;; - First (outermost) call: installs a handler; any Scheme error produces
;;;   a one-line message and a <vnb-error> return value.
;;; - Re-entrant calls: *vnb-guard-active* is #t so thunk runs directly,
;;;   letting errors propagate to the outermost guard unchanged.
(define (vnb-guard thunk)
  (if *vnb-guard-active*
      (thunk)
      (let ((result
             (call-with-current-continuation
               (lambda (k)
                 (fluid-let ((*vnb-guard-active* #t))
                   (with-exception-handler
                     (lambda (exn)
                       ;; condition/report-string only works on conditions;
                       ;; a user-level (raise <non-condition>) would itself
                       ;; error inside the handler.  Guard against that.
                       (k (%make-vnb-error
                           (if (condition? exn)
                               (condition/report-string exn)
                               (string-append
                                "non-condition raised: "
                                (call-with-output-string
                                  (lambda (p) (write exn p))))))))
                     thunk))))))
        (when (and (vnb-error? result) (not *vnb-guard-quiet*))
          (vnb-error-display result))
        result)))
