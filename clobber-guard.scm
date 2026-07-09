;;; clobber-guard.scm -- the gate CLAUDE.md says does not exist.
;;;
;;; Both the VNB reader and MIT Scheme fold symbols to lowercase, so a proof
;;; file's innocent-looking
;;;
;;;     (define BC '(succ p))
;;;
;;; rebinds the `bc' TACTIC to a term.  Every later (bc 'thm) -- in that file
;;; and in every file loaded after it -- dies with "The object (...) is not
;;; applicable", or worse, quietly does the wrong thing.  Real cases: BC in
;;; bordered-eq-border-proof.scm (broke four suite tests in a different file),
;;; TT in hahn-banach-full-proof.scm and nn-least-element.scm, SP in a Smith
;;; driver, ID in mat-equiv-proof.scm.
;;;
;;; `case-fold-audit' and `constant-binder-audit' both inspect WFF binders and
;;; never Scheme defines, so neither sees it.
;;;
;;; The invariant enforced here is stronger than "do not shadow a tactic", and
;;; needs no registry of tactic names:
;;;
;;;   NO FILE MAY REBIND, TO A NON-PROCEDURE, A NAME THAT WAS A PROCEDURE
;;;   BEFORE IT LOADED.
;;;
;;; That is exactly the bug: `bc' was a procedure, `(define BC '(...))' makes it
;;; a list.  Redefining a procedure with another procedure stays legal, which
;;; matters -- several drivers re-define the shared `proof-leaves' / `any-pred'
;;; helpers, and that is (for now) load-bearing.
;;;
;;; The check is a lookup per guarded name per file: a few thousand times a
;;; hundred files, which is nothing next to one `di'.
;;;
;;; Loads after `minimize' and before the first proof file; `prover-load'
;;; (load.scm) calls clobber-guard-check! after each subsequent file.  Files
;;; loaded before the snapshot are unguarded (the guard is #f and does nothing).

;;; The environment proof files are loaded into.  MIT's `load' with no
;;; environment argument uses the CALLER's environment, and load.scm's caller is
;;; this same top level -- so `bc' and friends live in this very frame, and
;;; environment-bound-names sees them (it reports the own frame only).
(define *clobber-guard-env* (the-environment))

(define *clobber-guard-procs* #f)        ; name -> #t, or #f before the snapshot

;; environment-lookup REFUSES a syntactic keyword ("Variable reference to a
;; syntactic keyword: bc*") and errors on an unassigned binding, so it cannot be
;; called bare over environment-bound-names.  Macros are simply never watched:
;; they answer 'unavailable both at snapshot and at check time, consistently.
(define (clobber-guard--value n)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler (lambda (e) (k 'clobber-guard--unavailable))
        (lambda () (environment-lookup *clobber-guard-env* n))))))

(define (clobber-guard--procedure? n)
  (and (environment-bound? *clobber-guard-env* n)
       (procedure? (clobber-guard--value n))))

(define (clobber-guard-snapshot!)
  (let ((h (make-strong-eqv-hash-table)))
    (for-each (lambda (n) (if (clobber-guard--procedure? n) (hash-table-set! h n #t)))
              (environment-bound-names *clobber-guard-env*))
    (set! *clobber-guard-procs* h)
    (display ";; clobber-guard: watching ")
    (display (length (hash-table-keys h)))
    (display " procedure bindings")
    (newline)))

;;; Report EVERY casualty, not just the first: one bad `define' usually comes
;;; with siblings, and a second 11-minute load to find the next one is a waste.
(define (clobber-guard-check! file)
  (if *clobber-guard-procs*
      (let ((bad '()))
        (hash-table-walk *clobber-guard-procs*
          (lambda (n ignored)
            (if (not (clobber-guard--procedure? n)) (set! bad (cons n bad)))))
        (if (not (null? bad))
            (begin
              ;; drop them from the watch set: the damage is already reported,
              ;; and leaving them in would re-blame every later file.
              (for-each (lambda (n) (hash-table-delete! *clobber-guard-procs* n)) bad)
              (error
               (string-append
                "clobber-guard: " file
                " rebound a procedure to a non-procedure -- almost certainly a"
                " top-level (define X ...) whose name case-folds onto a tactic."
                " Use the file's helper prefix instead.  Casualties:")
               (sort bad (lambda (a b) (string<? (symbol->string a)
                                                 (symbol->string b))))))))))

(clobber-guard-snapshot!)
