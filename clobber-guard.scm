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
;;; helpers, and that is (for now) load-bearing.  It is also the one gap:
;;; `(define (append a b) ...)' -- procedure over procedure -- is NOT caught.
;;;
;;; Loads FIRST, before any other VNB file (load.scm); `prover-load' calls
;;; clobber-guard-check! after each subsequent file.  It used to load at
;;; load.scm:518, and its own header admitted the consequence -- "files loaded
;;; before the snapshot are unguarded".  Measured 2026-08-16: **126 library
;;; files loaded before it, 118 after**, so more than half the library --
;;; including all of `structure-library/' -- was outside the alarm.

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

;;; SEED FROM THE GLOBAL ENVIRONMENT TOO (2026-08-16), and this is the point.
;;; `environment-bound-names' reports the OWN FRAME ONLY -- the comment above
;;; says so -- and at the head of the load that frame holds nine names.  MIT's
;;; own procedures live in the PARENT, so `append', `list', `cons', `length'
;;; were never in the watch set at all, at any snapshot point, early or late.
;;;
;;; They are exactly the names that matter.  Each is simultaneously a live
;;; Scheme procedure and a VNB head symbol, so a proof file's
;;; `(define APPEND '(...))' shadows a procedure the prover itself calls with a
;;; list.  `environment-bound?' DOES search the parent chain, so a shadow in the
;;; top frame is caught by the ordinary check once the name is in the set.
(define (clobber-guard-snapshot!)
  (let ((h (make-strong-eqv-hash-table)))
    (for-each (lambda (n) (if (clobber-guard--procedure? n) (hash-table-set! h n #t)))
              (append (environment-bound-names *clobber-guard-env*)
                      (environment-bound-names system-global-environment)))
    (set! *clobber-guard-procs* h)
    (display ";; clobber-guard: watching ")
    (display (length (hash-table-keys h)))
    (display " procedure bindings")
    (newline)))

;;; ONE PASS OVER THE OWN FRAME does both jobs -- detect casualties, and absorb
;;; what the file newly defined -- and it is what makes watching MIT's ~3900
;;; globals affordable.
;;;
;;; The obvious implementation walks the WATCH SET after every file, re-looking
;;; up each member.  That is 3975 names x ~250 files, each a `bound?' plus a
;;; lookup inside a continuation and an exception handler, and it cost 23 s on
;;; top of a 48 s cold load -- measured, not guessed.
;;;
;;; The direction was simply wrong.  A file can only turn a procedure into a
;;; non-procedure by DEFINING that name, and a definition lands in the top
;;; frame.  So the names that can possibly have changed are exactly the own
;;; frame's -- whether the victim was a VNB tactic or a shadowed MIT global.
;;; Walking the own frame is therefore COMPLETE for the invariant and costs in
;;; proportion to what the file did rather than to how much is being watched.
;;;
;;; The same pass grows the set: a name in the own frame that is a procedure and
;;; not yet watched becomes watched, so VNB's own tactics join as they appear
;;; and the early snapshot loses nothing.
;;;
;;; Report EVERY casualty, not just the first: one bad `define' usually comes
;;; with siblings, and a second 11-minute load to find the next one is a waste.
(define (clobber-guard-check! file)
  (if *clobber-guard-procs*
      (let ((bad '()))
        (for-each
         (lambda (n)
           (let ((watched (hash-table-ref/default *clobber-guard-procs* n #f))
                 (proc?   (clobber-guard--procedure? n)))
             (cond ((and watched (not proc?)) (set! bad (cons n bad)))
                   ((and (not watched) proc?)
                    (hash-table-set! *clobber-guard-procs* n #t)))))
         (environment-bound-names *clobber-guard-env*))
        (if (not (null? bad))
            (begin
              ;; drop them from the watch set: the damage is already reported,
              ;; and leaving them in would re-blame every later file.
              (for-each (lambda (n) (hash-table-delete! *clobber-guard-procs* n)) bad)
              (error
               (string-append
                "clobber-guard: " file
                " rebound a procedure to a non-procedure -- almost certainly a"
                " top-level (define X ...) whose name case-folds onto a tactic"
                " or onto one of MIT Scheme's own procedures."
                "  Use the file's helper prefix instead.  Casualties:")
               (sort bad (lambda (a b) (string<? (symbol->string a)
                                                 (symbol->string b))))))))))

(clobber-guard-snapshot!)
