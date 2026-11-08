;;; structure-library/is-set-laws.scm -- THE GENERATED SETHOOD THEOREMS (W1I, 2026-11-06).
;;;
;;; build-is-axiom (structures.scm) ends every IS-X with the conjunct (IN s SET) (the
;;; user's decision of 2026-11-06, "Go with the s in SET sweep").  This file gives every
;;; declared structure X its citable form, PROVEN:
;;;
;;;     is-X-is-set :  forall s. IS-X(s) => s in SET
;;;
;;; by the generic driver `dk-is-set-theorem!' (driver-kit.scm): for a shape structure the
;;; projection of the last conjunct of IS-X, for a same-shape refinement its parent's
;;; theorem through the parent conjunct.  Each is modulo 0.  Redundant with the conjunct;
;;; the user prefers the guard and the citation both.
;;;
;;; WHERE.  The proofs need the tactics, which load after structures.scm.  A structure
;;; declared before this file is queued by `isx-set--declared!' (structures.scm) and
;;; proved HERE, the catch-up; this file is loaded after the last tactic file and before
;;; the first proof file (load.scm).  It then installs `*isx-set-hook*', so a structure
;;; declared LATER (isom2-vocab, the strand-space files, tg-vocab, sip-vocab, nets, ...)
;;; proves its theorem at its declaration, in its own file.  Either way is-X-is-set exists
;;; before any proof that could cite it.
;;;
;;; The hook keeps the proof-state globals of whatever proof is in progress (a structure
;;; declared at the REPL or in the suite mid-proof): the run is held in a fluid-let, as
;;; display-proof holds its file run (proof-reader.scm).

;;; A generation that fails does not stop the declaration: it prints one loud line and is
;;; listed in `*isx-set-failures*', which the suite (block ISSET) requires to be empty.
(define *isx-set-failures* '())

(define (isl-prove! name)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler
        (lambda (e)
          (let ((why (if (condition? e) (condition/report-string e) e)))
            (display ";; is-set-laws: FAILED to prove is-") (display name) (display "-is-set: ")
            (display why) (newline)
            (set! *isx-set-failures* (cons (list name why) *isx-set-failures*))
            (k #f)))
        (lambda () (isl-prove-1! name))))))

(define (isl-prove-1! name)
  (fluid-let ((*vnb-loading* #t)
              (*ps* *ps*) (*proof-script* *proof-script*)
              (*proof-hidden-citations* *proof-hidden-citations*)
              (*proof-mints* *proof-mints*)
              (*fresh-mark-at-last-record* *fresh-mark-at-last-record*)
              (*witness-aliases* *witness-aliases*)
              (*current-goal* *current-goal*)
              (*sp-counter-snapshot* *sp-counter-snapshot*)
              (*live-trace* *live-trace*)
              (*vnb-undo-stack* *vnb-undo-stack*)
              (*dg-journal* *dg-journal*))
    (dk-is-set-theorem! name)))

(let ((pending *isx-set-pending*))
  (set! *isx-set-pending* '())
  (for-each isl-prove! pending))
(set! *isx-set-hook* isl-prove!)
