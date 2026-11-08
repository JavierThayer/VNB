;;; core-replay-stub.scm -- a STAND-IN for the four core-replay commands, for the
;;; panel check only (emacs/vnb-panel-check.el loads it into the band).  Never in
;;; load.scm.  The real commands are core-replay.scm (built separately); this file
;;; fixes their CONTRACT for the Emacs surface (docs/core-replay-design-2026-11-05.md
;;; s.5a):
;;;
;;;   (core-page-text 'NAME)    a string: one line "step K: (CMD ...)" per core step,
;;;                             optionally a line "goal K: TEXT" (the focus goal
;;;                             before step K), then "verdict: ...";
;;;                             or "no core page for NAME".
;;;   (core-replay-begin 'NAME) starts the replay (an `sp' of the statement), returns
;;;                             the step count.
;;;   (core-replay-next)        runs the next step, returns its number, or 'done when
;;;                             every step has run.
;;;   (core-replay-back)        takes the last step back, returns the number of the
;;;                             step the replay now stands after (0 at the start).
;;;
;;; The stub has ONE page, for the name `vpc-core-demo', of two steps on the goal
;;; forall([x in nn], x in nn).  The steps are run as surface commands, so each
;;; prints its state block and the workspace repaints as for any command.

(define *crs-stub-statement* "forall([x in nn], x in nn)")
(define *crs-stub-steps* '("(di)" "(ass)"))
(define *crs-stub-cmds* (list di ass))
(define *crs-stub-at* 0)

(define (crs-stub--page? name) (eq? name 'vpc-core-demo))

(define (core-page-text name)
  (if (not (crs-stub--page? name))
      (string-append "no core page for " (symbol->string name))
      (string-append
       "goal 1: forall([x in nn], x in nn)\n"
       "step 1: (di)\n"
       "goal 2: x in nn  =>  x in nn\n"
       "step 2: (ass)\n"
       "verdict: core-replayed (2 steps)")))

(define (core-replay-begin name)
  (if (not (crs-stub--page? name))
      (error "core-replay-begin: no core page for" name))
  (sp (make-wff-from-string *crs-stub-statement*))
  (set! *crs-stub-at* 0)
  (length *crs-stub-steps*))

(define (core-replay-next)
  (if (>= *crs-stub-at* (length *crs-stub-cmds*))
      'done
      (begin
        ((list-ref *crs-stub-cmds* *crs-stub-at*))
        (set! *crs-stub-at* (+ *crs-stub-at* 1))
        *crs-stub-at*)))

(define (core-replay-back)
  (if (> *crs-stub-at* 0)
      (begin (undo) (set! *crs-stub-at* (- *crs-stub-at* 1))))
  *crs-stub-at*)
