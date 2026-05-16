;;; interactive.scm -- short-form commands for interactive proof sessions
;;;
;;; Maintains *ps* (current proof state) and provides single-letter wrappers
;;; around the cmd-* proof commands.  Each wrapper records itself in
;;; *proof-script* (so the proof can be saved and replayed later), mutates
;;; *ps*, and calls (show) so the new state is always displayed.
;;;
;;; State output is bracketed by sentinel lines that the Emacs interface
;;; strips from the REPL display and forwards to the proof-state buffer.
;;; Without Emacs the sentinels appear as two comment lines -- ignorable.

(define *ps* #f)

;;; -----------------------------------------------------------------------
;;; Proof-script recording
;;;
;;; *proof-script* accumulates the commands applied since the last (sp).
;;; Each entry is (cmd-name . args).  (qed name) auto-saves the current
;;; script under the given name; (save-proof name) does the same on demand.
;;; (replay-proof name [subst]) re-runs a saved script, optionally with a
;;; capture-avoiding substitution applied to every command argument.

(define *proof-script* '())

(define (record-cmd! name args)
  (set! *proof-script* (append *proof-script* (list (cons name args)))))

(define *proof-script-table* (make-equal-hash-table))

(define (save-proof name)
  (hash-table-set! *proof-script-table* name *proof-script*)
  name)

(define (lookup-proof name)
  (or (hash-table-ref/default *proof-script-table* name #f)
      (error "lookup-proof: unknown proof script" name)))

;;; Print the current proof state wrapped in sentinel markers.
(define (show)
  (display ";;VNB-STATE-BEGIN\n")
  (if *ps*
      (print-proof-state *ps*)
      (display "No current proof.  Use (sp (make-wff '(formula))) to start one.\n"))
  (display ";;VNB-STATE-END\n"))

(define (pp w)
  (display (wff->string w))
  (newline))

;;; Evaluate a ground arithmetic term and display the result.
;;; Accepts a string ("2^10") or a raw S-expression ('(POWER 2 10)).
(define (calc t)
  (vnb-guard
    (lambda ()
      (let* ((raw (if (string? t) (parse-string t) t))
             (v   (arith-eval-term raw)))
        (if v
            (begin (display v) (newline) v)
            (error "calc: not a ground arithmetic term" raw))))))

(define (vnb--require-proof!)
  (unless *ps*
    (error "No current proof.  Use (sp (make-wff-from-string \"...\")) to start one.")))

;;; Convert a formula argument to a raw S-expression.
;;; Accepts either a string (parsed via parse-string) or a raw S-expression.
(define (->raw-formula f)
  (if (string? f) (parse-string f) f))

;;; -----------------------------------------------------------------------
;;; Start a proof.  Resets the proof-script accumulator.

(define (sp wic)
  (vnb-guard
    (lambda ()
      (unless (wff? wic)
        (error "sp: expected a wff -- use (make-wff-from-string \"...\") first" wic))
      (set! *proof-script* '())
      (set! *ps* (start-proof wic))
      (show))))

;;; -----------------------------------------------------------------------
;;; Short-form proof commands.
;;;
;;; vnb--run! executes a cmd-* thunk, records and updates *ps* on success,
;;; or displays the warning message and leaves *ps* unchanged on soft failure.

(define (vnb--run! sym args thunk)
  (let ((result (vnb-guard (lambda () (vnb--require-proof!) (thunk)))))
    (cond
      ((vnb-error? result) #f)          ; already displayed by vnb-guard
      ((vnb-warning? result)
       (display ";VNB warning: ")
       (display (vnb-warning-message result))
       (newline))
      (else
       (record-cmd! sym args)
       (set! *ps* result)
       (show)))))

(define (di)    (vnb--run! 'di    '()    (lambda () (cmd-direct-inference *ps*))))
(define (pbc)   (vnb--run! 'pbc   '()    (lambda () (cmd-proof-by-contradiction *ps*))))
(define (ass)   (vnb--run! 'ass   '()    (lambda () (cmd-assumption *ps*))))
(define (arith) (vnb--run! 'arith '()    (lambda () (cmd-arith *ps*))))
(define (rs)    (vnb--run! 'rs    '()    (lambda () (cmd-ring-simplify *ps*))))
(define (rfl)   (vnb--run! 'rfl   '()    (lambda () (cmd-reflexivity *ps*))))
(define (qrfl)  (vnb--run! 'qrfl  '()    (lambda () (cmd-quasi-reflexivity *ps*))))
(define (oi-l)  (vnb--run! 'oi-l  '()    (lambda () (cmd-or-intro-left *ps*))))
(define (oi-r)  (vnb--run! 'oi-r  '()    (lambda () (cmd-or-intro-right *ps*))))
(define (ci)    (vnb--run! 'ci    '()    (lambda () (cmd-cartesian-intro *ps*))))
(define (ti)    (vnb--run! 'ti    '()    (lambda () (cmd-tuples-intro *ps*))))
(define (nth-r) (vnb--run! 'nth-r '()    (lambda () (cmd-nth-reduce *ps*))))
(define (beta)  (vnb--run! 'beta  '()    (lambda () (cmd-functoid-beta *ps*))))
(define (ii)    (vnb--run! 'ii    '()    (lambda () (cmd-intersection-intro *ps*))))
(define (tfi)   (vnb--run! 'tfi   '()    (lambda () (cmd-tfi *ps*))))
(define (tfi3)  (vnb--run! 'tfi3  '()    (lambda () (cmd-tfi3 *ps*))))
(define (ni)    (vnb--run! 'ni    '()    (lambda () (cmd-nn-induction *ps*))))

(define (ai f)  (let ((raw (->raw-formula f)))
                  (vnb--run! 'ai (list raw) (lambda () (cmd-antecedent-inference *ps* raw)))))
(define (cut f) (let ((raw (->raw-formula f)))
                  (vnb--run! 'cut (list raw) (lambda () (cmd-cut *ps* raw)))))
(define (ew t)  (let ((raw (->raw-formula t)))
                  (vnb--run! 'ew (list raw) (lambda () (cmd-exists-witness *ps* raw)))))
(define (bc f)  (let ((raw (->raw-formula f)))
                  (vnb--run! 'bc (list raw) (lambda () (cmd-backchain *ps* raw)))))
(define (wk f)  (let ((raw (->raw-formula f)))
                  (vnb--run! 'wk (list raw) (lambda () (cmd-weaken *ps* raw)))))
(define (ui k)  (vnb--run! 'ui (list k) (lambda () (cmd-union-intro *ps* k))))
(define (ue f)  (let ((raw (->raw-formula f)))
                  (vnb--run! 'ue (list raw) (lambda () (cmd-union-elim *ps* raw)))))

(define (ta n)  (vnb--run! 'ta (list n) (lambda () (cmd-theorem-assumption *ps* n))))
(define (mac n) (vnb--run! 'mac (list n) (lambda () (cmd-apply-macete *ps* n))))

;;; D-7 short forms (REVIEW.md D-7) — SEP / COMP / IOTA / VNB-LAMBDA
(define (sep-set)  (vnb--run! 'sep-set  '() (lambda () (cmd-sep-sethood       *ps*))))
(define (sep-mi)   (vnb--run! 'sep-mi   '() (lambda () (cmd-sep-mem-intro     *ps*))))
(define (sep-me f) (let ((raw (->raw-formula f)))
                     (vnb--run! 'sep-me (list raw) (lambda () (cmd-sep-mem-elim *ps* raw)))))
(define (comp-mi)  (vnb--run! 'comp-mi  '() (lambda () (cmd-comp-mem-intro    *ps*))))
(define (comp-me f) (let ((raw (->raw-formula f)))
                      (vnb--run! 'comp-me (list raw) (lambda () (cmd-comp-mem-elim *ps* raw)))))
(define (iota-d t)  (let ((raw (->raw-formula t)))
                      (vnb--run! 'iota-d (list raw) (lambda () (cmd-iota-def *ps* raw)))))
(define (lam-t)    (vnb--run! 'lam-t    '() (lambda () (cmd-lambda-type      *ps*))))
(define (lam-b)    (vnb--run! 'lam-b    '() (lambda () (cmd-lambda-beta      *ps*))))

(define (inst f t) (let ((raw (->raw-formula f)))
                     (vnb--run! 'inst (list raw t) (lambda () (cmd-instantiate *ps* raw t)))))
(define (ce f k)   (let ((raw (->raw-formula f)))
                     (vnb--run! 'ce (list raw k) (lambda () (cmd-cartesian-elim *ps* raw k)))))
(define (te f k)   (let ((raw (->raw-formula f)))
                     (vnb--run! 'te (list raw k) (lambda () (cmd-tuples-elim *ps* raw k)))))
(define (ie f k)   (let ((raw (->raw-formula f)))
                     (vnb--run! 'ie (list raw k) (lambda () (cmd-intersection-elim *ps* raw k)))))

;;; Switch focus to the n-th open goal (1-based).  Recorded for replay.
(define (focus n)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (let ((goals (proof-open-goals *ps*)))
        (if (and (integer? n) (>= n 1) (<= n (length goals)))
            (begin
              (record-cmd! 'focus (list n))
              (set! *ps* (focus-on *ps* (list-ref goals (- n 1))))
              (show))
            (begin
              (display ";VNB warning: focus: index out of range: ")
              (display n) (display " (")
              (display (length goals)) (display " open goals)")
              (newline)))))))

;;; -----------------------------------------------------------------------
;;; Install the completed current proof as a named theorem AND save the
;;; proof script under the same name.

(define (qed name)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (cmd-qed *ps* name)
      (save-proof name)
      name)))

;;; -----------------------------------------------------------------------
;;; Replay a saved proof script on the current proof state.
;;;
;;; (replay-proof name)             -- replay verbatim
;;; (replay-proof name '((x . term-x) (y . term-y)))
;;;     -- substitute free variables in every command argument before applying.

(define (replay-proof name . maybe-subst)
  (vnb-guard
    (lambda ()
      (vnb--require-proof!)
      (let ((script (lookup-proof name))
            (subst  (if (null? maybe-subst) '() (car maybe-subst))))
        (for-each (lambda (entry)
                    (let ((cmd-name (car entry))
                          (args     (cdr entry)))
                      (apply-recorded-cmd! cmd-name
                                           (map (lambda (a) (replay--subst-args subst a))
                                                args))))
                  script)
        (show)))))

(define (replay--subst-args subst expr)
  (let loop ((s subst) (e expr))
    (if (null? s)
        e
        (loop (cdr s)
              (subst-free (caar s) (cdar s) e)))))

;;; Dispatch a recorded command back to its underlying cmd-* function.
;;; Bypasses recording (we call cmd-* directly, not the short form), so
;;; replay does not corrupt *proof-script*.
;;; A warning during replay is a hard error: the saved proof is broken.
(define (apply-recorded-cmd! name args)
  (let ((result
    (case name
      ((di)     (cmd-direct-inference *ps*))
      ((pbc)    (cmd-proof-by-contradiction *ps*))
      ((ass)    (cmd-assumption *ps*))
      ((arith)  (cmd-arith *ps*))
      ((rfl)    (cmd-reflexivity *ps*))
      ((qrfl)   (cmd-quasi-reflexivity *ps*))
      ((oi-l)   (cmd-or-intro-left *ps*))
      ((oi-r)   (cmd-or-intro-right *ps*))
      ((ci)     (cmd-cartesian-intro *ps*))
      ((ti)     (cmd-tuples-intro *ps*))
      ((nth-r)  (cmd-nth-reduce *ps*))
      ((beta)   (cmd-functoid-beta *ps*))
      ((ii)     (cmd-intersection-intro *ps*))
      ((tfi)    (cmd-tfi  *ps*))
      ((tfi3)   (cmd-tfi3 *ps*))
      ((ai)     (cmd-antecedent-inference *ps* (car args)))
      ((cut)    (cmd-cut *ps* (car args)))
      ((ew)     (cmd-exists-witness *ps* (car args)))
      ((bc)     (cmd-backchain *ps* (car args)))
      ((wk)     (cmd-weaken *ps* (car args)))
      ((ui)     (cmd-union-intro *ps* (car args)))
      ((ue)     (cmd-union-elim *ps* (car args)))
      ((ta)     (cmd-theorem-assumption *ps* (car args)))
      ((mac)    (cmd-apply-macete *ps* (car args)))
      ((inst)   (cmd-instantiate *ps* (car args) (cadr args)))
      ((ce)     (cmd-cartesian-elim *ps* (car args) (cadr args)))
      ((ie)     (cmd-intersection-elim *ps* (car args) (cadr args)))
      ((te)     (cmd-tuples-elim *ps* (car args) (cadr args)))
      ((ni)     (cmd-nn-induction *ps*))
      ((rs)     (cmd-ring-simplify *ps*))
      ;; D-7 replay dispatch
      ((sep-set) (cmd-sep-sethood       *ps*))
      ((sep-mi)  (cmd-sep-mem-intro     *ps*))
      ((sep-me)  (cmd-sep-mem-elim      *ps* (car args)))
      ((comp-mi) (cmd-comp-mem-intro    *ps*))
      ((comp-me) (cmd-comp-mem-elim     *ps* (car args)))
      ((iota-d)  (cmd-iota-def          *ps* (car args)))
      ((lam-t)   (cmd-lambda-type       *ps*))
      ((lam-b)   (cmd-lambda-beta       *ps*))
      ((focus)  (focus-on *ps*
                          (list-ref (proof-open-goals *ps*)
                                    (- (car args) 1))))
      (else (error "replay: unknown recorded command" name)))))
    (if (vnb-warning? result)
        (error "replay: command failed" name (vnb-warning-message result))
        (set! *ps* result))))

;;; -----------------------------------------------------------------------
;;; Multi-variable quantification expanders
;;;
;;; Each binding is either (x) for a bare variable ranging over all objects,
;;; or (in x A) for a bounded variable restricted to class A.
;;;
;;; (fa '((x) (in y NN) (z)) 'BODY)
;;;   => (FORALL x (FORALL y (IMPLIES (IN y NN) (FORALL z BODY))))
;;;
;;; (fs '((x) (in y NN)) 'BODY)
;;;   => (FORSOME x (FORSOME y (AND (IN y NN) BODY)))

(define (fa bindings body)
  (if (null? bindings)
      body
      (let* ((b    (car bindings))
             (rest (fa (cdr bindings) body)))
        (cond
          ((and (pair? b) (= (length b) 1) (symbol? (car b)))
           `(FORALL ,(car b) ,rest))
          ((and (pair? b) (= (length b) 3)
                (eq? (cadr b) 'IN) (symbol? (car b)))
           `(FORALL ,(car b) (IMPLIES (IN ,(car b) ,(caddr b)) ,rest)))
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN) (symbol? (cadr b)))
           `(FORALL ,(cadr b) (IMPLIES (IN ,(cadr b) ,(caddr b)) ,rest)))
          ;; (IN (LIST x1 ... xn) A) — tuple destructuring; expansion deferred to make-wff
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN)
                (pair? (cadr b)) (eq? (car (cadr b)) 'LIST)
                (all-symbols? (cdr (cadr b))))
           `(FORALL ,b ,rest))
          (else (error "fa: invalid binding" b))))))

(define (fs bindings body)
  (if (null? bindings)
      body
      (let* ((b    (car bindings))
             (rest (fs (cdr bindings) body)))
        (cond
          ((and (pair? b) (= (length b) 1) (symbol? (car b)))
           `(FORSOME ,(car b) ,rest))
          ((and (pair? b) (= (length b) 3)
                (eq? (cadr b) 'IN) (symbol? (car b)))
           `(FORSOME ,(car b) (AND (IN ,(car b) ,(caddr b)) ,rest)))
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN) (symbol? (cadr b)))
           `(FORSOME ,(cadr b) (AND (IN ,(cadr b) ,(caddr b)) ,rest)))
          ;; (IN (LIST x1 ... xn) A) — tuple destructuring; expansion deferred to make-wff
          ((and (pair? b) (= (length b) 3)
                (eq? (car b) 'IN)
                (pair? (cadr b)) (eq? (car (cadr b)) 'LIST)
                (all-symbols? (cdr (cadr b))))
           `(FORSOME ,b ,rest))
          (else (error "fs: invalid binding" b))))))

;;; -----------------------------------------------------------------------
;;; vnb-unwind / vnb-wind
;;;
;;; Operate on surface S-expressions in the new binding-list syntax.
;;; They do NOT expand to primitive form; use make-wff for that.
;;;
;;; vnb-unwind: (FORALL ((b1 b2 ... bn) ...) body)
;;;             => (FORALL ((b1)) (FORALL ((b2)) ... (FORALL ((bn)) body)...))
;;;
;;; vnb-wind:   (FORALL ((b1)) (FORALL ((b2)) body))
;;;             => (FORALL ((b1) (b2)) body)   [same quantifier type only]

;;; Flatten a binding spec to a list of single-var specs.
;;; (x y z) -> ((x) (y) (z));  (x) -> ((x));  (IN x A) -> ((IN x A))
(define (flatten-binding-spec b)
  (if (and (pair? b) (not (null? b)) (all-symbols? b) (not (eq? (car b) 'in)))
      (map list b)
      (list b)))

(define (vnb-unwind expr)
  (if (not (pair? expr))
      expr
      (cond
        ((and (memq (car expr) '(FORALL FORSOME))
              (= (length expr) 3)
              (pair? (cadr expr))
              (all-binding-specs? (cadr expr)))
         (let* ((q          (car expr))
                (flat-specs (apply append (map flatten-binding-spec (cadr expr))))
                (body       (vnb-unwind (caddr expr))))
           (let loop ((ss (reverse flat-specs)) (acc body))
             (if (null? ss)
                 acc
                 (loop (cdr ss) `(,q (,(car ss)) ,acc))))))
        (else (cons (car expr) (map vnb-unwind (cdr expr)))))))

(define (vnb-wind expr)
  (if (not (pair? expr))
      expr
      (let ((expr (cons (car expr) (map vnb-wind (cdr expr)))))
        (if (and (memq (car expr) '(FORALL FORSOME))
                 (= (length expr) 3)
                 (pair? (cadr expr))
                 (all-binding-specs? (cadr expr)))
            (let loop ((q     (car expr))
                       (specs (cadr expr))
                       (body  (caddr expr)))
              (if (and (pair? body)
                       (eq? (car body) q)
                       (= (length body) 3)
                       (pair? (cadr body))
                       (all-binding-specs? (cadr body)))
                  (loop q
                        (append specs (cadr body))
                        (caddr body))
                  `(,q ,specs ,body)))
            expr))))

;;; -----------------------------------------------------------------------
;;; Structure specialization shorthand
;;;
;;; (spec 'HARP 'RING 'harp-is-ring)
;;; Installs all ring theorems specialized to HARP.
;;; Not a proof command — does not touch *ps*.

(define (spec instance struct is-thm)
  (specialize-structure instance struct is-thm))
