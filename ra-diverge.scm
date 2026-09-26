;;; Where does a replay first DIVERGE from the proof as it ran?
;;; *proof-live-trace* holds (entry goal asms focus-id open-ids) captured live,
;;; one record per recorded step, so the comparison is exact.
(load "/home/ubuntu/prover/scratchpad/replay-audit.scm")

(define (rd--state)
  (let ((done (proof-done? *ps*)))
    (list (and (not done) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
          (if done '() (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
          (length (proof-open-goals *ps*)))))

(define (rd--compare st rec i cmd bail)
  (cond ((not (equal? (car st)   (cadr rec)))   (bail (list 'goal i cmd)))
        ((not (equal? (cadr st)  (caddr rec)))  (bail (list 'asms i cmd)))
        ((not (=      (caddr st) (length (list-ref rec 4)))) (bail (list 'open i cmd)))
        (else #t)))

(define (rd--body name goal script trace bail)
  (fluid-let ((*fresh-counter*
               (hash-table-ref/default *proof-start-counter* name *fresh-counter*)))
    (sp (make-wff goal))
    ;; The live trace does NOT hold a record for every script entry: `focus',
    ;; `focus-id', `prop' and `minimize!' call record-cmd! directly and never
    ;; vnb--capture-step!.  So align by ENTRY: compare only where the trace has
    ;; a record for the step just applied.
    (let loop ((s script) (t trace) (i 1))
      (if (null? s)
          'same
          (begin
            (fluid-let ((*replaying?* #t))
              (apply-recorded-cmd! (caar s) (cdar s)))
            (if (and (pair? t) (equal? (car s) (caar t)))
                (begin (rd--compare (rd--state) (car t) i (caar s) bail)
                       (loop (cdr s) (cdr t) (+ i 1)))
                (loop (cdr s) t (+ i 1))))))))

(define (rd--one name)
  (let ((goal   (ignore-errors (lambda () (lookup-theorem name))))
        (script (hash-table-ref/default *proof-script-table* name '()))
        (trace  (hash-table-ref/default *proof-live-trace* name '())))
    (if (not (and (pair? goal) (pair? script) (pair? trace)))
        #f
        (call-with-current-continuation
         (lambda (bail)
           (bind-condition-handler (list condition-type:error)
             (lambda (c) (bail (list 'raised 0 'x)))
             (lambda ()
               (quietly (lambda () (rd--body name goal script trace bail))))))))))

(define *rd* '())
(define (rd-run!)
  (set! *rd* '())
  (for-each (lambda (nm)
              (let ((r (rd--one nm)))
                (if r (set! *rd* (cons (cons nm r) *rd*)))))
            (sort (hash-table-keys *proof-script-table*)
                  (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
  (let ((h (make-equal-hash-table)))
    (for-each (lambda (r)
                (let ((k (if (eq? (cdr r) 'same) 'same (cons (cadr r) (cadddr r)))))
                  (hash-table-set! h k (+ 1 (hash-table-ref/default h k 0)))))
              *rd*)
    (newline)
    (display ";; ==== DIVERGENCE vs LIVE trace, ") (display (length *rd*))
    (display " comparable scripts ====") (newline)
    (for-each (lambda (p) (display ";;  ") (display (cdr p)) (display "  ") (write (car p)) (newline))
              (sort (map (lambda (k) (cons k (hash-table-ref h k 0))) (hash-table-keys h))
                    (lambda (a b) (> (cdr a) (cdr b))))))
  (let ((ds (filter (lambda (r) (not (eq? (cdr r) 'same))) *rd*)))
    (newline) (display ";; -- 20 earliest divergences (name kind step cmd) --") (newline)
    (for-each (lambda (r)
                (display ";;  ") (display (car r)) (display "  ") (display (cadr r))
                (display "  step ") (display (caddr r))
                (display "  ") (display (cadddr r)) (newline))
              (list-head (sort ds (lambda (a b) (< (caddr a) (caddr b))))
                         (min 20 (length ds))))))
(rd-run!)
