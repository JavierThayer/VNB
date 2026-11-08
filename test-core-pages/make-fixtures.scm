;;; test-core-pages/make-fixtures.scm -- writes the hand-chosen core-page FIXTURES of the
;;; suite (core-replay checks) by running a CORE-ONLY script and recording, per step, the
;;; node, the sequent and the hypothesis sequents the entry point produced.  It is NOT the
;;; lowering (core-capture.scm): it handles only scripts that are already core, one entry
;;; point per step, run at the current focus.  Regenerate after a kernel change:
;;;
;;;     ./prover -b test-core-pages/make-fixtures.scm < /dev/null
;;;
;;; Script items:  (CMD ARG ...)  run at the focus, then focus the first open hypothesis it
;;; produced, else the first open leaf.  An argument (%mint K) is the K-th name minted so
;;; far in the run; (%thm NAME) is the raw statement of theorem NAME.  The kernel-hash field
;;; is written as "*" (a hand-written page; the replayer does not compare it).

(define (cfx--subst-arg a minted)
  (cond ((and (pair? a) (eq? (car a) '%mint)) (list-ref minted (- (cadr a) 1)))
        ((and (pair? a) (eq? (car a) '%thm))
         (let ((s (lookup-theorem (cadr a)))) (if (wff? s) (wff-formula s) s)))
        (#t a)))

(define (cfx-page name statement script)
  (fluid-let ((*ps* #f) (*fresh-counter* *fresh-counter*) (*fresh-log* *fresh-log*)
              (*proof-used-defs* '()) (*pi-owed-nodes* '()) (*dg-journal* '()))
    (let* ((mark *fresh-log*)
           (ps (start-proof (make-wff statement)))
           (dg (proof-state-dg ps))
           (ids (list (cons (proof-state-root ps) 1)))
           (next-id 2)
           (k 0)
           (steps '()))
      (define (id-of n)
        (let ((e (assq n ids)))
          (if e (cdr e)
              (begin (set! ids (cons (cons n next-id) ids)) (set! next-id (+ next-id 1)) (- next-id 1)))))
      (for-each
       (lambda (item)
         (let* ((node (proof-state-focus ps))
                (row (or (assq (car item) *core-dispatch*) (error "cfx: not a core command" item)))
                (args (map (lambda (a) (cfx--subst-arg a (fresh-log-since mark))) (cdr item)))
                (seq (cr--node-raw node))
                (old (dg-inference-nodes dg))
                (res (apply (cadddr row) node args)))
           (if (not res) (error "cfx: the entry point declined" name item))
           (let* ((new (let loop ((l (dg-inference-nodes dg)) (acc '()))
                         (if (eq? l old) acc (loop (cdr l) (cons (car l) acc)))))
                  (hyps (append-map inference-node-hypotheses new)))
             (set! k (+ k 1))
             (set! steps
                   (cons `(step ,k (at-node ,(id-of node)) ,(cons (car item) args)
                                (sequent ,@seq)
                                (hyps ,@(map (lambda (h) (cons 'sequent (cr--node-raw h))) hyps)))
                         steps))
             (let ((open (filter (lambda (h) (not (sequent-node-grounded? h))) hyps)))
               (if (pair? open) (focus-on ps (car open)) (focus-on-first-open ps))))))
       script)
      (if (not (proof-done? ps)) (error "cfx: the script does not ground the root" name))
      (let* ((minted (fresh-log-since mark))
             (M (let loop ((ms minted) (i 1) (acc '()))
                  (if (null? ms) (reverse acc)
                      (loop (cdr ms) (+ i 1)
                            (cons (cons (car ms) (string->symbol (string-append "v" (number->string i)))) acc))))))
        (cr--map M
                 `(core-page ,name (statement ,statement) (kernel-hash "*") (mints ,@(map cdr M))
                             ,@(reverse steps)))))))

(define (cfx-write! page)
  (let ((p (string-append *prover-dir* "test-core-pages/" (symbol->string (cadr page)) ".core")))
    (call-with-output-file p
      (lambda (port)
        (display ";;; core page FIXTURE (hand-chosen proof, core-only script), written by" port) (newline port)
        (display ";;; test-core-pages/make-fixtures.scm.  Format: docs/core-page-format.md." port) (newline port)
        (display "(core-page " port) (write (cadr page) port) (newline port)
        (for-each (lambda (f) (display "  " port) (write f port) (newline port)) (cddr page))
        (display ")" port) (newline port)))
    (display ";; wrote ") (display p) (newline)))

(define *cfx-fixtures*
  (list
   (list 'core-fixture-and-comm
         '(FORALL p (FORALL q (IMPLIES (AND (IN p SET) (IN q SET)) (AND (IN q SET) (IN p SET)))))
         '((di) (di) (ai (AND (IN p SET) (IN q SET))) (di) (ass) (ass)))
   (list 'core-fixture-mint
         '(FORALL a (IMPLIES (FORSOME x (IN x a)) (FORSOME y (IN y a))))
         '((di) (di) (ai (FORSOME x (IN x a))) (ew (%mint 1)) (ass)))
   (list 'core-fixture-ineq
         '(FORALL x (IMPLIES (IN x RR) (IMPLIES (<= x 0) (<= x 1))))
         '((di) (di) (ineq (<= x 0) (IN x RR))))
   (list 'core-fixture-cite
         '(FORALL k (IMPLIES (IN k NN) (IN k RR)))
         '((di) (ta nn-in-rr) (inst (%thm nn-in-rr) k) (detach! (IMPLIES (IN k NN) (IN k RR))) (ass)))
   (list 'core-fixture-share
         '(FORALL a (AND (IMPLIES (IN a SET) (IN a SET)) (IMPLIES (IN a SET) (IN a SET))))
         '((di) (di) (di) (ass)))
   (list 'core-fixture-arith
         '(= (+ 2 2) 4)
         '((arith)))))

(for-each (lambda (f) (cfx-write! (cfx-page (car f) (cadr f) (caddr f)))) *cfx-fixtures*)
