;;; Does every minted-variable USE in a script trace to a unique minting STEP?
;;; B's precondition: to record a witness as "the variable step 47 minted" there
;;; must BE such a step, exactly one, findable from the script alone.
;;;
;;; Attribution needs no guessing.  fresh-var names a variable <hint>_<n> where n
;;; is *fresh-counter* at mint time (expressions.scm:635-644) and the counter only
;;; rises, so the step during which the counter crossed n is the minter.

(define (mint--suffix x)
  (and (symbol? x)
       (let* ((s (symbol->string x)) (n (string-length s)))
         (let loop ((i (- n 1)) (digits 0))
           (cond ((< i 0) #f)
                 ((char-numeric? (string-ref s i)) (loop (- i 1) (+ digits 1)))
                 ((and (char=? #\_ (string-ref s i)) (> digits 0) (> i 0))
                  (string->number (string-tail s (+ i 1))))
                 (else #f))))))

(define (mint--names-in f acc)
  (cond ((pair? f) (mint--names-in (car f) (mint--names-in (cdr f) acc)))
        ((mint--suffix f) (if (memq f acc) acc (cons f acc)))
        (else acc)))

;;; Run the script, returning ((step lo hi) ...) for the steps that minted.
(define (mint--spans goal script)
  (let ((spans '()))
    (sp (make-wff goal))
    (let loop ((s script) (i 1))
      (if (null? s)
          (reverse spans)
          (let ((lo *fresh-counter*))
            (fluid-let ((*replaying?* #t))
              (apply-recorded-cmd! (caar s) (cdar s)))
            (if (> *fresh-counter* lo)
                (set! spans (cons (list i lo *fresh-counter*) spans)))
            (loop (cdr s) (+ i 1)))))))

(define (mint--score nm goal script)
  (let* ((spans (mint--spans goal script))
         (used  (mint--names-in script '()))
         (attr 0) (unattr 0) (multi 0) (orphans '()))
    (for-each
     (lambda (v)
       (let* ((k     (mint--suffix v))
              (owner (filter (lambda (sp) (and (>= k (cadr sp)) (< k (caddr sp)))) spans)))
         (cond ((null? owner) (set! unattr (+ unattr 1))
                              (set! orphans (cons v orphans)))
               ((> (length owner) 1) (set! multi (+ multi 1)))
               (else (set! attr (+ attr 1))))))
     used)
    (list nm (if (= unattr 0) 'all-attributed 'has-orphan) attr unattr multi
          (reverse orphans) (length spans))))

(define *mint* '())

(define (mint--one nm)
  (let ((goal   (hash-table-ref/default *theorem-table* nm #f))
        (script (hash-table-ref/default *proof-script-table* nm '())))
    (if (and goal (pair? script) (pair? (mint--names-in script '())))
        (let ((res
               (call-with-current-continuation
                (lambda (bail)
                  (bind-condition-handler (list condition-type:error)
                    (lambda (c) (bail (list nm 'replay-error 0 0 0 '() 0)))
                    (lambda ()
                      (let ((out #f))
                        (with-output-to-string
                          (lambda ()
                            (fluid-let ((*ps* *ps*)
                                        (*current-goal* *current-goal*)
                                        (*proof-script* *proof-script*)
                                        (*live-trace* *live-trace*)
                                        (*vnb-undo-stack* *vnb-undo-stack*)
                                        (*fresh-counter*
                                         (hash-table-ref/default
                                          *proof-start-counter* nm *fresh-counter*)))
                              (quietly
                               (lambda ()
                                 (set! out (mint--score nm goal script)))))))
                        out)))))))
          (set! *mint* (cons res *mint*))))))

(define (mint-run!)
  (set! *mint* '())
  (for-each mint--one (sort (hash-table-keys *proof-script-table*)
                            (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
  (let ((ok 0) (orph 0) (err 0) (ta 0) (tu 0) (tm 0) (worst '()))
    (for-each
     (lambda (r)
       (case (cadr r)
         ((all-attributed) (set! ok (+ ok 1)))
         ((has-orphan) (set! orph (+ orph 1))
                       (if (< (length worst) 10)
                           (set! worst (cons (list (car r) (list-ref r 5)) worst))))
         (else (set! err (+ err 1))))
       (set! ta (+ ta (caddr r)))
       (set! tu (+ tu (list-ref r 3)))
       (set! tm (+ tm (list-ref r 4))))
     *mint*)
    (newline)
    (display ";; ==== MINT ATTRIBUTION: ") (display (length *mint*))
    (display " scripts naming a minted variable ====") (newline)
    (display ";;   every use traced to a step : ") (display ok) (newline)
    (display ";;   has an UNATTRIBUTABLE use  : ") (display orph) (newline)
    (display ";;   replay error (not scored)  : ") (display err) (newline)
    (display ";;   uses: traced ") (display ta)
    (display "  orphaned ") (display tu)
    (display "  ambiguous ") (display tm) (newline)
    (newline)
    (display ";;   orphan examples (script, the names):") (newline)
    (for-each (lambda (w) (display ";;     ") (display (car w))
                      (display "  ") (write (cadr w)) (newline))
              worst)))
(mint-run!)
