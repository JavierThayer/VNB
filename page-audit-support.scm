;;; Can a PRINTED script be typed back in?  Two questions, measured.

;; 1. How many scripts name a MINTED eigenvariable (u_4, n__1591, ...)?
(define (eigen-sym? x)
  (and (symbol? x)
       (let* ((s (symbol->string x)) (n (string-length s)))
         (let loop ((i (- n 1)) (digits 0))
           (cond ((< i 0) #f)
                 ((char-numeric? (string-ref s i)) (loop (- i 1) (+ digits 1)))
                 ((and (char=? #\_ (string-ref s i)) (> digits 0) (> i 0)) #t)
                 (else #f))))))
(define (mentions-eigen? f)
  (cond ((pair? f) (or (mentions-eigen? (car f)) (mentions-eigen? (cdr f))))
        (else (eigen-sym? f))))

(let ((with 0) (tot 0) (examples '()))
  (for-each (lambda (nm)
              (let ((sc (hash-table-ref/default *proof-script-table* nm '())))
                (when (pair? sc)
                  (set! tot (+ tot 1))
                  (when (mentions-eigen? sc)
                    (set! with (+ with 1))
                    (when (< (length examples) 5)
                      (set! examples (cons nm examples)))))))
            (hash-table-keys *proof-script-table*))
  (display ";; scripts total: ") (display tot) (newline)
  (display ";; scripts naming a minted eigenvariable: ") (display with) (newline)
  (display ";; examples: ") (display examples) (newline))

;; 2. Emit a stored proof as a standalone file and LOAD it, the way a person
;;    who typed the page would.  No counter restore, no harness.
(define (paper-test nm newnm)
  (let ((goal (lookup-theorem nm))
        (sc   (hash-table-ref/default *proof-script-table* nm '()))
        (file (string-append "/tmp/claude-1000/-home-ubuntu/db8c729a-9183-49e2-9a0c-e7eadabd7621/scratchpad/" (symbol->string newnm) ".scm")))
    (call-with-output-file file
      (lambda (port) (script--write-block port newnm goal sc)))
    (display ";; --- ") (display nm) (display " -> ") (display file)
    (display "  (") (display (length sc)) (display " steps, eigen=")
    (display (mentions-eigen? sc)) (display ")") (newline)
    (call-with-current-continuation
     (lambda (bail)
       (bind-condition-handler (list condition-type:error)
         (lambda (c) (display ";;   LOAD RAISED: ")
                     (display (condition/report-string c)) (newline) (bail #f))
         (lambda ()
           (quietly (lambda () (load file)))
           (display ";;   loaded; proof-done? = ")
           (display (and *ps* (proof-done? *ps*))) (newline)))))))
