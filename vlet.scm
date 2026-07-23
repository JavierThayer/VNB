;;; vlet.scm -- (vlet (names...) FORMER): bind names to proof objects.
;;;
;;; FORMERs:
;;;   (match PATTERN)  -- bind each name to its position in a context formula (or
;;;                       subterm) matching PATTERN.  The binder names ARE the holes
;;;                       (wildcards); everything else in PATTERN is literal.  Pure
;;;                       selection -- no proof step, no obligation.  Hard error if
;;;                       nothing matches (you named a piece of something absent).
;;;   (choice)         -- eliminate the sole existential in context; bind its witness.
;;;   (choice v BODY)  -- present-else-debt: if (FORSOME v BODY) is in context (alpha),
;;;                       eliminate it; else cut it, LEAVE the existence side-goal OPEN
;;;                       (the debt leaf), and eliminate on the main branch.  Either
;;;                       way the witness is bound AND its defining property BODY[witness]
;;;                       is landed in context (that is what `ai' on the existential does).
;;;
;;; No choice AXIOM: a single witness is plain existential-elimination (present, or
;;; cut-as-debt then eliminate).  The Hilbert selector would only be needed to make
;;; (choice P) a reusable term, which vlet does not form.  iota is the same shape with
;;; a unique-existence obligation -- not yet wired.
;;;
;;; Reuses driver-kit (any-pred, dk-asms, dk-goal-of, dk-focus!, dk-opened) and sketch
;;; (sk--split!); loads after both.

(define (vlet--find p) (any-pred p (dk-asms)))

;; structural match; symbols in HOLES are wildcards.  Returns alist hole->term, or #f.
(define (vlet--pm pat form holes binds)
  (cond ((not binds) #f)
        ((and (symbol? pat) (memq pat holes))
         (let ((prev (assq pat binds)))
           (if prev (and (equal? (cdr prev) form) binds) (cons (cons pat form) binds))))
        ((and (pair? pat) (pair? form))
         (vlet--pm (cdr pat) (cdr form) holes (vlet--pm (car pat) (car form) holes binds)))
        ((and (null? pat) (null? form)) binds)
        ((equal? pat form) binds)
        (else #f)))

;; match PATTERN at FORM or any subterm (destructure reaches nested conjuncts).
(define (vlet--match-in pattern holes form)
  (or (vlet--pm pattern form holes '())
      (and (pair? form)
           (let loop ((subs form))
             (and (pair? subs)
                  (or (and (pair? (car subs)) (vlet--match-in pattern holes (car subs)))
                      (loop (cdr subs))))))))

(define (vlet--match pattern holes)
  (let loop ((fs (dk-asms)))
    (cond ((null? fs) (error "vlet match: no context formula matches" pattern))
          ((vlet--match-in pattern holes (car fs)))
          (else (loop (cdr fs))))))

;; ai every AND in the tree rooted at F to exhaustion (full unpack of a landed body).
(define (vlet--split-conj! f)
  (when (and (pair? f) (eq? (car f) 'AND))
    (vnb-guard (lambda () (ai f)))
    (vlet--split-conj! (cadr f))
    (vlet--split-conj! (caddr f))))

;; eliminate an in-context existential EX; ai LANDS its body P[witness] into context
;; (the defining property, granted for free), then split it; return the witness symbol.
(define (vlet--elim! ex)
  (let ((fv0 (apply append (map free-vars (dk-asms)))) (ctx0 (dk-asms)))
    (ai ex)
    (for-each vlet--split-conj!
              (filter (lambda (f) (and (not (member f ctx0)) (pair? f) (eq? (car f) 'AND)))
                      (dk-asms)))
    (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                         (apply append (map free-vars (dk-asms))))))
      (if (pair? fresh) (car fresh) (error "vlet: no witness landed for" ex)))))

(define (vlet--sole-existential)
  (or (vlet--find (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))))
      (error "vlet choice: no existential in context")))

(define (vlet--choice! . opt)
  (cond
    ((null? opt) (vlet--elim! (vlet--sole-existential)))          ; eliminate sole existential
    (else
     (let* ((ex  (list 'FORSOME (car opt) (cadr opt)))
            (hit (vlet--find (lambda (f) (alpha-equiv? f ex)))))
       (if hit
           (vlet--elim! hit)                                       ; present: free
           (let* ((new  (dk-opened (lambda () (cut ex))))          ; absent: debt + eliminate
                  (side (any-pred (lambda (s) (alpha-equiv? (dk-goal-of s) ex)) new))
                  (main (any-pred (lambda (s) (not (eq? s side))) new)))
             (display ";; vlet: existence not in context -- LEAVING debt leaf: ")
             (write ex) (newline)
             (dk-focus! main)                                      ; side stays OPEN = the debt
             (vlet--elim! ex)))))))

(define-syntax vlet
  (syntax-rules (match choice)
    ((vlet (nm ...) (match pattern))
     (begin (define nm (cdr (or (assq 'nm (vlet--match 'pattern '(nm ...)))
                                (error "vlet: hole not bound" 'nm)))) ...))
    ((vlet (nm) (choice))         (define nm (vlet--choice!)))
    ((vlet (nm) (choice v body))  (define nm (vlet--choice! 'v 'body)))))
