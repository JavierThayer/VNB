;;; probe-rewrite.scm -- can the complement<->preimage rewrite even fire,
;;; and in the direction the closed-preimage proof needs?
(define (==> label val)
  (display "==> ") (display label) (display ": ") (write val) (newline))
(define (--- title)
  (newline) (display ";;; ----- ") (display title) (display " -----") (newline))
(define (goal) (expression->string (sequent-node-assertion (proof-state-focus *ps*))))

(--- "is preimage-complement a macete? is there a -rev?")
(==> "preimage-complement registered as theorem"
     (and (hash-table-ref/default *theorem-table* 'preimage-complement #f) #t))
(==> "preimage-complement-rev registered"
     (and (hash-table-ref/default *theorem-table* 'preimage-complement-rev #f) #t))

(--- "forward dir: mac preimage-complement on a goal holding the L-form")
;; L-form = preimage(s,f,complement-in(x(t),A)); rewrite should give R-form.
(sp (make-wff '(IS-OPEN s (PREIMAGE s f (COMPLEMENT-IN (X t) A)))))
(==> "before" (goal))
(mac 'preimage-complement)
(==> "after mac preimage-complement" (goal))

(--- "reverse dir: the direction the closed proof needs (R-form -> L-form)")
;; R-form = complement-in(x(s),preimage(s,f,A)); need it -> preimage(s,f,complement-in(x(t),A)).
;; t is introduced, not present in R -- watch for it going undetermined.
(sp (make-wff '(IS-OPEN s (COMPLEMENT-IN (X s) (PREIMAGE s f A)))))
(==> "before" (goal))
(mac 'preimage-complement-rev)
(==> "after mac preimage-complement-rev" (goal))

(==> "DONE-PROBE" 'ok)
