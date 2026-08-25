;;; proof-map.scm -- (proof-map): see the WHOLE proof tree, closed branches
;;; included.
;;;
;;; WHY THIS EXISTS.  Every view VNB offered was a view of the OPEN leaves:
;;; `(proof-leaves)', the Focus panel, `(show)'.  A branch that closes simply
;;; vanishes from all of them.  So the ordinary question in the middle of an
;;; induction -- "is the base case actually finished, or did I just wander off
;;; it?" -- had no direct answer; the user reported exactly that on 2026-08-16
;;; ("It's hard to tell, because I don't see a way of navigating to non-leaf
;;; nodes").  The information was always in the graph: `dg-sequent-nodes' holds
;;; every node ever posted, and each carries its `in-arrows' -- the inference
;;; nodes that justify it -- so the tree can be walked from the root.  Nothing
;;; exposed it.
;;;
;;; This is a READ-ONLY inspector.  It mutates nothing, proves nothing, and
;;; cannot affect a bill; it is a printout of state that already exists.
;;;
;;;   (proof-map)          the tree from the root, one line per node
;;;   (proof-map 'goals)   the same, with each node's full goal
;;;
;;; Reading it: `*' marks the FOCUS, `+' a closed (grounded) node, `o' an open
;;; leaf -- an obligation you still owe -- and the rule name in brackets is the
;;; inference that justifies the node beneath it.

(define (pm--status sqn)
  (cond ((sequent-node-grounded? sqn) "+")
        ((null? (sequent-node-in-arrows sqn)) "o")
        (else ".")))          ; justified, but a child is still open

(define (pm--goal-str sqn)
  (expression->string (wff-formula (sequent-node-assertion sqn))))

(define (pm--abbrev s n)
  (if (<= (string-length s) n)
      s
      (string-append (substring s 0 (- n 3)) "...")))

;;; The children of SQN: the hypotheses of the inference that justifies it.
;;; A node has at most one justifying inference in practice; if it somehow has
;;; more, they are all shown, since hiding one would misreport the tree.
(define (pm--children sqn)
  (apply append (map inference-node-hypotheses (sequent-node-in-arrows sqn))))

(define (pm--rule sqn)
  (let ((ins (sequent-node-in-arrows sqn)))
    (and (pair? ins) (inference-node-rule (car ins)))))

;;; THE VALUE, separately from the printout.  Scheme returns values; a renderer
;;; (Emacs, or the REPL printer below) decides how to show them.  `(proof-map)'
;;; is the renderer; this is the datum, so anything driving the prover
;;; programmatically -- Emacs, a test, an agent -- can ask "is the base case
;;; closed?" without parsing prose.
;;;
;;; Each node is
;;;   ((number . n) (status . closed|open|partial) (focus . bool)
;;;    (rule . <symbol or #f>) (goal . <raw formula>) (children . (...)))
;;; A node reached a second time (the graph hash-conses alpha-equivalent
;;; sequents) is emitted as ((number . n) (repeat . #t)) rather than expanded,
;;; which is what keeps this finite.
(define (proof-map-data)
  (and *ps*
       (let ((focus (proof-state-focus *ps*))
             (seen  '()))
         (let walk ((sqn (proof-state-root *ps*)))
           (if (memq sqn seen)
               (list (cons 'number (sequent-node-number sqn)) (cons 'repeat #t))
               (begin
                 (set! seen (cons sqn seen))
                 (list (cons 'number (sequent-node-number sqn))
                       (cons 'status (cond ((sequent-node-grounded? sqn) 'closed)
                                           ((null? (sequent-node-in-arrows sqn)) 'open)
                                           (else 'partial)))
                       (cons 'focus  (eq? sqn focus))
                       (cons 'rule   (pm--rule sqn))
                       (cons 'goal   (wff-formula (sequent-node-assertion sqn)))
                       (cons 'children (map walk (pm--children sqn))))))))))

(define (proof-map . opts)
  (let ((full? (memq 'goals opts)))
    (cond
      ((not *ps*) (display ";; proof-map: no proof in progress.") (newline))
      (else
       (let ((focus (proof-state-focus *ps*))
             (seen  '()))
         (display ";; proof map -- `+' closed, `o' OPEN (you owe this), `.' partly")
         (display " closed, `*' focus") (newline)
         (let walk ((sqn (proof-state-root *ps*)) (depth 0))
           ;; The graph hash-conses alpha-equivalent sequents, so a node can be
           ;; reached twice; print it once and mark the repeat, rather than
           ;; looping forever.
           (if (memq sqn seen)
               (begin
                 (display ";;   ")
                 (let lp ((k 0)) (when (< k depth) (display "  ") (lp (+ k 1))))
                 (display "^ (already shown above)") (newline))
               (begin
                 (set! seen (cons sqn seen))
                 (display ";;   ")
                 (let lp ((k 0)) (when (< k depth) (display "  ") (lp (+ k 1))))
                 (display (pm--status sqn))
                 (if (eq? sqn focus) (display "*") (display " "))
                 (display " [") (display (or (sequent-node-number sqn) '?))
                 (display "] ")
                 (display (if full? (pm--goal-str sqn)
                              (pm--abbrev (pm--goal-str sqn) 60)))
                 (let ((r (pm--rule sqn)))
                   (when r (display "   <") (display r) (display ">")))
                 (newline)
                 (for-each (lambda (c) (walk c (+ depth 1)))
                           (pm--children sqn)))))
         (let ((open (length (proof-open-leaves *ps*))))
           (display ";;   ")
           (if (proof-done? *ps*)
               (display "PROVED -- no open leaves.")
               (begin (display open)
                      (display (if (= open 1) " open leaf still owed."
                                   " open leaves still owed."))))
           (newline)))))))
