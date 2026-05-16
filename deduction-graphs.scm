;;; deduction-graphs.scm -- deduction graph: sequent nodes and inference nodes
;;;
;;; A DEDUCTION GRAPH is a directed acyclic graph where:
;;;   - SEQUENT NODES hold sequents (hypotheses => goal)
;;;   - INFERENCE NODES connect a list of hypothesis sequent nodes
;;;     (the "hypotheses" of the inference) to a single conclusion sequent node
;;;
;;; An inference node represents: "the conclusion is justified by these hypotheses
;;; via this rule."
;;;
;;; A sequent node is GROUNDED when it has an inference node whose own
;;; hypothesis nodes are all grounded.  The root is grounded iff the proof
;;; is complete.
;;;
;;; Arrows:
;;;   sqn --out-arrow--> infn  means sqn is a hypothesis of infn
;;;   infn --in-arrow--> sqn   means infn is a justification of sqn
;;;
;;; (Following IMPS naming conventions.)

;;; -----------------------------------------------------------------------
;;; Sequent nodes

(define-record-type <sequent-node>
  (%make-sequent-node sequent)
  sequent-node?
  (sequent    sequent-node-sequent)
  (graph      sequent-node-graph      set-sequent-node-graph!)
  (out-arrows sequent-node-out-arrows set-sequent-node-out-arrows!) ; infns where this is hyp
  (in-arrows  sequent-node-in-arrows  set-sequent-node-in-arrows!)  ; infns that justify this
  (grounded?  sequent-node-grounded?  set-sequent-node-grounded?!)
  (number     sequent-node-number     set-sequent-node-number!))

(define (make-sequent-node sequent)
  (let ((sqn (%make-sequent-node sequent)))
    (set-sequent-node-out-arrows! sqn '())
    (set-sequent-node-in-arrows!  sqn '())
    (set-sequent-node-grounded?!  sqn #f)
    (set-sequent-node-graph!      sqn #f)
    (set-sequent-node-number!     sqn #f)
    sqn))

(define (sequent-node-assumptions sqn)
  (sequent-assumptions (sequent-node-sequent sqn)))

(define (sequent-node-assertion sqn)
  (sequent-assertion (sequent-node-sequent sqn)))

(define (sequent-node->string sqn)
  (string-append
   "[" (number->string (or (sequent-node-number sqn) -1)) "] "
   (sequent->string (sequent-node-sequent sqn))
   (if (sequent-node-grounded? sqn) "  [GROUNDED]" "")))

;;; -----------------------------------------------------------------------
;;; Inference nodes

(define-record-type <inference-node>
  (make-inference-node rule hypotheses conclusion)
  inference-node?
  (rule        inference-node-rule)
  (hypotheses  inference-node-hypotheses)   ; list of sequent-nodes
  (conclusion  inference-node-conclusion))  ; sequent-node

;;; -----------------------------------------------------------------------
;;; Deduction graphs

(define-record-type <deduction-graph>
  (%make-deduction-graph)
  deduction-graph?
  (sequent-nodes  dg-sequent-nodes  set-dg-sequent-nodes!)
  (inference-nodes dg-inference-nodes set-dg-inference-nodes!)
  (node-counter   dg-node-counter   set-dg-node-counter!))

(define (make-deduction-graph)
  (let ((dg (%make-deduction-graph)))
    (set-dg-sequent-nodes!   dg '())
    (set-dg-inference-nodes! dg '())
    (set-dg-node-counter!    dg 0)
    dg))

(define (dg-add-sequent-node! dg sqn)
  (set-sequent-node-graph!  sqn dg)
  (set-sequent-node-number! sqn (dg-node-counter dg))
  (set-dg-node-counter!     dg (+ 1 (dg-node-counter dg)))
  (set-dg-sequent-nodes!    dg (append (dg-sequent-nodes dg) (list sqn)))
  sqn)

(define (dg-add-inference-node! dg infn)
  (set-dg-inference-nodes! dg (cons infn (dg-inference-nodes dg)))
  infn)

;;; Post a new sequent into the graph (or find an existing alpha-equivalent one).
(define (dg-post! dg sequent)
  (or (dg-find-sequent-node dg sequent)
      (dg-add-sequent-node! dg (make-sequent-node sequent))))

(define (dg-find-sequent-node dg sequent)
  (let ((asms  (sequent-assumptions sequent))
        (assrt (sequent-assertion   sequent)))
    (find-first
     (lambda (sqn)
       (and (wff-equiv? assrt (sequent-node-assertion sqn))
            (context-same? asms (sequent-node-assumptions sqn))))
     (dg-sequent-nodes dg))))

(define (context-same? asms1 asms2)
  (and (= (length asms1) (length asms2))
       (every (lambda (f) (context-contains? asms2 f)) asms1)))

(define (find-first pred lst)
  (cond ((null? lst) #f)
        ((pred (car lst)) (car lst))
        (else (find-first pred (cdr lst)))))

(define (every pred lst)
  (cond ((null? lst) #t)
        ((pred (car lst)) (every pred (cdr lst)))
        (else #f)))

;;; -----------------------------------------------------------------------
;;; Recording an inference in the graph
;;;
;;; (dg-apply-rule! dg rule hyp-sequents conclusion-sqn)
;;;   hyp-sequents: list of raw sequents (will be posted into graph)
;;;   conclusion-sqn: the sequent node being justified
;;;
;;; Returns the list of hypothesis sequent nodes (new or existing).

(define (dg-apply-rule! dg rule hyp-sequents conclusion-sqn)
  (let ((hyp-nodes (map (lambda (s) (dg-post! dg s)) hyp-sequents)))
    (let ((infn (make-inference-node rule hyp-nodes conclusion-sqn)))
      (dg-add-inference-node! dg infn)
      (for-each (lambda (h)
                  (set-sequent-node-out-arrows!
                   h (cons infn (sequent-node-out-arrows h))))
                hyp-nodes)
      (set-sequent-node-in-arrows!
       conclusion-sqn
       (cons infn (sequent-node-in-arrows conclusion-sqn)))
      (dg-propagate-grounding! conclusion-sqn)
      hyp-nodes)))

;;; A sequent node is grounded when it has at least one inference node
;;; all of whose hypothesis nodes are themselves grounded.
(define (dg-propagate-grounding! sqn)
  (when (not (sequent-node-grounded? sqn))
    (when (any (lambda (infn)
                 (every sequent-node-grounded?
                        (inference-node-hypotheses infn)))
               (sequent-node-in-arrows sqn))
      (set-sequent-node-grounded?! sqn #t)
      ;; Propagate upward to any inference nodes this sqn is a hypothesis of
      (for-each (lambda (infn)
                  (dg-propagate-grounding!
                   (inference-node-conclusion infn)))
                (sequent-node-out-arrows sqn)))))

;;; -----------------------------------------------------------------------
;;; Status

(define (dg-ungrounded-nodes dg)
  ;; Leaf nodes (no in-arrows = not yet justified) come first —
  ;; these are the actual open proof obligations.
  (let ((all (filter (lambda (sqn) (not (sequent-node-grounded? sqn)))
                     (dg-sequent-nodes dg))))
    (append (filter (lambda (sqn) (null? (sequent-node-in-arrows sqn))) all)
            (filter (lambda (sqn) (not (null? (sequent-node-in-arrows sqn)))) all))))

(define (dg-proved? dg root-sqn)
  (sequent-node-grounded? root-sqn))

(define (dg-print dg)
  (display "Deduction graph:\n")
  (for-each (lambda (sqn)
              (display "  ")
              (display (sequent-node->string sqn))
              (newline))
            (dg-sequent-nodes dg)))
