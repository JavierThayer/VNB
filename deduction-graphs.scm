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

;;; -----------------------------------------------------------------------
;;; THE UNDO JOURNAL  --  the mechanism under both `backup-one' and the
;;; inert-command notice.
;;;
;;; The graph is mutated in exactly four places, and nowhere else:
;;;
;;;   dg-add-sequent-node!    -- appends to dg-sequent-nodes, bumps the counter
;;;   dg-add-inference-node!  -- conses onto dg-inference-nodes
;;;   dg-apply-rule!          -- writes out-arrows on the hypothesis nodes and
;;;                              an in-arrow on the conclusion node
;;;   dg-propagate-grounding! -- sets grounded? on a node and its ancestors
;;;
;;; The two node LISTS are rebuilt, never destructively spliced (`append' copies
;;; and `cons' shares a tail), so each is restorable in O(1) from a value read
;;; before the command -- a pointer for the inference list, and for the sequent
;;; list the node COUNTER, which is its length (see the mark below for why the
;;; pointer is the wrong thing to hold there).  The PER-NODE fields are the part
;;; that is overwritten in place, so those are journalled: old value recorded
;;; before the write.
;;;
;;; A `proof-state' is NOT a snapshot of anything.  There is exactly one of them
;;; per proof (start-proof is its only constructor) and every cmd-* mutates it
;;; through set-proof-state-focus! and returns THAT SAME OBJECT.  So an undo
;;; built by pushing the old *ps* on a stack would push the object it is about to
;;; mutate and restore nothing; the graph is where the state lives.
;;;
;;; Journalling costs one vector and one cons per field write and is on whenever
;;; a proof is running.  It is bounded by (sp), which clears it.

(define *dg-journal* '())        ; grows by cons; each entry #(field node old)
(define *dg-journaling?* #t)

(define (dg-journal-in! sqn)
  (if *dg-journaling?*
      (set! *dg-journal*
            (cons (vector 'in sqn (sequent-node-in-arrows sqn)) *dg-journal*))))

(define (dg-journal-out! sqn)
  (if *dg-journaling?*
      (set! *dg-journal*
            (cons (vector 'out sqn (sequent-node-out-arrows sqn)) *dg-journal*))))

(define (dg-journal-grounded! sqn)
  (if *dg-journaling?*
      (set! *dg-journal*
            (cons (vector 'grounded sqn (sequent-node-grounded? sqn)) *dg-journal*))))

(define (dg-journal-reset!) (set! *dg-journal* '()))

(define (dg-undo-entry! e)
  (case (vector-ref e 0)
    ((in)       (set-sequent-node-in-arrows!  (vector-ref e 1) (vector-ref e 2)))
    ((out)      (set-sequent-node-out-arrows! (vector-ref e 1) (vector-ref e 2)))
    ((grounded) (set-sequent-node-grounded?!  (vector-ref e 1) (vector-ref e 2)))
    (else (error "dg-undo-entry!: unknown journal field" (vector-ref e 0)))))

;;; A MARK is everything needed to put the graph back exactly as it stood: the
;;; inference list, the node counter, and the journal tail.
;;;
;;; The sequent-node list is NOT held here, and deliberately.  `dg-node-counter'
;;; is bumped once per dg-add-sequent-node! and by nothing else, so it IS the
;;; length of that list, and holding the number instead of the list keeps a
;;; live mark from pinning a whole copy of the node list (`append' rebuilds it
;;; on every post, so each held pointer is a distinct copy).  Rollback rebuilds
;;; the prefix with list-head, once, at rollback time.  The INFERENCE list is
;;; held directly: it is cons-built, so its old value is a shared tail and
;;; costs nothing to keep.
(define-record-type <dg-mark>
  (%make-dg-mark dg infs counter journal)
  dg-mark?
  (dg      dg-mark-dg)
  (infs    dg-mark-infs)
  (counter dg-mark-counter)
  (journal dg-mark-journal))

(define (dg-take-mark dg)
  (%make-dg-mark dg
                 (dg-inference-nodes dg)
                 (dg-node-counter    dg)
                 *dg-journal*))

;;; #t exactly when nothing in the graph has moved since the mark was taken:
;;; no node posted, no inference recorded, no arrow written, no node grounded.
(define (dg-mark-unchanged? m)
  (let ((dg (dg-mark-dg m)))
    (and (eq? *dg-journal*            (dg-mark-journal m))
         (eq? (dg-inference-nodes dg) (dg-mark-infs m))
         (eqv? (dg-node-counter   dg) (dg-mark-counter m)))))

;;; Roll the graph back to M.  Undo the journalled field writes newest-first,
;;; then restore the two lists and the counter -- which drops every node and
;;; inference posted since the mark, so no orphan survives to be counted as an
;;; open leaf.
(define (dg-rollback! m)
  (let loop ()
    (if (not (eq? *dg-journal* (dg-mark-journal m)))
        (begin
          (if (null? *dg-journal*)
              (error "dg-rollback!: journal was reset under the mark"))
          (dg-undo-entry! (car *dg-journal*))
          (set! *dg-journal* (cdr *dg-journal*))
          (loop))))
  (let ((dg (dg-mark-dg m)))
    (set-dg-sequent-nodes!   dg (list-head (dg-sequent-nodes dg)
                                           (dg-mark-counter m)))
    (set-dg-inference-nodes! dg (dg-mark-infs m))
    (set-dg-node-counter!    dg (dg-mark-counter m)))
  m)

;;; Post a new sequent into the graph (or find an existing alpha-equivalent one).
(define (dg-post! dg sequent)
  (or (dg-find-sequent-node dg sequent)
      (dg-add-sequent-node! dg (make-sequent-node sequent))))

;;; Find the sequent node alpha-equivalent to SEQUENT, or #f.
;;;
;;; This is a LINEAR SCAN over every node in the graph, so posting the n-th
;;; sequent of a proof costs n comparisons and a proof of n steps costs O(n^2).
;;; Measured over a full library load on 2026-08-21: 39,288 posts, 3,616,694
;;; nodes visited, 14.7 s of a 59 s load.
;;;
;;; A digest index over `formula-hash' (expressions.scm) was built and MEASURED
;;; here, then removed on the user's decision the same day.  The numbers, same
;;; binary, only the lookup differing: linear 59.44 / 61.32 s, indexed 55.68 /
;;; 56.34 s -- a 7% load, not the 25% the scan cost, because computing an
;;; alpha-invariant digest for every wff is itself about three times a full
;;; alpha-equiv? traversal and almost every wff needs one.
;;;
;;; It was dropped for the SILENT FAILURE it introduced, not for the size of the
;;; win.  With an index, `alpha-equiv?' stops being the single source of truth:
;;; a digest that is wrong about some form -- a new binder head, or a shape the
;;; walk treats generically when it should bind -- sends the lookup to the wrong
;;; bucket, hash-consing quietly stops, `ass' can fail where it used to close,
;;; and none of that is an error.  `binder-walker-audit' catches a DECLARED head
;;; a walker forgot; it cannot catch a head nobody declared.  The digest itself
;;; is kept (it is what `formula-canon' and the wff print form are built on);
;;; nothing that can change an answer depends on it.
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

;;; Every rule tag this procedure ever stamps, recorded as it is stamped.
;;;
;;; The trusted base is exactly the set of these tags (tactics-help.scm's
;;; *tactic-kind* says so, and reference/KERNEL-RULES.md documents them), but
;;; nothing used to observe the set, so the prose drifted from the code -- by
;;; 2026-07-28 the file was missing the four ORACLE tags, both `macete' tags and
;;; the three `arith-' tags, and glossed transfinite induction as "tuple-function
;;; image".  `kernel-rules-audit' (tactics-help.scm) compares this table against
;;; the documented list at the end of every load.
;;;
;;; A computed tag -- `(macete <source> <replacement>)', `(union-intro k)' -- is
;;; recorded under its HEAD symbol only; the arguments are per-application data,
;;; not part of the trusted surface.
(define *rules-applied* (make-equal-hash-table))

(define (rule-tag-head rule) (if (pair? rule) (car rule) rule))

(define (rules-applied)
  (sort (hash-table-keys *rules-applied*)
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

(define (dg-apply-rule! dg rule hyp-sequents conclusion-sqn)
  (hash-table-set! *rules-applied* (rule-tag-head rule) #t)
  (let ((hyp-nodes (map (lambda (s) (dg-post! dg s)) hyp-sequents)))
    (let ((infn (make-inference-node rule hyp-nodes conclusion-sqn)))
      (dg-add-inference-node! dg infn)
      (for-each (lambda (h)
                  (dg-journal-out! h)
                  (set-sequent-node-out-arrows!
                   h (cons infn (sequent-node-out-arrows h))))
                hyp-nodes)
      (dg-journal-in! conclusion-sqn)
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
      (dg-journal-grounded! sqn)
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
