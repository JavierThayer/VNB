;;; core-capture.scm -- CORE REPLAY, steps 1-3: capture, the kernel bill, the lowering.
;;;
;;; Design: docs/core-replay-design-2026-11-05.md (s.3, s.4 item 3, s.5 steps 1-3).
;;; The replayer (step 4) is core-replay.scm, a separate file; this file only
;;; WRITES what it reads, in the format of docs/core-page-format.md.
;;;
;;; THE SWITCH.  VNB_CORE_REPLAY=on (read once, when this file loads).  Off -- the
;;; default, and every daytime load -- this file defines procedures and records
;;; the original binding of every entry point it would wrap, and changes NOTHING:
;;; no binding is replaced (suite check 9 tests that every one is `eq?' to its
;;; original), and the qed hook is not set.  On, it does four things:
;;;
;;;  1. CAPTURE.  Every kernel entry point (the named procedures of
;;;     reference/kernel-map-static.sexp that call `dg-apply-rule!' and are still
;;;     defined -- 52; `pi-contraposit!' and `pi-truth!' are listed there but no
;;;     longer exist -- plus `apply-macete!', which reaches the elementary-macete
;;;     closures: 53) is replaced
;;;     by `environment-assign!' with a wrapper that calls the original and then
;;;     attributes the inference nodes the call added to the graph (the prefix of
;;;     `dg-inference-nodes' before the pointer read on entry; that list is
;;;     cons-built, deduction-graphs.scm) to a record: entry point, target node,
;;;     the non-node arguments CONVERTED to what they denote (an assumption index
;;;     to the formula, an `ineq' premise index to the premise formula), and the
;;;     values of the dynamic variables the rewriter reads.  A nested call claims
;;;     its nodes first (it returns first), so attribution is to the INNERMOST
;;;     entry point.  The wrapper writes nothing to the graph.  `start-proof' is
;;;     also wrapped, to mark the eigenvariable log at the start of each proof.
;;;
;;;  2. THE SURVIVING-INFERENCE FILTER and THE KERNEL BILL, at `qed' (one hook,
;;;     interactive.scm, after the certificate record).  The final graph is walked
;;;     from the root; for every reachable node ONE in-arrow is chosen whose
;;;     hypotheses were grounded first (a queue in grounding order: well founded).
;;;     The chosen inferences are the proof.  Their theorem-assumption names
;;;     (from the capture record) and macete names (from the rule tag) are the
;;;     KERNEL CITATION LIST; the oracle heads are the kernel oracle list.  The
;;;     kernel bill is the union of the cited names' debt, computed as `debt-of'
;;;     computes it (proof-debt.scm) except that a proven citation contributes its
;;;     own KERNEL bill when this image computed one.  It is compared with the
;;;     ledger's bill; a difference is listed, warn-only (the user, 2026-11-07:
;;;     no recorded bill is changed).  Load-end line:
;;;         ;; kernel-bill: N agree, M differ
;;;
;;;  3. THE LOWERING.  The chosen inferences are emitted depth first as a CORE
;;;     PAGE, written to <tree>/core-pages/<theorem>.core (format: the contract in
;;;     the brief; docs/core-page-format.md).  Where a capture record is missing the
;;;     command and its arguments are RECOVERED from the inference node (the rule
;;;     tag and the relation between conclusion and hypotheses); every recovered
;;;     command is counted, and an inference that cannot be recovered is emitted
;;;     as (unrecovered TAG) and counted.
;;;
;;;  4. THE PAGE CORPUS (step 1).  At load end every stored proof's PAGE (the
;;;     surface script, page-audit.scm `page-of') is written to one gzipped text
;;;     file OUTSIDE the tree (VNB_CORE_CORPUS, default /home/ubuntu/core-corpus/);
;;;     scratchpad/core-corpus-count.py counts the commands by name.
;;;
;;; Nothing here is in *cert-kernel-files* or *kernel-caller-files*: this file
;;; calls entry points through their wrappers and never calls `dg-apply-rule!'.

;;; ---------------------------------------------------------------- the switch
(define *cc-flag-on?*
  (let ((v (get-environment-variable "VNB_CORE_REPLAY")))
    (and v (string=? v "on"))))

(define *cc-env* user-initial-environment)
(define *cc-installed?* #f)              ; wrappers in place
(define *cc-write-pages?* #f)            ; core pages written to <tree>/core-pages/

;;; ---------------------------------------------------------------- the entry table
;;; (ENTRY CMD SQN-POSITION ARG-KIND ...).  SQN-POSITION is the 0-based position
;;; of the sequent-node argument; the ARG-KINDs describe the remaining arguments
;;; in order:  f = formula (raw, a <wff>, or an assumption INDEX), t = term,
;;; n = name, k = number (data, e.g. a projection index), p = `ineq' premise
;;; indices (a list), r = raw data kept as given.  CMD #f = an entry point with
;;; no core command (unexercised in the library, design s.1): its record is
;;; emitted as (non-core ENTRY ARG ...) and the page is not core.
(define *cc-entry-table*
  '((pi-direct-inference!        di        0)
    (pi-antecedent-inference!    ai        0 f)
    (pi-weaken!                  wk        0 f)
    (pi-cut!                     cut       0 f)
    (pi-instantiate!             inst      0 f t)
    (pi-spec!                    #f        0 n r)
    (pi-exists-witness!          ew        0 t)
    (pi-assumption!              ass       0)
    (pi-or-intro-left!           oi-l      0)
    (pi-or-intro-right!          oi-r      0)
    (pi-backchain!               bc        0 f)
    (pi-detach!                  detach!   0 f)
    (pi-eq-subst!                subst     0 f)
    (pi-if-true!                 if-true   0 t)
    (pi-if-false!                if-false  0 t)
    (pi-reflexivity!             rfl       0)
    (pi-quasi-reflexivity!       qrfl      0)
    (pi-proof-by-contradiction!  pbc       0)
    (pi-theorem-assumption!      ta        0 n)
    (pi-cartesian-intro!         ci        0)
    (pi-cartesian-elim!          ce        0 f k)
    (pi-tuples-intro!            ti        0)
    (pi-tuples-elim!             te        0 f k)
    (pi-nth-reduce!              nth-r     0)
    (pi-length-reduce!           len-r     0)
    (pi-functoid-beta!           beta      0)
    (pi-union-intro!             ui        0 k)
    (pi-union-elim!              ue        0 f)
    (pi-tfi!                     tfi       0)
    (pi-tfi3!                    tfi3      0)
    (pi-nn-induction!            ni        0)
    (pi-intersection-intro!      ii        0)
    (pi-intersection-elim!       ie        0 f k)
    (pi-sep-sethood!             sep-set   0)
    (pi-sep-mem-intro!           sep-mi    0)
    (pi-sep-mem-elim!            sep-me    0 f)
    (pi-comp-mem-intro!          comp-mi   0)
    (pi-comp-mem-elim!           comp-me   0 f)
    (pi-big-union-sethood!       bu-set    0)
    (pi-big-union-mem-intro!     bu-mi     0 t)
    (pi-big-union-mem-elim!      bu-me     0 f)
    (pi-iota-def!                iota-d    0 t)
    (pi-iota-in-elim!            iota-e    0 t)
    (pi-lambda-type!             lam-t     0)
    (pi-lambda-beta!             lam-b     0)
    (pi-lambda-beta-hyp!         lam-b-h   0 f)
    (pi-arith!                   arith     0)
    (pi-comm-ring-simplify!      crs       0)
    (pi-ring-simplify!           rs        0)
    (pi-ineq!                    ineq      0 p)
    (pi-sos!                     sos       0 r)
    ;; the macete doors: (apply-macete! NAME SQN), (apply-macete-to-assumption! NAME F SQN)
    (apply-macete!               mac       1 n)
    (apply-macete-to-assumption! mac-h     2 n f)))

;;; THE 56 CORE NAMES (design s.1): 48 kernel rules, 5 oracles, sp / qed / at-node.
(define *core-command-names*
  '(di ai pbc oi-l oi-r ew ci ti ii ui ni tfi tfi3 ass ta inst detach! bc cut wk
    ce te ie ue mac macm mac-h subst rfl qrfl beta lam-t lam-b lam-b-h nth-r len-r
    if-true if-false sep-set sep-mi sep-me comp-mi comp-me iota-d iota-e
    bu-set bu-mi bu-me
    arith crs rs ineq sos
    sp qed at-node))

(define (core-command-name? s) (and (memq s *core-command-names*) #t))

;;; The originals, read when this file loads (every entry point is defined by then:
;;; load.scm loads this after certificates.scm).  An entry not bound is skipped.
(define *cc-originals*
  (let loop ((es *cc-entry-table*) (acc '()))
    (if (null? es)
        (reverse acc)
        (let ((name (caar es)))
          (loop (cdr es)
                (if (and (environment-bound? *cc-env* name)
                         (procedure? (environment-lookup *cc-env* name)))
                    (cons (cons name (environment-lookup *cc-env* name)) acc)
                    acc))))))
(define *cc-start-proof-original* (environment-lookup *cc-env* 'start-proof))

;;; ---------------------------------------------------------------- dynamic state
;;; The rewriter's fluids (design s.5 R1).  Defaults read at load; a step whose
;;; values differ carries (dyn (VAR VALUE) ...).
(define (cc--dyn-now)
  (list (list '*macete-spawn-conditions?* *macete-spawn-conditions?*)
        (list '*match-var-head* *match-var-head*)
        (list '*rewrite-path-bvars* *rewrite-path-bvars*)
        (list '*rewrite-owe-definedness?* *rewrite-owe-definedness?*)))
(define *cc-dyn-defaults* (cc--dyn-now))
(define (cc--dyn-delta dyn)
  (filter (lambda (e) (not (equal? e (assq (car e) *cc-dyn-defaults*)))) dyn))

;;; ---------------------------------------------------------------- per-graph state
;;; dg -> (eq table: inference node -> record), and dg -> the *fresh-log* pointer at
;;; start-proof.  Weak keys: a scratch graph a probe abandoned is collected.
(define *cc-graph-records* (make-key-weak-eqv-hash-table))
(define *cc-graph-mints*   (make-key-weak-eqv-hash-table))

;;; A record: #(ENTRY TARGET-SQN ARGS DYN INFERENCES-IN-CREATION-ORDER).
(define (cc-rec-entry r)  (vector-ref r 0))
(define (cc-rec-target r) (vector-ref r 1))
(define (cc-rec-args r)   (vector-ref r 2))
(define (cc-rec-dyn r)    (vector-ref r 3))
(define (cc-rec-infns r)  (vector-ref r 4))

(define *cc-calls* 0)                    ; wrapped calls that ran under capture
(define *cc-converted-indices* 0)        ; positional arguments turned into formulas

(define (cc--records-of dg)
  (or (hash-table-ref/default *cc-graph-records* dg #f)
      (let ((t (make-strong-eqv-hash-table)))
        (hash-table-set! *cc-graph-records* dg t)
        t)))

;;; Every inference the call created (the nested calls' included) is kept in the
;;; record's slot 4, in creation order: a core step's `hyps' are the hypotheses of
;;; all of them (docs/core-page-format.md s.2), since replaying the call creates
;;; them all.  ATTRIBUTION is innermost: an inference already claimed by a nested
;;; call keeps that call's record.
(define (cc--claim! dg before rec)
  (let ((t (cc--records-of dg)))
    (let loop ((l (dg-inference-nodes dg)) (made '()))
      (if (and (pair? l) (not (eq? l before)))
          (begin
            (if (not (hash-table-ref/default t (car l) #f))
                (hash-table-set! t (car l) rec))
            (loop (cdr l) (cons (car l) made)))
          (vector-set! rec 4 made)))))

;;; ---------------------------------------------------------------- argument conversion
(define (cc--raw x) (if (wff? x) (wff-formula x) x))

(define (cc--asm-formula sqn i)
  (let ((asms (sequent-node-assumptions sqn)))
    (and (exact-nonnegative-integer? i) (>= i 1) (<= i (length asms))
         (wff-formula (list-ref asms (- i 1))))))

(define (cc--convert-one kind x sqn)
  (case kind
    ((f) (cond ((wff? x) (wff-formula x))
               ((and (exact-nonnegative-integer? x) (cc--asm-formula sqn x))
                (set! *cc-converted-indices* (+ *cc-converted-indices* 1))
                (cc--asm-formula sqn x))
               (#t x)))
    ((t) (cc--raw x))
    ((p) (if (list? x)
             (map (lambda (i)
                    (let ((f (cc--asm-formula sqn i)))
                      (if f
                          (begin (set! *cc-converted-indices* (+ *cc-converted-indices* 1)) f)
                          (list 'bad-premise-index i))))
                  x)
             x))
    (else x)))

;;; The non-node arguments of a call, converted.  Never raises: a conversion that
;;; fails keeps the argument as given (and the page then shows it).
(define (cc--convert spec args sqn)
  (let ((pos (caddr spec)) (kinds (cdddr spec)))
    (let loop ((as args) (i 0) (ks kinds) (acc '()))
      (cond ((null? as) (reverse acc))
            ((= i pos) (loop (cdr as) (+ i 1) ks acc))
            (#t (let ((k (if (pair? ks) (car ks) 'r)))
                  (loop (cdr as) (+ i 1) (if (pair? ks) (cdr ks) ks)
                        (cons (call-with-current-continuation
                               (lambda (esc)
                                 (with-exception-handler
                                  (lambda (e) (esc (car as)))
                                  (lambda () (cc--convert-one k (car as) sqn)))))
                              acc))))))))

;;; ---------------------------------------------------------------- the wrappers
(define (cc--make-wrapper spec orig)
  (let ((entry (car spec)) (pos (caddr spec)))
    (lambda args
      (let ((sqn (and (> (length args) pos) (list-ref args pos))))
        (if (not (and *cc-installed?* (sequent-node? sqn) (sequent-node-graph sqn)))
            (apply orig args)
            (let* ((dg     (sequent-node-graph sqn))
                   (before (dg-inference-nodes dg))
                   (cargs  (cc--convert spec args sqn))
                   (dyn    (cc--dyn-now)))
              (set! *cc-calls* (+ *cc-calls* 1))
              (call-with-values (lambda () (apply orig args))
                (lambda vals
                  (cc--claim! dg before (vector entry sqn cargs dyn '()))
                  (apply values vals)))))))))

(define (cc--start-proof-wrapper wic)
  (let ((ps (*cc-start-proof-original* wic)))
    (if (and *cc-installed?* (proof-state? ps))
        (hash-table-set! *cc-graph-mints* (proof-state-dg ps) *fresh-log*))
    ps))

(define (core-capture-install!)
  (if (not *cc-installed?*)
      (begin
        (for-each (lambda (p)
                    (environment-assign! *cc-env* (car p)
                                         (cc--make-wrapper (assq (car p) *cc-entry-table*) (cdr p))))
                  *cc-originals*)
        (environment-assign! *cc-env* 'start-proof cc--start-proof-wrapper)
        (set! *cc-installed?* #t)))
  (length *cc-originals*))

(define (core-capture-uninstall!)
  (for-each (lambda (p) (environment-assign! *cc-env* (car p) (cdr p))) *cc-originals*)
  (environment-assign! *cc-env* 'start-proof *cc-start-proof-original*)
  (set! *cc-installed?* #f)
  (length *cc-originals*))

;;; Suite check 9: every entry point is its original (#t), or the list of those
;;; that are not.
(define (core-capture-originals-intact?)
  (let ((bad (filter (lambda (p) (not (eq? (environment-lookup *cc-env* (car p)) (cdr p))))
                     *cc-originals*)))
    (if (and (null? bad) (eq? (environment-lookup *cc-env* 'start-proof) *cc-start-proof-original*))
        #t
        (map car bad))))
(define (core-capture-wrapped-names) (map car *cc-originals*))

;;; ---------------------------------------------------------------- the surviving proof
;;; Reachable nodes and inferences from ROOT; then ONE chosen in-arrow per node, in
;;; grounding order (an inference is ready when every hypothesis has a chosen
;;; justification), so the choice is well founded.  Returns the eq table
;;; node -> chosen inference, or #f when the root gets none.
(define (cc--choose root)
  (let ((nodes (make-strong-eqv-hash-table))
        (infs  (make-strong-eqv-hash-table))
        (pending (make-strong-eqv-hash-table))
        (chosen (make-strong-eqv-hash-table))
        (queue '()))
    (let walk ((todo (list root)))
      (if (pair? todo)
          (let ((n (car todo)))
            (if (hash-table-ref/default nodes n #f)
                (walk (cdr todo))
                (begin
                  (hash-table-set! nodes n #t)
                  (walk (append (apply append
                                       (map (lambda (i)
                                              (if (hash-table-ref/default infs i #f)
                                                  '()
                                                  (begin (hash-table-set! infs i #t)
                                                         (inference-node-hypotheses i))))
                                            (sequent-node-in-arrows n)))
                                (cdr todo))))))))
    (hash-table-walk infs
      (lambda (i v)
        (let ((k (length (inference-node-hypotheses i))))
          (hash-table-set! pending i k)
          (if (= k 0) (set! queue (cons i queue))))))
    (let loop ()
      (if (pair? queue)
          (let* ((i (car queue)) (c (inference-node-conclusion i)))
            (set! queue (cdr queue))
            (if (not (hash-table-ref/default chosen c #f))
                (begin
                  (hash-table-set! chosen c i)
                  (for-each (lambda (j)
                              (if (hash-table-ref/default infs j #f)
                                  (let ((k (- (hash-table-ref/default pending j 0) 1)))
                                    (hash-table-set! pending j k)
                                    (if (= k 0) (set! queue (cons j queue))))))
                            (sequent-node-out-arrows c))))
            (loop))))
    (and (hash-table-ref/default chosen root #f) chosen)))

;;; ---------------------------------------------------------------- recovery
(define (cc--asm-raws sqn) (map wff-formula (sequent-node-assumptions sqn)))
(define (cc--raw-member? f fs) (any (lambda (g) (alpha-equiv? f g)) fs))
;;; the formulas of A that are not in B (up to alpha), in order
(define (cc--minus a b) (filter (lambda (f) (not (cc--raw-member? f b))) a))

(define (cc--first-removed infn)        ; the assumption of the conclusion its first hypothesis lost
  (let ((hs (inference-node-hypotheses infn)))
    (and (pair? hs)
         (let ((d (cc--minus (cc--asm-raws (inference-node-conclusion infn))
                             (cc--asm-raws (car hs)))))
           (and (pair? d) (car d))))))

(define (cc--first-added infn)          ; the assumption the first hypothesis gained
  (let ((hs (inference-node-hypotheses infn)))
    (and (pair? hs)
         (let ((d (cc--minus (cc--asm-raws (car hs))
                             (cc--asm-raws (inference-node-conclusion infn)))))
           (and (pair? d) (car d))))))

(define (cc--theorem-with-statement f)
  (let ((hit #f))
    (call-with-current-continuation
     (lambda (k)
       (hash-table-walk *theorem-table*
         (lambda (name stmt)
           (if (alpha-equiv? (cc--raw stmt) f) (begin (set! hit name) (k #t)))))))
    hit))

(define (cc--ineq-premises infn)        ; premise ids hI / hI-rev of the certificate
  (let* ((rule (inference-node-rule infn))
         (cert (and (pair? rule) (pair? (cdr rule)) (cadr rule)))
         (alists (cond ((not (pair? cert)) '())
                       ((and (pair? (car cert)) (pair? (caar cert))) (list (car cert) (cdr cert)))
                       (#t (list cert))))
         (ids '()))
    (for-each (lambda (al)
                (if (list? al)
                    (for-each (lambda (e)
                                (if (and (pair? e) (symbol? (car e)))
                                    (let* ((s (symbol->string (car e)))
                                           (core (if (string-search-forward "-rev" s 0)
                                                     (substring s 0 (string-search-forward "-rev" s 0))
                                                     s)))
                                      (if (and (> (string-length core) 1) (char=? (string-ref core 0) #\h))
                                          (let ((n (string->number (substring core 1 (string-length core)))))
                                            (if (and n (not (memv n ids))) (set! ids (cons n ids))))))))
                              al)))
              alists)
    (filter (lambda (x) x)
            (map (lambda (i) (cc--asm-formula (inference-node-conclusion infn) i))
                 (sort ids <)))))

;;; (CMD ARG ...) from the inference node alone, or #f.
(define (cc--recover infn)
  (let* ((rule (inference-node-rule infn))
         (head (rule-tag-head rule))
         (concl (inference-node-conclusion infn))
         (hs (inference-node-hypotheses infn)))
    (case head
      ((and-intro implies-intro iff-intro not-intro forall-intro) '(di))
      ((and-elim or-elim iff-elim forsome-elim)
       (let ((f (cc--first-removed infn))) (and f (list 'ai f))))
      ((not-elim)
       (let* ((asms (cc--asm-raws concl))
              (f (find-first (lambda (a) (and (pair? a) (eq? (car a) 'NOT)
                                               (cc--raw-member? (cadr a) asms)))
                             asms)))
         (and f (list 'ai f))))
      ((weakening) (let ((f (cc--first-removed infn))) (and f (list 'wk f))))
      ((cut) (and (pair? hs) (list 'cut (wff-formula (sequent-node-assertion (car hs))))))
      ((assumption) '(ass))
      ((or-intro-left) '(oi-l))
      ((or-intro-right) '(oi-r))
      ((reflexivity) '(rfl))
      ((quasi-reflexivity) '(qrfl))
      ((proof-by-contradiction) '(pbc))
      ((cartesian-intro) '(ci))
      ((tuples-intro) '(ti))
      ((intersection-intro) '(ii))
      ((nth-reduce) '(nth-r))
      ((length-reduce) '(len-r))
      ((functoid-beta) '(beta))
      ((lambda-type) '(lam-t))
      ((lambda-beta) '(lam-b))
      ((sep-sethood) '(sep-set))
      ((sep-mem-intro) '(sep-mi))
      ((comp-mem-intro) '(comp-mi))
      ((big-union-sethood) '(bu-set))
      ((transfinite-induction) '(tfi))
      ((transfinite-induction-3cases) '(tfi3))
      ((nn-induction) '(ni))
      ((union-intro) (and (pair? rule) (pair? (cdr rule)) (list 'ui (cadr rule))))
      ((macete) (and (pair? rule) (pair? (cdr rule)) (symbol? (cadr rule)) (list 'mac (cadr rule))))
      ((macete-hyp)
       (let ((f (cc--first-removed infn)))
         (and f (pair? rule) (symbol? (cadr rule)) (list 'mac-h (cadr rule) f))))
      ((arith-ground arith-forsome arith-simplify) '(arith))
      ((comm-ring-simplify) '(crs))
      ((ring-simplify) '(rs))
      ((ineq) (cons 'ineq (cc--ineq-premises infn)))
      ((theorem-assumption)
       (let* ((f (cc--first-added infn)) (nm (and f (cc--theorem-with-statement f))))
         (and nm (list 'ta nm))))
      (else #f))))

;;; ---------------------------------------------------------------- the command of a record
(define (cc--command rec)
  (let* ((entry (cc-rec-entry rec))
         (spec  (assq entry *cc-entry-table*))
         (cmd   (cadr spec))
         (args  (cc-rec-args rec))
         (dyn   (cc-rec-dyn rec)))
    (cond ((not cmd) (cons 'non-core (cons entry args)))
          ((and (eq? cmd 'mac) (cadr (assq '*macete-spawn-conditions?* dyn)))
           (cons 'macm args))
          ((eq? cmd 'ineq) (cons 'ineq (if (list? (car args)) (car args) args)))
          ((eq? cmd 'sos) (cons 'sos args))
          (#t (cons cmd args)))))

;;; The kernel citations an inference makes: (ta . NAME), (macete . NAME), (oracle . VERB).
(define (cc--oracle-verb head)
  (case head
    ((arith-ground arith-forsome arith-simplify) 'arith)
    ((comm-ring-simplify) 'crs)
    ((ring-simplify) 'rs)
    ((ineq) 'ineq)
    ((sos) 'sos)
    (else #f)))

;;; ---------------------------------------------------------------- eigenvariables
(define (cc--mints-since dg)
  (let ((mark (hash-table-ref/default *cc-graph-mints* dg #f)))
    (if (not mark)
        '()
        (let loop ((l *fresh-log*) (acc '()))
          (if (or (null? l) (eq? l mark)) acc (loop (cdr l) (cons (car l) acc)))))))

(define (cc--note-symbols! x table)
  (cond ((symbol? x) (hash-table-set! table x #t))
        ((pair? x) (cc--note-symbols! (car x) table) (cc--note-symbols! (cdr x) table))
        (#t #f)))

;;; Every symbol occurring in the STEPS into TABLE: the set `cc--note-symbols!' of
;;; the steps notes.  CORE-GC (2026-11-11): the formulas of the sequent forms (a
;;; step's sequent, its hypotheses) are walked once per formula OBJECT; the page
;;; shares one context's formulas between all the steps under it, and the unshared
;;; walk revisited every context at every step (quadratic in a proof's depth).
(define (cc--note-symbols-of-steps! steps table)
  (let ((seen (make-strong-eqv-hash-table)))
    (define (f! x)
      (if (and (pair? x) (hash-table-ref/default seen x #f))
          #f
          (begin (if (pair? x) (hash-table-set! seen x #t))
                 (cc--note-symbols! x table))))
    (define (seq! sq)                    ; (sequent ASMS GOAL), the form seq-of builds
      (if (and (pair? sq) (eq? (car sq) 'sequent) (pair? (cdr sq)) (list? (cadr sq))
               (pair? (cddr sq)) (null? (cdddr sq)))
          (begin (hash-table-set! table 'sequent #t) (for-each f! (cadr sq)) (f! (caddr sq)))
          (cc--note-symbols! sq table)))
    (for-each
     (lambda (st)
       (if (list? st)
           (for-each (lambda (fld)
                       (cond ((and (pair? fld) (eq? (car fld) 'sequent)) (seq! fld))
                             ((and (pair? fld) (eq? (car fld) 'hyps) (list? fld))
                              (hash-table-set! table 'hyps #t) (for-each seq! (cdr fld)))
                             (#t (cc--note-symbols! fld table))))
                     st)
           (cc--note-symbols! st table)))
     steps)))

;;; Renaming keeps SHARING: a context list is shared by many steps, and a copy per
;;; occurrence multiplied the page in memory (and the writer's work, below).
;;; The symbols free in some formula of the steps (sequents, hypotheses, command
;;; arguments), one `free-vars' per distinct formula object.
(define (cc--free-symbols-of-steps steps)
  (let ((free (make-strong-eqv-hash-table)) (seen (make-strong-eqv-hash-table)))
    (define (f! x)
      (cond ((symbol? x) (hash-table-set! free x #t))
            ((and (pair? x) (not (hash-table-ref/default seen x #f)))
             (hash-table-set! seen x #t)
             (for-each (lambda (v) (if (symbol? v) (hash-table-set! free v #t))) (free-vars x)))
            (#t #f)))
    (define (seq! sq) (for-each f! (cadr sq)) (f! (caddr sq)))
    (for-each
     (lambda (st)
       (for-each (lambda (fld)
                   (cond ((and (pair? fld) (eq? (car fld) 'sequent)) (seq! fld))
                         ((and (pair? fld) (eq? (car fld) 'hyps)) (for-each seq! (cdr fld)))
                         (#t #f)))
                 (cddddr st))
       (for-each f! (cdr (list-ref st 3))))
     steps)
    free))

(define (cc--rename x alist)
  ;; Rename the mints at their FREE occurrences only.  A bound occurrence keeps the
  ;; name it was minted with (a binder renamed by capture-avoiding substitution in
  ;; inst, lam-t, iota-d may carry a minted name that later becomes an eigenvariable
  ;; when di peels it); alpha-equivalence absorbs it at replay.  The walk reads the
  ;; binder shapes of expressions.scm; a shared subterm is copied once while no
  ;; mint is shadowed.
  (if (null? alist)
      x
      (let ((tbl (make-strong-eqv-hash-table)) (m (make-strong-eqv-hash-table)))
        (define (bvars-of spec)
          (cond ((symbol? spec) (list spec))
                ((and (pair? spec) (eq? (car spec) 'LIST)) (filter symbol? (cdr spec)))
                ((pair? spec) (filter symbol? spec))
                (else '())))
        (define (shadow bound vs)
          (append (filter (lambda (v) (hash-table-ref/default m v #f)) vs) bound))
        (for-each (lambda (p) (hash-table-set! m (car p) (cdr p))) alist)
        (let walk ((x x) (bound '()))
          (define (in-scope y vs) (walk y (shadow bound vs)))
          (cond ((symbol? x)
                 (if (memq x bound) x (hash-table-ref/default m x x)))
                ((pair? x)
                 (or (and (null? bound) (hash-table-ref/default tbl x #f))
                     (let* ((shape (and (pair? (cdr x)) (binder-shape (car x))))
                            (y (cond
                                ((and (eq? shape 'simple) (pair? (cddr x)))
                                 (cons (car x)
                                       (cons (cadr x)
                                             (map (lambda (b) (in-scope b (list (cadr x))))
                                                  (cddr x)))))
                                ((and (memq shape '(domain lambda)) (pair? (cddr x))
                                      (pair? (cdddr x)))
                                 (let ((vs (bvars-of (cadr x))))
                                   (cons (car x)
                                         (cons (cadr x)
                                               (cons (walk (caddr x) bound)
                                                     (map (lambda (b) (in-scope b vs))
                                                          (cdddr x)))))))
                                (else (cons (walk (car x) bound) (walk (cdr x) bound))))))
                       (if (null? bound) (hash-table-set! tbl x y))
                       y)))
                (#t x))))))

;;; `(delete-duplicates L eq?)', the first occurrence kept, in linear time (the mint
;;; log of a long proof holds thousands of names; CORE-GC, 2026-11-11).
(define (cc--delete-duplicates-eq l)
  (let ((seen (make-strong-eqv-hash-table)))
    (let loop ((l l) (acc '()))
      (cond ((null? l) (reverse acc))
            ((hash-table-ref/default seen (car l) #f) (loop (cdr l) acc))
            (#t (hash-table-set! seen (car l) #t) (loop (cdr l) (cons (car l) acc)))))))

;;; ---------------------------------------------------------------- the lowering
(define *cc-pages-lowered* 0)
(define *cc-pages-failed* '())           ; (name . reason)
(define *cc-steps-emitted* 0)
(define *cc-steps-recovered* 0)
(define *cc-steps-unrecovered* 0)
(define *cc-steps-noncore* 0)
(define *cc-steps-off-target* 0)          ; a record emitted at a node other than its target
(define *cc-mint-clashes* 0)              ; a page already held a symbol named vK
(define *cc-last-page* #f)
(define *cc-hook-errors* '())
(define *cc-hook-seconds* 0.)
(define *cc-t-lower* 0.) (define *cc-t-bill* 0.) (define *cc-t-write* 0.)

;;; Returns (values PAGE CITATIONS) where CITATIONS is a list of (kind . name).
(define (cc--lower name ps)
  (let* ((dg     (proof-state-dg ps))
         (root   (proof-state-root ps))
         (recs   (cc--records-of dg))
         (chosen (cc--choose root)))
    (if (not chosen)
        (error "core-capture: the root has no well-founded surviving justification" name))
    (let ((ids (make-strong-eqv-hash-table)) (next-id 1)
          (emitted-recs (make-strong-eqv-hash-table))
          (visited (make-strong-eqv-hash-table))
          (steps '()) (k 0) (cites '()))
      (define (id-of n)
        (or (hash-table-ref/default ids n #f)
            (begin (hash-table-set! ids n next-id) (set! next-id (+ next-id 1))
                   (- next-id 1))))
      ;; One sequent form per NODE (eq): the page writer shares a sequent written once
      ;; (sequent-ref) and writes a hypothesis as a difference from its step's sequent
      ;; (sequent-delta), keyed on these objects; cc--rename keeps the sharing.
      (define seq-memo (make-strong-eqv-hash-table))
      (define (seq-of n)
        (or (hash-table-ref/default seq-memo n #f)
            (let ((sq (list 'sequent (cc--asm-raws n) (wff-formula (sequent-node-assertion n)))))
              (hash-table-set! seq-memo n sq)
              sq)))
      (define (cite! c) (if (not (member c cites)) (set! cites (cons c cites))))
      ;; INFNS: the inferences the step's call recorded, in creation order (a
      ;; recovered step: the one inference).  Page node ids are given at first use in
      ;; an at-node, so they are dense in emission order and the root is 1.
      (define (emit! n infns cmd extra)
        (set! k (+ k 1))
        (let ((nid (id-of n)))
          (set! steps
                (cons (append
                       (list 'step k (list 'at-node nid) cmd (seq-of n)
                             (cons 'hyps (apply append
                                                (map (lambda (i) (map seq-of (inference-node-hypotheses i)))
                                                     infns)))
                             (cons 'rules (map (lambda (i) (rule-tag-head (inference-node-rule i))) infns)))
                       extra)
                      steps))))
      (define (rec-infns rec infn)
        (let ((l (cc-rec-infns rec))) (if (pair? l) l (list infn))))
      (let loop ((todo (list root)))
        (if (pair? todo)
            (let ((n (car todo)))
              (if (hash-table-ref/default visited n #f)
                  (loop (cdr todo))
                  (let* ((infn (hash-table-ref/default chosen n #f))
                         (rec  (hash-table-ref/default recs infn #f))
                         (rule (inference-node-rule infn))
                         (head (rule-tag-head rule)))
                    (hash-table-set! visited n #t)
                    ;; kernel citations of the chosen inference
                    (cond ((memq head '(macete macete-hyp))
                           (if (and (pair? rule) (symbol? (cadr rule))) (cite! (cons 'macete (cadr rule)))))
                          ((cc--oracle-verb head) (cite! (cons 'oracle (cc--oracle-verb head)))))
                    (cond
                     ((and rec (eq? (cc-rec-target rec) n))
                      (hash-table-set! emitted-recs rec #t)
                      (let ((cmd (cc--command rec)))
                        (if (eq? (car cmd) 'non-core) (set! *cc-steps-noncore* (+ *cc-steps-noncore* 1)))
                        (if (and (eq? (car cmd) 'ta) (pair? (cdr cmd))) (cite! (cons 'ta (cadr cmd))))
                        (emit! n (rec-infns rec infn) cmd
                               (let ((d (cc--dyn-delta (cc-rec-dyn rec))))
                                 (if (null? d) '() (list (cons 'dyn d)))))))
                     ((and rec (hash-table-ref/default emitted-recs rec #f))
                      ;; a later inference of a call already emitted at its target: the
                      ;; node is justified when that step replays -- no step of its own
                      'chain)
                     (rec
                      (set! *cc-steps-off-target* (+ *cc-steps-off-target* 1))
                      (hash-table-set! emitted-recs rec #t)
                      (let ((cmd (cc--command rec)))
                        (if (and (eq? (car cmd) 'ta) (pair? (cdr cmd))) (cite! (cons 'ta (cadr cmd))))
                        (emit! n (rec-infns rec infn) cmd '((off-target #t)))))
                     (#t
                      (let ((cmd (cc--recover infn)))
                        (if cmd
                            (begin (set! *cc-steps-recovered* (+ *cc-steps-recovered* 1))
                                   (if (eq? (car cmd) 'ta) (cite! (cons 'ta (cadr cmd))))
                                   (emit! n (list infn) cmd '((recovered #t))))
                            (begin (set! *cc-steps-unrecovered* (+ *cc-steps-unrecovered* 1))
                                   (if (eq? head 'theorem-assumption) (cite! (cons 'ta '<unknown>)))
                                   (emit! n (list infn) (list 'unrecovered head) '()))))))
                    (loop (append (inference-node-hypotheses infn) (cdr todo))))))))
      (set! *cc-steps-emitted* (+ *cc-steps-emitted* k))
      ;; canonical eigenvariables: the proof's mints that occur on the page, in
      ;; minting order, renamed v1, v2, ...
      (let* ((steps (reverse steps))
             (stmt  (wff-formula (sequent-node-assertion root)))
             (present (make-strong-eqv-hash-table)))
        (cc--note-symbols-of-steps! steps present)
        ;; A page MINT is a minted name that occurs FREE in some formula of the page
        ;; (an eigenvariable, a witness).  A name minted only to rename a BOUND
        ;; variable (capture-avoiding substitution in inst, iota-d, lam-t) stays as
        ;; it is: alpha-equivalence absorbs it at replay, and the replayer learns a
        ;; mint only from the free symbols of the hypotheses a step produced.
        (let* ((free (cc--free-symbols-of-steps steps))
               (mints (filter (lambda (m) (hash-table-ref/default free m #f))
                              (cc--delete-duplicates-eq (cc--mints-since dg))))
               (alist (let lp ((ms mints) (i 1) (acc '()))
                        (if (null? ms) (reverse acc)
                            (lp (cdr ms) (+ i 1)
                                (cons (cons (car ms) (string->symbol (string-append "v" (number->string i))))
                                      acc))))))
          (if (any (lambda (p) (and (hash-table-ref/default present (cdr p) #f)
                                    (not (assq (cdr p) alist))))
                   alist)
              (set! *cc-mint-clashes* (+ *cc-mint-clashes* 1)))
          (values
           (append (list 'core-page name
                         (list 'statement stmt)
                         (list 'kernel-hash (cert-kernel-hash))
                         (cons 'mints (map cdr alist)))
                   (cc--rename steps alist))
           (reverse cites)))))))

;;; ---------------------------------------------------------------- the kernel bill
(define *cc-kernel-bill* (make-strong-eqv-hash-table))     ; name -> kernel bill
(define *cc-kernel-oracles* (make-strong-eqv-hash-table))  ; name -> kernel oracle verbs
(define *cc-kernel-citations* (make-strong-eqv-hash-table)); name -> ((kind . name) ...)
(define *cc-bill-agree* 0)
(define *cc-bill-differ* '())     ; (name kernel-bill ledger-bill), newest first
(define *cc-oracle-differ* '())   ; (name kernel-oracles ledger-oracles)

(define (cc--fact-name? c)
  (or (hash-table-ref/default *theorem-table* c #f)
      (hash-table-ref/default *provenance* c #f)))

(define (cc--kdebt c)
  (let ((src (pd-source-of c)))
    (if src
        (cc--kdebt src)
        (case (provenance-of c)
          ((primitive definitional) '())
          ((proven certified)
           (or (hash-table-ref/default *cc-kernel-bill* c #f)
               (hash-table-ref/default *proof-debt* c '())))
          (else (if (cc--fact-name? c) (list c) '()))))))

(define (cc--koracles c)
  (let ((src (pd-source-of c)))
    (if src
        (cc--koracles src)
        (if (memq (provenance-of c) '(proven certified))
            (or (hash-table-ref/default *cc-kernel-oracles* c #f)
                (hash-table-ref/default *proof-oracles* c '()))
            '()))))

(define (cc--set-equal? a b)
  (and (every (lambda (x) (memq x b)) a) (every (lambda (x) (memq x a)) b)))

(define (cc--kernel-bill! name cites ledger-bill)
  (let* ((names (pd-uniq (filter (lambda (c) (and (symbol? c) (not (eq? c name))))
                                 (map cdr (filter (lambda (c) (memq (car c) '(ta macete))) cites)))))
         (bill (fold-left (lambda (acc c) (pd-union acc (cc--kdebt c))) '() names))
         (ors  (fold-left (lambda (acc c) (pd-union acc (cc--koracles c)))
                          (pd-uniq (map cdr (filter (lambda (c) (eq? (car c) 'oracle)) cites)))
                          names))
         (lors (pd-uniq (map (lambda (v) (if (eq? v 'simp) 'crs v))
                             (hash-table-ref/default *proof-oracles* name '())))))
    (hash-table-set! *cc-kernel-citations* name cites)
    (hash-table-set! *cc-kernel-bill* name bill)
    (hash-table-set! *cc-kernel-oracles* name ors)
    (if (cc--set-equal? bill ledger-bill)
        (set! *cc-bill-agree* (+ *cc-bill-agree* 1))
        (set! *cc-bill-differ* (cons (list name bill ledger-bill) *cc-bill-differ*)))
    (if (not (cc--set-equal? ors lors))
        (set! *cc-oracle-differ* (cons (list name ors lors) *cc-oracle-differ*)))
    bill))

;;; ---------------------------------------------------------------- the qed hook
(define (cc--page-path name)
  (let* ((s (symbol->string name))
         (safe (list->string (apply append
                                    (map (lambda (ch) (if (char=? ch #\/) (string->list "%2F") (list ch)))
                                         (string->list s))))))
    (string-append *prover-dir* "core-pages/" safe ".core")))

;;; THE WRITER.  Two kinds of sharing, both lossless (docs/core-page-format.md s.1a):
;;;  * each FORMULA object is printed once per page and the string reused (eq table):
;;;    `write' of the same formula hundreds of times was most of the qed hook's time;
;;;  * each SEQUENT form of the page is NUMBERED in reading order (1, 2, ...), and a
;;;    sequent form already written (the same node: a step's sequent is a hypothesis
;;;    of an earlier step) is written `(sequent-ref J)'; a hypothesis is written as a
;;;    difference from its step's sequent J, `(sequent-delta J (drop I ...) (add A ...)
;;;    [GOAL])': the assumptions are the ADDED formulas followed by J's assumptions
;;;    with the 0-based positions I removed (the order `context-add-assumption'
;;;    builds), and the goal is J's when GOAL is absent.  The delta is written only
;;;    when it reproduces the assumption list EXACTLY (eq, element by element, in
;;;    order); otherwise the sequent is written in full.  Before this (CR-A's slice,
;;;    946 pages) every step carried every context in full: 161 MB.
(define *cc-seq-full* 0) (define *cc-seq-ref* 0) (define *cc-seq-delta* 0)

;;; The delta of sequent form SQ against BASE: (values DROP ADD SAME-GOAL?) or #f.
(define (cc--seq-delta base sq)
  (or (cc--seq-delta-prefix base sq) (cc--seq-delta-general base sq)))

;;; The common case without a hash table: SQ's assumptions are K new formulas in
;;; front of BASE's, eq element by element (a rule that added K <= 4 assumptions).
(define (cc--seq-delta-prefix base sq)
  (let* ((ba (cadr base)) (ta (cadr sq))
         (k (- (length ta) (length ba))))
    (and (<= 0 k 4)
         (let loop ((a (list-tail ta k)) (b ba))
           (or (and (null? a) (null? b))
               (and (pair? a) (pair? b) (eq? (car a) (car b)) (loop (cdr a) (cdr b)))))
         (list '() (list-head ta k)
               (or (eq? (caddr sq) (caddr base)) (equal? (caddr sq) (caddr base)))))))

(define (cc--seq-delta-general base sq)
  (let ((ba (cadr base)) (ta (cadr sq))
        (inb (make-strong-eqv-hash-table)) (int (make-strong-eqv-hash-table)))
    (for-each (lambda (f) (hash-table-set! inb f #t)) ba)
    (for-each (lambda (f) (hash-table-set! int f #t)) ta)
    (let* ((add  (filter (lambda (f) (not (hash-table-ref/default inb f #f))) ta))
           (drop (let loop ((l ba) (i 0) (acc '()))
                   (cond ((null? l) (reverse acc))
                         ((hash-table-ref/default int (car l) #f) (loop (cdr l) (+ i 1) acc))
                         (#t (loop (cdr l) (+ i 1) (cons i acc))))))
           (kept (let loop ((l ba) (i 0) (d drop) (acc '()))
                   (cond ((null? l) (reverse acc))
                         ((and (pair? d) (= (car d) i)) (loop (cdr l) (+ i 1) (cdr d) acc))
                         (#t (loop (cdr l) (+ i 1) d (cons (car l) acc))))))
           (rebuilt (append add kept)))
      (and (= (length rebuilt) (length ta))
           (let loop ((a rebuilt) (b ta))     ; eq?, element by element (the tree's `every' takes one list)
             (or (null? a) (and (eq? (car a) (car b)) (loop (cdr a) (cdr b)))))
           (list drop add (or (eq? (caddr sq) (caddr base)) (equal? (caddr sq) (caddr base))))))))

;;; `write-simple': the page is a tree (no cycles), so the R7RS cycle detection of
;;; `write' is work for nothing; the text is the same.
(define cc--write
  (if (environment-bound? system-global-environment 'write-simple) write-simple write))

;;; CORE-GC (2026-11-11): the page's own printer.  A page datum is lists of symbols
;;; and exact numbers (docs/core-page-format.md s.1); this walk writes a pair, the
;;; empty list, a symbol and an exact rational itself and hands anything else to
;;; `cc--write'.  The text is the text `write-simple' writes (which abbreviates no
;;; quote form: (quote a) is written (quote a)); a symbol's spelling is `write-simple'
;;; of it, computed once per symbol per page (SYMS, an eq table).
(define (cc--write-datum x emit syms)
  (let walk ((x x))
    (cond ((pair? x)
           (emit #\()
           (walk (car x))
           (let loop ((d (cdr x)))
             (cond ((pair? d) (emit #\space) (walk (car d)) (loop (cdr d)))
                   ((null? d) #t)
                   (#t (emit " . ") (walk d))))
           (emit #\)))
          ((symbol? x)
           (emit (or (hash-table-ref/default syms x #f)
                     (let ((t (call-with-output-string (lambda (p) (cc--write x p)))))
                       (hash-table-set! syms x t)
                       t))))
          ((null? x) (emit "()"))
          ((and (number? x) (exact-rational? x)) (emit (number->string x 10)))
          (#t (emit (call-with-output-string (lambda (p) (cc--write x p))))))))

;;; The page TEXT.  CORE-GC (2026-11-11): built with MIT's `string-builder' rather than
;;; a string port (a port operation cost ~0.4 us, eight times a builder call), and
;;; every formula through `cc--write-datum'; the text is the same, character for
;;; character, as the port writer's of before (checked on 1608 pages).
(define (cc--page-text page)
  (let ((sb (string-builder))
        (memo (make-strong-eqv-hash-table))
        (syms (make-strong-eqv-hash-table))       ; symbol -> its written spelling
        (seqnum (make-strong-eqv-hash-table))     ; sequent form -> its number
        (nseq 0))
    (define (num n) (sb (number->string n 10)))  ; `write' of an exact integer
    (define (wf f)
      (sb (or (hash-table-ref/default memo f #f)
              (let ((str (let ((sub (string-builder))) (cc--write-datum f sub syms) (sub))))
                (if (pair? f) (hash-table-set! memo f str))
                str))))
    (define (wlist fs)
      (let loop ((as fs) (first #t))
        (if (pair? as)
            (begin (if (not first) (sb #\space)) (wf (car as)) (loop (cdr as) #f)))))
    (define (number! sq)
      (set! nseq (+ nseq 1))
      (if (not (hash-table-ref/default seqnum sq #f)) (hash-table-set! seqnum sq nseq))
      nseq)
    (define (wseq-full sq)               ; (sequent (A ...) G)
      (set! *cc-seq-full* (+ *cc-seq-full* 1))
      (sb "(sequent (") (wlist (cadr sq))
      (sb ") ") (wf (caddr sq)) (sb ")"))
    ;; BASE: the step's sequent form (already numbered), or #f
    (define (wseq sq base)
      (let ((j (hash-table-ref/default seqnum sq #f)))
        (cond
         (j (set! *cc-seq-ref* (+ *cc-seq-ref* 1))
            (sb "(sequent-ref ") (num j) (sb ")"))
         ((and base (hash-table-ref/default seqnum base #f) (cc--seq-delta base sq))
          => (lambda (d)
               (set! *cc-seq-delta* (+ *cc-seq-delta* 1))
               (sb "(sequent-delta ") (num (hash-table-ref seqnum base (lambda () 0)))
               (sb " (drop")
               (for-each (lambda (i) (sb #\space) (num i)) (car d))
               (sb ") (add")
               (for-each (lambda (f) (sb #\space) (wf f)) (cadr d))
               (sb ")")
               (if (not (caddr d)) (begin (sb #\space) (wf (caddr sq))))
               (sb ")")))
         (#t (wseq-full sq))))
      (number! sq))
    (define (wfield x base)              ; a step field
      (cond ((and (pair? x) (eq? (car x) 'sequent)) (wseq x #f))
            ((and (pair? x) (eq? (car x) 'hyps))
             (sb "(hyps")
             (for-each (lambda (h) (sb #\space) (wseq h base)) (cdr x))
             (sb ")"))
            (#t (cc--write-datum x sb syms))))
    (sb "(core-page ") (cc--write-datum (cadr page) sb syms) (sb #\newline)
    (for-each (lambda (field)
                (sb "  ")
                (if (and (pair? field) (eq? (car field) 'step))
                    (let ((base (find (lambda (x) (and (pair? x) (eq? (car x) 'sequent))) (cdr field))))
                      (sb "(step")
                      (for-each (lambda (x) (sb #\space) (wfield x base)) (cdr field))
                      (sb ")"))
                    (cc--write-datum field sb syms))
                (sb #\newline))
              (cddr page))
    (sb ")") (sb #\newline)
    (sb)))

(define (cc--write-page-to-port page port)
  (write-string (cc--page-text page) port))

(define (core-page->string page)
  (cc--page-text page))

(define (cc--write-page! name page)
  (let ((dir (string-append *prover-dir* "core-pages/"))
        (path (cc--page-path name)))
    (if (not (file-directory? dir)) (make-directory dir))
    ;; a compressed page of an earlier run must not shadow this one
    (if (file-exists? (string-append path ".gz")) (delete-file (string-append path ".gz")))
    ;; written under a temporary name and renamed: a page that failed half-way is never read
    (let ((tmp (string-append path ".tmp")))
      (call-with-current-continuation
       (lambda (k)
         (with-exception-handler
          (lambda (e) (if (file-exists? tmp) (delete-file tmp)) (raise e))
          (lambda ()
            ;; the text is built in a string port and written as UTF-8 bytes in one call:
            ;; a textual file port encodes character by character
            (let ((bytes (string->utf8 (cc--page-text page)))
                  (out (open-binary-output-file tmp)))
              (write-bytevector bytes out)
              (close-port out))))))
      (rename-file tmp path))
    path))

;;; Compress every page of core-pages/ (one gzip process, at load end): the reader
;;; (core-replay.scm `core-page-read') takes NAME.core, else NAME.core.gz.
(define (core-capture-gzip-pages!)
  (let ((dir (string-append *prover-dir* "core-pages")))
    (if (file-directory? dir)
        (begin
          (load-option 'synchronous-subprocess)
          (run-shell-command
           (string-append "find '" dir "' -maxdepth 1 -name '*.core' -print0 < /dev/null | xargs -0 -r gzip -f"))))))

;;; ---------------------------------------------------------------- the replay at qed
;;; Design Q2 (decided as recommended): under VNB_CORE_REPLAY=on the page just written
;;; is READ BACK from its file and replayed in this image by `core-replay-page'
;;; (core-replay.scm), with the capture wrappers passed through (*cc-installed?* #f
;;; inside the replay, so the replay's own calls are not captured).  No time budget:
;;; the exam replays every page to the end (a budget is for interactive use only, and
;;; the workspace command budget of vnb.el is that budget).  Warn-only: the verdict is
;;; counted and listed at load end, `;; core-replay: core-replayed N of M'.
(define *cc-replay-at-qed?* #f)
(define *cc-replayed* 0)
(define *cc-replay-refused* '())      ; (name K CMD REASON), newest first
(define *cc-replay-raised* '())       ; (name . message)
(define *cc-t-replay* 0.)
(define *cc-replay-slowest* '())      ; (seconds . name), the ten slowest

(define (cc--note-slow! secs name)
  (set! *cc-replay-slowest*
        (list-head (sort (cons (cons secs name) *cc-replay-slowest*) (lambda (a b) (> (car a) (car b))))
                   (min 10 (+ 1 (length *cc-replay-slowest*))))))

(define (cc--replay-written! name path)
  (let ((t0 (current-jiffy)))
    (call-with-current-continuation
     (lambda (k)
       (with-exception-handler
        (lambda (e)
          (set! *cc-replay-raised*
                (cons (cons name (if (condition? e) (condition/report-string e) e)) *cc-replay-raised*))
          (k #f))
        (lambda ()
          (let* ((page (core-page-expand (core-page-read-plain-file path)))   ; core-replay.scm
                 (v (fluid-let ((*cc-installed?* #f)) (core-replay-page page))))
            (if (eq? (car v) 'core-replayed)
                (set! *cc-replayed* (+ *cc-replayed* 1))
                (set! *cc-replay-refused* (cons (cons name (cdr v)) *cc-replay-refused*))))))))
    (let ((secs (/ (- (current-jiffy) t0) (exact->inexact (jiffies-per-second)))))
      (set! *cc-t-replay* (+ *cc-t-replay* secs))
      (cc--note-slow! secs name))))

;;; Called by qed--guarded (interactive.scm) after the certificate record, with the
;;; ledger's bill.  Never raises: a failure is counted and listed at load end.
(define (core-capture-on-qed! name bill)
  (if (and *cc-installed?* *ps*)
      (let ((t0 (runtime)))
        (call-with-current-continuation
         (lambda (k)
           (with-exception-handler
            (lambda (e)
              (set! *cc-hook-errors*
                    (cons (cons name (if (condition? e) (condition/report-string e) e)) *cc-hook-errors*))
              (set! *cc-pages-failed* (cons (cons name 'error) *cc-pages-failed*))
              (k #f))
            (lambda ()
              (call-with-values (lambda () (cc--lower name *ps*))
                (lambda (page cites)
                  (let ((t1 (runtime)))
                    (set! *cc-t-lower* (+ *cc-t-lower* (- t1 t0)))
                    (set! *cc-last-page* page)
                    (set! *cc-pages-lowered* (+ *cc-pages-lowered* 1))
                    (cc--kernel-bill! name cites bill)
                    (let ((t2 (runtime)))
                      (set! *cc-t-bill* (+ *cc-t-bill* (- t2 t1)))
                      (let ((path (and *cc-write-pages?* (cc--write-page! name page))))
                        (set! *cc-t-write* (+ *cc-t-write* (- (runtime) t2)))
                        (if (and path *cc-replay-at-qed?*) (cc--replay-written! name path)))))))))))
        ;; capture records of this graph are dropped: only the verdict, the kernel
        ;; citation list and the bill are kept (design s.5, isolation)
        (hash-table-delete! *cc-graph-records* (proof-state-dg *ps*))
        (hash-table-delete! *cc-graph-mints* (proof-state-dg *ps*))
        (set! *cc-hook-seconds* (+ *cc-hook-seconds* (- (runtime) t0))))))

(set! *core-capture-qed-hook* core-capture-on-qed!)

;;; A page uses core commands only (the lowering check of the suite).
(define (core-page-commands page)
  (map (lambda (st) (car (list-ref st 3)))
       (filter (lambda (f) (and (pair? f) (eq? (car f) 'step))) page)))
(define (core-page-core-only? page)
  (every core-command-name? (core-page-commands page)))
(define (script-core-only? script)
  (every (lambda (e) (core-command-name? (car e))) script))

;;; ---------------------------------------------------------------- step 1: the page corpus
(define (cc--corpus-dir)
  (let ((v (get-environment-variable "VNB_CORE_CORPUS")))
    (if (and v (> (string-length v) 0)) v "/home/ubuntu/core-corpus/")))

(define (core-capture-write-corpus!)
  (let* ((dir  (let ((d (cc--corpus-dir)))
                 (if (char=? (string-ref d (- (string-length d) 1)) #\/) d (string-append d "/"))))
         (file (string-append dir "pages.txt"))
         (n 0))
    (if (not (file-directory? dir)) (make-directory dir))
    (call-with-output-file file
      (lambda (port)
        (for-each (lambda (nm)
                    (let ((text (page-of nm)))
                      (if text
                          (begin (set! n (+ n 1))
                                 (write-string ";;; PAGE " port) (write nm port) (newline port)
                                 (write-string text port) (newline port)))))
                  (sort (hash-table-keys *proof-script-table*)
                        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))))
    ;; run-shell-command is unassigned until this option is loaded (proof-reader.scm)
    (load-option 'synchronous-subprocess)
    (run-shell-command (string-append "gzip -f " file " < /dev/null"))
    (display ";; core-corpus: ") (display n) (display " page(s) written to ")
    (display file) (display ".gz") (newline)
    n))

;;; ---------------------------------------------------------------- load end
;;; The summary lines are printed and also written to core-pages/SUMMARY.txt, which the
;;; exam carries back with the pages (vnb-band-pull) and the nightly report quotes.
(define (cc--summary-lines)
  (with-output-to-string
    (lambda ()
      (display ";; kernel-bill: ") (display *cc-bill-agree*) (display " agree, ")
      (display (length *cc-bill-differ*)) (display " differ")
      (if (pair? *cc-bill-differ*)
          (let* ((d (reverse *cc-bill-differ*))
                 (kernel-only (filter (lambda (r) (any (lambda (x) (not (memq x (caddr r)))) (cadr r))) d)))
            (display " (") (display (length kernel-only))
            (display " where the kernel cites a leaf the ledger misses)")))
      (newline)
      (for-each (lambda (r)
                  (display ";;   kernel-bill differs: ") (write (car r))
                  (display " kernel ") (write (cadr r)) (display " ledger ") (write (caddr r)) (newline))
                (list-head (reverse *cc-bill-differ*) (min 40 (length *cc-bill-differ*))))
      (display ";; kernel-oracles: ") (display (length *cc-oracle-differ*)) (display " differ") (newline)
      (for-each (lambda (r)
                  (display ";;   kernel-oracles differ: ") (write (car r))
                  (display " kernel ") (write (cadr r)) (display " ledger ") (write (caddr r)) (newline))
                (list-head (reverse *cc-oracle-differ*) (min 20 (length *cc-oracle-differ*))))
      (display ";; core-lowering: ") (display *cc-pages-lowered*) (display " page(s) lowered, ")
      (display (length *cc-pages-failed*)) (display " failed; ")
      (display *cc-steps-emitted*) (display " step(s), ")
      (display *cc-steps-recovered*) (display " recovered, ")
      (display *cc-steps-unrecovered*) (display " unrecovered, ")
      (display *cc-steps-noncore*) (display " non-core, ")
      (display *cc-steps-off-target*) (display " off-target; ")
      (display *cc-converted-indices*) (display " index argument(s) converted; ")
      (display *cc-mint-clashes*) (display " mint clash(es); ")
      (display *cc-calls*) (display " captured call(s); sequents written ")
      (display *cc-seq-full*) (display " full, ") (display *cc-seq-ref*) (display " shared, ")
      (display *cc-seq-delta*) (display " as differences; qed hook ")
      (display (round *cc-hook-seconds*)) (display " s CPU (lower ")
      (display (round *cc-t-lower*)) (display ", bill ") (display (round *cc-t-bill*))
      (display ", write ") (display (round *cc-t-write*)) (display ")") (newline)
      (for-each (lambda (e) (display ";;   core-capture error: ") (write (car e))
                        (display " -- ") (display (cdr e)) (newline))
                (list-head (reverse *cc-hook-errors*) (min 20 (length *cc-hook-errors*))))
      (if *cc-replay-at-qed?*
          (begin
            (display ";; core-replay: core-replayed ") (display *cc-replayed*) (display " of ")
            (display *cc-pages-lowered*)
            (display " (") (display (length *cc-replay-refused*)) (display " refused, ")
            (display (length *cc-replay-raised*)) (display " raised; replay ")
            (display (round *cc-t-replay*)) (display " s wall)") (newline)
            (for-each (lambda (r)
                        (display ";;   core-replay refused: ") (write (car r))
                        (display " at step ") (display (cadr r)) (display " (") (write (caddr r))
                        (display "): ") (display (cadddr r)) (newline))
                      (reverse *cc-replay-refused*))
            (for-each (lambda (r)
                        (display ";;   core-replay raised: ") (write (car r))
                        (display " -- ") (display (cdr r)) (newline))
                      (reverse *cc-replay-raised*))
            (display ";;   core-replay slowest:")
            (for-each (lambda (p) (display " ") (write (cdr p)) (display " ")
                              (display (/ (round (* 10 (car p))) 10.)) (display "s"))
                      *cc-replay-slowest*)
            (newline))))))

(define (core-capture-load-end!)
  (if *cc-installed?*
      (begin
        (core-capture-uninstall!)
        (let ((text (cc--summary-lines)))
          (display text)
          (if *cc-write-pages?*
              (call-with-current-continuation
               (lambda (k)
                 (with-exception-handler
                  (lambda (e) (display ";; core-pages: FAILED -- ")
                          (display (if (condition? e) (condition/report-string e) e)) (newline) (k #f))
                  (lambda ()
                    (let ((dir (string-append *prover-dir* "core-pages/")))
                      (if (not (file-directory? dir)) (make-directory dir))
                      (call-with-output-file (string-append dir "SUMMARY.txt")
                        (lambda (port) (write-string text port))))
                    (core-capture-gzip-pages!)
                    (display ";; core-pages: ") (display *cc-pages-lowered*)
                    (display " page(s) gzipped in ") (display *prover-dir*) (display "core-pages/")
                    (newline)))))))
        (call-with-current-continuation
         (lambda (k)
           (with-exception-handler
            (lambda (e) (display ";; core-corpus: FAILED -- ")
                    (display (if (condition? e) (condition/report-string e) e)) (newline) (k #f))
            (lambda () (core-capture-write-corpus!))))))))

(define (core-capture-report)
  (list (list 'agree *cc-bill-agree*)
        (list 'differ (reverse *cc-bill-differ*))
        (list 'oracle-differ (reverse *cc-oracle-differ*))
        (list 'lowered *cc-pages-lowered*)
        (list 'failed (reverse *cc-pages-failed*))
        (list 'steps *cc-steps-emitted*)
        (list 'recovered *cc-steps-recovered*)
        (list 'unrecovered *cc-steps-unrecovered*)
        (list 'non-core *cc-steps-noncore*)
        (list 'off-target *cc-steps-off-target*)
        (list 'converted-indices *cc-converted-indices*)
        (list 'calls *cc-calls*)
        (list 'hook-seconds *cc-hook-seconds*)))

;;; ---------------------------------------------------------------- arm under the flag
(if *cc-flag-on?*
    (begin
      (set! *cc-write-pages?* #t)
      (set! *cc-replay-at-qed?* #t)
      ;; the pages of an earlier run go: a retired theorem's page must not survive
      (let ((dir (string-append *prover-dir* "core-pages")))
        (if (file-directory? dir)
            (begin (load-option 'synchronous-subprocess)
                   (run-shell-command (string-append "rm -rf '" dir "' < /dev/null")))))
      (core-capture-install!)
      (display ";; core-capture: VNB_CORE_REPLAY=on -- ")
      (display (length *cc-originals*)) (display " entry points wrapped; core pages to ")
      (display *prover-dir*) (display "core-pages/, each replayed at its qed") (newline)))
