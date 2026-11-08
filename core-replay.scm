;;; core-replay.scm -- the CORE REPLAYER (core replay, design step 4) and the
;;; prover-side API the Emacs surface calls.
;;;
;;; Design: docs/core-replay-design-2026-11-05.md (s.1 the core, s.3, s.4, s.5 step 4).
;;; Format:  docs/core-page-format.md (the contract, as a specification).
;;;
;;; A CORE PAGE is DATA: a statement and a list of steps, each one call of one kernel
;;; entry point at one named node, with the sequent of that node and the hypothesis
;;; sequents the call produced.  This file re-creates the proof from the page:
;;;
;;;   (core-replay-page PAGE)  ->  (core-replayed N)  |  (refused K CMD REASON)
;;;
;;; on a FRESH proof state, inside a `fluid-let' of every global a proof writes, so
;;; that nothing it does is visible afterwards (no theorem is installed, the fresh
;;; counter, the mint log, the journal and the check counters are restored).
;;;
;;; What it checks, per step K:
;;;   1. the step is well formed and numbered K, its command is one of the core names
;;;      in the DISPATCH TABLE below (no `eval', ever: a command that is not in the
;;;      table is refused, whatever it is);
;;;   2. the page node N it names maps to a replay node (the NODE MAP, matched by
;;;      sequent up to alpha and the mint map, never by number), and that node's
;;;      sequent is the recorded one;
;;;   3. if the replay node is already justified by an inference whose hypotheses are
;;;      the recorded ones, the step is accepted WITHOUT RUNNING (hash-consing; a
;;;      chain); if it is already GROUNDED by another inference it is skipped and
;;;      counted (design R2);
;;;   4. otherwise the entry point is called with the step's arguments (mint names
;;;      mapped to this session's names; `ineq' premises resolved from FORMULAS to
;;;      this node's indices), and the hypothesis sequents of the inferences the call
;;;      recorded must equal the recorded ones, in order, up to alpha and the map;
;;;   5. at a step whose recorded hypotheses mention a page mint not yet mapped, the
;;;      map is LEARNED from the produced hypotheses, and must stay a bijection.
;;; Then, as `qed' does, the root must be grounded.
;;;
;;; Trust: none added.  The replayer calls the same entry points the tactics call,
;;; under the same checkers; it calls no `dg-apply-rule!' itself, so
;;; *kernel-caller-files* is unchanged, and it is in no kernel-hash file.

;;; -----------------------------------------------------------------------
;;; Where pages live.  The exam writes <tree>/core-pages/NAME.core (core-capture.scm);
;;; the hand-written fixtures of the suite are in <tree>/test-core-pages/ and are named
;;; core-fixture-*, so they can never shadow a theorem's page.
(define *core-pages-dirs*
  (list (string-append *prover-dir* "core-pages/")
        (string-append *prover-dir* "test-core-pages/")))

(define (cr--file-name name)              ; as core-capture.scm `cc--page-path' spells it
  (list->string (append-map (lambda (ch) (if (char=? ch #\/) (string->list "%2F") (list ch)))
                            (string->list (symbol->string name)))))

;;; NAME.core, else NAME.core.gz (the exam compresses its pages at load end).
(define (core-page-path name)
  (let ((f (cr--file-name name)))
    (let loop ((ds *core-pages-dirs*))
      (cond ((null? ds) #f)
            ((file-exists? (string-append (car ds) f ".core")) (string-append (car ds) f ".core"))
            ((file-exists? (string-append (car ds) f ".core.gz")) (string-append (car ds) f ".core.gz"))
            (#t (loop (cdr ds)))))))

(define (cr--shell-quote s)
  (string-append "'" (apply string-append
                            (map (lambda (ch) (if (char=? ch #\') "'\\''" (string ch))) (string->list s)))
                 "'"))

;;; `run-shell-command' (gzip) is unassigned until this option is loaded; loaded here,
;;; once, so that an interactive core-page-text prints no `;Loading' lines.
(load-option 'synchronous-subprocess)

;;; The datum of a page file, plain or gzipped (gzip -dc through a string port).
(define (cr--read-page-file p)
  (if (string-suffix? ".gz" p)
      (begin
        (load-option 'synchronous-subprocess)
        (let ((text (call-with-output-string
                     (lambda (port)
                       (run-shell-command (string-append "gzip -dc " (cr--shell-quote p) " < /dev/null")
                                          'output port)))))
          (read (open-input-string text))))
      (call-with-input-file p read)))

;;; The page as the reader returns it, EXPANDED (s.1a of the format: every shared or
;;; difference-written sequent replaced by its full form), or #f when there is no file.
;;; A file that does not hold a (core-page ...) form is an error, not a missing page.
(define (core-page-read name)
  (let ((p (core-page-path name)))
    (and p
         (let ((d (cr--read-page-file p)))
           (if (and (pair? d) (eq? (car d) 'core-page))
               (core-page-expand d)
               (error "core-page-read: not a (core-page ...) form:" p))))))

;;; -----------------------------------------------------------------------
;;; THE COMPACT FORMS (docs/core-page-format.md s.1a).  Every SEQUENT form of the page
;;; -- a step's sequent field, each element of its hyps -- is numbered 1, 2, ... in
;;; reading order.  (sequent-ref J) is sequent J; (sequent-delta J (drop I ...) (add A
;;; ...) [GOAL]) has the assumptions A ... followed by sequent J's assumptions without
;;; the 0-based positions I (strictly increasing), and goal GOAL, else J's goal.  The
;;; expansion returns the page with every such form replaced by a full (sequent ASMS
;;; GOAL); a reference to the same number is the SAME (eq) form, which the replayer
;;; uses to find the node of a step without a search.  A form that does not resolve
;;; becomes (sequent-invalid FORM), and the step that holds it is refused.  A page
;;; with full forms only is returned with its forms unchanged.
(define (cr--drop-positions l ps)
  (let loop ((l l) (i 0) (ps ps) (acc '()))
    (cond ((null? l) (and (null? ps) (reverse acc)))
          ((and (pair? ps) (= (car ps) i)) (loop (cdr l) (+ i 1) (cdr ps) acc))
          (#t (loop (cdr l) (+ i 1) ps (cons (car l) acc))))))

(define (cr--increasing-naturals? l)
  (let loop ((l l) (prev -1))
    (or (null? l)
        (and (exact-nonnegative-integer? (car l)) (> (car l) prev) (loop (cdr l) (car l))))))

(define (core-page-expand page)
  (if (not (and (pair? page) (eq? (car page) 'core-page) (list? page)))
      page
      (let ((table (make-strong-eqv-hash-table)) (n 0))
        (define (lookup j) (and (exact-positive-integer? j) (hash-table-ref/default table j #f)))
        (define (resolve f)
          (cond ((and (pair? f) (eq? (car f) 'sequent)) f)
                ((and (pair? f) (eq? (car f) 'sequent-ref) (pair? (cdr f)) (null? (cddr f)))
                 (lookup (cadr f)))
                ((and (pair? f) (eq? (car f) 'sequent-delta) (list? f) (memv (length f) '(4 5)))
                 (let ((b (lookup (cadr f))) (drop (caddr f)) (add (cadddr f)))
                   (and b
                        (pair? drop) (eq? (car drop) 'drop) (list? drop) (cr--increasing-naturals? (cdr drop))
                        (pair? add) (eq? (car add) 'add) (list? add)
                        (pair? (cdr b)) (list? (cadr b)) (pair? (cddr b))
                        (let ((kept (cr--drop-positions (cadr b) (cdr drop))))
                          (and kept
                               (list 'sequent (append (cdr add) kept)
                                     (if (= (length f) 5) (list-ref f 4) (caddr b))))))))
                (#t #f)))
        (define (seq-form? f)
          (and (pair? f) (memq (car f) '(sequent sequent-ref sequent-delta))))
        (define (number! f)
          (set! n (+ n 1))
          (let ((r (resolve f)))
            (if r (hash-table-set! table n r))
            (or r (list 'sequent-invalid f))))
        (define (step-field x)
          (cond ((seq-form? x) (number! x))
                ((and (pair? x) (eq? (car x) 'hyps) (list? x))
                 (cons 'hyps (map (lambda (h) (if (seq-form? h) (number! h) h)) (cdr x))))
                (#t x)))
        (cons* 'core-page (cadr page)
               (map (lambda (fld)
                      (if (and (pair? fld) (eq? (car fld) 'step) (list? fld)
                               (pair? (cdr fld)) (pair? (cddr fld)) (pair? (cdddr fld)))
                          ;; (step K (at-node N) CMD field ...): the command is not a field
                          (cons* 'step (cadr fld) (caddr fld) (cadddr fld) (map step-field (cddddr fld)))
                          fld))
                    (cddr page))))))

;;; -----------------------------------------------------------------------
;;; Page accessors (unknown fields are ignored, as the contract requires).
(define (cp--field forms tag)
  (let loop ((fs forms))
    (cond ((null? fs) #f)
          ((and (pair? (car fs)) (eq? (caar fs) tag)) (car fs))
          (#t (loop (cdr fs))))))
(define (cp-name page) (cadr page))
(define (cp-statement page) (let ((f (cp--field (cddr page) 'statement))) (and f (cadr f))))
(define (cp-kernel-hash page) (let ((f (cp--field (cddr page) 'kernel-hash))) (and f (cadr f))))
(define (cp-mints page) (let ((f (cp--field (cddr page) 'mints))) (if f (cdr f) '())))
(define (cp-steps page)
  (filter (lambda (f) (and (pair? f) (eq? (car f) 'step))) (cddr page)))

;;; A step: (step K (at-node N) (CMD ARG ...) field ...).  The command is the form
;;; IMMEDIATELY after (at-node N); the fields after it are read by head.
(define (cps-k s) (and (pair? (cdr s)) (cadr s)))
(define (cps-node s)
  (and (pair? (cdr s)) (pair? (cddr s))
       (let ((a (caddr s)))
         (and (pair? a) (eq? (car a) 'at-node) (pair? (cdr a)) (cadr a)))))
(define (cps-cmd s) (and (pair? (cdr s)) (pair? (cddr s)) (pair? (cdddr s)) (cadddr s)))
(define (cps-rest s) (if (and (pair? (cdr s)) (pair? (cddr s)) (pair? (cdddr s))) (cddddr s) '()))
;;; (sequent (ASM ...) GOAL) -> (ASMS GOAL), or #f
(define (cr--seq-form f)
  (and (pair? f) (eq? (car f) 'sequent) (= (length f) 3) (list? (cadr f))
       (list (cadr f) (caddr f))))
(define (cps-sequent s) (let ((f (cp--field (cps-rest s) 'sequent))) (and f (cr--seq-form f))))
(define (cps-sequent-form s) (cp--field (cps-rest s) 'sequent))
(define (cps-hyp-forms s) (let ((f (cp--field (cps-rest s) 'hyps))) (if f (cdr f) '())))
(define (cps-invalid s)                  ; a compact form of the step that did not resolve
  (or (cp--field (cps-rest s) 'sequent-invalid)
      (find (lambda (h) (and (pair? h) (eq? (car h) 'sequent-invalid))) (cps-hyp-forms s))))
(define (cps-hyps s)
  (let ((f (cp--field (cps-rest s) 'hyps)))
    (and f (let ((l (map cr--seq-form (cdr f)))) (and (not (memq #f l)) l)))))

;;; -----------------------------------------------------------------------
;;; THE DISPATCH TABLE.  One row per core command:
;;;   (NAME ENTRY-POINTS ARG-KINDS PROCEDURE)
;;; ENTRY-POINTS names the kernel-map entries the row covers (coverage gate, check 8).
;;; ARG-KINDS: f = formula or term (mint names mapped), name = a symbol taken as is,
;;; nat = a nonnegative integer, f* = any number of formulas (`ineq' premises, resolved
;;; to this node's 1-based indices), t* = any number of terms.
;;; PROCEDURE takes the replay node and the converted arguments and returns what the
;;; entry point returns.  The entry points are referenced by name, resolved at call
;;; time; nothing is evaluated from the page.
(define *core-dispatch*
  (list
   (list 'di      '(pi-direct-inference!)        '()       (lambda (n) (pi-direct-inference! n)))
   (list 'ai      '(pi-antecedent-inference!)    '(f)      (lambda (n f) (pi-antecedent-inference! n f)))
   (list 'pbc     '(pi-proof-by-contradiction!)  '()       (lambda (n) (pi-proof-by-contradiction! n)))
   (list 'oi-l    '(pi-or-intro-left!)           '()       (lambda (n) (pi-or-intro-left! n)))
   (list 'oi-r    '(pi-or-intro-right!)          '()       (lambda (n) (pi-or-intro-right! n)))
   (list 'ew      '(pi-exists-witness!)          '(f)      (lambda (n t) (pi-exists-witness! n t)))
   (list 'ci      '(pi-cartesian-intro!)         '()       (lambda (n) (pi-cartesian-intro! n)))
   (list 'ti      '(pi-tuples-intro!)            '()       (lambda (n) (pi-tuples-intro! n)))
   (list 'ii      '(pi-intersection-intro!)      '()       (lambda (n) (pi-intersection-intro! n)))
   (list 'ui      '(pi-union-intro!)             '(nat)    (lambda (n k) (pi-union-intro! n k)))
   (list 'ni      '(pi-nn-induction!)            '()       (lambda (n) (pi-nn-induction! n)))
   (list 'tfi     '(pi-tfi!)                     '()       (lambda (n) (pi-tfi! n)))
   (list 'tfi3    '(pi-tfi3!)                    '()       (lambda (n) (pi-tfi3! n)))
   (list 'ass     '(pi-assumption!)              '()       (lambda (n) (pi-assumption! n)))
   (list 'ta      '(pi-theorem-assumption!)      '(name)   (lambda (n m) (pi-theorem-assumption! n m)))
   (list 'inst    '(pi-instantiate!)             '(f f)    (lambda (n f t) (pi-instantiate! n f t)))
   (list 'detach! '(pi-detach!)                  '(f)      (lambda (n f) (pi-detach! n f)))
   (list 'bc      '(pi-backchain!)               '(f)      (lambda (n f) (pi-backchain! n f)))
   (list 'cut     '(pi-cut!)                     '(f)      (lambda (n f) (pi-cut! n f)))
   (list 'wk      '(pi-weaken!)                  '(f)      (lambda (n f) (pi-weaken! n f)))
   (list 'ce      '(pi-cartesian-elim!)          '(f nat)  (lambda (n f k) (pi-cartesian-elim! n f k)))
   (list 'te      '(pi-tuples-elim!)             '(f nat)  (lambda (n f k) (pi-tuples-elim! n f k)))
   (list 'ie      '(pi-intersection-elim!)       '(f nat)  (lambda (n f k) (pi-intersection-elim! n f k)))
   (list 'ue      '(pi-union-elim!)              '(f)      (lambda (n f) (pi-union-elim! n f)))
   ;; `mac' addresses every macete by name, the two procedural decomposition macetes
   ;; of library.scm included (install-macete! puts them in the same table).
   (list 'mac     '(<elementary-macete> <macete:cartesian-decompose> <macete:tuple-equality-decompose>)
                  '(name)
                  (lambda (n m) (apply-macete! m n)))
   (list 'macm    '(<elementary-macete>)         '(name)
                  (lambda (n m) (fluid-let ((*macete-spawn-conditions?* #t)) (apply-macete! m n))))
   (list 'mac-h   '(apply-macete-to-assumption!) '(name f) (lambda (n m f) (apply-macete-to-assumption! m f n)))
   (list 'subst   '(pi-eq-subst!)                '(f)      (lambda (n e) (pi-eq-subst! n e)))
   (list 'rfl     '(pi-reflexivity!)             '()       (lambda (n) (pi-reflexivity! n)))
   (list 'qrfl    '(pi-quasi-reflexivity!)       '()       (lambda (n) (pi-quasi-reflexivity! n)))
   (list 'beta    '(pi-functoid-beta!)           '()       (lambda (n) (pi-functoid-beta! n)))
   (list 'lam-t   '(pi-lambda-type!)             '()       (lambda (n) (pi-lambda-type! n)))
   (list 'lam-b   '(pi-lambda-beta!)             '()       (lambda (n) (pi-lambda-beta! n)))
   (list 'lam-b-h '(pi-lambda-beta-hyp!)         '(f)      (lambda (n f) (pi-lambda-beta-hyp! n f)))
   (list 'nth-r   '(pi-nth-reduce!)              '()       (lambda (n) (pi-nth-reduce! n)))
   (list 'len-r   '(pi-length-reduce!)           '()       (lambda (n) (pi-length-reduce! n)))
   (list 'if-true '(pi-if-true!)                 '(f)      (lambda (n t) (pi-if-true! n t)))
   (list 'if-false '(pi-if-false!)               '(f)      (lambda (n t) (pi-if-false! n t)))
   (list 'sep-set '(pi-sep-sethood!)             '()       (lambda (n) (pi-sep-sethood! n)))
   (list 'sep-mi  '(pi-sep-mem-intro!)           '()       (lambda (n) (pi-sep-mem-intro! n)))
   (list 'sep-me  '(pi-sep-mem-elim!)            '(f)      (lambda (n f) (pi-sep-mem-elim! n f)))
   (list 'comp-mi '(pi-comp-mem-intro!)          '()       (lambda (n) (pi-comp-mem-intro! n)))
   (list 'comp-me '(pi-comp-mem-elim!)           '(f)      (lambda (n f) (pi-comp-mem-elim! n f)))
   (list 'iota-d  '(pi-iota-def!)                '(f)      (lambda (n t) (pi-iota-def! n t)))
   (list 'iota-e  '(pi-iota-in-elim!)            '(f)      (lambda (n t) (pi-iota-in-elim! n t)))
   (list 'bu-set  '(pi-big-union-sethood!)       '()       (lambda (n) (pi-big-union-sethood! n)))
   (list 'bu-mi   '(pi-big-union-mem-intro!)     '(f)      (lambda (n w) (pi-big-union-mem-intro! n w)))
   (list 'bu-me   '(pi-big-union-mem-elim!)      '(f)      (lambda (n f) (pi-big-union-mem-elim! n f)))
   ;; The oracles: one step each, certificate-checked (the user's decision).
   (list 'arith   '(pi-arith!)                   '()       (lambda (n) (pi-arith! n)))
   (list 'crs     '(pi-comm-ring-simplify!)      '()       (lambda (n) (pi-comm-ring-simplify! n)))
   (list 'rs      '(pi-ring-simplify!)           '()       (lambda (n) (pi-ring-simplify! n)))
   (list 'ineq    '(pi-ineq!)                    '(f*)
                  (lambda (n . fs) (pi-ineq! n (cr--premise-indices n fs))))
   (list 'sos     '(pi-sos!)                     '(t*)     (lambda (n . ts) (pi-sos! n ts)))))

;;; The structural core names: not steps of a page.  `sp' is the statement, `qed' the
;;; final check, `at-node' the node field.  Together with the 53 rows above: 56.
(define *core-structural* '(sp qed at-node))

;;; Entry points of the kernel map with no core command: unexercised in the library
;;; (reference/KERNEL-MAP.md).  A page cannot name them; a lowering that needs one
;;; must emit a command that is refused.
(define *core-refused-unexercised* '(pi-spec! pi-truth! pi-contraposit!))

(define (core-names) (append (map car *core-dispatch*) *core-structural*))

;;; -----------------------------------------------------------------------
;;; COVERAGE (suite check 8).  Every entry point of reference/kernel-map-static.sexp
;;; has a dispatch row or is on the refused-unexercised list.
(define (core-replay-kernel-entry-points)
  (let* ((p (string-append *prover-dir* "reference/kernel-map-static.sexp"))
         (d (call-with-input-file p read))
         (k (assq 'kernel d)))
    (if (not k) (error "core-replay: no (kernel ...) list in" p))
    (map car (cadr k))))

(define (core-replay-coverage-missing #!optional table refused)
  (let* ((tb (if (default-object? table) *core-dispatch* table))
         (rf (if (default-object? refused) *core-refused-unexercised* refused))
         (covered (append rf (append-map cadr tb))))
    (filter (lambda (e) (not (memq e covered))) (core-replay-kernel-entry-points))))

;;; -----------------------------------------------------------------------
;;; Refusal.  Inside a replay a refusal escapes to the replay's own continuation.
(define *cr--refuse-k* #f)
(define (cr--refuse! reason . irritants)
  (let ((msg (call-with-output-string
              (lambda (port)
                (display reason port)
                (for-each (lambda (x) (write-char #\space port) (cr--write-brief x port)) irritants)))))
    (if *cr--refuse-k* (*cr--refuse-k* msg) (error "core-replay refusal outside a replay:" msg))))

(define (cr--write-brief x port)
  (let ((s (call-with-output-string (lambda (p) (write x p)))))
    (write-string (if (> (string-length s) 300) (string-append (string-head s 297) "...") s) port)))

;;; Call THUNK; an error raised inside it becomes a refusal with the error's text.
(define (cr--guarded thunk)
  (let ((r (call-with-current-continuation
            (lambda (k)
              (with-exception-handler
               (lambda (e) (k (cons '%cr-error e)))
               (lambda () (cons '%cr-ok (thunk))))))))
    (if (eq? (car r) '%cr-ok)
        (cdr r)
        (cr--refuse! (string-append "the entry point raised: "
                                    (let ((e (cdr r)))
                                      (if (condition? e)
                                          (condition/report-string e)
                                          (call-with-output-string (lambda (p) (write e p))))))))))

;;; -----------------------------------------------------------------------
;;; Formulas, maps and comparison.
(define (cr--some p l) (cond ((null? l) #f) ((p (car l)) #t) (#t (cr--some p (cdr l)))))
(define (cr--all p l) (cond ((null? l) #t) ((p (car l)) (cr--all p (cdr l))) (#t #f)))

;;; Apply the mint map M (alist page-name -> session name) to a raw form.
(define (cr--map M x)
  (if (null? M) x
      (let walk ((x x))
        (cond ((pair? x) (cons (walk (car x)) (walk (cdr x))))
              ((and (symbol? x) (assq x M)) => cdr)
              (#t x)))))

;;; The page mint names occurring in X that M does not map.
(define (cr--unmapped mints M x)
  (let ((acc '()))
    (let walk ((x x))
      (cond ((pair? x) (walk (car x)) (walk (cdr x)))
            ((and (symbol? x) (memq x mints) (not (assq x M)) (not (memq x acc)))
             (set! acc (cons x acc)))))
    (reverse acc)))

(define (cr--norm f) (expand-destructuring-quantifiers f))

;;; Does the recorded sequent RS = (ASMS GOAL) (raw, already mapped) equal the
;;; sequent of the node?  Goal up to alpha; context as a set up to alpha, as the
;;; kernel's own `context-same?' compares them.
(define (cr--node-raw n)
  (list (map wff-formula (sequent-node-assumptions n))
        (wff-formula (sequent-node-assertion n))))
(define (cr--seq-equal? rs n)
  (let ((na (map wff-formula (sequent-node-assumptions n)))
        (ng (wff-formula (sequent-node-assertion n))))
    ;; fast path: the same formulas in the same order (the common case: the replay
    ;; node was built by the same entry point as the recorded one)
    (or (and (= (length (car rs)) (length na)) (equal? (cadr rs) ng) (equal? (car rs) na))
        (let ((ra (map cr--norm (car rs))) (rg (cr--norm (cadr rs))))
          (and (alpha-equiv? rg ng)
               (= (length ra) (length na))
               (cr--all (lambda (a) (or (member a na) (cr--some (lambda (b) (alpha-equiv? a b)) na))) ra)
               (cr--all (lambda (b) (or (member b ra) (cr--some (lambda (a) (alpha-equiv? a b)) ra))) na))))))

(define (cr--free-symbols-of-node n)
  (let ((r (cr--node-raw n)))
    (apply append (free-vars (cadr r)) (map free-vars (car r)))))

;;; -----------------------------------------------------------------------
;;; The replay STATE.
(define-record-type <core-replay-state>
  (%make-cr-state page dg root nodemap mintmap mints literals stats seqnode)
  cr-state?
  (page     cr-page)
  (dg       cr-dg)
  (root     cr-root)
  (nodemap  cr-nodemap  set-cr-nodemap!)       ; alist page node id -> sequent node
  (mintmap  cr-mintmap  set-cr-mintmap!)       ; alist page mint name -> session name
  (mints    cr-mints)                          ; the page's mint names
  (literals cr-literals)                       ; free symbols the page uses as themselves
  (stats    cr-stats    set-cr-stats!)         ; (ran shared skipped)
  (seqnode  cr-seqnode))                       ; eq table: recorded hypothesis form -> replay node

;;; Every free symbol of the page that is not a mint name: a mint's image may not be
;;; one of these, or two page names would denote one variable.
(define (cr--page-literals page mints)
  (let ((acc (make-strong-eqv-hash-table)) (seen (make-strong-eqv-hash-table)))
    (define (add! f)
      (if (not (and (pair? f) (hash-table-ref/default seen f #f)))
          (begin
            (if (pair? f) (hash-table-set! seen f #t))
            (for-each (lambda (v) (if (not (memq v mints)) (hash-table-set! acc v #t)))
                      (free-vars f)))))
    (define (add-seq! s) (if s (begin (for-each add! (car s)) (add! (cadr s)))))
    (if (cp-statement page) (add! (cp-statement page)))
    (for-each (lambda (st)
                (let ((f (cps-sequent-form st)))
                  (if (and f (not (hash-table-ref/default seen f #f)))
                      (begin (hash-table-set! seen f #t) (add-seq! (cps-sequent st)))))
                (for-each (lambda (h)
                            (if (not (hash-table-ref/default seen h #f))
                                (begin (hash-table-set! seen h #t) (add-seq! (cr--seq-form h)))))
                          (cps-hyp-forms st)))
              (cp-steps page))
    (hash-table-keys acc)))

;;; The seed of the mint map: '() except in the suite's bijection control (check 2),
;;; which forces a non-injective map.
(define *core-replay-seed-map* '())

(define (cr--make-state page dg root)
  (let ((mints (cp-mints page)))
    (%make-cr-state page dg root (list (cons 1 root)) *core-replay-seed-map*
                    mints (cr--page-literals page mints) (list 0 0 0) (make-strong-eqv-hash-table))))

(define (cr--stat! st i)
  (let ((s (list-copy (cr-stats st))))
    (list-set! s i (+ 1 (list-ref s i)))
    (set-cr-stats! st s)))

;;; Resolve `ineq' premise FORMULAS to 1-based indices of node N's context.
(define (cr--premise-indices n fs)
  (let ((asms (map wff-formula (sequent-node-assumptions n))))
    (map (lambda (f)
           (let ((nf (cr--norm f)))
             (let loop ((as asms) (i 1))
               (cond ((null? as) (cr--refuse! "ineq premise not in the node's context:" f))
                     ((alpha-equiv? nf (car as)) i)
                     (#t (loop (cdr as) (+ i 1)))))))
         fs)))

;;; Compare the produced hypothesis nodes P with the recorded sequents R, in order,
;;; LEARNING the mint map when R mentions an unmapped page mint.  Returns the new map,
;;; or a string saying why they differ.  PARENT is the node the step ran at: a mint's
;;; image is a symbol free in the produced hypotheses and not free in PARENT.
(define (cr--match-hyps st R P parent)
  (let ((M (cr-mintmap st)))
    (define (mismatch M)                 ; first difference under M, as text, or #f
      (if (not (= (length R) (length P)))
          (string-append "the step recorded " (number->string (length R))
                         " hypothesis sequent(s), the entry point produced "
                         (number->string (length P)))
          (let loop ((rs R) (ps P) (i 1))
            (cond ((null? rs) #f)
                  ((cr--seq-equal? (cr--map M (car rs)) (car ps)) (loop (cdr rs) (cdr ps) (+ i 1)))
                  (#t (call-with-output-string
                       (lambda (port)
                         (display "hypothesis " port) (display i port)
                         (display " differs: recorded " port) (cr--write-brief (cr--map M (car rs)) port)
                         (display ", produced " port) (cr--write-brief (cr--node-raw (car ps)) port))))))))
    (let ((U (cr--unmapped (cr-mints st) M R)))
      (if (null? U)
          (or (mismatch M) M)
          (let* ((pfree (cr--free-symbols-of-node parent))
                 (C (let loop ((vs (apply append (map cr--free-symbols-of-node P))) (acc '()))
                      (cond ((null? vs) (reverse acc))
                            ((or (memq (car vs) pfree) (memq (car vs) acc)) (loop (cdr vs) acc))
                            (#t (loop (cdr vs) (cons (car vs) acc)))))))
            (if (or (> (length U) 4) (> (length C) 8))
                (string-append "too many unmapped mints or candidates to learn the map at this step")
                ;; enumerate injective assignments U -> C; take the first that matches
                (let try ((assigns (cr--injections U C)))
                  (cond ((null? assigns)
                         (string-append "no assignment of the page's mint name(s) "
                                        (call-with-output-string (lambda (p) (write U p)))
                                        " to the names this step minted makes the hypotheses agree; "
                                        (or (mismatch M) "")))
                        ((not (mismatch (append (car assigns) M)))
                         (let ((M2 (append (car assigns) M)))
                           (cr--check-bijection! st M2)
                           M2))
                        (#t (try (cdr assigns)))))))))))

;;; All injective maps from the list U into the list C, as alists.
(define (cr--injections us cands)
  (if (null? us) (list '())
      (append-map (lambda (cand)
                    (map (lambda (rest) (cons (cons (car us) cand) rest))
                         (cr--injections (cdr us) (filter (lambda (d) (not (eq? d cand))) cands))))
                  cands)))

;;; The mint map must stay a BIJECTION between page mint names and session names,
;;; and no image may be a name the page uses as itself.
(define (cr--check-bijection! st M)
  (let loop ((m M))
    (if (pair? m)
        (let ((other (find (lambda (e) (and (not (eq? (car e) (caar m))) (eq? (cdr e) (cdar m))))
                           (cdr m))))
          (cond (other
                 (cr--refuse! "the mint map is not a bijection: page names" (caar m) (car other)
                              "both denote" (cdar m)))
                ((memq (cdar m) (cr-literals st))
                 (cr--refuse! "the mint map is not a bijection: page mint" (caar m) "denotes" (cdar m)
                              "which the page also uses as a literal name"))
                (#t (loop (cdr m))))))))

;;; -----------------------------------------------------------------------
;;; ONE STEP.  Returns normally when the step is accepted; refuses (escapes) otherwise.
;;; EXPECTED-K is the step's position (1-based).
(define (cr--find-node st rs)
  (find (lambda (n) (cr--seq-equal? rs n)) (dg-sequent-nodes (cr-dg st))))

(define (cr--resolve-node st page-n rs #!optional form)
  (let ((e (assv page-n (cr-nodemap st))))
    (if e
        (if (cr--seq-equal? rs (cdr e))
            (cdr e)
            (cr--refuse! (string-append "page node " (number->string page-n)
                                        ": its recorded sequent is not the sequent of the replay node it maps to")))
        (let ((n (let ((c (and (not (default-object? form)) form
                               (hash-table-ref/default (cr-seqnode st) form #f))))
                   ;; the node the recorded hypothesis form was matched to, when its
                   ;; sequent is this one (no search); else the search by sequent
                   (if (and c (cr--seq-equal? rs c)) c (cr--find-node st rs)))))
          (if (not n)
              (cr--refuse! (string-append "no replay node matches the recorded sequent of page node "
                                          (number->string page-n))))
          (set-cr-nodemap! st (cons (cons page-n n) (cr-nodemap st)))
          n))))

(define (cr--convert-args st kinds args)
  (let ((M (cr-mintmap st)) (mints (cr-mints st)))
    (define (formula a)
      (let ((u (cr--unmapped mints M a)))
        (if (pair? u) (cr--refuse! "an argument mentions a mint not yet learned:" (car u)))
        (cr--map M a)))
    (let loop ((ks kinds) (as args) (acc '()))
      (cond ((null? ks)
             (if (pair? as) (cr--refuse! "too many arguments"))
             (reverse acc))
            ((memq (car ks) '(f* t*)) (append (reverse acc) (map formula as)))
            ((null? as) (cr--refuse! "too few arguments"))
            ((eq? (car ks) 'f) (loop (cdr ks) (cdr as) (cons (formula (car as)) acc)))
            ((eq? (car ks) 'name)
             (if (not (symbol? (car as))) (cr--refuse! "a name argument is not a symbol:" (car as)))
             (loop (cdr ks) (cdr as) (cons (car as) acc)))
            ((eq? (car ks) 'nat)
             (if (not (exact-nonnegative-integer? (car as)))
                 (cr--refuse! "an index argument is not a nonnegative integer:" (car as)))
             (loop (cdr ks) (cdr as) (cons (car as) acc)))
            (#t (error "core-replay: unknown argument kind" (car ks)))))))

;;; Returns the replay node the step worked at.
(define (cr--run-step! st step expected-k)
  (let ((K (cps-k step)) (N (cps-node step)) (cmd (cps-cmd step))
        (rs (cps-sequent step)) (R (cps-hyps step)))
    (if (not (eqv? K expected-k))
        (cr--refuse! (string-append "step numbers are not dense: expected step "
                                    (number->string expected-k))))
    (if (not (exact-positive-integer? N)) (cr--refuse! "no (at-node N) field, or N is not a positive integer"))
    (if (not (and (pair? cmd) (symbol? (car cmd)) (list? cmd)))
        (cr--refuse! "the command is not a form (CMD ARG ...)"))
    (let ((row (assq (car cmd) *core-dispatch*)))
      (cond ((memq (car cmd) *core-structural*)
             (cr--refuse! "a structural core name is not a step command:" (car cmd)))
            ((not row) (cr--refuse! "not a core command:" (car cmd))))
      (if (cps-invalid step)
          (cr--refuse! "a shared or difference-written sequent does not resolve:" (cadr (cps-invalid step))))
      (if (not rs) (cr--refuse! "no (sequent ASMS GOAL) field"))
      (if (not R) (cr--refuse! "no (hyps (sequent ...) ...) field"))
      (let ((u (cr--unmapped (cr-mints st) (cr-mintmap st) rs)))
        (if (pair? u) (cr--refuse! "the step's sequent mentions a mint not yet learned:" (car u))))
      (let* ((rsm  (cr--map (cr-mintmap st) rs))
             (node (cr--resolve-node st N rsm (cps-sequent-form step)))
             (bind! (lambda (P)            ; recorded hypothesis forms -> the nodes they matched
                      (for-each (lambda (h p) (hash-table-set! (cr-seqnode st) h p))
                                (cps-hyp-forms step) P))))
        (cond
         ;; 3. already justified by a matching inference: accepted without running
         ((and (pair? (sequent-node-in-arrows node))
               (cr--some (lambda (inf)
                           (let ((r (cr--match-hyps st R (inference-node-hypotheses inf) node)))
                             (and (not (string? r))
                                  (begin (set-cr-mintmap! st r)
                                         (bind! (inference-node-hypotheses inf))
                                         #t))))
                         (sequent-node-in-arrows node)))
          (cr--stat! st 1) node)
         ;; grounded by another inference: skipped and counted (design R2)
         ((sequent-node-grounded? node) (cr--stat! st 2) node)
         (#t
          (let* ((args (cr--convert-args st (caddr row) (cdr cmd)))
                 (dg   (cr-dg st))
                 (old  (dg-inference-nodes dg))
                 (res  (cr--guarded (lambda () (apply (cadddr row) node args)))))
            (if (not res) (cr--refuse! "the entry point declined (returned #f)"))
            (let ((new (let loop ((l (dg-inference-nodes dg)) (acc '()))
                         (if (or (null? l) (eq? l old)) acc (loop (cdr l) (cons (car l) acc))))))
              (if (null? new) (cr--refuse! "the entry point recorded no inference"))
              (if (not (eq? (inference-node-conclusion (car new)) node))
                  (cr--refuse! "the entry point recorded its inference at another node"))
              (let ((r (cr--match-hyps st R (append-map inference-node-hypotheses new) node)))
                (if (string? r) (cr--refuse! r))
                (set-cr-mintmap! st r)
                (bind! (append-map inference-node-hypotheses new))
                (cr--stat! st 0)
                node)))))))))

;;; -----------------------------------------------------------------------
;;; The page-level checks before step 1.
(define (cr--check-header! page)
  (if (not (and (pair? page) (eq? (car page) 'core-page) (pair? (cdr page)) (symbol? (cadr page))))
      (cr--refuse! "not a (core-page NAME ...) form"))
  (if (not (cp-statement page)) (cr--refuse! "no (statement ...) field"))
  (let ((h (cp-kernel-hash page)))
    (cond ((not (string? h)) (cr--refuse! "no (kernel-hash \"...\") field"))
          ((string=? h "*") 'hand-written)          ; a hand-written fixture: hash not checked
          ((not (string=? h (cert-kernel-hash)))
           (cr--refuse! (string-append "the page was written under kernel " h
                                       ", this image has kernel " (cert-kernel-hash))))))
  (if (not (cr--all symbol? (cp-mints page))) (cr--refuse! "a mint name is not a symbol")))

;;; The final check, as `qed' makes it: the root is grounded.
(define (cr--final-check! st)
  (if (not (sequent-node-grounded? (cr-root st)))
      (cr--refuse! (string-append "the root is not grounded: "
                                  (number->string (length (filter (lambda (n) (null? (sequent-node-in-arrows n)))
                                                                  (dg-ungrounded-nodes (cr-dg st)))))
                                  " open leaf/leaves"))))

;;; -----------------------------------------------------------------------
;;; (core-replay-page PAGE) -- the batch replay, isolated.
(define *core-replay-last-stats* #f)       ; (ran shared skipped) of the last batch replay
(define *core-replay-last-map* '())        ; its mint map
(define *core-replay-last-output* "")      ; what the entry points printed
(define *core-replay-kernel-refusals* 0)   ; checker refusals met inside replays, counted apart

(define (core-replay-page page0)
  (let* ((page (core-page-expand page0))
         (steps (if (and (pair? page) (list? page)) (cp-steps page) '()))
        (result #f))
    (set! *core-replay-last-output*
      (with-output-to-string
        (lambda ()
          (fluid-let ((*ps* #f)
                      (*proof-script* '()) (*proof-mints* '()) (*proof-hidden-citations* '())
                      (*fresh-mark-at-last-record* *fresh-mark-at-last-record*)
                      (*live-trace* '()) (*current-goal* #f) (*witness-aliases* '())
                      (*vnb-undo-stack* '())
                      (*fresh-counter* *fresh-counter*) (*fresh-log* *fresh-log*)
                      (*proof-used-defs* '()) (*pi-owed-nodes* '())
                      (*dg-journal* '())
                      (*dg-checked-count* *dg-checked-count*) (*dg-check-refusals* *dg-check-refusals*)
                      (*def-audit-total* *def-audit-total*) (*def-audit-uncert* *def-audit-uncert*)
                      (*def-audit-terms* *def-audit-terms*)
                      (*vnb-quiet* #t))
            (let* ((k 0) (cmd 'core-page) (refusals0 (length *dg-check-refusals*)) (st #f))
              (let ((msg (call-with-current-continuation
                          (lambda (esc)
                            (fluid-let ((*cr--refuse-k* esc))
                              (cr--check-header! page)
                              (let* ((w (cr--guarded (lambda () (make-wff (cp-statement page)))))
                                     (ps (start-proof w)))
                                (set! *ps* ps)
                                (set! st (cr--make-state page (proof-state-dg ps) (proof-state-root ps)))
                                (for-each (lambda (s)
                                            (set! k (+ k 1))
                                            (set! cmd (let ((c (cps-cmd s))) (if (pair? c) (car c) c)))
                                            (cr--run-step! st s k))
                                          steps)
                                (set! k (+ k 1)) (set! cmd 'qed)
                                (cr--final-check! st)
                                #f))))))
                (set! *core-replay-kernel-refusals*
                      (+ *core-replay-kernel-refusals* (- (length *dg-check-refusals*) refusals0)))
                (if st (begin (set! *core-replay-last-stats* (cr-stats st))
                              (set! *core-replay-last-map* (cr-mintmap st))))
                (set! result (if msg (list 'refused k cmd msg) (list 'core-replayed (length steps))))))))))
    result))

(define (core-replay-verdict-string v)
  (if (eq? (car v) 'core-replayed)
      (string-append "verdict: core-replayed " (number->string (cadr v)))
      (string-append "verdict: refused at step " (number->string (cadr v))
                     " (" (call-with-output-string (lambda (p) (write (caddr v) p))) "): "
                     (cadddr v))))

;;; -----------------------------------------------------------------------
;;; THE EMACS API.  Names fixed (the Emacs agent builds against them).

;;; (core-page-text 'NAME) -> the page, one step per line, each preceded by the
;;; line `goal K: TEXT' (the goal of the node the step works at, printed as the
;;; workspace prints a formula, with the page's mint names), then the verdict line.
(define (cr--goal-text s)
  (let ((rs (cps-sequent s)))
    (if (not rs)
        "(no sequent)"
        (let ((t (call-with-current-continuation
                  (lambda (k)
                    (with-exception-handler
                     (lambda (e) (k (call-with-output-string (lambda (p) (write (cadr rs) p)))))
                     (lambda () (expression->string (cadr rs))))))))
          (list->string (map (lambda (ch) (if (char=? ch #\newline) #\space ch)) (string->list t)))))))

(define (core-page-text name)
  (let ((page (core-page-read name)))
    (if (not page)
        (string-append "no core page for " (symbol->string name))
        (let ((v (core-replay-page page)))
          (call-with-output-string
           (lambda (port)
             (for-each (lambda (s)
                         (display "goal " port) (write (cps-k s) port) (display ": " port)
                         (display (cr--goal-text s) port) (newline port)
                         (display "step " port) (write (cps-k s) port) (display ": " port)
                         (write (cps-cmd s) port)
                         (display "    ; node " port) (write (cps-node s) port)
                         (newline port))
                       (cp-steps page))
             (display (core-replay-verdict-string v) port)))))))

;;; The WORKSPACE replay.  The page's statement is opened with `sp' in the workspace
;;; proof state; each `core-replay-next' runs one step on *ps* and pushes an undo mark
;;; (entry (core-step K)), so `core-replay-back' is the ordinary `backup-one'.  Nothing
;;; is recorded in *proof-script*: a qed after a core replay installs nothing the page
;;; audit could re-type, and should not be used.
(define *core-replay-session* #f)   ; #(name page steps-vector state index history ps)

(define (crs--get i) (vector-ref *core-replay-session* i))
(define (crs--set! i v) (vector-set! *core-replay-session* i v))

(define (core-replay-begin name)
  (let ((page (core-page-read name)))
    (cond
     ((not page) (vnb--print-warning (string-append "no core page for " (symbol->string name))) #f)
     (#t
      (sp (make-wff (cp-statement page)))
      (if (not *ps*) (error "core-replay-begin: the statement did not open" name))
      (let ((st (cr--make-state page (proof-state-dg *ps*) (proof-state-root *ps*)))
            (steps (list->vector (cp-steps page))))
        (set! *core-replay-session* (vector name page steps st 0 '() *ps*))
        (unless *vnb-quiet*
          (display ";; core replay of ") (display name) (display ": ")
          (display (vector-length steps)) (display " step(s); (core-replay-next) runs step 1") (newline))
        (vector-length steps))))))

(define (crs--live?)
  (and *core-replay-session* (eq? *ps* (crs--get 6))))

;;; Focus the node the NEXT step works at, when it is already known; else the first
;;; open leaf.
(define (crs--focus-next!)
  (let* ((steps (crs--get 2)) (i (crs--get 4)) (st (crs--get 3)))
    (let ((n (and (< i (vector-length steps))
                  (let* ((s (vector-ref steps i)) (rs (cps-sequent s)))
                    (or (let ((e (assv (cps-node s) (cr-nodemap st)))) (and e (cdr e)))
                        (and rs (null? (cr--unmapped (cr-mints st) (cr-mintmap st) rs))
                             (cr--find-node st (cr--map (cr-mintmap st) rs))))))))
      (if n (focus-on *ps* n) (focus-on-first-open *ps*)))))

(define (core-replay-next)
  (cond
   ((not (crs--live?))
    (vnb--print-warning "core-replay-next: no core replay in the workspace ((core-replay-begin 'NAME) first)")
    #f)
   ((>= (crs--get 4) (vector-length (crs--get 2)))
    (let ((v (call-with-current-continuation
              (lambda (esc)
                (fluid-let ((*cr--refuse-k* esc)) (cr--final-check! (crs--get 3)) #f)))))
      (display (core-replay-verdict-string
                (if v (list 'refused (+ 1 (vector-length (crs--get 2))) 'qed v)
                    (list 'core-replayed (vector-length (crs--get 2))))))
      (newline)
      'done))
   (#t
    (let* ((st (crs--get 3)) (i (crs--get 4)) (step (vector-ref (crs--get 2) i))
           (mark (vnb--take-mark (list 'core-step (+ i 1))))
           (snap (list (cr-nodemap st) (cr-mintmap st) (cr-stats st)))
           (msg (call-with-current-continuation
                 (lambda (esc)
                   (fluid-let ((*cr--refuse-k* esc))
                     (cr--run-step! st step (+ i 1))
                     #f)))))
      (if msg
          (begin
            (if mark (dg-rollback! (vnb-undo-mark-dg-mark mark)))
            (set-cr-nodemap! st (car snap)) (set-cr-mintmap! st (cadr snap)) (set-cr-stats! st (caddr snap))
            (hash-table-clear! (cr-seqnode st))     ; it may name nodes the rollback removed
            (vnb--print-warning (core-replay-verdict-string
                                 (list 'refused (+ i 1) (let ((c (cps-cmd step))) (if (pair? c) (car c) c)) msg)))
            (list 'refused (+ i 1) (cps-cmd step) msg))
          (begin
            (vnb--undo-push! mark)
            (crs--set! 5 (cons snap (crs--get 5)))
            (crs--set! 4 (+ i 1))
            (crs--focus-next!)
            (unless *vnb-quiet*
              (display ";; core step ") (display (+ i 1)) (display ": ") (write (cps-cmd step)) (newline))
            (show)
            (+ i 1)))))))

(define (core-replay-back)
  (cond
   ((not (crs--live?))
    (vnb--print-warning "core-replay-back: no core replay in the workspace") #f)
   ((null? (crs--get 5))
    (vnb--print-warning "core-replay-back: at step 0, nothing to back up") 0)
   ((not (and (pair? *vnb-undo-stack*)
              (equal? (vnb-undo-mark-entry (car *vnb-undo-stack*)) (list 'core-step (crs--get 4)))))
    (vnb--print-warning "core-replay-back: the last workspace step is not a core-replay step; use (undo)")
    (crs--get 4))
   (#t
    (let ((snap (car (crs--get 5))) (st (crs--get 3)))
      (backup-one)
      (set-cr-nodemap! st (car snap)) (set-cr-mintmap! st (cadr snap)) (set-cr-stats! st (caddr snap))
      (hash-table-clear! (cr-seqnode st))         ; it may name nodes the rollback removed
      (crs--set! 5 (cdr (crs--get 5)))
      (crs--set! 4 (- (crs--get 4) 1))
      ;; the state block, so the Focus workspace repaints as after any command
      (crs--focus-next!)
      (show)
      (crs--get 4)))))
