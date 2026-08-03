;;; audit.scm -- library hygiene diagnostics.
;;;
;;; (audit-unbounded) scans every installed theorem/axiom for the partial-
;;; equality hazard: an UNBOUNDED universal variable (one never constrained by
;;; an (IN v D) typing) that feeds a PARTIAL term, under a strict `=' in
;;; ASSERTION position.  Because VNB `=' is partial (t=t is the definedness
;;; predicate), such a statement quietly asserts `undefined = undefined' at
;;; off-domain arguments -- false in the intended model.
;;;
;;; Two hazard categories:
;;;   A  arithmetic partial ops      (+ * - / binplus bintimes binneg recip power abs magnitude)
;;;   B  function application / structure ops   (f(...) ; ((ADD s) ...) etc.)
;;;
;;; Predicate definitions are NOT flagged: the filter requires the CORE (after
;;; stripping universals and (IN v D) typing antecedents) to be a strict `=' or
;;; a conjunction containing one -- an `iff' core (is-metric) is excluded, since
;;; a predicate is total over its arguments.

(define *audit-arith-partial-heads*
  '(+ * - / binplus bintimes binneg recip power abs magnitude))

;;; Term heads that do NOT introduce partiality: logical/relational heads (never
;;; in term position, but listed defensively) and the total class constructors
;;; (UNION/INTERSECTION/... are total over classes -- theory.scm).
(define *audit-total-or-logical-heads*
  '(= == IFF IMPLIES AND OR NOT FORALL FORSOME IN SUBSET <= < > >= TRUTH FALSITY
    IS-SET UNION INTERSECTION COMPLEMENT COMPLEMENT-IN CARTESIAN LIST SET COMP
    ;; POWER, not POWERSET: the powerset constructor is POWER (theory.scm).  This
    ;; list said POWERSET, a name the theory has never had -- so a POWER term was
    ;; being treated as a partial function APPLICATION by audit-unbounded, and it
    ;; is the stale name that seeded the TOP-SPACE bug.  See unknown-head-audit.
    SEP BIG-UNION POWER PAIR))

(define (audit--occurs? v e)
  (if (pair? e) (any (lambda (x) (audit--occurs? v x)) e) (eq? e v)))

;;; Partiality category of compound term E by its head: 'A arithmetic, 'B
;;; application/structure op, or #f if E's head is total/logical.
(define (audit--partial-cat e)
  (and (pair? e)
       (let ((h (car e)))
         (cond ((memq h *audit-arith-partial-heads*) 'A)
               ((memq h *audit-total-or-logical-heads*) #f)
               ((pair? h)   'B)            ; ((ADD s) ..) structure operator
               ((symbol? h) 'B)            ; f(..) function application
               (else #f)))))

;;; The categories (subset of {A,B}) of partial terms within E that CONTAIN v.
(define (audit--cats-feeding v e)
  (let ((acc '()))
    (let walk ((e e))
      (when (pair? e)
        (let ((c (audit--partial-cat e)))
          (when (and c (audit--occurs? v e) (not (memq c acc)))
            (set! acc (cons c acc))))
        (for-each walk e)))
    acc))

;;; Every FORALL-bound variable anywhere in F.
(define (audit--forall-vars f)
  (cond ((not (pair? f)) '())
        ((eq? (car f) 'FORALL) (cons (cadr f) (audit--forall-vars (caddr f))))
        (else (append-map audit--forall-vars (cdr f)))))

;;; Every variable typed by an (IN v _) anywhere in F.
(define (audit--typed-vars f)
  (cond ((not (pair? f)) '())
        ((and (eq? (car f) 'IN) (symbol? (cadr f)))
         (cons (cadr f) (append-map audit--typed-vars (cdr f))))
        (else (append-map audit--typed-vars f))))

;;; An antecedent that only TYPES variables -- (IN v _) or an AND of such.
(define (audit--typing-antecedent? a)
  (and (pair? a)
       (or (and (eq? (car a) 'IN) (symbol? (cadr a)))
           (and (eq? (car a) 'AND) (every audit--typing-antecedent? (cdr a))))))

;;; Strip leading FORALLs and (IN v D)-typing implications to the matrix.
(define (audit--core f)
  (cond ((and (pair? f) (eq? (car f) 'FORALL)) (audit--core (caddr f)))
        ((and (pair? f) (eq? (car f) 'IMPLIES) (audit--typing-antecedent? (cadr f)))
         (audit--core (caddr f)))
        (else f)))

;;; Is CORE a strict `=' in assertion position (itself, or an AND conjunct)?
(define (audit--assertion-=? core)
  (and (pair? core)
       (or (eq? (car core) '=)
           (and (eq? (car core) 'AND) (any audit--assertion-=? (cdr core))))))

;;; Scan F: (cons A-culprit-vars B-culprit-vars) when the core is an assertion
;;; `=' and some unbounded var feeds a partial term; else #f.
(define (audit--scan f)
  (let ((core (audit--core f)))
    (and (audit--assertion-=? core)
         (let* ((fv  (audit--forall-vars f))
                (tv  (audit--typed-vars f))
                (unb (filter (lambda (v) (not (memq v tv))) fv))
                (av '()) (bv '()))
           (for-each
             (lambda (v)
               (let ((cats (audit--cats-feeding v core)))
                 (when (memq 'A cats) (set! av (cons v av)))
                 (when (memq 'B cats) (set! bv (cons v bv)))))
             unb)
           (and (or (pair? av) (pair? bv)) (cons (reverse av) (reverse bv)))))))

;;; A theorem name's "base" = strip the auto-companion suffixes -rev / -list.
(define (audit--base-name s)
  (let loop ((s s))
    (let ((n (string-length s)))
      (cond ((and (> n 4) (string=? (substring s (- n 4) n) "-rev")) (loop (substring s 0 (- n 4))))
            ((and (> n 5) (string=? (substring s (- n 5) n) "-list")) (loop (substring s 0 (- n 5))))
            (else s)))))

(define (audit-unbounded)
  (let ((names (sort (hash-table-keys *theorem-table*)
                     (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
        (a-names '()) (b-names '()) (bases (make-equal-hash-table)))
    (display ";; === unbounded-quantification audit (partial term under strict =) ===\n")
    (for-each
      (lambda (n)
        (let* ((f (lookup-theorem n)) (r (and f (audit--scan f))))
          (when r
            (hash-table-set! bases (audit--base-name (symbol->string n)) #t)
            (when (pair? (car r))
              (set! a-names (cons (list n (car r) f) a-names)))
            (when (pair? (cdr r))
              (set! b-names (cons (list n (cdr r) f) b-names))))))
      names)
    (define (dump label rows)
      (display ";; --- ") (display label) (display " (")
      (display (length rows)) (display ") ---\n")
      (for-each
        (lambda (row)
          (display ";;   ") (display (car row))
          (display "   unbounded: ") (display (cadr row)) (newline)
          (display ";;       ") (display (expression->string (caddr row))) (newline))
        (reverse rows)))
    (dump "A: arithmetic partial ops" a-names)
    (dump "B: function application / structure ops" b-names)
    (display ";; total: ")
    (display (+ (length a-names) (length b-names)))
    (display " flag(s) across ")
    (display (hash-table/count bases))
    (display " distinct base name(s) (collapsing -rev / -list companions)\n")
    (+ (length a-names) (length b-names))))

;;; -----------------------------------------------------------------------
;;; ACCESSOR-CALLSITE AUDIT -- the pin on a provisional design.
;;;
;;; An accessor's reduction is global and unconditional: (CARR s) -> (NTH 1 s)
;;; for EVERY s.  That is a choice we can reverse (route 2: make it conditional
;;; on IS-X(s), so a name may sit at a different slot in each structure), and the
;;; reversal is cheap ONLY while nothing depends on the reduction firing without
;;; a typing hypothesis.  Today exactly one procedure does: `slot' (interactive).
;;;
;;; The number stays one because this audit fails if any file fires an accessor
;;; macete BY NAME -- (mac 'carr), (mac-h 'opr), (macm 'mul) -- instead of going
;;; through `slot'.  Left unguarded, the coupling grows by ordinary use, one
;;; driver at a time, and the "reversible" claim rots without anyone noticing.
;;;
;;; Comments are stripped before scanning (everything from the first `;'), so the
;;; many prose mentions of "(mac 'mul)" -- the false rewrite that started all of
;;; this -- do not register.  A mention inside a STRING would, which is a false
;;; positive we accept: it is the safe direction.
;;; Plain character-level substring search.  NOT string-search-forward: its range
;;; rule on a start index is not what it looks like (it rejects starts that are
;;; comfortably inside the string), and a scanner that walks a line hits that
;;; edge constantly.  Returns the index of PAT in S at or after FROM, or #f.
(define (audit--index-of pat s from)
  (let ((plen (string-length pat))
        (slen (string-length s)))
    (let loop ((i from))
      (cond
        ((> (+ i plen) slen) #f)
        ((let match ((j 0))
           (cond ((= j plen) #t)
                 ((char=? (string-ref s (+ i j)) (string-ref pat j)) (match (+ j 1)))
                 (else #f)))
         i)
        (else (loop (+ i 1)))))))

(define (audit--strip-comment line)
  (let ((i (audit--index-of ";" line 0)))
    (if i (substring line 0 i) line)))

(define (audit--accessor-callsites-in file)
  (let ((path (string-append *prover-dir* file ".scm"))
        (hits '()))
    (if (not (file-exists? path))
        '()
        (call-with-input-file path
          (lambda (port)
            (let loop ((n 1))
              (let ((line (read-line port)))
                (if (eof-object? line)
                    (reverse hits)
                    (let ((code (audit--strip-comment line)))
                      (for-each
                        (lambda (tac)
                          (let* ((pat  (string-append "(" tac " '"))
                                 (plen (string-length pat))
                                 (clen (string-length code)))
                            (let scan ((from 0))
                              (let ((i (audit--index-of pat code from)))
                                (when i
                                  (let* ((start (+ i plen))
                                         (end   (let find ((j start))
                                                  (cond
                                                    ((>= j clen) j)
                                                    ((memv (string-ref code j)
                                                           '(#\) #\space #\tab)) j)
                                                    (else (find (+ j 1))))))
                                         (nm    (string->symbol
                                                  (string-downcase
                                                    (substring code start end)))))
                                    ;; Both doors are `slot's: the global (NTH k s)
                                    ;; reduction keyed by the accessor's name, and
                                    ;; the per-instance value macete ZZ-RING@MUL
                                    ;; that declare-instance! precomputed.  Firing
                                    ;; either by name is reaching past `slot'.
                                    (when (or (eq? (constant-head? nm) 'accessor)
                                              (instance-value-macete-name? nm))
                                      (set! hits (cons (list file n tac nm) hits)))
                                    (scan end)))))))
                        '("mac" "mac-h" "macm"))
                      (loop (+ n 1)))))))))))

;;; Every place that fires an accessor macete by name instead of using `slot'.
;;; Empty => the projection's unconditionality has exactly ONE dependant, and
;;; route 2 remains a change to one procedure.
(define (accessor-callsite-audit)
  (append-map audit--accessor-callsites-in
              (append *vnb-files* (list "test-suite"))))

;;; -----------------------------------------------------------------------
;;; UNKNOWN APPLIED HEADS -- the gate for "that name is not what it looks like".
;;;
;;; VNB's reader accepts (POWERSET x) exactly as happily as (POWER x): a head it
;;; does not know is read as a FREE FUNCTION VARIABLE applied to an argument, and
;;; a free function variable in a closed library axiom is a symbol with nothing
;;; attached to it -- no axioms, no definition, no meaning.  The formula is still
;;; well-formed, still prints, still renders in a card, and says NOTHING.
;;;
;;; TOP-SPACE was declared on 2026-07-13 with the slot type (POWERSET (POWER-
;;; SET PTS)).  The powerset constructor in this theory is POWER (theory.scm:
;;; power-set, power-set-membership).  So IS-TOP-SPACE read "opens(s) in
;;; powerset(powerset(pts(s)))" with `powerset' an uninterpreted symbol, the
;;; structure loaded, the card rendered, and the whole suite passed.  It is the
;;; case-fold disease one level out: a name that is not the name you think.
;;;
;;; So: every symbol APPLIED in an installed theorem must be known -- a kernel
;;; head, a registered operator (def-predicate/def-functoid/accessor/structure),
;;; or BOUND in the formula (a genuine function variable, (f x) under FORALL f).
;;; Anything else is a typo with axioms hanging off nothing.
;;;
;;; The allowlist below is the pre-existing baseline: real constants introduced
;;; by bare theory-add-axiom! that never got a register-operator! call.  They are
;;; a TO-TRIAGE list, not a design -- each should get a def-functoid / notation!
;;; and leave this list -- but they are known-good, and pinning them here is what
;;; makes a NEW unknown head fail loudly instead of joining the noise.

(define *audit-known-unregistered-heads*
  '(binplus bintimes binneg          ; the polymorphic binary numeric ops
    bijection delete-at splice restvar ; combinatorics + list surgery
    eplus                            ; extended-real addition
    <=_ord <_ord                     ; the ordinal order
    is-fun))                         ; the function predicate

(define *audit-kernel-heads*
  '(NOT AND OR IMPLIES IFF FORALL FORSOME = == IN SUBSET <= < > >= + - * / ^
    TRUTH FALSITY UNION INTERSECTION COMPLEMENT COMPLEMENT-IN CARTESIAN DIFFERENCE
    FUN SEP BIG-UNION BIG-INTERSECTION POWER LIST NTH MAKE-SET LENGTH CHOICE IOTA
    IF TUPLES COMP PAIR SINGLETON VNB-LAMBDA apply-functoid succ))

(define (audit--binder-head? h)
  (memq h '(FORALL FORSOME IOTA SEP BIG-UNION BIG-INTERSECTION COMP VNB-LAMBDA)))

;;; Every symbol applied in E that is free, not a kernel head, not a registered
;;; operator, and not allowlisted.
(define (formula-unknown-applied-heads e0)
  (let ((hits '()))
    (let scan ((e (if (wff? e0) (wff-formula e0) e0)) (bound '()))
      (when (pair? e)
        (if (audit--binder-head? (car e))
            (let ((bv (cadr e)))
              (let ((bound* (cond ((symbol? bv) (cons bv bound))
                                  ((pair? bv)   (append (filter symbol? (cdr bv)) bound))
                                  (else bound))))
                (for-each (lambda (x) (scan x bound*)) (cddr e))))
            (let ((h (car e)))
              (when (and (symbol? h)
                         (not (memq h bound))
                         (not (memq h *audit-kernel-heads*))
                         (not (memq h *audit-known-unregistered-heads*))
                         (not (operator-ref h))
                         (not (constant-head? h)))
                (if (not (memq h hits)) (set! hits (cons h hits))))
              (for-each (lambda (x) (scan x bound)) (cdr e))
              (if (pair? h) (scan h bound))))))
    (reverse hits)))

;;; ((theorem head ...) ...) -- empty means every applied head in the library is
;;; a head somebody declared.
(define (unknown-head-audit)
  (let ((bad '()))
    (for-each
      (lambda (name)
        (let* ((f    (hash-table-ref/default *theorem-table* name #f))
               (hits (and f (formula-unknown-applied-heads f))))
          (if (pair? hits) (set! bad (cons (cons name hits) bad)))))
      (hash-table-keys *theorem-table*))
    (sort bad (lambda (a b) (string<? (symbol->string (car a))
                                      (symbol->string (car b)))))))

;;; -----------------------------------------------------------------------
;;; connective-arity-audit -- every installed formula's AND / OR / IMPLIES /
;;; IFF is BINARY, and every quantifier binds exactly one variable.
;;;
;;; `make-wff' already rejects a flat `(AND a b c)' -- "make-wff: connective
;;; arity" -- but `theory-add-axiom!' and `support' install a raw S-expression
;;; WITHOUT validating it (theory.scm: the body is `install-theorem!' and
;;; nothing else).  So a malformed formula can sit in *theorem-table* looking
;;; perfectly healthy.
;;;
;;; That is not a cosmetic problem.  The kernel reads a connective with
;;; `binary-left' / `binary-right' (cadr / caddr), so the THIRD conjunct of a
;;; flat AND is silently dropped: `pi-direct-inference!' proves `(AND a b c)'
;;; from a and b alone, and `pi-antecedent-inference!' splits it into a and b.
;;; The formula the checker uses is then not the formula the author wrote, and
;;; nothing anywhere says so.
;;;
;;; `fun-domain-extensionality' (theory.scm) carried exactly this bug: its
;;; antecedent was a flat three-conjunct AND whose third conjunct was the
;;; agreement hypothesis "f and g agree on A".  Dropped, the axiom reads "any
;;; two functions with the same domain are equal".  Found 2026-07-28.
;;;
;;; This audit is a HARD gate in load.scm -- unlike the nudges, a hit here means
;;; the trusted base does not say what it appears to say.

(define *arity-2-connectives* '(AND OR IMPLIES IFF))
(define *arity-2-predicates*  '(= == IN <= SUBSET subset))

;;; ((head . arity) ...) for every malformed node in E.
(define (formula-bad-arities e0)
  (let ((bad '()))
    (let scan ((e (if (wff? e0) (wff-formula e0) e0)))
      (when (and (pair? e) (symbol? (car e)))
        (let ((h (car e)) (n (length e)))
          (cond
            ((and (memq h *arity-2-connectives*) (not (= n 3)))
             (set! bad (cons (cons h n) bad)))
            ((and (memq h *arity-2-predicates*) (not (= n 3)))
             (set! bad (cons (cons h n) bad)))
            ((and (memq h '(NOT)) (not (= n 2)))
             (set! bad (cons (cons h n) bad)))
            ((and (memq h '(FORALL FORSOME)) (not (= n 3)))
             (set! bad (cons (cons h n) bad)))))
        (for-each (lambda (x) (scan x)) (cdr e))))
    (reverse bad)))

;;; ((theorem (head . arity) ...) ...) -- empty is the good case.
(define (connective-arity-audit)
  (let ((bad '()))
    (for-each
      (lambda (name)
        (let* ((f    (hash-table-ref/default *theorem-table* name #f))
               (hits (and f (formula-bad-arities f))))
          (if (pair? hits) (set! bad (cons (cons name hits) bad)))))
      (hash-table-keys *theorem-table*))
    (sort bad (lambda (a b) (string<? (symbol->string (car a))
                                      (symbol->string (car b)))))))

;;; -----------------------------------------------------------------------
;;; free-variable-audit -- no installed formula should have a FREE VARIABLE.
;;;
;;; `support' and `theory-add-axiom!' install a raw S-expression with no
;;; validation (this is the same door connective-arity-audit watches).  A
;;; formula that forgot to bind one of its variables is not a schema: the
;;; kernel reads the free name literally, so the fact means whatever that name
;;; denotes AT THE POINT OF CITATION.  It therefore appears to work exactly
;;; when the citing proof happens to have chosen the same spelling for its own
;;; eigenvariable, and changes meaning silently when someone renames it.
;;;
;;; Found by this audit when it was written (2026-08-03): taylor-G-in-fun and
;;; taylor-H-in-fun left the Taylor DEGREE `n' free, alone among the taylor-*
;;; supports, and were cited by taylor-lagrange -- whose fourth eigenvariable
;;; is spelled `n'.  Both now bind it.  That is the case-fold disease one level
;;; down: not two spellings colliding, but a fact whose content depends on the
;;; caller's choice of names.
;;;
;;; WHAT IS NOT A HIT.  free-vars reports a bare class constant (NN, RR, SET)
;;; and an un-applied predicate name as free, because the constant registry
;;; keys on APPLIED heads.  Those are noise here, so the audit reports a free
;;; variable only when it is not a registered constant head and does not look
;;; like a class or predicate name.  The four n-ary decompose axioms
;;; (union-decompose, intersection-decompose and their -rev) legitimately carry
;;; the splice metavariables `e' and `or', and are whitelisted by name.
(define *free-var-audit-exempt*
  '(union-decompose union-decompose-rev
    intersection-decompose intersection-decompose-rev))

(define (audit--free-var-suspicious? v)
  (and (symbol? v)
       (not (constant-head? v))
       (let ((s (symbol->string v)))
         (and (<= (string-length s) 2)
              (not (memq v '(nn zz qq rr cc <= >= < > = ==)))))))

;;; ((theorem free-var ...) ...) -- empty is the good case.
(define (free-variable-audit)
  (let ((bad '()))
    (for-each
      (lambda (name)
        (unless (memq name *free-var-audit-exempt*)
          (let* ((f  (hash-table-ref/default *theorem-table* name #f))
                 (fv (and f (filter audit--free-var-suspicious? (free-vars f)))))
            (if (pair? fv) (set! bad (cons (cons name fv) bad))))))
      (hash-table-keys *theorem-table*))
    (sort bad (lambda (a b) (string<? (symbol->string (car a))
                                      (symbol->string (car b)))))))
