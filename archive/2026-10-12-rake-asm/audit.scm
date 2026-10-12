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
;;; (UNION/INTERSECTION/... are total over classes -- library.scm).
(define *audit-total-or-logical-heads*
  '(= == IFF IMPLIES AND OR NOT FORALL FORSOME IN SUBSET <= < > >= TRUTH FALSITY
    IS-SET UNION INTERSECTION COMPLEMENT COMPLEMENT-IN CARTESIAN LIST SET COMP
    ;; POWER, not POWERSET: the powerset constructor is POWER (library.scm).  This
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
;;; SET PTS)).  The powerset constructor in this theory is POWER (library.scm:
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
;;; by bare add-axiom! that never got a register-operator! call.  They are
;;; a TO-TRIAGE list, not a design -- each should get a def-functoid / notation!
;;; and leave this list -- but they are known-good, and pinning them here is what
;;; makes a NEW unknown head fail loudly instead of joining the noise.

(define *audit-known-unregistered-heads*
  '(binplus bintimes binneg          ; the polymorphic binary numeric ops
    bijection delete-at splice restvar ; combinatorics + list surgery
    eplus                            ; extended-real addition
    ord-le ord-lt                     ; the ordinal order
    is-fun))                         ; the function predicate

(define *audit-kernel-heads*
  '(NOT AND OR IMPLIES IFF FORALL FORSOME = == IN SUBSET <= < > >= + - * / ^
    TRUTH FALSITY UNION INTERSECTION COMPLEMENT COMPLEMENT-IN CARTESIAN DIFFERENCE
    FUN SEP BIG-UNION POWER LIST NTH MAKE-SET LENGTH CHOICE IOTA
    IF TUPLES COMP PAIR SINGLETON VNB-LAMBDA apply-functoid succ))

;;; BIG-INTERSECTION was in both lists until 2026-09-20 and was never a kernel
;;; head: no rule, no macete, no membership law, and `wff.scm' did not know it
;;; as a binder.  Listing it here made the head-registry sweep accept the two
;;; formulas that used it (HAS-FIP, compact-iff-fip) although nothing could
;;; interpret them, and listing it below made this audit skip its BINDER
;;; position -- which held the registered accessor CARR.  The object is now the
;;; defined functoid INTERSECTION-OF (structure-library/intersection-of.scm),
;;; which needs no entry in either list; the symbol occurs nowhere in the tree.
(define (audit--binder-head? h)
  (memq h '(FORALL FORSOME IOTA SEP BIG-UNION COMP VNB-LAMBDA)))

;; The head-registry sweeps skip a binder's VARIABLE position through this
;; predicate; a binder missing from it would have its bound variable read as an
;; applied head.  Watched by binder-walker-audit (expressions.scm:
;; declare-binder-walker!).
(declare-binder-walker! 'audit--binder-head?
                        '(FORALL FORSOME IOTA COMP SEP BIG-UNION VNB-LAMBDA))

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
;;; arity" -- but `add-axiom!' and `support' install a raw S-expression
;;; WITHOUT validating it (library.scm: the body is `install-theorem!' and
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
;;; `fun-domain-extensionality' (library.scm) carried exactly this bug: its
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
;;; `support' and `add-axiom!' install a raw S-expression with no
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

;;; -----------------------------------------------------------------------
;;; head-registry-sweep -- every applied head in the library, checked against
;;; the ONE table the walkers consult.
;;;
;;; `unknown-head-audit' above answers a DOCUMENTATION question: did somebody
;;; declare this head?  It accepts a head that is in `*operators*' (operators.scm)
;;; or in `*audit-known-unregistered-heads*'.  Neither buys anything at proof
;;; time: `free-vars' and `subst-free' (expressions.scm) consult
;;; `*constant-registry*' and nothing else, and an unregistered symbol at the
;;; head of a compound is treated as an applied FUNCTION VARIABLE -- free, and
;;; substitutable.  `register-operator!' does NOT call `register-constant!', so
;;; the two tables drift apart silently.
;;;
;;; What that costs, twice on 2026-08-04 alone: `BIJECTION' is registered as an
;;; operator but not as a constant, so
;;;     (free-vars '(IN phi (BIJECTION X Y)))  =>  (phi bijection x y)
;;; -- `bijection' reported as a free variable of `fin-enum-is-bijection',
;;; `well-ordering-principle', `delete-at-is-bijection' and the `inverse-bij'
;;; family; `/' was the same omission found the same morning.  Both were invisible
;;; to `unknown-head-audit' (the first is allowlisted, the second is in its kernel
;;; list) which reported 0.
;;;
;;; So this sweep asks the walkers' question and only theirs: is the head in
;;; `*constant-registry*'?  A head BOUND by an enclosing binder is a legitimate
;;; function variable and is skipped; everything else that is unregistered is a
;;; constant the walkers cannot see.
;;;
;;; Returns ((head n-formulas (theorem ...)) ...), most-cited first -- data, so a
;;; caller can rank or filter; `report-head-registry' prints it.

;;; The heads every walker in expressions.scm handles with an EXPLICIT case
;;; branch -- so the registry is never consulted for them and their absence from
;;; it costs nothing.  Keep this list in step with the case branches of
;;; free-vars / subst-free / alpha-equiv-under?; everything else those walkers
;;; name (LIST, NTH, SEP, POWER, ...) is in *wff-term-form-heads* and therefore
;;; registered anyway.  NOTE what is NOT here: <= and SUBSET are in
;;; *wff-only-heads* but in no walker's case list, which is exactly how they
;;; leaked.
(define *audit-structural-heads*
  '(NOT AND OR IMPLIES IFF FORALL FORSOME = == IN))

;;; Every applied SYMBOL head in E that is not bound by an enclosing binder and
;;; not a registered constant head.  Walks functoid records too.
(define (formula-unregistered-applied-heads e0)
  (let ((hits '()))
    (let scan ((e (if (wff? e0) (wff-formula e0) e0)) (bound '()))
      (cond
        ((functoid? e)
         (let ((bvars (map car (functoid-bindings e))))
           (for-each (lambda (b) (scan (cdr b) bound)) (functoid-bindings e))
           (scan (functoid-body e) (append bvars bound))))
        ((pair? e)
         (if (audit--binder-head? (car e))
             (let* ((bv     (cadr e))
                    (bound* (cond ((symbol? bv) (cons bv bound))
                                  ((pair? bv)   (append (filter symbol? (cdr bv)) bound))
                                  (else bound))))
               (for-each (lambda (x) (scan x bound*)) (cddr e)))
             (let ((h (car e)))
               (when (and (symbol? h)
                          (not (memq h bound))
                          (not (memq h *audit-structural-heads*))
                          (not (constant-head? h)))
                 (if (not (memq h hits)) (set! hits (cons h hits))))
               (if (pair? h) (scan h bound))
               (for-each (lambda (x) (scan x bound)) (cdr e)))))))
    (reverse hits)))

;;; ((head count (theorem ...)) ...) -- empty means every applied head in every
;;; installed formula is one the walkers can see.
(define (head-registry-sweep)
  (let ((tbl (make-equal-hash-table)))
    (for-each
      (lambda (name)
        (let ((f (hash-table-ref/default *theorem-table* name #f)))
          (if f
              (for-each (lambda (h)
                          (hash-table-set! tbl h
                            (cons name (hash-table-ref/default tbl h '()))))
                        (formula-unregistered-applied-heads f)))))
      (hash-table-keys *theorem-table*))
    (sort (map (lambda (h)
                 (let ((names (sort (hash-table-ref/default tbl h '())
                                    (lambda (a b) (string<? (symbol->string a)
                                                            (symbol->string b))))))
                   (list h (length names) names)))
               (hash-table-keys tbl))
          (lambda (a b)
            (if (= (cadr a) (cadr b))
                (string<? (symbol->string (car a)) (symbol->string (car b)))
                (> (cadr a) (cadr b)))))))

;;; Printer for the load-time report.  N caps the theorem names shown per head.
(define (report-head-registry #!optional n)
  (let ((n  (if (default-object? n) 4 n))
        (sw (head-registry-sweep)))
    (if (null? sw)
        (display ";; head-registry-sweep: ok (every applied head is a registered constant)\n")
        (begin
          (display "\n;; head-registry-sweep: ") (display (length sw))
          (display " applied head(s) NOT in the constant registry --\n")
          (display ";; free-vars / subst-free read each as an applied function VARIABLE:\n")
          (display ";; free, substitutable, and alpha-renamable.  Register the constant\n")
          (display ";; ones (*wff-term-form-heads* in wff.scm, or the def-* that should\n")
          (display ";; have introduced them):\n")
          (for-each
            (lambda (e)
              (display ";;   ") (display (cadr e))
              (display (if (< (cadr e) 10) "   " "  "))
              (display (car e)) (display "   e.g. ")
              (let loop ((ns (caddr e)) (i 0))
                (when (and (pair? ns) (< i n))
                  (display (car ns))
                  (if (and (pair? (cdr ns)) (< (+ i 1) n)) (display " "))
                  (loop (cdr ns) (+ i 1))))
              (if (> (cadr e) n) (display " ..."))
              (newline))
            sw)))))

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

;;; -----------------------------------------------------------------------
;;; SETHOOD AUDIT (2026-08-05) -- the axiom routes around pi-lambda-type!'s
;;; (IN A SET) obligation.
;;;
;;; WHY IT EXISTS.  The 2026-08-02 soundness repair made the KERNEL refuse to
;;; certify a VNB-LAMBDA on a proper-class domain into FUN.  It did not, and
;;; could not, touch the AXIOMS: `bijection-identity' was stated
;;; `forall X. (VNB-LAMBDA x_ X x_) in BIJECTION(X, X)' with no guard, so at
;;; X := ORD it asserted -- through bijection-in-fun -- exactly the membership
;;; the rule refuses.  Repairing a rule does not repair the assertions that
;;; claim what the rule declines to derive.  This audit enumerates that class of
;;; defect instead of waiting for the next one.
;;;
;;; WHAT IT FLAGS: a universally quantified CLASS parameter, with no (IN X SET)
;;; guard, standing in a SETHOOD-CARRYING position of a function membership the
;;; formula ASSERTS.
;;;
;;;   positions      FUN(A,B) / INJECTION(A,B): the DOMAIN A only -- a function
;;;                  with a proper-class domain is a proper class and can be a
;;;                  member of nothing, while FUN(a, C) for a proper class C is
;;;                  a perfectly good class of set functions.
;;;                  BIJECTION / SURJECTION: BOTH, the codomain being the image
;;;                  of a set.
;;;   asserted       antecedent occurrences are skipped: a formula that merely
;;;                  says "if f is in FUN(A,B) then ..." is vacuous, not false,
;;;                  when A is a proper class.  So are IFF characterisations,
;;;                  where each direction has the membership as a hypothesis,
;;;                  and formulas whose guards already mention the variable in
;;;                  a class position (they PROPAGATE a membership handed to
;;;                  them rather than manufacture one).
;;;   bare variable  a compound class term -- (PTS m), (CARR r) -- carries its
;;;                  own typing and is not flagged.
;;;
;;; WHAT IT DOES NOT CHECK, so the gap is visible: IS-FUN / POWER / CARTESIAN
;;; positions, class parameters bound by FORSOME, and constant classes written
;;; literally into an axiom.
;;;
;;; WARN-ONLY.  The two standing entries are exempt below, with the argument.

(define *sethood-audit-exempt*
  ;; res-codomain / res-typing (library.scm): RES(f,b) in FUN(b,...) with b only
  ;; SUBSET a.  Safe by vacuity of the antecedent -- (IN f (FUN a c)) can hold
  ;; only for a set a (a function with a proper-class domain is a proper class,
  ;; hence a member of nothing), and then b subset a is a set by separation.
  ;; The library cannot DERIVE that step (it has no unguarded "the domain of a
  ;; set function is a set"; dom-of-fun is itself guarded), which is why the
  ;; audit cannot see it and the exemption is recorded here instead.
  '(res-codomain res-typing))

(define *sethood-classes* '(FUN BIJECTION INJECTION SURJECTION))

(define (audit--sethood-args app)
  (case (car app)
    ((FUN INJECTION) (list (cadr app)))
    ((BIJECTION SURJECTION) (cdr app))
    (else '())))

(define (audit--flatten-and f)
  (if (and (pair? f) (eq? (car f) 'AND) (= (length f) 3))
      (append (audit--flatten-and (cadr f)) (audit--flatten-and (caddr f)))
      (list f)))

(define (audit--split-guards f vars guards)
  (cond ((and (pair? f) (eq? (car f) 'FORALL) (= (length f) 3))
         (audit--split-guards (caddr f) (cons (cadr f) vars) guards))
        ((and (pair? f) (eq? (car f) 'IMPLIES) (= (length f) 3))
         (audit--split-guards (caddr f) vars
                              (append (audit--flatten-and (cadr f)) guards)))
        (else (list vars guards f))))

(define (audit--class-apps f)
  (cond ((not (pair? f)) '())
        ((memq (car f) *sethood-classes*)
         (cons f (apply append (map audit--class-apps (cdr f)))))
        (else (apply append (map audit--class-apps f)))))

(define (audit--membership-apps f)
  (cond ((not (pair? f)) '())
        ((and (eq? (car f) 'IN) (= (length f) 3)
              (pair? (caddr f)) (memq (car (caddr f)) *sethood-classes*))
         (cons (caddr f) (apply append (map audit--membership-apps (cdr f)))))
        (else (apply append (map audit--membership-apps f)))))

;;; ((theorem var class-application) ...) -- empty is the good case.
(define (sethood-audit)
  (let ((bad '()))
    (for-each
      (lambda (name)
        ;; A PROVEN statement is not examined (2026-09-20): it went through the
        ;; kernel, where `lam-t' posts the (IN A SET) obligation this audit stands
        ;; in for, so it cannot assert a function over a proper class.  The audit
        ;; is about what is ASSERTED (restrict-in-fun, diff-on-in-fun and
        ;; holomorphic-on-in-fun, all proven, were being listed).
        (unless (or (memq name *sethood-audit-exempt*)
                    (memq (provenance-of name) '(proven certified)))
          (let ((f (hash-table-ref/default *theorem-table* name #f)))
            (if f
                (let* ((parts  (audit--split-guards f '() '()))
                       (vars   (car parts))
                       (guards (cadr parts))
                       (conseq (caddr parts))
                       (apps   (if (and (pair? conseq) (eq? (car conseq) 'IFF))
                                   '()
                                   (audit--membership-apps conseq))))
                  (for-each
                    (lambda (app)
                      (for-each
                        (lambda (a)
                          (if (and (symbol? a)
                                   (memq a vars)
                                   (not (member (list 'IN a 'SET) guards))
                                   (not (there-exists? guards
                                          (lambda (g)
                                            (there-exists? (audit--class-apps g)
                                              (lambda (ap) (memq a (cdr ap))))))))
                              (set! bad (cons (list name a app) bad))))
                        (audit--sethood-args app)))
                    apps))))))
      (hash-table-keys *theorem-table*))
    (sort bad (lambda (a b) (string<? (symbol->string (car a))
                                      (symbol->string (car b)))))))

;;; -----------------------------------------------------------------------
;;; binder-walker-audit -- every walker agrees with *binder-shapes*
;;;
;;; Four separate traversals have to know which heads bind a variable and over
;;; what: `free-vars', `subst-free', `alpha-equiv-under?' and `formula-hash'
;;; (plus `match-expr', `rewrite-expr' and `replace-term', which are the same
;;; knowledge again).  Until 2026-08-15 each knew it privately, and `COMP' --
;;; the set-comprehension binder, on the surface since the beginning -- was
;;; missing from ALL of them: free-vars called its bound variable free,
;;; subst-free rewrote it and captured into it, alpha-equiv? said two
;;; alpha-variants differed.  The defect was invisible because no INSTALLED
;;; formula in the tree contains a COMP; only a user who typed `{x | p}' could
;;; reach it.
;;;
;;; *binder-shapes* (expressions.scm) is now the one declaration.  This audit
;;; builds a throwaway formula per head and asks each walker what it thinks,
;;; so a head that is declared there and forgotten in a traversal is named at
;;; the next load rather than found by a user months later.
;;;
;;; FATAL, on the connective-arity-audit precedent: a walker that does not know
;;; a binder binds gives WRONG ANSWERS silently -- a captured substitution is a
;;; different theorem, not a failure -- and there is no safe way to carry one.
(define (binder-walker-audit)
  (let ((bad '()))
    (define (note! head why) (set! bad (cons (cons head why) bad)))
    (for-each
     (lambda (entry)
       (let* ((head  (car entry))
              (shape (cdr entry))
              (body  (list 'FUBA 'bv_ 'gv_))
              (body2 (list 'FUBA 'ww_ 'gv_))
              (build (lambda (v dom bd)
                       (case shape
                         ((simple) (list head v bd))
                         ((domain) (list head v dom bd))
                         ((lambda) (list head v dom bd))
                         (else #f))))
              (e  (build 'bv_ 'guba_ body))
              (e2 (build 'ww_ 'guba_ body2)))
         (if (not e)
             (note! head "unknown shape in *binder-shapes*")
             (begin
               (let ((fv (free-vars e)))
                 (if (memq 'bv_ fv)
                     (note! head "free-vars calls the bound variable free"))
                 (if (not (memq 'gv_ fv))
                     (note! head "free-vars loses a genuinely free variable")))
               (if (not (equal? (subst-free 'bv_ 'zz_ e) e))
                   (note! head "subst-free rewrites the bound variable"))
               (if (not (memq 'bv_ (free-vars (subst-free 'gv_ (list 'f_ 'bv_) e))))
                   (note! head "subst-free captures into the binder"))
               (if (not (alpha-equiv? e e2))
                   (note! head "alpha-equiv? does not see the binder"))
               ;; Reported only when the two DIRECTIONS disagree; a head the
               ;; walker misses answers #f both ways and is the line above.
               (if (not (eq? (alpha-equiv? e e2) (alpha-equiv? e2 e)))
                   (note! head "alpha-equiv? is not symmetric here"))
               (if (not (= (formula-hash e) (formula-hash e2)))
                   (note! head "formula-hash is not alpha-invariant here"))
               (if (not (equal? (formula-canon e) (formula-canon e2)))
                   (note! head "formula-canon is not alpha-invariant here"))
               ;; The DOMAIN of a domain/lambda binder is outside the binder's
               ;; scope, so an occurrence of the bound name there is FREE.
               (if (memq shape '(domain lambda))
                   (if (not (memq 'bv_ (free-vars (build 'bv_ 'bv_ body))))
                       (note! head "the binder wrongly scopes over its own domain")))))))
     *binder-shapes*)
    (append (reverse bad) (binder-walker-registration-audit))))

;;; -----------------------------------------------------------------------
;;; binder-walker-registration-audit -- the walkers that cannot be tested
;;;
;;; The four traversals above can be TESTED: build a formula, ask them what
;;; binds.  A rewriter, a validator, a rule checker and a beta reducer cannot be
;;; interrogated that way, and those are exactly where the two holes of
;;; 2026-09-20 were (BIG-UNION missing from `rewrite-subexpressions'; every
;;; shadowing binder missing from `reduce-lambda-in-expr/scope').  What is
;;; available for them is a DECLARATION beside the code -- the list of heads
;;; that walker handles, written where its case is, through
;;; `declare-binder-walker!' (expressions.scm) -- and this audit, which fails
;;; when *binder-shapes* declares a head a walker's list does not have.
;;;
;;; It does not prove a walker handles what it claims; it makes ADDING A BINDER
;;; loud.  A new head in *binder-shapes* fails the load at every walker that has
;;; not been told, by name, instead of being discovered months later by a user
;;; -- which is the history of COMP, and of BIG-UNION twice over.  A walker that
;;; declares `from-binder-shapes' reads the table itself and is exempt: it has
;;; no second list to forget.  EXTRA heads are never an error (a walker may know
;;; a functoid record or LAMBDOID, which this layer gives no shape).
(define (binder-walker-registration-audit)
  (let ((heads (map car *binder-shapes*)))
    (let loop ((ws *binder-walkers*) (bad '()))
      (cond
        ((null? ws) (reverse bad))
        ((not (pair? (cdar ws))) (loop (cdr ws) bad))   ; 'from-binder-shapes
        (else
         (let ((missing (filter (lambda (h) (not (memq h (cdar ws)))) heads)))
           (loop (cdr ws)
                 (if (null? missing)
                     bad
                     (cons (cons (caar ws)
                                 (string-append
                                  "declares no case for "
                                  (audit--join-names missing)
                                  " -- *binder-shapes* declares it a binder"))
                           bad)))))))))

(define (audit--join-names syms)
  (let loop ((ss (map symbol->string syms)) (acc ""))
    (cond ((null? ss) acc)
          ((string=? acc "") (loop (cdr ss) (car ss)))
          (else (loop (cdr ss) (string-append acc ", " (car ss)))))))

;;; -----------------------------------------------------------------------
;;; duplicate-define-audit -- one file, one definition per name
;;;
;;; A second `(define (f ...))' for a name the same file already defines is
;;; always a bug, and it is INVISIBLE to every gate here.  `clobber-guard'
;;; watches for a procedure rebound to a NON-procedure, so a
;;; procedure-over-procedure redefinition sails past it -- CLAUDE.md records
;;; that exact escape once already (`what-now--show-forward' silently redefined
;;; an existing lane of that name and the panel died with an arity error), and
;;; it happened again on 2026-08-21: a second `dk-focus-goal!' appended to
;;; driver-kit.scm shadowed the real one at :805 and broke
;;; theorem-library/nn-pairing.scm, which had been using it for months.
;;;
;;; It uses the READER, so a name inside a quote or a string is not a
;;; definition -- which a line scan cannot tell.  Returns ((file name count)
;;; ...); empty is the good case.  NOT wired into the load: it reads every file,
;;; which a load should not pay for.  The suite runs it.

(define (duplicate--defined-names path)
  (let ((acc '()))
    (call-with-input-file path
      (lambda (port)
        (let loop ()
          (let ((form (read port)))
            (if (not (eof-object? form))
                (begin
                  (if (and (pair? form) (eq? (car form) 'define) (pair? (cdr form)))
                      (let ((target (cadr form)))
                        (set! acc (cons (if (pair? target) (car target) target) acc))))
                  (loop)))))))
    (reverse acc)))

(define *duplicate-define-files*
  '("driver-kit.scm" "suggest.scm" "interactive.scm" "macetes.scm"
    "expressions.scm" "wff.scm" "sequents.scm" "audit.scm" "preamble.scm"
    "ineq-supply.scm" "contra.scm" "prop.scm" "deduction-graphs.scm"
    "primitive-inferences.scm" "minimize.scm" "tactics-help.scm"))

;;; The names appearing more than once in NAMES, as ((name count) ...).
;;; Factored out so the suite can control the DETECTION without writing a file
;;; with a deliberate duplicate in it.
(define (duplicate--repeats names)
  (let ((seen (make-strong-eqv-hash-table)) (out '()))
    (for-each (lambda (n)
                (hash-table-set! seen n (+ 1 (hash-table-ref/default seen n 0))))
              names)
    (hash-table-walk seen
      (lambda (n c) (if (> c 1) (set! out (cons (list n c) out)))))
    (reverse out)))

(define (duplicate-define-audit)
  (let ((bad '()))
    (for-each
     (lambda (f)
       (for-each (lambda (r) (set! bad (cons (cons f r) bad)))
                 (duplicate--repeats
                  (duplicate--defined-names
                   ;; `*prover-dir*' (load.scm), NOT a literal: the tree is read
                   ;; wherever it was loaded from.  A hard-coded /home/ubuntu
                   ;; makes this gate fail silently on any other machine or
                   ;; account -- found 2026-09-05 when the user ran on sanblas.
                   (string-append *prover-dir* f)))))
     *duplicate-define-files*)
    (reverse bad)))


;;; -----------------------------------------------------------------------
;;; structure-satisfiability-audit -- does a structure predicate have a MODEL?
;;;
;;; The five install gates (connective-arity-audit, free-variable-audit,
;;; head-registry-sweep, install-grading, sethood-audit) all grade a formula's
;;; SHAPE.  None of them asks whether the formula can be satisfied, and on
;;; 2026-08-23 that was found to cost two structures.
;;;
;;; `build-is-axiom' (structures.scm) puts (= (LENGTH s) n) at the head of every
;;; shape structure's defining IFF: a tuple of the wrong length is not of that
;;; shape.  That conjunct is therefore a LENGTH PIN, and a declaration may
;;; acquire a second pin on the same term without saying so, by three doors:
;;;
;;;   * a (substructure SLOT TYPE) clause, whose conjunct (IS-TYPE (SLOT s))
;;;     pins length(SLOT s) to TYPE's arity;
;;;   * a (law "is-other(slot(s))") clause -- or, for a (same-shape-as PARENT)
;;;     refinement, a law inherited from the parent -- pinning the same term to
;;;     a DIFFERENT structure's arity;
;;;   * a law pinning a slot to a CLOSED tuple whose length a declaration
;;;     already fixes: a LIST literal, a declare-instance! name, or a
;;;     def-functor view (whose target shape gives the arity).
;;;
;;; Two pins with different numbers make IS-X unsatisfiable, and a theorem whose
;;; hypothesis is unsatisfiable is VACUOUSLY true: it proves, and it says
;;; nothing.  Both known cases had exactly this form -- NORMED-VECTOR-SPACE,
;;; whose SCAL slot was a RING by substructure (6) and the 7-tuple
;;; RR-NORMED-FIELD by law, and VECTOR-SPACE, whose SCAL slot is a RING through
;;; MODULE (6) and a FIELD (8) by law.  scratchpad/sat-audit-control.scm
;;; declares a decoy of each form, plus the repaired form, and checks that this
;;; reports two and not three: a gate that passes everything reads exactly like
;;; a clean library.
;;;
;;; The check is SYNTACTIC and needs no proof search: unfold the installed
;;; defining IFF by substitution, recursing through every nested structure
;;; predicate, and collect the pins.  It DECIDES this class of defect; it says
;;; nothing about any other reason a predicate might be empty.  Two known blind
;;; spots, both deliberate: a pin buried under a quantifier is not seen (the
;;; conjunct walk does not descend into a FORSOME, which is where
;;; METRIZABLE-TOP-SPACE's `s == LIST(...)' law lives -- consistent, checked by
;;; hand), and only `declare-structure' predicates are scanned, so a
;;; `def-predicate' that conjoins one (IS-FINITE-DIMENSIONAL = IS-VECTOR-SPACE
;;; and IS-NOETHERIAN) inherits the defect without being named here.
;;;
;;; WARN-ONLY.  A clash is a mathematical defect in a declaration, and the
;;; repair -- which structure the slot is supposed to hold -- is a decision, not
;;; a mechanical fix.

;;; The defining IFF of IS-NAME, as (INSTANCE-VAR . BODY), under either naming
;;; convention: def-structure names the axiom IS-NAME, def-substructure names it
;;; is-name-def.
(define (structure--def-body name)
  (let* ((is-nm (symbol-append 'IS- name))
         (raw   (or (hash-table-ref/default *theorem-table* is-nm #f)
                    (hash-table-ref/default *theorem-table*
                                            (symbol-append is-nm '-def) #f)))
         (f     (and raw (if (wff? raw) (wff-formula raw) raw))))
    (and (pair? f) (eq? (car f) 'FORALL)
         (let ((v (cadr f)) (b (caddr f)))
           (and (pair? b) (eq? (car b) 'IFF) (cons v (caddr b)))))))

;;; NAME, if SYM is IS-NAME for a declared structure; else #f.
(define (structure--of-is-predicate sym)
  (and (symbol? sym)
       (let ((s (symbol->string sym)))
         (and (> (string-length s) 3)
              (string=? (substring s 0 3) "is-")
              (let ((n (string->symbol (substring s 3 (string-length s)))))
                (and (structure-declaration n) n))))))

(define (structure--conjuncts f)
  (if (and (pair? f) (eq? (car f) 'AND))
      (append (structure--conjuncts (cadr f)) (structure--conjuncts (caddr f)))
      (list f)))

;;; The length of a CLOSED tuple term, when a declaration says what it is:
;;;   (LIST a b ...)                  -- the components are right there;
;;;   a name declared by declare-instance!  -- the length of its tuple;
;;;   (VIEW arg) for a def-functor VIEW     -- the arity of its target shape.
;;; #f when nothing in the tree pins it.  This is the half of the check that
;;; catches a slot pinned to a NAMED INSTANCE of the wrong arity, which is the
;;; form the NORMED-VECTOR-SPACE defect took (SCAL a RING by substructure, and
;;; the 7-tuple RR-NORMED-FIELD by law).
(define (structure--closed-term-length t)
  (cond ((and (pair? t) (eq? (car t) 'LIST)) (length (cdr t)))
        ((symbol? t)
         (let ((tup (instance-tuple t))) (and tup (length tup))))
        ((and (pair? t) (symbol? (car t)) (lookup-view-as (car t)))
         (let ((accs (structure-accessor-names
                      (view-as-target-struct (lookup-view-as (car t))))))
           (and accs (length accs))))
        (else #f)))

;;; ((TERM LENGTH REASON) ...) -- every length pin IS-NAME(TERM) forces, with a
;;; printable reason.  DEPTH bounds the recursion through nested structure
;;; predicates (no declaration nests 12 deep).
(define (structure-length-pins name term #!optional depth0)
  (let ((depth (if (default-object? depth0) 12 depth0)))
    (if (<= depth 0)
        '()
        (let ((d (structure--def-body name)))
          (if (not d)
              '()
              (append-map
               (lambda (c)
                 (cond
                   ;; the shape conjunct build-is-axiom emits: (= (LENGTH t) n)
                   ((and (pair? c) (memq (car c) '(= ==))
                         (pair? (cadr c)) (eq? (car (cadr c)) 'LENGTH)
                         (number? (caddr c)))
                    (list (list (cadr (cadr c)) (caddr c)
                                (string-append "is-" (symbol->string name)))))
                   ;; a slot typed by another structure predicate
                   ((and (pair? c) (= (length c) 2)
                         (structure--of-is-predicate (car c)))
                    (structure-length-pins (structure--of-is-predicate (car c))
                                           (cadr c) (- depth 1)))
                   ;; a law pinning a slot to a closed tuple of known length
                   ((and (pair? c) (memq (car c) '(= ==))
                         (structure--closed-term-length (caddr c)))
                    (list (list (cadr c) (structure--closed-term-length (caddr c))
                                (string-append "the law pinning it to "
                                               (expression->string (caddr c))))))
                   (else '())))
               (structure--conjuncts
                (subst-free (car d) term (cdr d)))))))))

;;; ((STRUCT TERM (k1 . REASON1) (k2 . REASON2)) ...) -- every declared
;;; structure whose IS-X pins one term's length to two different numbers.
;;; Empty means no structure predicate in the tree is unsatisfiable this way.
(define (structure-satisfiability-audit)
  (let ((out '()))
    (for-each
     (lambda (nm)
       (let ((pins (structure-length-pins nm 's)))
         (let loop ((ps pins))
           (if (pair? ps)
               (let ((other (let scan ((l (cdr ps)))
                              (cond ((null? l) #f)
                                    ((and (equal? (caar l) (caar ps))
                                          (not (= (cadr (car l)) (cadr (car ps)))))
                                     (car l))
                                    (else (scan (cdr l)))))))
                 (if (and other
                          (not (there-exists? out
                                 (lambda (e) (and (eq? (car e) nm)
                                                  (equal? (cadr e) (caar ps)))))))
                     (set! out (cons (list nm (caar ps)
                                           (cons (cadr (car ps)) (caddr (car ps)))
                                           (cons (cadr other) (caddr other)))
                                     out)))
                 (loop (cdr ps)))))))
     (sort (hash-table-keys *structure-decl-table*)
           (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
    (reverse out)))

;;; -----------------------------------------------------------------------
;;; statement-satisfiability-audit -- the SAME question one level up: can a
;;; theorem's HYPOTHESIS be met?
;;;
;;; `structure-satisfiability-audit' above scans one DECLARATION at a time, and
;;; that is a structural blind spot, not an omission: a clash can be assembled
;;; out of two predicates that are individually satisfiable, by a THEOREM that
;;; conjoins them on the same term.  It cost five results, found by eye on
;;; 2026-08-23 and invisible to the gate written that morning:
;;;
;;;     IS-NORMED-VECTOR-SPACE(m)   pins length(m) = 7   (SCAL..ACT + VNRM)
;;;     IS-FINITE-DIMENSIONAL(m)    pins length(m) = 6   (IS-VECTOR-SPACE,
;;;                                                       hence MODULE's shape)
;;;
;;; -- each satisfiable alone, together unsatisfiable, and `hahn-banach',
;;; `norm-as-sup', `norm-attained-by-functional', `vector-taylor-remainder-bound'
;;; and `nvs-taylor-remainder-bound' all wrote them of ONE m.  A theorem whose
;;; hypothesis has no model is VACUOUSLY true: it proves, its bill reads like any
;;; other, and it says nothing.  The repair is to say which STRUCTURE each half
;;; is about -- IS-FINITE-DIMENSIONAL(NORMED-VECTOR-SPACE-AS-MODULE(m)) -- which
;;; is a decision about what the statement means, so this is WARN-ONLY too.
;;;
;;; Two things this does that the per-declaration walk does not:
;;;
;;;   * it follows a `def-predicate' into its defining IFF, which is how
;;;     IS-FINITE-DIMENSIONAL's pin is reached at all (it is not a declared
;;;     structure -- it is (AND (IS-VECTOR-SPACE m) (IS-NOETHERIAN m)));
;;;   * it collects the pins of a whole ASSUMPTION SET -- everything assumed
;;;     simultaneously at some node of the formula -- rather than of one IFF.
;;;
;;; Everything else is the machinery above, unchanged: `structure-length-pins'
;;; does the structure recursion, `structure--closed-term-length' recognises a
;;; term whose length a declaration fixes, and `structure--conjuncts' flattens.
;;;
;;; SCOPE, stated so a clean report is not over-read.  It is syntactic and
;;; decides exactly this class: two length pins on one term.  It says nothing
;;; about any other reason a hypothesis might be unsatisfiable, it inherits the
;;; per-declaration walk's blind spot under a FORSOME, and it reads HYPOTHESES
;;; -- a clash among positively asserted conjuncts of a CONCLUSION makes the
;;; theorem unprovable, which is loud, where a vacuous hypothesis is silent.
;;; The control is scratchpad/stmt-audit-control.scm: decoy statements, one of
;;; each defect form plus two that must NOT be reported.

;;; The defining IFF of a def-predicate (structures.scm:924 installs
;;; `forall p1..pn. P(p1..pn) <=> BODY' under the name P; some files spell the
;;; installed name P-def), as (VARS . BODY).  #f for anything that is not one.
(define (predicate--def-body sym)
  (and (symbol? sym)
       (let* ((raw (or (hash-table-ref/default *theorem-table* sym #f)
                       (hash-table-ref/default *theorem-table*
                                               (symbol-append sym '-def) #f)))
              (f   (and raw (if (wff? raw) (wff-formula raw) raw))))
         (and (pair? f)
              (let peel ((g f) (vs '()))
                (if (and (pair? g) (eq? (car g) 'FORALL))
                    (peel (caddr g) (cons (cadr g) vs))
                    (let ((params (reverse vs)))
                      (and (pair? g) (eq? (car g) 'IFF)
                           (pair? (cadr g)) (eq? (car (cadr g)) sym)
                           (equal? (cdr (cadr g)) params)
                           (cons params (caddr g))))))))))

;;; ((TERM LENGTH REASON) ...) -- every length pin the truth of the FORMULA F
;;; forces.  DEPTH bounds the recursion through nested predicates.
(define (formula-length-pins f #!optional depth0)
  (let ((depth (if (default-object? depth0) 12 depth0)))
    (if (<= depth 0)
        '()
        (append-map
         (lambda (c)
           (cond
             ;; a declared structure's predicate -- the declaration walk knows it
             ((and (pair? c) (= (length c) 2) (structure--of-is-predicate (car c)))
              (structure-length-pins (structure--of-is-predicate (car c))
                                     (cadr c) (- depth 1)))
             ;; a length equation stated outright: (= (LENGTH t) n)
             ((and (pair? c) (memq (car c) '(= ==))
                   (pair? (cadr c)) (eq? (car (cadr c)) 'LENGTH)
                   (number? (caddr c)))
              (list (list (cadr (cadr c)) (caddr c) "a stated length equation")))
             ;; an equation pinning a term to a closed tuple of known length
             ((and (pair? c) (memq (car c) '(= ==))
                   (structure--closed-term-length (caddr c)))
              (list (list (cadr c) (structure--closed-term-length (caddr c))
                          (string-append "the equation pinning it to "
                                         (expression->string (caddr c))))))
             ;; a def-predicate: unfold its defining IFF and go on.  The
             ;; substitution is SIMULTANEOUS (subst-free*): a fold of
             ;; subst-free would expose each argument to every later binding.
             ((and (pair? c) (symbol? (car c))
                   (let ((d (predicate--def-body (car c))))
                     (and d (= (length (car d)) (length (cdr c))) d)))
              => (lambda (d)
                   (map (lambda (p)
                          (list (car p) (cadr p)
                                (string-append (caddr p) ", through "
                                               (symbol->string (car c)))))
                        (formula-length-pins
                         (subst-free* (map cons (car d) (cdr c)) (cdr d))
                         (- depth 1)))))
             (else '())))
         (structure--conjuncts f)))))

;;; ((TERM (k1 . REASON1) (k2 . REASON2)) ...) -- one entry per term PINS pins
;;; to two different lengths.  Shared by both audits.
(define (pins--clashes pins)
  (let ((out '()))
    (let loop ((ps pins))
      (if (pair? ps)
          (let ((other (let scan ((l (cdr ps)))
                         (cond ((null? l) #f)
                               ((and (equal? (caar l) (caar ps))
                                     (not (= (cadr (car l)) (cadr (car ps)))))
                                (car l))
                               (else (scan (cdr l)))))))
            (if (and other
                     (not (there-exists? out
                            (lambda (e) (equal? (car e) (caar ps))))))
                (set! out (cons (list (caar ps)
                                      (cons (cadr (car ps)) (caddr (car ps)))
                                      (cons (cadr other) (caddr other)))
                                out)))
            (loop (cdr ps)))))
    (reverse out)))

;;; Every set of formulas F assumes SIMULTANEOUSLY at some node: the antecedents
;;; accumulated down each FORALL/IMPLIES spine.  A conjunctive antecedent stays
;;; one element and is flattened inside the pin walk, so (IMPLIES (AND A B) C)
;;; and (IMPLIES A (IMPLIES B C)) are read alike.
;;;
;;; A DEFINING IFF COUNTS TOO, and it is not a technicality: `def-predicate'
;;; installs `forall p... . P(p...) <=> BODY', so an unsatisfiable BODY makes P
;;; itself empty and every theorem assuming P vacuous.  That is the state of
;;; IS-SEMINORM / IS-SEMINORM-FAMILY / IS-FRECHET-STRUCTURE, each of which
;;; asserts IS-MODULE(m) -- hence IS-RING(scal(m)), pinning 6 -- beside
;;; IS-NORMED-FIELD(scal(m)), pinning 7.  Reporting only their consumers names
;;; four supports and hides the three definitions that are the cause.  The
;;; right-hand side is emitted as an assumption set of its own; the left is a
;;; bare application and pins nothing that the right does not.
(define (statement--assumption-sets f)
  (let walk ((f f) (asms '()) (out '()))
    (cond ((not (pair? f)) out)
          ((eq? (car f) 'FORALL) (walk (caddr f) asms out))
          ((eq? (car f) 'IMPLIES)
           (let ((a (cons (cadr f) asms)))
             (walk (caddr f) a (cons a out))))
          ((eq? (car f) 'IFF)
           (walk (caddr f) asms
                 (walk (cadr f) asms (cons (cons (caddr f) asms) out))))
          ((eq? (car f) 'AND)
           (walk (caddr f) asms (walk (cadr f) asms out)))
          (else out))))

;;; ((THEOREM TERM (k1 . REASON1) (k2 . REASON2)) ...) -- every installed
;;; formula (theorems, axioms and PSS supports alike: `support' goes through
;;; install-theorem!) with an unsatisfiable hypothesis of this kind.  Empty
;;; means no statement in the tree conjoins two clashing length pins.
(define (statement-satisfiability-audit)
  (let ((out '()))
    (for-each
     (lambda (nm)
       (let* ((raw (hash-table-ref/default *theorem-table* nm #f))
              (f   (and raw (if (wff? raw) (wff-formula raw) raw))))
         (if (pair? f)
             (for-each
              (lambda (asms)
                (for-each
                 (lambda (cl)
                   (if (not (there-exists? out
                              (lambda (e) (and (eq? (car e) nm)
                                               (equal? (cadr e) (car cl))))))
                       (set! out (cons (cons nm cl) out))))
                 (pins--clashes (append-map formula-length-pins asms))))
              (statement--assumption-sets f)))))
     ;; A `-rev' companion is generated from its base (install-theorem!), so its
     ;; clash is never independent information -- it would double every finding
     ;; that comes from an equation or a defining IFF.
     (filter (lambda (nm)
               (let ((s (symbol->string nm)))
                 (not (and (> (string-length s) 4)
                           (string=? (substring s (- (string-length s) 4)
                                                (string-length s))
                                     "-rev")))))
             (sort (hash-table-keys *theorem-table*)
                   (lambda (a b) (string<? (symbol->string a)
                                           (symbol->string b))))))
    (reverse out)))

;;; Print one report line per finding, the way load.scm does.
(define (report-statement-satisfiability findings)
  (for-each (lambda (e)
              (display ";;   ") (display (car e))
              (display ": length(") (display (expression->string (cadr e)))
              (display ") is pinned to ") (display (car (caddr e)))
              (display " (by ") (display (cdr (caddr e)))
              (display ") and to ") (display (car (cadddr e)))
              (display " (by ") (display (cdr (cadddr e)))
              (display ")\n"))
            findings))

;;; -----------------------------------------------------------------------
;;; structure-exemplification-audit -- which structure predicates has anything
;;; ever been shown to satisfy?
;;;
;;; A structure nothing instantiates has never had its satisfiability tested by
;;; anything: `declare-instance!' checks the tuple's length against the shape
;;; (structures.scm), and that check is what caught the RR-NORMED-FIELD/IS-RING
;;; inconsistency in May 2026.  A predicate with no witness at all never meets
;;; it.
;;;
;;; UNEXEMPLIFIED IS NOT UNSATISFIABLE.  A structure with no witness is an
;;; ordinary missing construction (nobody has built R^n as a NORMED-VECTOR-SPACE
;;; yet), not a defect.  This is a QUERY, not a gate, and it is deliberately not
;;; run at load time; `structure-satisfiability-audit' above is the gate.
;;;
;;; Returns (SEEDED REACHABLE UNWITNESSED), three name lists:
;;;   SEEDED     -- a declared instance, or a witness theorem with no structure
;;;                 hypothesis: the predicate is inhabited outright.
;;;   REACHABLE  -- inhabited by a construction all of whose structure
;;;                 hypotheses are themselves reachable from the seeds.
;;;   UNWITNESSED-- neither: nothing in the tree exhibits an X.

;;; The structure predicates appearing in F's hypotheses.
(define (structure--hypothesis-predicates f)
  (let outer ((f f) (acc '()))
    (cond ((not (pair? f)) acc)
          ((eq? (car f) 'FORALL) (outer (caddr f) acc))
          ((eq? (car f) 'IMPLIES)
           (outer (caddr f)
                  (let scan ((g (cadr f)) (a acc))
                    (cond ((not (pair? g)) a)
                          ((and (= (length g) 2)
                                (structure--of-is-predicate (car g)))
                           (cons (structure--of-is-predicate (car g)) a))
                          ((memq (car g) '(AND OR IMPLIES))
                           (scan (cadr g) (scan (caddr g) a)))
                          (else a)))))
          (else acc))))

;;; The structure F concludes something is, or #f.  An IFF is a DEFINITION and
;;; witnesses nothing, so the walk stops at one.
(define (structure--conclusion-predicate f)
  (let loop ((f f))
    (cond ((not (pair? f)) #f)
          ((memq (car f) '(FORALL IMPLIES)) (loop (caddr f)))
          ((eq? (car f) 'IFF) #f)
          ((and (= (length f) 2) (structure--of-is-predicate (car f)))
           (structure--of-is-predicate (car f)))
          (else #f))))

(define (structure-exemplification-audit)
  (let* ((names (sort (hash-table-keys *structure-decl-table*)
                      (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))
         (rules '())          ; (TARGET (SOURCE ...)) per witness theorem
         (seeded '()))
    (for-each
     (lambda (nm)
       (let* ((raw (hash-table-ref/default *theorem-table* nm #f))
              (f   (and raw (if (wff? raw) (wff-formula raw) raw)))
              (t   (and f (structure--conclusion-predicate f))))
         (if t (set! rules (cons (list t (structure--hypothesis-predicates f)) rules)))))
     (hash-table-keys *theorem-table*))
    (for-each (lambda (i)
                (let ((s (instance-structure i)))
                  (if (and (memq s names) (not (memq s seeded)))
                      (set! seeded (cons s seeded)))))
              (hash-table-keys *structure-instances*))
    (for-each (lambda (r)
                (if (and (null? (cadr r)) (not (memq (car r) seeded)))
                    (set! seeded (cons (car r) seeded))))
              rules)
    (let ((reach seeded))
      (let loop ()
        (let ((before (length reach)))
          (for-each (lambda (r)
                      (if (and (not (memq (car r) reach))
                               (let all ((h (cadr r)))
                                 (or (null? h)
                                     (and (memq (car h) reach) (all (cdr h))))))
                          (set! reach (cons (car r) reach))))
                    rules)
          (if (> (length reach) before) (loop))))
      (list (filter (lambda (n) (memq n seeded)) names)
            (filter (lambda (n) (and (memq n reach) (not (memq n seeded)))) names)
            (filter (lambda (n) (not (memq n reach))) names)))))

;;; -----------------------------------------------------------------------
;;; EIGHTH GATE: one object, two exact domains.
;;;
;;; `IN f (FUN A ...)' pins DOM(f) = A EXACTLY.  library.scm:321 states the
;;; reading in as many words -- "(FUN A) = all total functions whose domain IS
;;; A" -- and `dom-of-fun' (library.scm:500) draws the equation out.  So a single
;;; object asserted into two function classes with DIFFERENT domains proves
;;; those two domains equal.
;;;
;;; This is not hypothetical.  `binneg' is asserted into FUN(ZZ,ZZ), FUN(QQ,QQ),
;;; FUN(RR,RR) and FUN(CC,CC) (numeric-instances.scm:86-92), collapsing the whole
;;; numeric hierarchy; composed with cc-i-in and cc-i-squared that yields
;;; 0 <= -1, i.e. FALSITY -- derived with 0 open leaves in
;;; scratchpad/bridge-falsity-probe.scm.
;;;
;;; WHY THIS GATE IS A DIFFERENT SPECIES FROM THE SEVEN ABOVE IT.  The
;;; install-door gates grade one formula's SHAPE (arity, free variables, head
;;; registration, wff-vs-term position).  `structure-satisfiability-audit' reads
;;; one DECLARATION; `statement-satisfiability-audit' reads one FORMULA's
;;; hypotheses.  Every axiom involved here is impeccably well-formed and
;;; individually satisfiable: the defect is assembled ACROSS formulas, by a
;;; shared constant, and nothing else in the tree looks there.  A
;;; per-declaration gate does not see per-formula composition, and a per-formula
;;; gate does not see per-CORPUS composition.
;;;
;;; WARN-ONLY, deliberately.  The three findings it reports today are known and
;;; their repair is a foundational decision about how a numeric operation is
;;; presented to a structure slot (see the file header of numeric-instances.scm).
;;; A hard gate here would refuse to load the library.

(define *dc-binders*
  '(FORALL FORSOME IOTA COMP VNB-LAMBDA SEP BIG-UNION LAMBDOID))

;; Declared for binder-walker-audit (expressions.scm: declare-binder-walker!).
;; LAMBDOID is an EXTRA head, which the audit allows: this walk wants "is the
;; occurrence under any binder at all", and a functoid record is one.
(declare-binder-walker! 'dc--grouped *dc-binders*)

;;; #t when T mentions no symbol currently bound.  An occurrence under a binder
;;; that captures the object or the domain is an honest quantified statement
;;; (`forall f. f in FUN(a) => ...'), not an assertion about a particular object.
(define (dc--closed? t bound)
  (cond ((symbol? t) (not (memq t bound)))
        ((pair? t)   (and (dc--closed? (car t) bound) (dc--closed? (cdr t) bound)))
        (else #t)))

;;; Every closed (IN obj (FUN dom ...)) in the installed corpus, grouped:
;;;   ((OBJ (DOM NAME ...) (DOM NAME ...) ...) ...)
;;; one inner entry per distinct domain, naming the formulas that assert it.
(define (dc--grouped)
  (let ((hits '()))
    (define (scan f bound name)
      (if (pair? f)
          (if (and (memq (car f) *dc-binders*) (pair? (cdr f)))
              (let ((b2 (cons (cadr f) bound)))
                (for-each (lambda (s) (scan s b2 name)) (cddr f)))
              (begin
                (if (and (eq? (car f) 'IN)
                         (= (length f) 3)
                         (pair? (caddr f))
                         (eq? (car (caddr f)) 'FUN)
                         (pair? (cdr (caddr f))))
                    (let ((obj (cadr f)) (dom (cadr (caddr f))))
                      (if (and (dc--closed? obj bound) (dc--closed? dom bound))
                          (set! hits (cons (list obj dom name) hits)))))
                (for-each (lambda (s) (scan s bound name)) (cdr f))))))
    (hash-table-walk *theorem-table*
      (lambda (name formula) (scan formula '() name)))
    ;; GROUP MODULO ALPHA, not by equal?.  Two alpha-variant lambdas -- the SAME
    ;; function written with different bound-variable names -- are the same
    ;; object, and a gate keyed by equal? files them separately and reports no
    ;; clash.  This is not hypothetical: `matact-summand-type' and
    ;; `matact-summand-type-le' (mod-seq.scm) asserted one lambda into
    ;; FUN(INTERVAL 1 n, ..) and FUN(INTERVAL 1 k, ..) under a guard requiring
    ;; only k <= n -- a LIVE inconsistency in the asserted base, found in August
    ;; 2026 by a probe that grouped installed (IN <lambda> (FUN A B)) by the
    ;; lambda MOD ALPHA.  That probe is what this audit should have been from the
    ;; start; keyed by equal? it would have missed exactly that case.
    ;;
    ;; Domains are compared mod alpha for the same reason.
    (define (dc--key-of obj keys)
      (let loop ((ks keys))
        (cond ((null? ks) obj)
              ((alpha-equiv? (car ks) obj) (car ks))
              (else (loop (cdr ks))))))
    (let ((tbl (make-equal-hash-table)))
      (for-each
       (lambda (h)
         (let* ((obj (dc--key-of (car h) (hash-table-keys tbl)))
                (dom (cadr h)) (nm (caddr h)))
           (hash-table-set! tbl obj
             (let bump ((ds (hash-table-ref/default tbl obj '()))
                        (seen #f) (out '()))
               (cond ((null? ds)
                      (reverse (if seen out (cons (list dom nm) out))))
                     ((alpha-equiv? (caar ds) dom)
                      (bump (cdr ds) #t
                            (cons (if (memq nm (cdar ds))
                                      (car ds)
                                      (cons dom (cons nm (cdar ds))))
                                  out)))
                     (else (bump (cdr ds) seen (cons (car ds) out))))))))
       hits)
      (sort (map (lambda (k) (cons k (hash-table-ref/default tbl k '())))
                 (hash-table-keys tbl))
            (lambda (a b) (string<? (expression->string (car a))
                                    (expression->string (car b))))))))

;;; The audit proper: every object carrying two or more DISTINCT domains.
;;; Each such pair proves the two domains equal.
(define (domain-clash-audit)
  (filter (lambda (e) (pair? (cddr e))) (dc--grouped)))

;;; How many objects carry a closed FUN-membership assertion at all -- the
;;; denominator, so a reader can tell "3 of 13" from "3 of 3".  It is also the
;;; audit's own control: if this equals the number of clashes, the filter is
;;; not filtering.
(define (domain-clash-population)
  (length (dc--grouped)))


;;; -----------------------------------------------------------------------
;;; kernel-callers-audit -- WHO MAY WRITE THE DEDUCTION GRAPH
;;;
;;; `dg-apply-rule!' (deduction-graphs.scm:283) is the single choke point for
;;; every write into a deduction graph.  Until 2026-09-20 it VALIDATED NOTHING (since then it
;;; checks each inference against the operation's checker first); at the time it recorded the
;;; rule tag it is handed, posts the premise sequents and writes the arrows.
;;; The soundness of a step therefore rests entirely on the procedure that
;;; requested it, so the trusted code base is exactly the set of procedures that
;;; CALL this one -- and until this gate, nothing in the tree bounded that set.
;;;
;;; The kernel map of 2026-09-12 (reference/KERNEL-MAP.md) measured it:
;;; 69 call sites belonging to 57 entry points (re-measured 2026-09-20), in the 8 files below, and 0 uses
;;; of the name as a VALUE.  A run-time pass over the whole library recorded
;;; 197,669 graph writes with 0 outside an entry point.  That was a measurement
;;; of one afternoon, not an invariant; this gate makes it one.
;;;
;;; It counts two things, because the first alone has an escape hatch:
;;;   * CALLS -- the name in operator position.
;;;   * VALUE uses -- the name anywhere else, e.g. (map dg-apply-rule! ...),
;;;     which hands the graph writer to a caller in another file entirely.  The
;;;     count is 0 today and a non-zero one is a finding wherever it appears,
;;;     allowlisted file or not.
;;;
;;; Done with the READER, for the reason CLAUDE.md records twice over: a textual
;;; scan cannot tell code from a comment, a string or a quote, and got the
;;; compile-skip list wrong in both of its textual incarnations.  A definition's
;;; FORMAL LIST is skipped -- `(define (dg-apply-rule! dg rule hyps concl) ...)'
;;; has the same S-expression shape as a call, and counting it reported 69 sites
;;; in 9 files (deduction-graphs.scm, where the writer LIVES, is not a caller).
;;; With the formals skipped this scan and the kernel map's independent one agree
;;; exactly: 68 and 8.

;;; The list itself lives in certificates.scm (2026-09-26), which loads before
;;; the first proof and hashes these files into every proof certificate's kernel
;;; key: ONE list, so the key and this gate cannot drift apart.  Enlarge it THERE.
(define *kernel-caller-files* *cert-kernel-caller-files*)

;;; -> (calls . value-uses) for one read form.
(define (kca--counts form)
  (let ((calls 0) (vals 0))
    (define (walk-list l)
      (cond ((pair? l) (walk (car l)) (walk-list (cdr l)))
            ((symbol? l) (walk l))))
    (define (walk x)
      (cond ((symbol? x) (if (eq? x 'dg-apply-rule!) (set! vals (+ vals 1))))
            ((not (pair? x)) 'datum)
            ((eq? (car x) 'quote) 'datum)
            ;; (define (NAME . formals) body ...): the target is a BINDING, and
            ;; a formal list is spelled exactly like a call.
            ((and (memq (car x) '(define define-integrable))
                  (pair? (cdr x)) (pair? (cadr x)))
             (walk-list (cddr x)))
            ((and (memq (car x) '(lambda named-lambda)) (pair? (cdr x)))
             (walk-list (cddr x)))
            ((eq? (car x) 'dg-apply-rule!)
             (set! calls (+ calls 1))
             (walk-list (cdr x)))
            (else (walk-list x))))
    (walk form)
    (cons calls vals)))

;;; Cheap pre-filter.  A file whose TEXT does not contain the characters cannot
;;; call it, so the reader pass runs on the 11 files that mention it rather than
;;; all 433.  Deliberately sloppy -- a hit in a comment or a string costs one
;;; reader pass and nothing else, because the READER makes the actual decision.
(define (kca--file-mentions? path)
  (call-with-input-file path
    (lambda (port)
      (let ((s (read-string (+ 1 (file-length path)) port)))
        (and (not (eof-object? s))
             (string-search-forward "dg-apply-rule!" s 0)
             #t)))))

(define (kca--file-counts f)
  ;; `*prover-dir*' (load.scm), never a literal: the tree is read wherever it
  ;; was loaded from, so this gate works on any machine or account.
  (let ((path (string-append *prover-dir* f ".scm")))
    (if (not (kca--file-mentions? path))
        (cons 0 0)
        (call-with-input-file path
          (lambda (port)
            (let loop ((calls 0) (vals 0))
              (let ((form (read port)))
                (if (eof-object? form)
                    (cons calls vals)
                    (let ((c (kca--counts form)))
                      (loop (+ calls (car c)) (+ vals (cdr c))))))))))))

;;; Every loaded file with a genuine use, as ((file calls value-uses) ...).
;;; Returned rather than printed, so the suite and the report can both read it.
(define (kernel-callers-census)
  (let loop ((fs *vnb-files*) (out '()))
    (if (null? fs)
        (reverse out)
        (let ((c (kca--file-counts (car fs))))
          (loop (cdr fs)
                (if (and (= 0 (car c)) (= 0 (cdr c)))
                    out
                    (cons (list (car fs) (car c) (cdr c)) out)))))))

;;; The audit proper: any file with a use that is not on the allowlist.  Empty
;;; is the good case.
(define (kernel-callers-audit)
  (filter (lambda (e) (not (member (car e) *kernel-caller-files*)))
          (kernel-callers-census)))

;;; Uses of the name as a VALUE, anywhere -- including inside an allowlisted
;;; file, where a call is fine but handing the writer out is not.
(define (kernel-callers-value-uses)
  (filter (lambda (e) (> (caddr e) 0)) (kernel-callers-census)))
