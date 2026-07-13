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
    SEP BIG-UNION POWERSET PAIR))

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
                                    (when (eq? (constant-head? nm) 'accessor)
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
