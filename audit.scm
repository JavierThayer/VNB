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
