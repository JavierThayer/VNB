;;; structures.scm -- mathematical structure definitions
;;;
;;; (def-structure name carriers op-specs axiom-names)
;;;
;;;   name        — symbol, e.g. 'NORMEDSPACE
;;;   carriers    — list of accessor names, e.g. '(VECTORS)
;;;   op-specs    — list of (op-name domain range), e.g.
;;;                   '((SCALAR-TIMES (CARTESIAN CC VECTORS) VECTORS)
;;;                     (PLUS         (CARTESIAN VECTORS VECTORS) VECTORS)
;;;                     (NORM         VECTORS RR))
;;;                 Carrier and op accessor names appear bare in domain/range;
;;;                 def-structure expands them to (ACCESSOR s) automatically.
;;;   axiom-names — list of theorem names that characterize the structure
;;;
;;; Auto-generates:
;;;   Accessor macetes:
;;;     (CARRIER s)  ->  (NTH k s)   for k = 1, 2, ... (carriers first)
;;;     (OP s)       ->  (NTH k s)   for k = n+1, n+2, ... (ops after carriers)
;;;   IS-NAME definitional axiom in *current-theory*:
;;;     (FORALL s (IFF (IS-NAME s)
;;;                    (AND (SET (carrier1 s))
;;;                         ...
;;;                         (IN (op1 s) (FUN domain1 range1))
;;;                         ...)))

(define-record-type <structure-def>
  (%make-structure-def name carriers op-specs axiom-names)
  structure-def?
  (name         structure-def-name)
  (carriers     structure-def-carriers)   ; list of symbols
  (op-specs     structure-def-op-specs)   ; list of (op-name domain range)
  (axiom-names  structure-def-axiom-names))

(define *structure-table* (make-equal-hash-table))

(define (lookup-structure name)
  (hash-table-ref/default *structure-table* name #f))

;;; Install macete: (accessor s) -> (NTH k s) for any s.
(define (install-accessor-macete! accessor-name k)
  (install-macete! accessor-name
    (make-elementary-macete
      '(svar)
      '()
      `(,accessor-name svar)
      `(NTH ,k svar))))

;;; Expand bare accessor names in a domain/range expression to (ACCESSOR s).
;;; Recurses through the full cons tree so nested CARTESIAN etc. are handled.
(define (expand-accessors expr all-accessors ivar)
  (cond
    ((and (symbol? expr) (member expr all-accessors))
     `(,expr ,ivar))
    ((pair? expr)
     (cons (expand-accessors (car expr) all-accessors ivar)
           (expand-accessors (cdr expr) all-accessors ivar)))
    (else expr)))

;;; Build the IS-NAME definitional axiom formula.
;;; Instance variable is always 's.
(define (build-is-axiom struct-name carriers op-specs)
  (let* ((ivar          's)
         (all-accessors (append carriers (map car op-specs)))
         (is-name       (symbol-append 'IS- struct-name))
         (n             (+ (length carriers) (length op-specs)))
         (conjuncts
          (cons
           `(= (LENGTH ,ivar) ,n)         ; s is a VNB list of exactly n components
           (append
            ;; Carriers must be sets.  We use the membership form (IN _ SET),
            ;; not the predicate form (SET _), because the manual states
            ;; categorically that there is no separate predicate `SET(_)`.
            (map (lambda (acc)
                   `(IN (,acc ,ivar) SET))
                 carriers)
            (map (lambda (spec)
                   (let ((op (car spec)))
                     (if (= (length spec) 2)
                         ;; constant spec (op set): op(s) ∈ set
                         (let ((set (expand-accessors (cadr spec) all-accessors ivar)))
                           `(IN (,op ,ivar) ,set))
                         ;; function spec (op domain range): op(s) ∈ FUN(domain, range)
                         (let ((dom (expand-accessors (cadr spec)  all-accessors ivar))
                               (rng (expand-accessors (caddr spec) all-accessors ivar)))
                           `(IN (,op ,ivar) (FUN ,dom ,rng))))))
                 op-specs))))
         (body (conjuncts->and conjuncts)))
    `(FORALL ,ivar (IFF (,is-name ,ivar) ,body))))

(define (conjuncts->and cs)
  (cond
    ((null? cs)        'TRUTH)
    ((null? (cdr cs))  (car cs))
    (else              `(AND ,(car cs) ,(conjuncts->and (cdr cs))))))

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

(define (def-structure name carriers op-specs axiom-names)
  (let* ((sd (%make-structure-def name carriers op-specs axiom-names))
         (num-carriers (length carriers)))
    (hash-table-set! *structure-table* name sd)
    ;; Carrier accessor macetes
    (let loop ((accs carriers) (k 1))
      (unless (null? accs)
        (install-accessor-macete! (car accs) k)
        (loop (cdr accs) (+ k 1))))
    ;; Op accessor macetes (indexed after carriers)
    (let loop ((ops op-specs) (k (+ num-carriers 1)))
      (unless (null? ops)
        (install-accessor-macete! (caar ops) k)
        (loop (cdr ops) (+ k 1))))
    ;; IS-NAME definitional axiom
    (let ((is-name (symbol-append 'IS- name))
          (axiom   (build-is-axiom name carriers op-specs)))
      (theory-add-axiom! *current-theory* is-name axiom))
    ;; Associated class: NAME itself is the proper class
    ;;   { s | IS-NAME(s) }.  Letting NAME (and not just IS-NAME) name
    ;;   the class makes bounded quantification natural:
    ;;     forall([s in NAME], ...)
    ;;   rather than the unbounded form
    ;;     forall([s], IS-NAME(s) implies ...).
    (let ((is-name           (symbol-append 'IS- name))
          (class-axiom-name  (symbol-append name '-class)))
      (theory-add-axiom! *current-theory* class-axiom-name
        `(FORALL s (IFF (IN s ,name) (,is-name s)))))
    name))

;;; -----------------------------------------------------------------------
;;; declare-structure — user-facing syntax (no quoting required)
;;;
;;; (declare-structure NAME
;;;   (carriers C1 C2 ...)
;;;   (op OPNAME (D1 D2 ...) RANGE)  ; domain = CARTESIAN(D1,D2,...) if multiple
;;;   (op OPNAME (D) RANGE)          ; domain = D when only one
;;;   (constant CNAME SET))          ; element of SET (uses 2-arg spec internally)
;;;
;;; Characteristic axioms are installed by separate theory-add-axiom! calls
;;; in the file that defines the structure.  The axioms clause is deliberately
;;; absent: MIT Scheme evaluates macro arguments before quoting kicks in for
;;; symbol literals, so axiom names cannot safely appear unquoted here.

(define-syntax declare-structure
  (syntax-rules ()
    ((_ name clause ...)
     (def-structure-from-clauses 'name (list 'clause ...)))))

(define (def-structure-from-clauses name clauses)
  (let loop ((rest clauses) (carriers '()) (op-specs '()))
    (if (null? rest)
        (def-structure name carriers op-specs '())
        (let* ((clause (car rest))
               (kind   (car clause)))
          (cond
            ((eq? kind 'carriers)
             (loop (cdr rest) (append carriers (cdr clause)) op-specs))
            ((eq? kind 'op)
             (let* ((op-name (cadr clause))
                    (doms    (caddr clause))
                    (range   (cadddr clause))
                    (domain  (if (null? (cdr doms)) (car doms) (cons 'CARTESIAN doms))))
               (loop (cdr rest) carriers
                     (append op-specs (list (list op-name domain range))))))
            ((eq? kind 'constant)
             (loop (cdr rest) carriers
                   (append op-specs (list (list (cadr clause) (caddr clause))))))
            (else
             (error "declare-structure: unknown clause kind" kind)))))))

;;; -----------------------------------------------------------------------
;;; def-functoid
;;;
;;; (def-functoid name (param ...) body)
;;;
;;; Installs a macete that rewrites (name arg ...) to body[args/params].
;;; The params list may be a single symbol or a list of symbols.
;;; def-functoid is a definitional device: it installs a named rewrite rule
;;; at the proof-checker level.  There is no formal quantifier over functoids.
;;;
;;; Example:
;;;   (def-functoid GroupCarrier (G) (CARRIER G))
;;;   => installs macete that rewrites (groupcarrier x) to (carrier x)

(define (def-functoid name params body)
  (let* ((pvars (if (pair? params) params (list params))))
    (install-macete! name
      (make-elementary-macete pvars '() (cons name pvars) body))
    name))

;;; -----------------------------------------------------------------------
;;; def-predicate
;;;
;;; (def-predicate pred-name params body)
;;;
;;;   pred-name : symbol        -- the predicate being defined, e.g. 'IS-CAUCHY-SEQ
;;;   params    : (p1 p2 ...)   -- argument variable symbols
;;;   body      : S-expression  -- defining formula in terms of p1, p2, ...
;;;
;;; Installs one characterising axiom named pred-name:
;;;   forall p1 p2 ... . pred-name(p1,p2,...) <=> body
;;;
;;; Example:
;;;   (def-predicate 'IS-CAUCHY-SEQ '(X f) '(AND ... ))

(define (def-predicate pred-name params body)
  (let* ((app     `(,pred-name ,@params))
         (iff     `(IFF ,app ,body))
         (formula (fold-right (lambda (p f) `(FORALL ,p ,f)) iff params)))
    (theory-add-definition! *current-theory* pred-name
      (list (cons pred-name formula)))))

;;; -----------------------------------------------------------------------
;;; specialize-structure
;;;
;;; (specialize-structure 'HARP 'RING 'harp-is-ring)
;;;
;;; Given a proved theorem `is-thm-name` of the form (IS-RING HARP), scans
;;; *theorem-table* for every theorem of the shape
;;;
;;;   (FORALL s (IMPLIES (IS-RING s) P[s]))
;;;
;;; and installs P[HARP] as a new theorem named <original-name>-harp.
;;;
;;; Soundness: the inference is forall-elim + modus-ponens on the certified
;;; IS-RING(HARP) witness.  No new axioms are introduced.

(define (generic-for-struct? formula is-pred)
  ;; Returns (cons bound-var P[var]) if formula matches
  ;;   (FORALL s (IMPLIES (IS-PRED s) P[s])), else #f.
  (and (pair? formula)
       (eq? (car formula) 'FORALL)
       (let* ((s    (quantifier-var formula))
              (body (quantifier-body formula)))
         (and (pair? body)
              (eq? (car body) 'IMPLIES)
              (let ((ante (binary-left body)))
                (and (pair? ante)
                     (= (length ante) 2)
                     (eq? (car ante) is-pred)
                     (eq? (cadr ante) s)
                     (cons s (binary-right body))))))))

(define (specialize-structure instance-name struct-name is-thm-name)
  (let* ((is-pred    (symbol-append 'IS- struct-name))
         (is-formula (lookup-theorem is-thm-name)))
    (unless (and (pair? is-formula)
                 (= (length is-formula) 2)
                 (eq? (car is-formula) is-pred)
                 (eq? (cadr is-formula) instance-name))
      (error "specialize-structure: theorem does not prove (IS-STRUCT instance)"
             is-thm-name is-formula))
    (let* ((suffix (string->symbol
                    (string-append "-"
                     (string-downcase (symbol->string instance-name)))))
           (count  0)
           (all    (hash-table->alist *theorem-table*)))
      (for-each
        (lambda (entry)
          (let ((match (generic-for-struct? (cdr entry) is-pred)))
            (when match
              (let* ((thm-name  (car entry))
                     (special-p (subst-free (car match) instance-name (cdr match)))
                     (new-name  (symbol-append thm-name suffix)))
                (install-theorem! new-name special-p)
                (set! count (+ count 1))))))
        all)
      (display (number->string count))
      (display " theorems specialized for ")
      (display instance-name)
      (newline)
      count)))
