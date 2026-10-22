;;; statement-types.scm -- THE IMPLIED TYPES OF A STATEMENT (the user's request, 2026-10-17)
;;;
;;;   (implied-types 'NAME)        a theorem by name
;;;   (implied-types FORMULA)      a wff or a raw formula
;;;   (implied-types X 'no-check)  derive without confirming
;;;
;;; For each variable of the statement's prefix, prints and returns
;;;
;;;   * the STATED typings: the guards and hypotheses that mention it;
;;;   * the ENTAILED typings, each with the rule that produced it:
;;;       law        a structure predicate IS-X(t) in the statement gives the typing
;;;                  conjuncts of its characteristic law (the theorem IS-X, or
;;;                  is-x-def for a refinement): memberships and structure predicates;
;;;       view       an equation T = V(d), V a def-functor view, gives the slot
;;;                  read-offs  src_i(d) == tgt_i(T);
;;;       functor    IS-SRC(d) gives IS-TGT(V(d)) by the view's typing axiom V-is-TGT;
;;;       transport  a membership x in C carried along a read-off equation, a
;;;                  structure predicate IS-Y(T) along an equation T = T';
;;;   * a NO TYPING FOUND note for a variable with no typing of its own (a membership,
;;;     an inclusion or a structure predicate on the variable itself), naming the terms
;;;     it occurs under, and for each view whose source predicate is missing, that the
;;;     view's typing axiom runs one way only.  The note says what THESE RULES find: a
;;;     typing that only the definition of a functoid would give (c in ccint(a, b)) is
;;;     not looked for.
;;;
;;; Each entailed line is CONFIRMED by a scratch proof of the statement with its
;;; conclusion replaced by that line, driven by the rule that produced it (the
;;; derivation replayed through dk-project!, dk-rewrite-h!, dk-cite!).  A line whose
;;; scratch proof does not close is listed apart, as NOT CONFIRMED.  The scratch
;;; proof holds and restores the proof-state globals (as display-proof does); nothing
;;; is recorded or installed, and no bill is touched.
;;;
;;; The procedure adds no trust: it reads the library and runs the kernel on scratch
;;; states.  It is a reading aid; a statement means what its formula says.

;;; ---------------------------------------------------------------------------
;;; The prefix: (vars stated concl); stated is a list of formulas, conjunctions split.

(define (st--split-and f)
  (if (and (pair? f) (eq? (car f) 'AND))
      (append (st--split-and (cadr f)) (st--split-and (caddr f)))
      (list f)))

(define (st--prefix f)
  (let loop ((f f) (vars '()) (stated '()))
    (cond ((and (pair? f) (eq? (car f) 'FORALL) (symbol? (cadr f)))
           (loop (caddr f) (cons (cadr f) vars) stated))
          ((and (pair? f) (eq? (car f) 'IMPLIES))
           (loop (caddr f) vars (append (reverse (st--split-and (cadr f))) stated)))
          (#t (list (reverse vars) (reverse stated) f)))))

(define (st--replace-concl f new)
  (cond ((and (pair? f) (eq? (car f) 'FORALL) (symbol? (cadr f)))
         (list 'FORALL (cadr f) (st--replace-concl (caddr f) new)))
        ((and (pair? f) (eq? (car f) 'IMPLIES))
         (list 'IMPLIES (cadr f) (st--replace-concl (caddr f) new)))
        (#t new)))

;;; ---------------------------------------------------------------------------
;;; Small readers

(define (st--head-is? f h) (and (pair? f) (eq? (car f) h)))

(define (st--occurs? x e)
  (or (equal? x e) (and (pair? e) (or (st--occurs? x (car e)) (st--occurs? x (cdr e))))))

(define (st--binder? e)
  (and (pair? e)
       (or (memq (car e) '(FORALL FORSOME EXISTS IOTA SEP VNB-LAMBDA LAMBDOID))
           (st--binder? (car e)) (st--binder? (cdr e)))))

;;; IS-X -> (theorem-name . kind) of X's characteristic law, or #f
(define (st--law-name h)
  (and (symbol? h)
       (let ((s (symbol->string h)))
         (and (> (string-length s) 3) (string-ci=? (substring s 0 3) "is-")
              (let ((base (string->symbol (substring s 3 (string-length s)))))
                (cond ((and (lookup-structure base)
                            (hash-table-ref/default *theorem-table* (symbol-append 'IS- base) #f))
                       (symbol-append 'IS- base))
                      ((lookup-definitional-structure base)
                       (let ((n (string->symbol (string-append "is-" (string-downcase (symbol->string base)) "-def"))))
                         (and (hash-table-ref/default *theorem-table* n #f) n)))
                      (#t #f)))))))

(define (st--structure-pred? f)
  (and (pair? f) (= (length f) 2) (st--law-name (car f)) #t))

(define (st--typing? f)
  (and (pair? f)
  (or (and (memq (car f) '(IN SUBSET)) (= (length f) 3) (not (st--binder? f)))
      (st--structure-pred? f))))

(define (st--view-of t)
  (and (pair? t) (= (length t) 2) (symbol? (car t))
       (hash-table-ref/default *view-as-table* (car t) #f)))

(define (st--raw x)
  (cond ((wff? x) (wff-formula x))
        ((symbol? x)
         (let ((t (hash-table-ref/default *theorem-table* x #f)))
           (or t (error "implied-types: unknown theorem" x))
           (if (wff? t) (wff-formula t) t)))
        (#t (->raw-formula x))))

;;; ---------------------------------------------------------------------------
;;; The derivation.  A fact is (formula rule source parents); rule is one of
;;; stated law view functor transport.

(define (st--fact f rule src parents) (list f rule src parents))
(define st--fact-formula car)
(define st--fact-rule cadr)
(define st--fact-source caddr)
(define st--fact-parents cadddr)

(define (st--theorem-formula name)
  (let ((x (hash-table-ref/default *theorem-table* name #f))) (if (wff? x) (wff-formula x) x)))

;;; A predicate atom F = (P t1 ... tn) -> (LAW-NAME . RHS) with RHS the right side of
;;; P's characteristic law at the arguments, or #f.  The law is the structure's (IS-X,
;;; is-x-def) for a one-argument structure predicate, else a def-predicate's defining
;;; IFF  (FORALL x1 ... (FORALL xn (IFF (P x1 ... xn) RHS)))  from library-definitions.
(define (st--law-of f)
  (define (instantiate law)
    (let loop ((g (st--theorem-formula law)) (xs '()))
      (cond ((not (pair? g)) #f)
            ((and (eq? (car g) 'FORALL) (symbol? (cadr g))) (loop (caddr g) (cons (cadr g) xs)))
            ((and (eq? (car g) 'IFF) (pair? (cadr g)) (eq? (car (cadr g)) (car f))
                  (equal? (cdr (cadr g)) (reverse xs)) (= (length xs) (length (cdr f))))
             (cons law (subst-free* (map cons (reverse xs) (cdr f)) (caddr g))))
            (#t #f))))
  (and (pair? f) (symbol? (car f)) (pair? (cdr f))
       (or (and (= (length f) 2) (st--law-name (car f)) (instantiate (st--law-name (car f))))
           (let ((e (assq (car f) (library-definitions *library*))))
             (and e (find-first (lambda (x) x)
                                (map (lambda (nf) (instantiate (car nf))) (cdr e))))))))

;;; A defined predicate on several arguments (IS-SEMINORM-FAMILY(fld, m, fam)) met as a
;;; conjunct of a law: not a typing itself, but a STEP -- its own law holds the typings
;;; (IS-MODULE m, fam in FUN(...)).  Kept as a fact so the next round unfolds it, never
;;; shown in a report.  Until 2026-10-22 the filter dropped it, and the chain stopped one
;;; level down: open-mapping-theorem's m, g, x, h, t were reported untyped (the user).
(define (st--intermediate? f)
  (and (pair? f) (symbol? (car f))
       (not (memq (car f) '(IN SUBSET = == AND OR NOT IMPLIES IFF FORALL FORSOME)))
       (not (st--typing? f))
       (not (st--binder? f))
       (st--law-of f)
       #t))

;;; the conjuncts of a law worth showing: memberships, structure predicates, and
;;; equations between terms, none under a binder; plus the intermediate predicates
;;; the next round unfolds
(define (st--law-conjuncts f)
  (let ((l (st--law-of f)))
    (if l
        (filter (lambda (c) (or (st--typing? c)
                                (st--intermediate? c)
                                (and (pair? c) (memq (car c) '(= ==)) (= (length c) 3) (not (st--binder? c))
                                     ;; (= (length s) 6) is the shape's bookkeeping, not a typing
                                     (not (st--head-is? (cadr c) 'LENGTH)))))
                (st--split-and (cdr l)))
        '())))

(define (st--derive vars stated)
  (let ((facts (map (lambda (f) (st--fact f 'stated #f '())) stated)))
    (define (known f) (find-first (lambda (x) (equal? (st--fact-formula x) f)) facts))
    (define (add! f rule src parents)
      (if (known f) #f
          (begin (set! facts (append facts (list (st--fact f rule src parents)))) #t)))
    (define (var-subject? t) (memq t vars))
    (define (round!)
      (let ((changed #f) (snapshot facts))
        (for-each
         (lambda (x)
           (let ((f (st--fact-formula x)))
             ;; law: a stated predicate, or one on a statement variable
             (if (and (pair? f) (not (memq (car f) '(IN = == AND OR NOT IMPLIES IFF FORALL FORSOME)))
                      (or (eq? (st--fact-rule x) 'stated) (and (pair? (cdr f)) (every var-subject? (cdr f))))
                      (st--law-of f))
                 (let ((law (car (st--law-of f))))
                   (for-each (lambda (c) (if (add! c 'law law (list f)) (set! changed #t)))
                             (st--law-conjuncts f))))
             ;; view: T = V(d), either orientation
             (if (and (memq (car f) '(= ==)) (= (length f) 3))
                 (for-each
                  (lambda (pr)
                    (let ((vw (st--view-of (cdr pr))) (tt (car pr)))
                      (if vw
                          (let ((d (cadr (cdr pr))))
                            (for-each
                             (lambda (sc tc)
                               (if (add! (list '== (list sc d) (list tc tt)) 'view
                                         (view-as-name vw) (list f))
                                   (set! changed #t)))
                             (view-as-source-comps vw) (view-as-target-comps vw))))))
                  (list (cons (cadr f) (caddr f)) (cons (caddr f) (cadr f)))))
             ;; functor: IS-SRC(d) with V(d) in the statement
             (if (st--structure-pred? f)
                 (for-each
                  (lambda (name)
                    (let ((vw (hash-table-ref/default *view-as-table* name #f)))
                      (if (and (eq? (car f) (symbol-append 'IS- (view-as-source-struct vw)))
                               (find-first (lambda (y) (st--occurs? (list name (cadr f)) (st--fact-formula y)))
                                           snapshot))
                          (if (add! (list (symbol-append 'IS- (view-as-target-struct vw)) (list name (cadr f)))
                                    'functor (symbol-append name '-is- (view-as-target-struct vw)) (list f))
                              (set! changed #t)))))
                  (hash-table-keys *view-as-table*)))
             ;; transport
             (for-each
              (lambda (e)
                (let ((ef (st--fact-formula e)))
                  (if (and (memq (car ef) '(= ==)) (= (length ef) 3))
                      (let ((l (cadr ef)) (r (caddr ef)))
                        (cond
                         ;; a membership of a statement variable, along a READ-OFF equation
                         ;; (a law equation whose right side is a view term would only
                         ;; trade carr(scal(m)) for carr(view(d)): the read-off says it better)
                         ((and (st--head-is? f 'IN) (var-subject? (cadr f))
                               (or (eq? (st--fact-rule e) 'view)
                                   (and (eq? (st--fact-rule e) 'law) (not (st--view-of r))))
                               (st--occurs? l (caddr f)))
                          (if (add! (list 'IN (cadr f) (dk--replace (caddr f) l r)) 'transport #f (list f ef))
                              (set! changed #t)))
                         ;; a read-off backwards: a member of tgt(T) is a member of src(d)
                         ((and (st--head-is? f 'IN) (var-subject? (cadr f))
                               (eq? (st--fact-rule e) 'view) (st--occurs? r (caddr f)))
                          (if (add! (list 'IN (cadr f) (dk--replace (caddr f) r l)) 'transport #f (list f ef))
                              (set! changed #t)))
                         ;; a structure predicate, along any equation, either way
                         ((and (st--structure-pred? f) (or (equal? (cadr f) l) (equal? (cadr f) r)))
                          (if (add! (list (car f) (if (equal? (cadr f) l) r l)) 'transport #f (list f ef))
                              (set! changed #t))))))))
              snapshot)))
         snapshot)
        changed))
    (let loop ((n 0)) (if (and (< n 6) (round!)) (loop (+ n 1))))
    facts))

;;; ---------------------------------------------------------------------------
;;; Confirmation: a scratch proof of the statement with its conclusion replaced.

(define (st--establish! fact facts)
  (let ((f (st--fact-formula fact)))
    (define (fact-of g) (find-first (lambda (x) (equal? (st--fact-formula x) g)) facts))
    (if (not (dk-asm? f))
        (begin
          (for-each (lambda (p) (let ((pf (fact-of p))) (if pf (st--establish! pf facts))))
                    (st--fact-parents fact))
          (case (st--fact-rule fact)
            ((law) (dk-project! f (st--fact-source fact) (car (st--fact-parents fact))))
            ((functor) (dk-cite! (st--fact-source fact) (cadr (cadr f))))
            ((transport)
             (let* ((p (car (st--fact-parents fact))) (e (cadr (st--fact-parents fact))))
               (if (st--head-is? p 'IN)
                   (if (equal? (dk--replace (caddr p) (cadr e) (caddr e)) (caddr f))
                       (dk-rewrite-h! p (cadr e) (caddr e))
                       (dk-rewrite-h! p (caddr e) (cadr e)))
                   (if (equal? (cadr p) (cadr e))
                       (dk-rewrite-h! p (cadr e) (caddr e))
                       (dk-rewrite-h! p (caddr e) (cadr e))))))
            ((view) (st--view-readoff! f (car (st--fact-parents fact)) (st--fact-source fact)))
            (else #f))))))

;;; f = (== (SC d) (TC T)), eqn = T = V(d) (either way): unfold V(d) to its literal
;;; list on a lane, carry the equation over, read the slot off (fom-view-acc!'s recipe).
(define (st--view-readoff! f eqn view)
  (let* ((d   (cadr (cadr f)))
         (tt  (cadr (caddr f)))
         (tc  (car (caddr f)))
         (vd  (list view d))
         (vw  (hash-table-ref/default *view-as-table* view #f))
         (lst (cons 'LIST (map (lambda (a) (list a d)) (view-as-source-comps vw)))))
    (dk-have! f
      (lambda ()
        (dk-have! (list '== vd lst) (lambda () (mac view) (qrfl)))
        (let ((e2 (dk-rewrite-h! eqn vd lst)))
          (subst (if (equal? (cadr e2) tt) e2 (list '= (caddr e2) (cadr e2))))
          ;; the slot read-off rewrites EVERY occurrence of the accessor: when source and
          ;; target accessor are one symbol (carr / carr) the left side becomes an NTH too,
          ;; and a CONSTANT's slot becomes its instance value (carr(rr-normed-field) is rr).
          ;; So: step until the two sides agree, each step only when it changes the goal.
          (let loop ((steps (list (lambda () (slot tc)) nth-r (lambda () (slot (car (cadr f))))
                                  nth-r (lambda () (slot tc)) nth-r)))
            (let ((gl (dk-goal)))
              (cond ((equal? (cadr gl) (caddr gl)) (qrfl))
                    ((null? steps) (qrfl))
                    (#t (call-with-current-continuation
                         (lambda (k) (with-exception-handler (lambda (e) (k #f)) (car steps))))
                        (loop (cdr steps)))))))))))

(define (st--confirm stmt facts fact)
  (call-with-current-continuation
   (lambda (k)
     (with-exception-handler
      (lambda (e) (k #f))
      (lambda ()
        (fluid-let ((*vnb-loading* #t) (*replaying?* #t)
                    (*ps* #f) (*proof-script* *proof-script*)
                    (*proof-hidden-citations* *proof-hidden-citations*)
                    (*proof-mints* *proof-mints*)
                    (*fresh-counter* *fresh-counter*)
                    (*fresh-mark-at-last-record* *fresh-mark-at-last-record*)
                    (*witness-aliases* *witness-aliases*)
                    (*current-goal* *current-goal*)
                    (*sp-counter-snapshot* *sp-counter-snapshot*)
                    (*live-trace* *live-trace*)
                    (*vnb-undo-stack* *vnb-undo-stack*)
                    (*dg-journal* *dg-journal*)
                    (*vnb-write-certs* #f))
          (let ((done #f))
            (with-output-to-string
              (lambda ()
                (quietly
                 (lambda ()
                   (sp (make-wff (st--replace-concl stmt (st--fact-formula fact))))
                   (dk-peel!)
                   ;; a conjunctive hypothesis arrives whole; the facts are its conjuncts
                   (call-with-current-continuation
                    (lambda (k) (with-exception-handler (lambda (e) (k #f)) (lambda () (dk-split-all!)))))
                   ;; the peel keeps the statement's names unless a clash renamed one:
                   ;; then the facts no longer match the context, and the line is not confirmed
                   (st--establish! fact facts)
                   (if (not (proof-done? *ps*)) (dk-ass!))
                   (set! done (proof-done? *ps*))))))
            done)))))))

;;; ---------------------------------------------------------------------------
;;; The report

(define (st--subject f)
  (cond ((st--head-is? f 'IN) (cadr f))
        ((st--structure-pred? f) (cadr f))
        ((memq (car f) '(= ==)) (cadr f))
        (#t f)))

(define (st--uses-of v e)
  ;; the applications (H ... v ...) in E with v an immediate argument
  (cond ((not (pair? e)) '())
        ((and (symbol? (car e)) (memq v (cdr e))) (cons e (append-map (lambda (x) (st--uses-of v x)) (cdr e))))
        (#t (append-map (lambda (x) (st--uses-of v x)) e))))

(define (st--dedup l)
  (let loop ((l l) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member (car l) acc) (loop (cdr l) acc))
          (#t (loop (cdr l) (cons (car l) acc))))))

(define (st--rule-text fact)
  (case (st--fact-rule fact)
    ((law) (string-append "law " (string-downcase (symbol->string (st--fact-source fact)))))
    ((view) (string-append "read off the view " (string-downcase (symbol->string (st--fact-source fact)))))
    ((functor) (string-append "axiom " (string-downcase (symbol->string (st--fact-source fact)))))
    ((transport) (string-append "from " (expression->string (car (st--fact-parents fact)))
                                " and " (expression->string (cadr (st--fact-parents fact)))))
    (else "")))


;;; The analysis: (ROWS FAILED).  A row is
;;;   (v STATED ENTAILED-FACTS untyped? MISSING-VIEWS USES)
;;; with ENTAILED-FACTS the confirmed (or, without checking, derived) facts whose subject
;;; mentions v, MISSING-VIEWS the view terms V(v) whose source predicate is absent.
(define (st--analyse stmt check?)
  (let* ((pre (st--prefix stmt))
         (vars (car pre)) (stated (cadr pre))
         (facts (st--derive vars stated))
         (derived (filter (lambda (y) (and (not (eq? (st--fact-rule y) 'stated))
                                           (not (st--intermediate? (st--fact-formula y)))))
                          facts))
         (status (map (lambda (y) (cons y (if check? (st--confirm stmt facts y) 'unchecked))) derived))
         (shown (map car (filter (lambda (p) (not (eq? (cdr p) #f))) status)))
         (failed (map car (filter (lambda (p) (eq? (cdr p) #f)) status))))
    (list
     (map (lambda (v)
            (let* ((st (filter (lambda (f) (st--occurs? v f)) stated))
                   (en (filter (lambda (y) (st--occurs? v (st--subject (st--fact-formula y)))) shown))
                   (own (filter (lambda (f) (and (st--typing? f) (equal? (cadr f) v)))
                                (append st (map st--fact-formula en))))
                   (uses (st--dedup (filter (lambda (u) (not (memq (car u) '(IN = == AND OR NOT IFF IMPLIES FORALL FORSOME))))
                                            (st--uses-of v stmt))))
                   (views (filter st--view-of uses))
                   (missing (filter (lambda (u)
                                      (let ((src (symbol-append 'IS- (view-as-source-struct (st--view-of u)))))
                                        (not (find-first (lambda (f) (equal? f (list src v)))
                                                         (append stated (map st--fact-formula shown))))))
                                    views)))
              (list v st en (null? own) missing uses)))
          vars)
     failed)))

(define (st--name v) (string-downcase (symbol->string v)))
(define (st--commas strs) (if (null? strs) "" (apply string-append (cdr (append-map (lambda (x) (list ", " x)) strs)))))

(define (st--view-note v u)
  (let ((vw (st--view-of u)))
    (string-append (expression->string (list (symbol-append 'IS- (view-as-source-struct vw)) v))
                   " is not given by the view: " (st--name (view-as-name vw))
                   " only reads its slots (" (st--commas (map st--name (view-as-source-comps vw)))
                   "), and its typing axiom runs from " (st--name (symbol-append 'IS- (view-as-source-struct vw)))
                   " to " (st--name (symbol-append 'IS- (view-as-target-struct vw))) ", not back.")))

;;; With no argument: the statement of the proof in progress.
(define (implied-types . args)
  (let* ((x (if (and (pair? args) (not (memq (car args) '(no-check)))) (car args)
                (begin (if (not *ps*) (error "implied-types: no proof in progress, and no statement given"))
                       (wff-formula (sequent-node-assertion (proof-state-root *ps*))))))
         (opt (if (and (pair? args) (not (memq (car args) '(no-check)))) (cdr args) args))
         (stmt (st--raw x))
         (an (st--analyse stmt (not (memq 'no-check opt))))
         (failed (cadr an)))
    (define (line . parts) (for-each display parts) (newline))
    (line (if (symbol? x) (string-append "Implied types of " (st--name x) ":") "Implied types:"))
    (for-each
     (lambda (row)
       (let ((v (car row)) (st (cadr row)) (en (caddr row)) (untyped? (cadddr row))
             (missing (list-ref row 4)) (uses (list-ref row 5)))
         (line "")
         (line "  " (st--name v))
         (for-each (lambda (f) (line "    stated     " (expression->string f))) st)
         (for-each (lambda (y) (line "    entailed   " (expression->string (st--fact-formula y))
                                     "      [" (st--rule-text y) "]"))
                   en)
         (if untyped?
             (begin
               (line "    NO TYPING FOUND: none of " (st--name v)
                     " is stated, and the rules (law, view, functor, transport) derive none.")
               (if (pair? uses)
                   (line "      It occurs only as an argument of: " (st--commas (map expression->string uses))))
               (for-each (lambda (u) (line "      " (st--view-note v u))) missing)))))
     (car an))
    (if (pair? failed)
        (begin
          (line "")
          (line "  NOT CONFIRMED (derived, but the scratch proof did not close; a defect of this procedure or of the rule):")
          (for-each (lambda (y) (line "    " (expression->string (st--fact-formula y)) "      [" (st--rule-text y) "]"))
                    failed)))
    (list (map (lambda (row) (list (car row) (cadr row) (map st--fact-formula (caddr row))
                                   (cadddr row) (list-ref row 4)))
               (car an))
          (map st--fact-formula failed))))

;;; ---------------------------------------------------------------------------
;;; The TeX block for display-proof 'with-types: per variable, its own typings (stated,
;;; then confirmed), the structure predicates on terms built from it, and for a variable
;;; with none, the read-off equations that constrain it and the view note.  Rendered
;;; inside the reader's renaming (*tex-variable-names*), so the letters match the
;;; proposition's.
(define (st--tex f) (string-append "$" (expr->tex-top f) "$"))

(define (st--rule-tex y)
  (case (st--fact-rule y)
    ((law) (string-append "by the definition of \\texttt{" (proof-tex--escape-tt (st--name (st--fact-source y))) "}"))
    ((view) (string-append "read off the view \\texttt{" (proof-tex--escape-tt (st--name (st--fact-source y))) "}"))
    ((functor) (string-append "by \\texttt{" (proof-tex--escape-tt (st--name (st--fact-source y))) "}"))
    ((transport) (string-append "from " (st--tex (car (st--fact-parents y))) " and " (st--tex (cadr (st--fact-parents y)))))
    (else "")))

(define (implied-types-tex stmt)
  (let* ((an (st--analyse stmt #t)))
    (define (item row)
      (let* ((v (car row)) (st (cadr row)) (en (caddr row)) (untyped? (cadddr row))
             (missing (list-ref row 4))
             (own-st (filter (lambda (f) (and (st--typing? f) (equal? (cadr f) v))) st))
             (own-en (filter (lambda (y) (let ((f (st--fact-formula y)))
                                           (or (and (st--typing? f) (equal? (cadr f) v))
                                               (and (not untyped?) (st--structure-pred? f) (pair? (cadr f))))))
                             en))
             (eqs (if untyped? (filter (lambda (y) (eq? (st--fact-rule y) 'view)) en) '())))
        (string-append
         "\\item " (st--tex v) ": "
         (if untyped?
             (string-append
              "\\emph{no typing of " (st--tex v) " is stated or derived.}"
              (if (pair? eqs)
                  (string-append " The statement constrains only its slots: "
                                 (st--commas (map (lambda (y) (st--tex (st--fact-formula y))) eqs)) ".")
                  "")
              (apply string-append
                     (map (lambda (u)
                            (let ((vw (st--view-of u)))
                              (string-append
                               " " (st--tex (list (symbol-append 'IS- (view-as-source-struct vw)) v))
                               " does not follow: the view \\texttt{" (proof-tex--escape-tt (st--name (view-as-name vw)))
                               "} reads only these slots, and its typing axiom \\texttt{"
                               (proof-tex--escape-tt (st--name (symbol-append (view-as-name vw) '-is- (view-as-target-struct vw))))
                               "} runs from " (st--tex (list (symbol-append 'IS- (view-as-source-struct vw)) v))
                               " to the view, not back.")))
                          missing)))
             (string-append
              (st--commas (append (map (lambda (f) (string-append (st--tex f) " (stated)")) own-st)
                                  (map (lambda (y) (string-append (st--tex (st--fact-formula y)) " (" (st--rule-tex y) ")"))
                                       own-en)))
              "."))
         "\n")))
    (string-append
     "\\paragraph{Types of the variables.} {\\small Each line is confirmed by a scratch proof from the hypotheses "
     "(\\texttt{implied-types}).}\n"
     "\\begin{itemize}\\small\\sloppy\n"
     (apply string-append (map item (car an)))
     "\\end{itemize}\n")))

;;; the printed report as a string (the workspace's "Implied Types..." reads it)
(define (implied-types-string . args)
  (with-output-to-string (lambda () (apply implied-types args))))
