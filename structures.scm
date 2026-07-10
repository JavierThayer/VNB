;;; structures.scm -- mathematical structure definitions
;;;
;;; (def-structure name slots axiom-names)
;;;
;;;   name        — symbol, e.g. 'NORMEDSPACE
;;;   slots       — list of (NAME KIND . EXTRA) entries in DECLARATION ORDER:
;;;                   (NAME carrier)
;;;                   (NAME op DOMAIN RANGE)
;;;                   (NAME constant SET)
;;;                 Carrier and op accessor names appear bare in domain/range;
;;;                 def-structure expands them to (ACCESSOR s) automatically.
;;;   axiom-names — list of (PROPERTY accessor ...) clauses: each names a
;;;                 characteristic law (operation-properties.scm) and the
;;;                 accessors it constrains, e.g. (is-associative MUL A).
;;;                 build-is-axiom folds them into the IS-NAME definition.
;;;
;;; Most callers use the surface form `def-structure-from-clauses` (or
;;; the syntax `declare-structure`), which parses `(carriers ...)`, `(op ...)`,
;;; `(constant ...)`, and `(property ...)` clauses into the slot list.
;;;
;;; Auto-generates:
;;;   Accessor macetes (one per slot, indexed by position in declaration order):
;;;     (ACCESSOR s)  ->  (NTH k s)   for k = 1, 2, ..., n
;;;   Declaration order matters: two structures may share an accessor name
;;;   only if it sits at the same slot index in both (the install is global).
;;;   E.g. FIELD declares (carriers A), then ops ADD MUL NEG, then constants
;;;   ZERO ONE, then (carriers NON-ZERO) and (op INV ...) -- so ADD/MUL/NEG/
;;;   ZERO/ONE keep the same indices they have under RING.
;;;   IS-NAME definitional axiom in *current-theory* -- SHAPE plus the named
;;;   characteristic laws, so IS-NAME genuinely means "is an X", not merely
;;;   "has the X-shape":
;;;     (FORALL s (IFF (IS-NAME s)
;;;                    (AND (= (LENGTH s) n)
;;;                         (IN (carrier1 s) SET)
;;;                         ...
;;;                         (IN (op1 s) (FUN domain1 range1))
;;;                         ...
;;;                         (property1 (accA s) ...)        ; from axiom-names
;;;                         ...)))
;;;   NAME-class axiom in *current-theory*:
;;;     (FORALL s (IFF (IN s NAME) (IS-NAME s)))
;;;   so the bare symbol NAME is usable as a class in bounded quantification.
;;;
;;; -----------------------------------------------------------------------
;;; What a structure name denotes, and why operations over it are functoids
;;;
;;; A structure *species* -- the symbol NAME (ABELIAN-GROUP, RING, ...) -- is
;;; not itself a structure.  By the NAME-class axiom above it denotes the
;;; **proper class** { s | IS-NAME(s) }.  It is proper, not a set: there are,
;;; e.g., abelian groups of unboundedly large carrier, so the collection of
;;; all of them is too big to be a set.
;;;
;;; An individual structure -- an `ag` with IS-ABELIAN-GROUP(ag) -- is just a
;;; VNB list (a tuple) of LENGTH n.  The accessors are literally projections:
;;; (CARR ag) = (NTH 1 ag), (MUL ag) = (NTH 2 ag), and so on.  The IS-NAME axiom
;;; is exactly the shape constraint: right length, carriers are sets, ops land
;;; in the declared FUN classes.
;;;
;;; Consequence for any operation defined over a structure argument -- e.g.
;;; SUM-AG(ag, f, n) in sequences.scm.  Such an operation is a **functoid** (a
;;; syntactic term-former with defining rewrite rules), never a VNB function
;;; (a set of ordered pairs).  Two independent reasons:
;;;
;;;   1. Proper-class argument.  Its structure argument ranges over NAME, a
;;;      proper class.  A VNB function is a set; its domain must be a set.
;;;
;;;   2. Dependent codomain.  SUM-AG(ag,f,n) lands in (CARR ag) -- the result
;;;      class depends on the argument.  FUN(X,Y) needs fixed X,Y; it cannot
;;;      express a codomain that varies with the input.
;;;
;;; So a "signature" like  ABELIAN-GROUP x FUN(NN,CARR(ag)) x NN -> CARR(ag)  is
;;; informal shorthand, not a VNB object: a functoid has no membership type.
;;; What is real is a conditional **typing theorem** -- e.g. sum-ag-type:
;;;   IS-ABELIAN-GROUP(ag) AND f in FUN(NN,CARR(ag)) AND n in NN
;;;     ==> SUM-AG(ag,f,n) in CARR(ag).
;;; The term (SUM-AG ag f n) is well-formed for any arguments; it denotes
;;; something well-behaved only when those hypotheses hold (VNB partiality).

;;; A structure-def stores its slots in a single list, in declaration order.
;;; Each slot entry is (NAME KIND . EXTRA) where KIND ∈ {carrier, op, constant}:
;;;     carrier:   (NAME carrier)
;;;     op:        (NAME op DOMAIN RANGE)
;;;     constant:  (NAME constant SET)
;;; The accessor index of NAME is its position in this list (1-based), so
;;; declaration order controls which (NTH k s) reduction (NAME s) gets.  This
;;; lets a structure with extra slots (e.g. FIELD = RING + NON-ZERO + INV)
;;; keep the shared accessor indices stable, avoiding collision with the
;;; parent structure's global accessor macetes.
(define-record-type <structure-def>
  (%make-structure-def name slots axiom-names source-file)
  structure-def?
  (name         structure-def-name)
  (slots        structure-def-slots)        ; list of (name kind . extra) in declaration order
  (axiom-names  structure-def-axiom-names)
  (source-file  structure-def-source-file))   ; pathname (or #f) captured at declaration

;;; Backward-compat derived accessors.  Both list slots in declaration order
;;; (filtered by kind).
(define (structure-def-carriers sd)
  (let loop ((rest (structure-def-slots sd)) (acc '()))
    (cond
      ((null? rest) (reverse acc))
      ((eq? (cadar rest) 'carrier)
       (loop (cdr rest) (cons (caar rest) acc)))
      (else (loop (cdr rest) acc)))))

(define (structure-def-op-specs sd)
  ;; Re-emit each op/constant slot in the old shape:
  ;;   (NAME DOMAIN RANGE) for ops, (NAME SET) for constants.
  (let loop ((rest (structure-def-slots sd)) (acc '()))
    (cond
      ((null? rest) (reverse acc))
      ((memq (cadar rest) '(op constant))
       (loop (cdr rest) (cons (cons (caar rest) (cddar rest)) acc)))
      (else (loop (cdr rest) acc)))))

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
;;; `properties' is the axiom-names list: each entry is (NAME accessor ...),
;;; a named operation-property (operation-properties.scm) applied to the
;;; structure's accessors.  It becomes the conjunct (NAME (acc1 s) ...) of
;;; the IS-X definition, so IS-X carries the structure's characteristic
;;; laws, not just its shape.
(define (build-is-axiom struct-name slots properties)
  (let* ((ivar          's)
         (all-accessors (map car slots))
         (is-name       (symbol-append 'IS- struct-name))
         (n             (length slots))
         (property-conjuncts
          (map (lambda (prop)
                 (cons (car prop)
                       (map (lambda (a) (expand-accessors a all-accessors ivar))
                            (cdr prop))))
               properties))
         (slot-conjuncts
          ;; Emit one membership conjunct per slot, in declaration order.
          ;; Carriers use the (IN _ SET) form (no separate SET(_) predicate).
          (map (lambda (slot)
                 (let ((name (car slot)) (kind (cadr slot)))
                   (case kind
                     ((carrier)
                      `(IN (,name ,ivar) SET))
                     ((op)
                      (let ((dom (expand-accessors (caddr  slot) all-accessors ivar))
                            (rng (expand-accessors (cadddr slot) all-accessors ivar)))
                        `(IN (,name ,ivar) (FUN ,dom ,rng))))
                     ((constant)
                      (let ((set (expand-accessors (caddr slot) all-accessors ivar)))
                        `(IN (,name ,ivar) ,set)))
                     ;; A substructure slot is typed by its structure predicate:
                     ;; (substructure K FIELD) -> conjunct (IS-FIELD (K s)).
                     ((substructure)
                      (let ((type (caddr slot)))
                        `(,(symbol-append 'IS- type) (,name ,ivar))))
                     (else
                      (error "build-is-axiom: unknown slot kind" kind slot)))))
               slots))
         (conjuncts
          (cons `(= (LENGTH ,ivar) ,n)
                (append slot-conjuncts property-conjuncts)))
         (body (conjuncts->and conjuncts)))
    `(FORALL ,ivar (IFF (,is-name ,ivar) ,body))))

(define (conjuncts->and cs)
  (cond
    ((null? cs)        'TRUTH)
    ((null? (cdr cs))  (car cs))
    (else              `(AND ,(car cs) ,(conjuncts->and (cdr cs))))))

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

(define (def-structure name slots axiom-names)
  (fluid-let ((*current-provenance* 'definitional))
   (let* ((source (current-load-pathname))   ; #f when not in a load context
         (sd (%make-structure-def name slots axiom-names source)))
    (hash-table-set! *structure-table* name sd)
    ;; Walk slots in declaration order: each slot's position is its accessor
    ;; index, regardless of whether it's a carrier, op, or constant.
    (let loop ((rest slots) (k 1))
      (unless (null? rest)
        (let ((slot-name (caar rest)))
          (register-constant! slot-name 'accessor)
          (install-accessor-macete! slot-name k)
          (loop (cdr rest) (+ k 1)))))
    ;; IS-NAME definitional axiom (shape + the named characteristic laws)
    (let ((is-name (symbol-append 'IS- name))
          (axiom   (build-is-axiom name slots axiom-names)))
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
    name)))

;;; -----------------------------------------------------------------------
;;; declare-structure — user-facing syntax (no quoting required)
;;;
;;; (declare-structure NAME
;;;   (carriers C1 C2 ...)
;;;   (op OPNAME DOMAIN RANGE)       ; OPNAME(s) ∈ FUN(DOMAIN, RANGE)
;;;   (constant CNAME SET)           ; element of SET (uses 2-arg spec internally)
;;;   (property PRED ACC ...))       ; characteristic law PRED applied to ACCs
;;;
;;; DOMAIN is a class expression: a carrier/op accessor name, or a compound
;;; like (CARTESIAN A A) for a binary operation.  No auto-tupling: every VNB
;;; function is unary on its domain; write the Cartesian product explicitly.
;;;
;;; --- Curried/tupled apply convention ---
;;; An op declared as `(op MUL (CARTESIAN A A) A)` is typed as the unary
;;; function `(MUL s) ∈ FUN(CARTESIAN(CARR(s), CARR(s)), CARR(s))` — its single
;;; argument is an element of CARTESIAN(A,A).  But the string-syntax form
;;;     mul(s)(a, b)
;;; parses into the curried S-expression
;;;     ((MUL s) a b)
;;; — a 3-element apply, not the unary apply ((MUL s) (LIST a b)).
;;; The two forms are reconciled by the `apply-tupling-N` axioms
;;; (theorem-library/axioms.scm):
;;;     (f a_1 ... a_n)  =  (f (LIST a_1 ... a_n))
;;; See those axioms' comment for the full story; see the manual
;;; (ch-defs.tex §def-structure, ch-expressions.tex §Function application,
;;; ch-proofs.tex §curried two-argument application) for the user-facing
;;; account.
;;;
;;; A (property PRED ACC ...) clause names a characteristic law from
;;; operation-properties.scm (is-associative, is-commutative, is-identity,
;;; has-inverses, is-distributive, is-metric) and the accessors it
;;; constrains; build-is-axiom folds (PRED (ACC s) ...) into the IS-NAME
;;; definition.  So IS-NAME means "is an X", not just "is X-shaped" --- and
;;; a richer structure (e.g. ABELIAN-GROUP = GROUP + is-commutative) is a
;;; genuine sub-predicate of its parent.  Equational law axioms may still be
;;; added by separate theory-add-axiom! calls; with the laws now in IS-NAME
;;; those are redundant restatements, kept only for direct use by name.

(define-syntax declare-structure
  (syntax-rules ()
    ((_ name clause ...)
     (def-structure-from-clauses 'name (list 'clause ...)))))

;;; A (property NAME accessor ...) clause names a characteristic law from
;;; operation-properties.scm and the accessors it constrains; collected into
;;; the axiom-names list and folded into IS-NAME by build-is-axiom.
(define (def-structure-from-clauses name clauses)
  ;; Build the slot list in declaration order.  A (carriers C1 C2 ...) clause
  ;; contributes one carrier slot per name, in left-to-right order.  Op and
  ;; constant clauses each contribute one slot.  Property clauses contribute
  ;; to the props list, not slots.
  (let loop ((rest clauses) (slots '()) (props '()))
    (if (null? rest)
        (def-structure name (reverse slots) (reverse props))
        (let* ((clause (car rest))
               (kind   (car clause)))
          (cond
            ((eq? kind 'carriers)
             (loop (cdr rest)
                   (append (map (lambda (c) (list c 'carrier))
                                (reverse (cdr clause)))
                           slots)
                   props))
            ((eq? kind 'op)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'op (caddr clause) (cadddr clause))
                         slots)
                   props))
            ((eq? kind 'constant)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'constant (caddr clause)) slots)
                   props))
            ;; (substructure NAME TYPE) -- the slot holds a whole structure
            ;; (e.g. a vector space's base FIELD), typed by IS-TYPE rather than
            ;; the bare (IN _ SET) of a carrier.  Op signatures reach into it
            ;; with foreign accessors, e.g. (op SMUL (CARTESIAN (CARR K) V) V) --
            ;; expand-accessors leaves A intact and rewrites K to (K s), giving
            ;; (CARR (K s)) = the carrier of the base field.
            ((eq? kind 'substructure)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'substructure (caddr clause)) slots)
                   props))
            ((eq? kind 'property)
             (loop (cdr rest) slots (cons (cdr clause) props)))
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

;; Catalog registry: name -> (list params body source-file).  *constant-registry*
;; records only the KIND tag, so functoids are otherwise invisible to the
;; reference docs (unlike def-constant/def-predicate, which land in
;; DEFINITIONS.md).  This lets (write-functoids-md) list them with their
;; unfolding bodies.  def-view-as functoids are recorded here too, but the
;; catalog writer filters them out via lookup-view-as (they have their own
;; STRUCTURE-INDEX section).
(define *functoid-registry* (make-equal-hash-table))

(define (def-functoid name params body)
  ;; A functoid is a DEFINITION: its unfold macete rewrites the defined symbol
  ;; to its body and so carries no logical debt.  Stamp it `definitional' (as
  ;; def-predicate does), otherwise its provenance defaults to `asserted' and a
  ;; mere unfold (e.g. `mac COMPOSE') shows up as an outstanding asserted leaf
  ;; in the proof-debt ledger -- a phantom debt.
  (fluid-let ((*current-provenance* 'definitional))
    (let* ((pvars (if (pair? params) params (list params))))
      (install-macete! name
        (make-elementary-macete pvars '() (cons name pvars) body))
      (register-provenance! name *current-provenance*)
      (register-constant! name 'functoid)
      (hash-table-set! *functoid-registry* name
        (list pvars body (current-load-pathname)))
      name)))

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
;;;   (def-predicate 'IS-CAUCHY-SEQ '(PTS f) '(AND ... ))

(define (def-predicate pred-name params body)
  (fluid-let ((*current-provenance* 'definitional))
   (let* ((app     `(,pred-name ,@params))
         (iff     `(IFF ,app ,body))
         (formula (fold-right (lambda (p f) `(FORALL ,p ,f)) iff params)))
    (theory-add-definition! *current-theory* pred-name
      (list (cons pred-name formula))))))

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

;;; -----------------------------------------------------------------------
;;; def-view-as -- declare one structure as a view of another
;;;
;;; (def-view-as NAME
;;;   SOURCE-STRUCT  (src-comp-1 src-comp-2 ... src-comp-n)
;;;   TARGET-STRUCT  (tgt-slot-1 tgt-slot-2 ... tgt-slot-n))
;;;
;;; A view-as is a FORGETFUL FUNCTOR, in exactly two cases: it forgets SHAPE
;;; (the source list is a sub-list of the source's slots -- some slots drop)
;;; and/or forgets PROPERTIES (the target's IS-X folds fewer laws than the
;;; source's).  The source list is written in the TARGET's coordinate order,
;;; which is all "reshuffle" / "re-carrier" amount to -- not extra functor
;;; kinds.  Non-forgetful functors (quotient, completion) are constructions,
;;; not views; they are plain def-functoids.
;;;
;;; Example:
;;;   (def-view-as RING-ADDITIVE-AG
;;;     RING          (CARR ADD NEG ZERO)
;;;     ABELIAN-GROUP (CARR MUL INV E))
;;;
;;; Reads as: given a RING r, build the ABELIAN-GROUP-shaped object whose A
;;; slot is r's A, MUL slot is r's ADD, INV slot is r's NEG, E slot is r's
;;; ZERO.  The TARGET component list must equal the target structure's slot
;;; order (the same order in which the target was declared); the form
;;; checks this.
;;;
;;; Installs three things:
;;;   1. A functoid (NAME r) whose defining equation is
;;;        (NAME r) = (LIST (src-comp-1 r) ... (src-comp-n r))
;;;   2. The typing axiom
;;;        forall r. IS-SOURCE(r) => IS-TARGET((NAME r))
;;;      named  <name>-is-<target>  (e.g. ring-additive-ag-is-abelian-group)
;;;      *Installed as an axiom*, not proved.  Per library-build policy: leave
;;;      results as axioms; promotion to proven theorem is a separate task.
;;;   3. Auto-specializations: for every theorem of the form
;;;        forall s. IS-TARGET(s) => P[s]
;;;      currently in *theorem-table*, install
;;;        forall r. IS-SOURCE(r) => P[s := (NAME r)]
;;;      with target-slot accessors reduced to source components (so
;;;      `(MUL (NAME r))` becomes `(ADD r)`, etc.).  Named
;;;        <original-thm>-<lowered-view-name>
;;;
;;; The view declaration is recorded in *view-as-table* so the catalog /
;;; Emacs browser can index it.

(define-record-type <view-as>
  (%make-view-as name source-struct source-comps target-struct target-comps source-file)
  view-as?
  (name           view-as-name)
  (source-struct  view-as-source-struct)
  (source-comps   view-as-source-comps)
  (target-struct  view-as-target-struct)
  (target-comps   view-as-target-comps)
  (source-file    view-as-source-file))   ; pathname (or #f) of the def-view-as call site

(define *view-as-table* (make-equal-hash-table))

(define (lookup-view-as name)
  (hash-table-ref/default *view-as-table* name #f))

(define (structure-slot-names sd)
  (map car (structure-def-slots sd)))

;;; Replace `(tgt-slot (view-name r-sym))` with `(src-comp r-sym)` throughout
;;; expr, using slot->comp alist.  Walks the full cons tree; safe on atoms.
(define (view-as-reduce-accessors expr view-name slot->comp r-sym)
  (cond
    ((and (pair? expr)
          (= (length expr) 2)
          (pair? (cadr expr))
          (= (length (cadr expr)) 2)
          (eq? (car  (cadr expr)) view-name)
          (eq? (cadr (cadr expr)) r-sym)
          (assq (car expr) slot->comp))
     `(,(cdr (assq (car expr) slot->comp)) ,r-sym))
    ((pair? expr)
     (cons (view-as-reduce-accessors (car expr) view-name slot->comp r-sym)
           (view-as-reduce-accessors (cdr expr) view-name slot->comp r-sym)))
    (else expr)))

;;; Specialize every theorem  (FORALL s (IMPLIES (IS-TARGET s) P[s]))
;;; via the view, installing  (FORALL r (IMPLIES (IS-SOURCE r) P[(NAME r)]))
;;; with accessor reduction.  Called once at def-view-as time; can be re-run
;;; manually after adding new TARGET theorems via (view-as-auto-specialize! 'NAME).
;;; companion name -> the TARGET-structure theorem it was specialized from.
;;; Read by debt-of (proof-debt.scm): a companion's bill is its source's bill.
(define *view-specialized-source* (make-equal-hash-table))
(define (view-specialized-source name)
  (hash-table-ref/default *view-specialized-source* name #f))

(define (view-as-auto-specialize! view-name)
  (fluid-let ((*current-provenance* 'definitional))
   (let* ((v          (or (lookup-view-as view-name)
                         (error "view-as-auto-specialize!: unknown view"
                                view-name)))
         (is-src     (symbol-append 'IS- (view-as-source-struct v)))
         (is-tgt     (symbol-append 'IS- (view-as-target-struct v)))
         (slot->comp (map cons
                          (view-as-target-comps v)
                          (view-as-source-comps v)))
         (suffix     (string->symbol
                      (string-append "-"
                       (string-downcase (symbol->string view-name)))))
         (r-sym      'r)
         (count      0)
         (all        (hash-table->alist *theorem-table*)))
    (for-each
      (lambda (entry)
        (let* ((thm-name (car entry))
               (formula  (cdr entry))
               (match    (generic-for-struct? formula is-tgt)))
          (when match
            (let* ((s         (car match))
                   (p-body    (cdr match))
                   (p-sub     (subst-free s `(,view-name ,r-sym) p-body))
                   (p-reduced (view-as-reduce-accessors
                                p-sub view-name slot->comp r-sym))
                   (new-formula
                    `(FORALL ,r-sym
                       (IMPLIES (,is-src ,r-sym) ,p-reduced)))
                   (new-name (symbol-append thm-name suffix)))
              (unless (hash-table-ref/default *theorem-table* new-name #f)
                (theory-add-axiom! *current-theory* new-name new-formula)
                ;; Record where this companion came from.  It is stamped
                ;; `definitional' (the fluid-let above) because the TRANSPORT is
                ;; definitional -- but the transported CONTENT is only as trusted
                ;; as thm-name.  Without this table, citing an asserted structure
                ;; law through its view companion would report zero debt; see
                ;; debt-of in proof-debt.scm.
                (hash-table-set! *view-specialized-source* new-name thm-name)
                (set! count (+ count 1)))))))
      all)
    (display ";; def-view-as ") (display view-name) (display ": ")
    (display count) (display " ")
    (display (view-as-target-struct v))
    (display " theorems specialized.") (newline)
    count)))

;;; Walk up the definitional-structure parent chain to find the underlying
;;; shape (i.e. def-structure-from-clauses) structure-def.  Definitional
;;; structures (COMMUTATIVE-RING, FIELD, …) share the shape of their parent,
;;; so a view-as FROM a definitional structure uses its ancestor's slots.
(define (find-shape-structure name)
  (or (lookup-structure name)
      (let ((dsd (lookup-definitional-structure name)))
        (and dsd (find-shape-structure
                  (definitional-structure-parent dsd))))))

(define (def-view-as name source-struct source-comps target-struct target-comps)
  (fluid-let ((*current-provenance* 'definitional))
  ;; Validation — source/target may be shape OR definitional structures;
  ;; in the latter case we walk up to the ancestor shape for the slot list.
  (let ((src-def (find-shape-structure source-struct))
        (tgt-def (find-shape-structure target-struct)))
    (unless src-def
      (error "def-view-as: unknown source structure" source-struct))
    (unless tgt-def
      (error "def-view-as: unknown target structure" target-struct))
    (unless (= (length source-comps) (length target-comps))
      (error "def-view-as: source/target component lists differ in length"
             source-comps target-comps))
    ;; Target components must equal the target's slot order exactly --
    ;; the form is self-documenting *and* self-checking.
    (let ((tgt-slots (structure-slot-names tgt-def)))
      (unless (equal? target-comps tgt-slots)
        (error "def-view-as: target components must equal target slot order"
               'got: target-comps 'expected: tgt-slots)))
    ;; Source components must all be valid accessors of source-struct.
    (let ((src-slots (structure-slot-names src-def)))
      (for-each (lambda (c)
                  (unless (member c src-slots)
                    (error "def-view-as: not a source accessor" c
                           'source-struct: source-struct
                           'source-slots: src-slots)))
                source-comps)))
  ;; Record the view.
  (hash-table-set! *view-as-table* name
    (%make-view-as name source-struct source-comps target-struct target-comps
                   (current-load-pathname)))
  ;; Functoid: (NAME r) = (LIST (c1 r) ... (cn r)).
  (def-functoid name '(r)
    `(LIST ,@(map (lambda (c) `(,c r)) source-comps)))
  ;; Typing axiom: forall r. IS-SOURCE(r) => IS-TARGET((NAME r)).
  (let ((is-src  (symbol-append 'IS- source-struct))
        (is-tgt  (symbol-append 'IS- target-struct))
        (ax-name (symbol-append name '-is- target-struct)))
    (theory-add-axiom! *current-theory* ax-name
      `(FORALL r (IMPLIES (,is-src r) (,is-tgt (,name r))))))
  ;; Auto-specialize target theorems.
  (view-as-auto-specialize! name)
  name))

;;; -----------------------------------------------------------------------
;;; Definitional structures
;;;
;;; A *definitional structure* is one whose IS-X is not a shape predicate
;;; (def-structure-from-clauses) but a genuine IFF axiom
;;;
;;;   (FORALL s (IFF (IS-X s) (AND (IS-PARENT s) <extra constraints>)))
;;;
;;; declared in the source file as `(theory-add-axiom! ... 'is-X-def ...)`
;;; alongside a sibling relation axiom `X-is-parent`.  COMMUTATIVE-RING,
;;; INTEGRAL-DOMAIN, FIELD, EUCLIDEAN-RING, NORMED-FIELD are declared this
;;; way (reusing RING's 6-slot shape with extra properties; see the comment
;;; at the top of commutative-ring.scm).
;;;
;;; `register-definitional-structure!` exposes these to the navigation
;;; index (structure-index in interactive.scm) without changing how the
;;; predicates themselves are declared.  Call it from the same file as the
;;; `is-X-def` axiom; `(current-load-pathname)` captures the source.

(define-record-type <definitional-structure>
  (%make-definitional-structure name parent source-file)
  definitional-structure?
  (name         definitional-structure-name)
  (parent       definitional-structure-parent)     ; e.g. 'RING for COMMUTATIVE-RING
  (source-file  definitional-structure-source-file))

(define *definitional-structure-table* (make-equal-hash-table))

(define (lookup-definitional-structure name)
  (hash-table-ref/default *definitional-structure-table* name #f))

(define (register-definitional-structure! name parent)
  (hash-table-set! *definitional-structure-table* name
    (%make-definitional-structure name parent (current-load-pathname)))
  name)

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
