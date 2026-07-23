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
;;; Nothing in the library calls this directly.  The surface is the macro
;;; `declare-structure`, which expands to the procedure
;;; `def-structure-from-clauses`; that parses `(carriers ...)`, `(op ...)`,
;;; `(constant ...)`, `(derived ...)`, `(substructure ...)`, `(property ...)`
;;; and `(law ...)` clauses into the slot list.  The two are the same thing:
;;; the macro exists only to spare the caller the quoting.
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
;;; (CARR ag) = (NTH 1 ag), (OPR ag) = (NTH 2 ag), and so on.  The IS-NAME axiom
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
;;; Carriers, INCLUDING the derived ones (NON-ZERO is a carrier -- it is just
;;; not an independent one).  The hom generator wants the independent ones only,
;;; and asks for kind `carrier' directly.
(define (structure-def-carriers sd)
  (let loop ((rest (structure-def-slots sd)) (acc '()))
    (cond
      ((null? rest) (reverse acc))
      ((memq (cadar rest) '(carrier derived))
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

;;; -----------------------------------------------------------------------
;;; The DECLARATION, kept verbatim.
;;;
;;; Everything else here stores the EXPANSION of a declaration -- the slot
;;; list, the IS-X axiom.  Neither can be printed back to the reader: the
;;; expansion of COMMUTATIVE-RING is a six-conjunct IFF over `s' whose one
;;; interesting clause is buried in it, and the pretty-printer that used to
;;; unbury it (destructure-isx-expr, interactive.scm) did so by inventing
;;; bound variables NAMED AFTER THE ACCESSORS -- printing a string that reads
;;; back, through the scope-blind head registry, as a different formula.
;;; What a reader wants is the two lines that were actually written:
;;;
;;;   (declare-structure COMMUTATIVE-RING
;;;     (same-shape-as RING)
;;;     (law "forall([a in carr(s), b in carr(s)], mul(s)(a, b) = mul(s)(b, a))"))
;;;
;;; so we keep them.  def-structure-from-clauses is the single funnel --
;;; `declare-structure' is a macro that expands to it, and nothing else in the
;;; library reaches def-structure directly -- so one hash-table set! there
;;; catches every structure, shape and refinement alike.  Law strings are stored
;;; AS WRITTEN, in surface syntax: they parse.
(define *structure-decl-table* (make-equal-hash-table))

(define (record-structure-declaration! name clauses)
  (hash-table-set! *structure-decl-table* name clauses))

(define (structure-declaration name)
  (hash-table-ref/default *structure-decl-table* name #f))

;;; The declaration as source text, ready to drop into a fenced code block.
;;;
;;; A law is a STRING and must print as one -- but `write' escapes the newlines
;;; of a law written over several lines into a literal \n, which is unreadable
;;; and is not how it appears in the source.  A Scheme string literal may span
;;; lines, so we emit the characters as they were written.  Laws contain no `"'
;;; or `\' (they are surface-syntax formulas), and we escape them anyway rather
;;; than rely on that.
(define (structure--write-clause-datum d)
  (cond
    ((string? d)
     (display "\"")
     (string-for-each (lambda (c)
                        (case c
                          ((#\" #\\) (display "\\") (display c))
                          (else      (display c))))
                      d)
     (display "\""))
    ((pair? d)
     (display "(")
     (let loop ((xs d) (first #t))
       (cond ((null? xs) (display ")"))
             ((not (pair? xs))            ; improper tail
              (display " . ") (structure--write-clause-datum xs) (display ")"))
             (else
              (unless first (display " "))
              (structure--write-clause-datum (car xs))
              (loop (cdr xs) #f)))))
    (else (write d))))

(define (structure-declaration->string name)
  (let ((clauses (structure-declaration name)))
    (and clauses
         (with-output-to-string
           (lambda ()
             (display "(declare-structure ") (display name) (newline)
             (let loop ((cs clauses))
               (unless (null? cs)
                 (display "  ") (structure--write-clause-datum (car cs))
                 (if (null? (cdr cs)) (display ")") (newline))
                 (loop (cdr cs)))))))))

;;; -----------------------------------------------------------------------
;;; ONE NAME, ONE SLOT.
;;;
;;; An accessor macete is keyed by NAME and is GLOBAL: `mul' rewrites (MUL s)
;;; to (NTH k s) for EVERY s, whatever structure s is.  So a name may live at
;;; exactly one index, library-wide.  Three names did not:
;;;
;;;     nrm : normed-ag@5  normed-field@7
;;;     mul : monoid@2 group@2 semigroup@2 abelian-group@2 comm-monoid@2
;;;           normed-ag@2   ...but ring@3 field@3 normed-field@3
;;;     inv : group@4 abelian-group@4 normed-ag@4   ...but field@8
;;;
;;; Only one rewrite survives per name (the last structure to declare it wins),
;;; and it is then WRONG for every other structure.  This was not theoretical:
;;; `mul' held the group family's index 2, so
;;;
;;;     (mac 'mul) on (MUL ZZ-RING)  -->  (NTH 2 ZZ-RING)  -->  binplus
;;;
;;; and the checker would take `mul(zz-ring) = binplus' -- the multiplication of
;;; the integers is ADDITION -- all the way to a qed.  (Billed, at least: the
;;; macete appears in the bill as the asserted leaf `mul'.  No library proof ever
;;; cited one, which is why nobody noticed.)  numeric-instances.scm advertises
;;; exactly this computation as a feature.
;;;
;;; So: an accessor name is registered with its index, and a name claimed at a
;;; SECOND index is AMBIGUOUS -- no global reduction can be right for it.  We
;;; install none, and withdraw the one already installed: (mac 'mul) is now an
;;; unknown macete rather than a false one.  `accessor-index-audit' names the
;;; ambiguous accessors, and the test suite pins the list, so a NEW collision --
;;; e.g. a numbered carrier CARRj put at slot j in one structure and slot j' in
;;; another -- fails loudly instead of installing a lie.
;;;
;;; Resolving the three (renaming one side of each, restoring the reductions) is
;;; a separate, deliberate change to library vocabulary.
(define *accessor-index* (make-equal-hash-table))   ; name -> (index . structure)
(define *ambiguous-accessors* (make-equal-hash-table))  ; name -> ((struct . idx) ...)

(define (accessor-ambiguous? name)
  (hash-table-ref/default *ambiguous-accessors* name #f))

;;; Every accessor claimed at more than one slot index, as
;;;   ((name (struct . idx) (struct . idx) ...) ...)
;;; Empty => every accessor name denotes one slot, and every accessor macete is
;;; sound.  Companion to case-fold-audit / constant-binder-audit.
(define (accessor-index-audit)
  (map (lambda (name)
         (cons name (reverse (hash-table-ref/default *ambiguous-accessors* name '()))))
       (sort (hash-table-keys *ambiguous-accessors*)
             (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

;;; Record NAME as living at slot K of structure STRUCT.  Returns #t if the name
;;; is unambiguous (so a global reduction is installable), #f if this claim
;;; collides with an earlier one -- in which case the earlier macete, now known
;;; to be wrong for at least one structure, is WITHDRAWN.
(define (register-accessor-index! name k struct)
  (let ((prev (hash-table-ref/default *accessor-index* name #f)))
    (cond
      ((not prev)
       (hash-table-set! *accessor-index* name (cons k struct))
       (not (accessor-ambiguous? name)))
      ((= (car prev) k)                    ; same slot: consistent, keep it
       (not (accessor-ambiguous? name)))
      (else
       (let ((hits (hash-table-ref/default *ambiguous-accessors* name '())))
         (hash-table-set! *ambiguous-accessors* name
           (cons (cons struct k)
                 (if (null? hits)
                     (list (cons (cdr prev) (car prev)))
                     hits))))
       ;; the installed rewrite is wrong for at least one of the claimants
       (hash-table-delete! *macete-table* name)
       #f))))

;;; Install macete: (accessor s) -> (NTH k s) for any s.
;;;
;;; PROVENANCE: definitional.  (CARR s) = (NTH 1 s) IS the definition of the
;;; accessor -- def-structure mints the name and this equation together, exactly
;;; as def-functoid mints a functoid and its unfold (which is stamped
;;; definitional for the same reason).  Left unstamped it defaults to `asserted',
;;; and every proof that so much as projects a slot picks up a phantom debt leaf
;;; named `carr' -- which is what the functoriality proofs' bills read before
;;; this line existed: "modulo {carr, opr, iden} [trust: none]".
;;;
;;; This is the same channel that billed the FALSE `mul' rewrite, so it is fair
;;; to ask what stops a wrong accessor macete from now being trusted silently.
;;; The answer is the two audits (accessor-index-audit, accessor-type-audit),
;;; both HARD gates in load.scm: an accessor name may denote only one slot, and
;;; may be applied only to a structure that has it.  A wrong one cannot load.
(define (install-accessor-macete! accessor-name k)
  (register-provenance! accessor-name 'definitional)
  (install-macete! accessor-name
    (make-elementary-macete
      '(svar)
      '()
      `(,accessor-name svar)
      `(NTH ,k svar))))

;;; -----------------------------------------------------------------------
;;; INSTANCES: an accessor of a CONCRETE structure reduces to its VALUE.
;;;
;;; (MUL ZZ-RING) MEANS bintimes.  Saying so took three steps -- `slot' to reach
;;; (NTH 3 ZZ-RING), `mac' the tuple equation to expose the list, `nth-r' to
;;; project -- of which the last two are pure bookkeeping: the answer is fixed
;;; the moment the instance is declared, and nothing about a proof can change it.
;;; Worse, the intermediate step puts NTH -- the REPRESENTATION -- in the user's
;;; goal.  Which slot MUL occupies is an implementation fact about the RING
;;; tuple; a reader of the goal should never meet it.
;;;
;;; So declare-instance! does the projection once, at declaration time, and
;;; installs (ACC NAME) -> value_k as a ground macete, one per slot.  `slot'
;;; fires those when the accessor's argument IS an instance, and falls back to
;;; the (NTH k s) reduction for a variable structure -- where there is nothing
;;; to project to, and where the machinery that wants NTH form
;;; (fnc--normalize-goal!) lives.
;;;
;;; THE TUPLE EQUATION IS A DEFINITION, and goes in through def-constant.
;;; (= ZZ-RING (LIST ZZ binplus bintimes binneg 0 1)) is what the name ZZ-RING
;;; MEANS -- nothing else pins it -- so it is `definitional', as rr-ms-def
;;; already was, and not an asserted phantom debt leaf that every proof touching
;;; the integers-as-a-ring had to pay.  The mathematical content of the instance
;;; is IS-RING(ZZ-RING), which stays an asserted axiom and stays billed.
;;;
;;; PROVENANCE IS THEN INHERITED, never invented: the value equation is the tuple
;;; equation plus two definitional steps, so it is worth exactly what the tuple
;;; equation is worth -- read off (provenance-of DEF-AXIOM), not hard-coded.  A
;;; hard-coded `definitional' here would silently launder any instance later
;;; declared on an asserted equation: the def-view-as bug, one level down.
;;;
;;; The length check is a gate, not a convenience: a tuple whose length differs
;;; from its structure's shape cannot satisfy that structure's IS-X (which pins
;;; length(s) = n), and declaring one was a real inconsistency once (the 7-tuple
;;; RR-NORMED-FIELD asserted IS-RING, fixed 2026-05-30).  Now it cannot load.

;; inst -> (struct . ((acc macete-name value) ...))
(define *structure-instances* (make-equal-hash-table))

(define (instance-structure inst)
  (let ((e (hash-table-ref/default *structure-instances* inst #f)))
    (and e (car e))))

;;; The macete (ACC INST) -> value, or #f if INST is not an instance / has no
;;; such slot.  The ONE lookup `slot' uses; nothing else should fire these.
;;; The instance's components, in slot order, or #f if INST is not an instance.
(define (instance-tuple inst)
  (let ((e (hash-table-ref/default *structure-instances* inst #f)))
    (and e (map caddr (cdr e)))))

(define (instance-value-macete inst acc)
  (let ((e (hash-table-ref/default *structure-instances* inst #f)))
    (and e (let ((hit (assq acc (cdr e)))) (and hit (cadr hit))))))

(define (instance-value-macete-name? name)
  (there-exists? (hash-table-values *structure-instances*)
    (lambda (e)
      (there-exists? (cdr e) (lambda (p) (eq? (cadr p) name))))))

;;; ((INST STRUCT (ACC . value) ...) ...) -- what the instances project to.
(define (instance-audit)
  (map (lambda (inst)
         (let ((e (hash-table-ref/default *structure-instances* inst '(#f))))
           (cons* inst (car e)
                  (map (lambda (p) (cons (car p) (caddr p))) (cdr e)))))
       (sort (hash-table-keys *structure-instances*)
             (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

;;; Declare NAME as the STRUCT-shaped tuple TUPLE, defining it by the equation
;;; DEF-AXIOM -- kept under the name it always had, so every existing
;;; (mac 'zz-ring-def) still cites it.
;;;
;;; It also registers NAME as a definitional structure with STRUCT as its parent,
;;; so that every declared instance HAS a card, appears in (known-structures) and
;;; is a node in the structure graph.  RR-MS and CC-MS did not: the six numeric
;;; instances were registered by hand (numeric-instances.scm) and the two metric
;;; spaces were forgotten, so `(describe-structure 'RR-MS)' answered "Unknown
;;; structure" -- for a constant the library proves theorems about.  A later,
;;; deeper registration still overrides this one (ZZ-RING's parent is
;;; EUCLIDEAN-RING, not the RING shape it was declared with); the point is that
;;; forgetting one can no longer LOSE it.
(define (declare-instance! name struct def-axiom tuple)
  (let ((slots (structure-accessor-names struct)))
    (if (not slots)
        (error "declare-instance!: unknown structure" struct))
    (if (not (= (length slots) (length tuple)))
        (error "declare-instance!: tuple length does not match the shape of"
               struct (list 'got (length tuple) 'want (length slots))))
    (def-constant name (list def-axiom `(= ,name (LIST ,@tuple))))
    (register-definitional-structure! name struct)
    (let ((prov (provenance-of def-axiom)))
      (hash-table-set! *structure-instances* name
        (cons struct
              (let loop ((accs slots) (vals tuple) (k 1) (acc '()))
                (if (null? accs)
                    (reverse acc)
                    (let ((mname (symbol-append name '@ (car accs))))
                      (if (hash-table-ref/default *macete-table* mname #f)
                          (error "declare-instance!: macete name already taken" mname))
                      ;; The slot equation goes in as a THEOREM, not as a bare
                      ;; rewrite rule.  install-theorem! builds the same
                      ;; elementary macete from it, so `slot' and `mac' behave
                      ;; exactly as before -- but the hypothesis side now works
                      ;; too: apply-macete-to-assumption! rebuilds its rule from
                      ;; (lookup-theorem name), so a macete that is not a theorem
                      ;; can never rewrite an assumption.  It IS a fact --
                      ;; (ADD ZZ-RING) == binplus is what ZZ-RING MEANS -- and
                      ;; transport! (transport.scm) needs to cite it as one.
                      ;; `==' (not `='): the slot value is unconditionally that
                      ;; term, so no definedness obligation is owed.
                      (fluid-let ((*current-provenance* prov))
                        (install-theorem! mname
                          `(== (,(car accs) ,name) ,(car vals))))
                      (register-provenance! mname prov)
                      (loop (cdr accs) (cdr vals) (+ k 1)
                            (cons (list (car accs) mname (car vals)) acc)))))))))
  name)

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
(define (build-is-axiom struct-name slots properties #!optional laws ivar0)
  (let* ((ivar          (if (default-object? ivar0) 's ivar0))
         (all-accessors (map car slots))
         (is-name       (symbol-append 'IS- struct-name))
         (n             (length slots))
         ;; extra LAWS: raw conjuncts (surface syntax welcome), free variable `s'.
         ;; MODULE's action axioms are of this kind -- no named operation-property
         ;; expresses r.(x+y) = r.x + r.y -- and it used to hand-write its whole
         ;; IS-MODULE IFF for want of them.
         (law-conjuncts (if (default-object? laws)
                            '()
                            (map structure--law->formula laws)))
         (property-conjuncts
          (map (lambda (prop)
                 (cons (car prop)
                       (map (lambda (a) (expand-accessors a all-accessors ivar))
                            (cdr prop))))
               properties))
         (slot-conjuncts
          ;; Emit the membership conjunct(s) per slot, in declaration order.
          ;; Carriers use the (IN _ SET) form (no separate SET(_) predicate).
          ;; A slot may contribute MORE than one conjunct (a derived carrier
          ;; contributes two), so this is append-map, not map: a nested (AND a b)
          ;; inside the conjunct chain would print the same but re-parse
          ;; right-associated, and the docs' round-trip gate rightly rejects that.
          (append-map
           (lambda (slot)
                 (let ((name (car slot)) (kind (cadr slot)))
                   (case kind
                     ((carrier)
                      `((IN (,name ,ivar) SET)))
                     ((op)
                      (let ((dom (expand-accessors (caddr  slot) all-accessors ivar))
                            (rng (expand-accessors (cadddr slot) all-accessors ivar)))
                        `((IN (,name ,ivar) (FUN ,dom ,rng)))))
                     ((constant)
                      (let ((set (expand-accessors (caddr slot) all-accessors ivar)))
                        `((IN (,name ,ivar) ,set))))
                     ;; A DERIVED carrier is a carrier CARVED OUT of another by a
                     ;; defining expression -- FIELD's NON-ZERO = CARR \ {ZERO}.
                     ;; It occupies a tuple slot (so accessor indices are stable),
                     ;; but it is not an independent sort: its value is FIXED by
                     ;; the others, so IS-X says so.  Until 2026-07-12 NON-ZERO was
                     ;; a plain carrier and IS-FIELD said NOTHING relating it to
                     ;; CARR -- a field's NON-ZERO could have been any set at all,
                     ;; the equation living in a separate ASSERTED axiom
                     ;; (field-non-zero-carrier).  A definition should not need a
                     ;; support to finish it.
                     ((derived)
                      (let ((defn (expand-accessors (cadddr slot) all-accessors ivar)))
                        `((IN (,name ,ivar) SET)
                          (= (,name ,ivar) ,defn))))
                     ;; A substructure slot is typed by its structure predicate:
                     ;; (substructure K FIELD) -> conjunct (IS-FIELD (K s)).
                     ((substructure)
                      (let ((type (caddr slot)))
                        `((,(symbol-append 'IS- type) (,name ,ivar)))))
                     (else
                      (error "build-is-axiom: unknown slot kind" kind slot)))))
               slots))
         (conjuncts
          (cons `(= (LENGTH ,ivar) ,n)
                (append slot-conjuncts property-conjuncts law-conjuncts)))
         (body (conjuncts->and conjuncts)))
    `(FORALL ,ivar (IFF (,is-name ,ivar) ,body))))

(define (conjuncts->and cs)
  (cond
    ((null? cs)        'TRUTH)
    ((null? (cdr cs))  (car cs))
    (else              `(AND ,(car cs) ,(conjuncts->and (cdr cs))))))

;;; Build a guarded universal  (FORALL v1..vn. a1 => a2 => ... => concl)  and an
;;; iff-over-a-conjunction  (FORALL v1..vn. IFF(lhs, AND(c1,...,ck)))  from FLAT
;;; lists, so a deep formula is written as data rather than a hand-counted paren
;;; pyramid.  (The recurring miscount is always the same: a right-nested AND/IMPLIES
;;; chain loses its last close.  There is no last close to lose here.)
(define (forall-guarded binders antecedents consequent)
  (nest-quantifiers 'FORALL binders
    (fold-right (lambda (a acc) `(IMPLIES ,a ,acc)) consequent antecedents)))

(define (forall-iff binders lhs conjuncts)
  (nest-quantifiers 'FORALL binders `(IFF ,lhs ,(conjuncts->and conjuncts))))

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

;;; --- the English of a structure predicate, derived from its name -----------
;;;
;;; IS-METRIC-SPACE -> "a is a metric space", and the same entry folds into a
;;; quantifier qualifier ("for every metric space a") because the table stores the
;;; bare NOUN plus its ARTICLE, not a finished sentence (wff-english.scm).
;;;
;;; Derived, never imposed: a `notation!' beside the structure overrides this, and
;;; `english-derived-nouns' lists every predicate still wearing the machine's
;;; wording -- which is where a human goes to write "Euclidean ring" over
;;; "euclidean ring".  A structure declared BEFORE this ran (or re-declared) keeps
;;; whatever a human already said.

(define *derived-structure-nouns* '())      ; is-name ... , in declaration order

(define (english-derived-nouns) (reverse *derived-structure-nouns*))

(define (structure--noun-of name)
  (let loop ((cs (string->list (string-downcase (symbol->string name)))) (acc '()))
    (cond ((null? cs) (list->string (reverse acc)))
          ((char=? (car cs) #\-) (loop (cdr cs) (cons #\space acc)))
          (else (loop (cdr cs) (cons (car cs) acc))))))

(define (structure--article-for phrase)
  (if (and (> (string-length phrase) 0)
           (memv (string-ref phrase 0) '(#\a #\e #\i #\o #\u)))
      "an" "a"))

(define (declare-structure-noun! is-name name)
  (let ((entry (operator-ref is-name)))
    (when (and entry (not (operator-noun entry)) (not (operator-english entry)))
      (let ((phrase (structure--noun-of name)))
        (notation! is-name 'kind 'predicate 'arity 1
                   'noun phrase 'article (structure--article-for phrase))
        (set! *derived-structure-nouns* (cons is-name *derived-structure-nouns*))))))

(define (def-structure name slots axiom-names #!optional laws ivar0)
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
          (register-operator! slot-name 'accessor '(s))
          ;; ONE NAME, ONE SLOT: install the (NAME s) -> (NTH k s) reduction only
          ;; if this name denotes slot k everywhere.  A second index makes it
          ;; ambiguous and the reduction is withdrawn -- see the comment above
          ;; register-accessor-index!.
          (if (register-accessor-index! slot-name k name)
              (install-accessor-macete! slot-name k))
          (loop (cdr rest) (+ k 1)))))
    ;; IS-NAME definitional axiom (shape + the named characteristic laws)
    (let ((is-name (symbol-append 'IS- name))
          (axiom   (build-is-axiom name slots axiom-names
                                   (if (default-object? laws) '() laws)
                                   (if (default-object? ivar0) 's ivar0))))
      (theory-add-axiom! *current-theory* is-name axiom)
      ;; the ONE table (operators.scm): every structure predicate is a unary
      ;; predicate, and def-structure is the only thing that makes one.
      (register-operator! is-name 'predicate '(s))
      ;; ... and it gets its ENGLISH here too.  This used to say "the noun is
      ;; declared with `notation!' beside the structure, since only a human knows
      ;; it" -- and the result was that 104 of 113 predicates had no reading at
      ;; all, so the proof reader said `is-metric-space(a)' where a human says
      ;; "a is a metric space".  The DEFAULT is derivable from the name; only the
      ;; wording of a proper noun is not (`euclidean ring' wants a capital E).
      ;; So: derive, record that it was derived, and let a human's `notation!'
      ;; override it.  english-derived-nouns names the ones still wearing the
      ;; machine's wording.
      (declare-structure-noun! is-name name))
    ;; the MORPHISMS of this species, read off the same slot list (see
    ;; build-hom-axiom).  Objects without morphisms are not a category.
    (install-hom-axiom! name slots)
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

;;; -----------------------------------------------------------------------
;;; def-substructure -- a SAME-SHAPE refinement.
;;;
;;;   (declare-structure EUCLIDEAN-RING
;;;     (same-shape-as INTEGRAL-DOMAIN)
;;;     (law (FORSOME deg ...)))            ; extra conditions, free variable `s'
;;;
;;; COMMUTATIVE-RING, INTEGRAL-DOMAIN, EUCLIDEAN-RING and PID are rings with
;;; MORE LAWS and the SAME SHAPE -- the same six slots.  They cannot be ordinary
;;; def-structures, and the reason is not bookkeeping:
;;;
;;;   def-structure's IS-NAME asserts the SHAPE (the tuple and its slot types)
;;;   plus the named laws.  A shape clause here would be a disaster.  A
;;;   shape-only IS-COMMUTATIVE-RING is EQUIVALENT to IS-RING -- same six slots
;;;   -- and would force every ring commutative; INTEGRAL-DOMAIN's ONE /= ZERO
;;;   would outright contradict the zero ring.
;;;
;;; So a refinement must not ADD a shape clause: it must INHERIT the shape by
;;; naming its parent, which is what the hand-written IFFs did:
;;;
;;;   IS-EUCLIDEAN-RING(s)  <=>  IS-INTEGRAL-DOMAIN(s) and <the new laws>
;;;
;;; That literal IS-PARENT conjunct is load-bearing twice over: it carries the
;;; shape, and it is why `euclidean-ring-is-integral-domain' is provable modulo 0
;;; by a single mac-h (subtype-laws.scm) -- the parent is right there on the RHS.
;;; Generated here, it holds by construction.
;;;
;;; What this funnel buys is the four things each of those files had to remember
;;; BY HAND, and did not always: the `definitional' provenance (a mere unfold
;;; must carry no debt), the NAME-class axiom, register-definitional-structure!
;;; (the parent chain the proof reader collapses subtype citations with), and
;;; register-operator! (the operator table -- which those five predicates were
;;; invisible to, being reachable by no def-* at all).
;;;
;;; It declares NO slots: the accessors are the parent's.  Declaring one is an
;;; error -- a different shape is a different structure, related by def-functor,
;;; not by this.
;;; A law may be written in the SURFACE SYNTAX, as a string -- and should be.
;;; The S-expression form of a real law is a paren thicket nobody can read or
;;; check by eye:
;;;
;;;   (law "forsome([deg in fun(carr(s), nn)], forall([a in carr(s), b in carr(s)],
;;;         not(b = zero(s)) implies forsome([q in carr(s), r in carr(s)],
;;;         a = add(s)(mul(s)(q, b), r) and (r = zero(s) or succ(deg(r)) <= deg(b)))))")
;;;
;;; parses and expands to exactly the S-expression it replaces (the typed-binder
;;; sugar `[a in carr(s), b in carr(s)]' expands the same way make-wff expands it).
(define (structure--law->formula l)
  (if (string? l)
      (expand-destructuring-quantifiers (parse-string l))
      l))

(define (def-substructure name parent laws0 #!optional ivar0)
  (let* ((laws      (map structure--law->formula laws0))
         (ivar      (if (default-object? ivar0) 's ivar0))
         (is-name   (symbol-append 'IS- name))
         (is-parent (symbol-append 'IS- parent))
         (def-name  (symbol-append 'is- name '-def))
         ;; IS-NAME(s) <=> IS-PARENT(s) and <laws>.  The parent FIRST and
         ;; LITERAL: subtype-laws.scm unfolds this and reads it straight off.
         (rhs       (conjuncts->and (cons `(,is-parent ,ivar) laws))))
    (fluid-let ((*current-provenance* 'definitional))
      (theory-add-axiom! *current-theory* def-name
        `(FORALL ,ivar (IFF (,is-name ,ivar) ,rhs)))
      ;; the associated proper class, exactly as def-structure installs one
      (theory-add-axiom! *current-theory* (symbol-append name '-class)
        `(FORALL ,ivar (IFF (IN ,ivar ,name) (,is-name ,ivar)))))
    (register-definitional-structure! name parent)
    (register-operator! is-name 'predicate (list ivar))
    (declare-structure-noun! is-name name)   ; "s is a commutative ring"
    ;; a hom of X's is a hom of PARENTs between X's -- same shape, same maps
    (install-refinement-hom-axiom! name parent)
    name))

;;; A (property NAME accessor ...) clause names a characteristic law from
;;; operation-properties.scm and the accessors it constrains; collected into
;;; the axiom-names list and folded into IS-NAME by build-is-axiom.
(define (def-structure-from-clauses name clauses)
  ;; A (same-shape-as PARENT) clause makes this a REFINEMENT, not a shape: it
  ;; inherits the parent's slots and accessors and adds laws.  See
  ;; def-substructure above for why it must not emit a shape clause of its own.
  ;; Keep the clauses as written: they, not the expansion, are what the
  ;; browser and describe-structure show (see *structure-decl-table*).
  (record-structure-declaration! name clauses)
  ;; The variable a (law ...) clause uses to name the instance is named EXPLICITLY
  ;; by an (instance-var VAR) clause, and REQUIRED whenever the declaration carries
  ;; any (law ...) clause: a law's bare `s' (or whatever) is a free variable captured
  ;; by the FORALL of the IS-NAME axiom, and a reader should not have to infer which
  ;; variable that is.  VAR is threaded through as the actual binder (build-is-axiom /
  ;; def-substructure), so a group's laws may read over `g' if declared so.  A
  ;; law-free declaration needs no instance variable and defaults to `s' internally.
  (let* ((iv-clause (find-first (lambda (c) (and (pair? c) (eq? (car c) 'instance-var)))
                                clauses))
         (has-law   (find-first (lambda (c) (and (pair? c) (eq? (car c) 'law))) clauses))
         (ivar      (if iv-clause (cadr iv-clause) 's))
         (clauses   (filter (lambda (c) (not (and (pair? c) (eq? (car c) 'instance-var))))
                            clauses)))
    (when (and has-law (not iv-clause))
      (error (string-append
              "declare-structure " (symbol->string name)
              ": a (law ...) clause uses a free variable for the structure instance,"
              " so the declaration must name it with an (instance-var VAR) clause"
              " (conventionally (instance-var s)).")))
    (unless (symbol? ivar)
      (error (string-append "declare-structure " (symbol->string name)
                            ": (instance-var VAR) needs a symbol") ivar))
    (let ((sh (find-first (lambda (c) (and (pair? c) (eq? (car c) 'same-shape-as)))
                          clauses)))
      (if sh
          (let ((strays (filter (lambda (c)
                                  (and (pair? c)
                                       (memq (car c) '(carriers op constant substructure))))
                                clauses)))
            (if (pair? strays)
                (error (string-append
                        "declare-structure " (symbol->string name)
                        ": (same-shape-as ...) inherits the parent's shape, so it "
                        "cannot declare slots.  A different shape is a different "
                        "structure -- relate it with def-functor.")
                       strays))
            (def-substructure name (cadr sh)
              (map cadr (filter (lambda (c) (and (pair? c) (eq? (car c) 'law))) clauses))
              ivar))
          (def-structure-from-shape-clauses name clauses ivar)))))

(define (def-structure-from-shape-clauses name clauses #!optional ivar0)
  ;; Build the slot list in declaration order.  A (carriers C1 C2 ...) clause
  ;; contributes one carrier slot per name, in left-to-right order.  Op and
  ;; constant clauses each contribute one slot.  Property clauses contribute
  ;; to the props list, not slots.
  (let loop ((rest clauses) (slots '()) (props '()) (laws '()))
    (if (null? rest)
        (def-structure name (reverse slots) (reverse props) (reverse laws)
                       (if (default-object? ivar0) 's ivar0))
        (let* ((clause (car rest))
               (kind   (car clause)))
          (cond
            ((eq? kind 'carriers)
             (loop (cdr rest)
                   (append (map (lambda (c) (list c 'carrier))
                                (reverse (cdr clause)))
                           slots)
                   props laws))
            ((eq? kind 'op)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'op (caddr clause) (cadddr clause))
                         slots)
                   props laws))
            ((eq? kind 'constant)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'constant (caddr clause)) slots)
                   props laws))
            ;; (substructure NAME TYPE) -- the slot holds a whole structure
            ;; (e.g. a vector space's base FIELD), typed by IS-TYPE rather than
            ;; the bare (IN _ SET) of a carrier.  Op signatures reach into it
            ;; with foreign accessors, e.g. (op SMUL (CARTESIAN (CARR K) V) V) --
            ;; expand-accessors leaves A intact and rewrites K to (K s), giving
            ;; (CARR (K s)) = the carrier of the base field.
            ((eq? kind 'substructure)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'substructure (caddr clause)) slots)
                   props laws))
            ;; (derived NAME BASE-CARRIER DEFINING-EXPR) -- a carrier carved out
            ;; of BASE-CARRIER, e.g. FIELD's
            ;;   (derived NON-ZERO CARR (DIFFERENCE CARR (SINGLETON ZERO)))
            ;; It gets a tuple slot, IS-X pins its value, and a HOMOMORPHISM does
            ;; not give it a map of its own: it rides the base carrier's map.
            ((eq? kind 'derived)
             (loop (cdr rest)
                   (cons (list (cadr clause) 'derived (caddr clause) (cadddr clause))
                         slots)
                   props laws))
            ((eq? kind 'property)
             (loop (cdr rest) slots (cons (cdr clause) props) laws))
            ;; (law FORMULA) -- a raw conjunct of IS-NAME, in the surface syntax:
            ;; the laws no named operation-property expresses (MODULE's action
            ;; axioms).  Free variable `s', like every other clause.
            ((eq? kind 'law)
             (loop (cdr rest) slots props (cons (cadr clause) laws)))
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
;; unfolding bodies.  def-functor functoids are recorded here too, but the
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
      (register-operator! name 'functoid pvars)     ; the ONE table (operators.scm)
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
  (register-operator! pred-name 'predicate params)   ; the ONE table (operators.scm)
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
;;; def-functor -- declare one structure as a view of another
;;;
;;; (def-functor NAME
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
;;;   (def-functor RING-ADDITIVE-AG
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
  (source-file    view-as-source-file))   ; pathname (or #f) of the def-functor call site

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
;;; with accessor reduction.  Called once at def-functor time; can be re-run
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
    (display ";; def-functor ") (display view-name) (display ": ")
    (display count) (display " ")
    (display (view-as-target-struct v))
    (display " theorems specialized.") (newline)
    count)))

;;; Walk up the definitional-structure parent chain to find the underlying
;;; shape structure-def (one declared with slot clauses).  Refinements
;;; (COMMUTATIVE-RING, EUCLIDEAN-RING, …) declare no slots of their own, so a
;;; view-as FROM a refinement uses its ancestor's slots.
(define (find-shape-structure name)
  (or (lookup-structure name)
      (let ((dsd (lookup-definitional-structure name)))
        (and dsd (find-shape-structure
                  (definitional-structure-parent dsd))))))

(define (def-functor name source-struct source-comps target-struct target-comps)
  (fluid-let ((*current-provenance* 'definitional))
  ;; Validation — source/target may be shape OR definitional structures;
  ;; in the latter case we walk up to the ancestor shape for the slot list.
  (let ((src-def (find-shape-structure source-struct))
        (tgt-def (find-shape-structure target-struct)))
    (unless src-def
      (error "def-functor: unknown source structure" source-struct))
    (unless tgt-def
      (error "def-functor: unknown target structure" target-struct))
    (unless (= (length source-comps) (length target-comps))
      (error "def-functor: source/target component lists differ in length"
             source-comps target-comps))
    ;; Target components must equal the target's slot order exactly --
    ;; the form is self-documenting *and* self-checking.
    (let ((tgt-slots (structure-slot-names tgt-def)))
      (unless (equal? target-comps tgt-slots)
        (error "def-functor: target components must equal target slot order"
               'got: target-comps 'expected: tgt-slots)))
    ;; Source components must all be valid accessors of source-struct.
    (let ((src-slots (structure-slot-names src-def)))
      (for-each (lambda (c)
                  (unless (member c src-slots)
                    (error "def-functor: not a source accessor" c
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
;;; A *definitional structure* (a REFINEMENT) is one whose IS-X declares no
;;; shape of its own but is an IFF against its parent:
;;;
;;;   (FORALL s (IFF (IS-X s) (AND (IS-PARENT s) <extra laws>)))
;;;
;;; It is written with a `(same-shape-as PARENT)` clause and its laws:
;;;
;;;   (declare-structure INTEGRAL-DOMAIN
;;;     (same-shape-as COMMUTATIVE-RING)
;;;     (law "not(one(s) = zero(s))")
;;;     ...)
;;;
;;; and def-structure-from-clauses routes it to `def-substructure`, which
;;; GENERATES that IFF (parent conjunct first and literal), the class axiom,
;;; the `definitional' provenance, the operator-table entry and this
;;; registration.  Nobody hand-writes the axiom any more.  COMMUTATIVE-RING,
;;; INTEGRAL-DOMAIN, EUCLIDEAN-RING, PID, VECTOR-SPACE are refinements; FIELD
;;; and NORMED-FIELD are NOT -- they declare their own slots (RECIP, FNRM) and
;;; so are shape structures with laws.
;;;
;;; `register-definitional-structure!` records the parent chain: the navigation
;;; index (structure-index in interactive.scm) reads it, and so does the proof
;;; reader, which collapses a run of subtype-subsumption citations with it.
;;; `(current-load-pathname)` captures the source.

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

;;; -----------------------------------------------------------------------
;;; ACCESSOR-TYPE AUDIT -- "is this accessor a slot of THAT structure?"
;;;
;;; The companion to the one-name-one-slot rule (register-accessor-index!).  That
;;; rule keeps a single accessor NAME from denoting two different slots.  This
;;; audit catches the other half: an accessor applied to a structure that has no
;;; such slot -- (OPR ag) where ag is an ABELIAN-GROUP whose operation is OPR.
;;;
;;; Such a formula is WELL-FORMED and therefore silent: the head registry is
;;; scope-blind and happily reads MUL as the ring accessor.  The formula just
;;; means something else.  That is the whole disease of this codebase, so it gets
;;; a checker rather than a convention.
;;;
;;; Method, deliberately simple and conservative:
;;;   -- collect every guard (IS-X v) anywhere in the formula, giving v : X
;;;      (a variable with two guards is allowed to satisfy either);
;;;   -- for every application (ACC v) whose head is a registered accessor and
;;;      whose argument is a guarded variable, require ACC to be a slot of the
;;;      SHAPE of X (refinements share their parent's shape).
;;; Unguarded variables and non-variable arguments ((MUL (SCAL m))) are skipped:
;;; the audit reports only what it is sure of, so a hit is a real hit.
(define (structure-accessor-names name)
  (let ((sd (find-shape-structure name)))
    (and sd (structure-slot-names sd))))

(define (isx-predicate->structure p)
  (let ((s (symbol->string p)))
    (and (> (string-length s) 3)
         (string=? (substring s 0 3) "is-")
         (let ((nm (string->symbol (substring s 3 (string-length s)))))
           (and (find-shape-structure nm) nm)))))

;;; ((ACC var STRUCT) ...) for every accessor application in E whose argument is
;;; a variable guarded by a structure predicate that has no such slot.
(define (formula-accessor-type-errors e0)
  (let ((e     (if (wff? e0) (wff-formula e0) e0))
        (types '())      ; (var . struct), from the guards
        (hits  '()))
    ;; pass 1 -- the guards
    (let collect ((x e))
      (when (pair? x)
        (let ((h (car x)))
          (if (and (symbol? h) (= (length x) 2) (symbol? (cadr x))
                   (isx-predicate->structure h))
              (set! types (cons (cons (cadr x) (isx-predicate->structure h)) types))))
        (for-each collect (cdr x))
        (if (pair? (car x)) (collect (car x)))))
    ;; pass 2 -- the accessor applications
    (let walk ((x e))
      (when (pair? x)
        (let ((h (car x)))
          (when (and (symbol? h) (= (length x) 2) (symbol? (cadr x))
                     (eq? (constant-head? h) 'accessor))
            (let ((guards (filter (lambda (p) (eq? (car p) (cadr x))) types)))
              (when (and (pair? guards)
                         ;; a hit only if NO guard on this variable admits the slot
                         (not (find-first (lambda (p)
                                            (let ((slots (structure-accessor-names (cdr p))))
                                              (and slots (memq h slots))))
                                          guards)))
                (set! hits (cons (list h (cadr x) (cdar guards)) hits))))))
        (for-each walk (cdr x))
        (if (pair? (car x)) (walk (car x)))))
    (reverse hits)))

;;; Sweep the whole installed library.  Empty => every accessor application whose
;;; argument is a guarded variable names a slot that structure actually has.
(define (accessor-type-audit)
  (let ((bad '()))
    (for-each
      (lambda (name)
        (let* ((f    (lookup-theorem name))
               (hits (and f (formula-accessor-type-errors f))))
          (if (pair? hits) (set! bad (cons (cons name hits) bad)))))
      (hash-table-keys *theorem-table*))
    (sort bad (lambda (a b) (string<? (symbol->string (car a))
                                      (symbol->string (car b)))))))

;;; -----------------------------------------------------------------------
;;; HOMOMORPHISMS, generated from the slot list.
;;;
;;; A structure species is a class of objects; a CATEGORY needs morphisms too.
;;; VNB had none: `def-functor' maps objects to objects, so calling it a functor
;;; was a promise the code did not keep.  A homomorphism, though, is completely
;;; determined by the slots -- so it is generated, once, for every species,
;;; present and future, exactly as build-is-axiom folds the slots into IS-X.
;;;
;;;   IS-HOM-X(a, b, f1, ..., fk)   -- k = the number of CARRIERS (many-sorted:
;;;                                     one map per carrier, so a Malcev-style
;;;                                     two-sorted structure just works)
;;;
;;; is defined to hold exactly when
;;;   IS-X(a), IS-X(b)                                   -- morphisms are between objects
;;;   fi in FUN(Ci(a), Ci(b))                            -- one map per carrier
;;;   S(a) = S(b)                for each SUBSTRUCTURE slot S
;;;   fi(c(a)) = c(b)            for each CONSTANT slot c landing in carrier i
;;;   fj(OP(a)(x...)) = OP(b)(f(x)...)   for each OP slot, argument by argument
;;;
;;; Two conventions, both deliberate:
;;;
;;; SUBSTRUCTURE slots are required EQUAL (module homs are maps between modules
;;; OVER THE SAME RING -- standard practice; the general (ring hom, additive map)
;;; pair is a different category, and we are not building it).
;;;
;;; A sort that is NOT a carrier of this structure -- a norm's RR, the scalars
;;; (CARR SCAL) -- is mapped by the IDENTITY.  So a norm slot generates
;;; NRM(b)(f x) = NRM(a)(x): the algebraic default for a normed structure is the
;;; ISOMETRY.  (Metric spaces will want to OVERRIDE this: their interesting
;;; category is the continuous one, not the isometric one.  The override is not
;;; built yet; when it is, it belongs beside the declaration, like `notation!'.)

(define (structure-hom-name name) (symbol-append 'IS-HOM- name))

;;; The sorts of an op's domain: (CARTESIAN d1 d2) -> (d1 d2), nested to the
;;; left as the library writes it; a bare sort -> a one-argument op.
(define (hom--domain-sorts dom)
  (if (and (pair? dom) (eq? (car dom) 'CARTESIAN))
      (append-map hom--domain-sorts (cdr dom))
      (list dom)))

;;; The map that carries a value of SORT from `a' to `b'.
;;;   -- an independent carrier: its own fi;
;;;   -- a DERIVED carrier (FIELD's NON-ZERO = CARR \ {ZERO}): the map of the
;;;      carrier it was carved from, so RECIP's law reads
;;;        f(recip(a)(x)) = recip(b)(f(x))   for x in non-zero(a)
;;;      with ONE map, not a second, unrelated one;
;;;   -- anything else (a norm's RR, the scalars (CARR SCAL)): the identity.
(define (hom--map-for sort carriers fvars #!optional derived-base)
  (let ((base (if (default-object? derived-base) '() derived-base)))
    (let loop ((s sort))
      (let inner ((cs carriers) (fs fvars))
        (cond ((null? cs)
               (let ((d (assq s base)))          ; derived -> follow to its base
                 (and d (loop (cdr d)))))
              ((eq? s (car cs)) (car fs))
              (else (inner (cdr cs) (cdr fs))))))))

(define (hom--apply mapf x) (if mapf (list mapf x) x))

(define (build-hom-axiom name slots)
  (let* ((avar     'a)
         (bvar     'b)
         (accs     (map car slots))
         ;; INDEPENDENT carriers only: a derived one is not a sort of its own.
         (carriers (map car (filter (lambda (s) (eq? (cadr s) 'carrier)) slots)))
         ;; derived carrier -> the carrier it is carved from
         (dbase    (map (lambda (s) (cons (car s) (caddr s)))
                        (filter (lambda (s) (eq? (cadr s) 'derived)) slots)))
         (k        (length carriers))
         ;; f, or f1 f2 ... when many-sorted.  Trailing digits, not underscores:
         ;; these are binders of the DEFINITION, not of a proof.
         (fvars    (if (= k 1)
                       '(f)
                       (map (lambda (i)
                              (symbol-append 'f (string->symbol (number->string i))))
                            (iota k 1))))
         (is-name  (symbol-append 'IS- name))
         (at       (lambda (e v) (expand-accessors e accs v))))
    (define (carrier-conjuncts)
      (map (lambda (c f) `(IN ,f (FUN (,c ,avar) (,c ,bvar))))
           carriers fvars))
    (define (slot-conjunct slot)
      (let ((nm (car slot)) (kind (cadr slot)))
        (case kind
          ((carrier) #f)                          ; handled above
          ;; A derived carrier is PINNED by IS-X (non-zero(a) = carr(a) \ {zero a}),
          ;; and rides its base carrier's map -- so it owes the hom nothing.
          ((derived) #f)
          ;; morphisms are between structures over the SAME base
          ((substructure) `(= (,nm ,avar) (,nm ,bvar)))
          ((constant)
           (let ((mapf (hom--map-for (caddr slot) carriers fvars dbase)))
             `(= ,(hom--apply mapf `(,nm ,avar)) (,nm ,bvar))))
          ((op)
           (let* ((sorts (hom--domain-sorts (caddr slot)))
                  (rng   (cadddr slot))
                  (xs    (map (lambda (i)
                                (symbol-append 'x (string->symbol (number->string i)) '_))
                              (iota (length sorts) 1)))
                  (rmap  (hom--map-for rng carriers fvars dbase))
                  (lhs   (hom--apply rmap (cons `(,nm ,avar) xs)))
                  (rhs   (cons `(,nm ,bvar)
                               (map (lambda (s x)
                                      (hom--apply (hom--map-for s carriers fvars dbase) x))
                                    sorts xs)))
                  (body  `(= ,lhs ,rhs)))
             ;; bind each argument in ITS OWN sort, taken in `a'
             (let loop ((vs (reverse xs)) (ss (reverse sorts)) (acc body))
               (if (null? vs)
                   acc
                   (loop (cdr vs) (cdr ss)
                         `(FORALL ,(car vs)
                            (IMPLIES (IN ,(car vs) ,(at (car ss) avar)) ,acc)))))))
          (else (error "build-hom-axiom: unknown slot kind" kind slot)))))
    (let* ((body (conjuncts->and
                   (append (list `(,is-name ,avar) `(,is-name ,bvar))
                           (carrier-conjuncts)
                           (filter (lambda (x) x) (map slot-conjunct slots)))))
           (hom  (structure-hom-name name))
           (args (append (list avar bvar) fvars)))
      (values hom args
              `(FORALL ,avar (FORALL ,bvar
                 ,(let loop ((fs fvars))
                    (if (null? fs)
                        `(IFF (,hom ,@args) ,body)
                        `(FORALL ,(car fs) ,(loop (cdr fs)))))))))))

;;; Install IS-HOM-NAME for a SHAPE structure.
;;; The English of a hom predicate.  IS-HOM-RING(a, b, f) reads "f is a
;;; homomorphism from a to b" -- derivable, because that is what the GENERATED hom
;;; means (preservation of the slots).  A species that OVERRIDES its morphisms
;;; means something else by them, and says so with `notation!' beside the
;;; declare-hom! (METRIC-SPACE: "f is continuous from a to b").  Only the
;;; single-map case gets a default; a many-sorted hom carries several maps and no
;;; one sentence fits.
(define (declare-hom-english! hom args)
  (let ((entry (operator-ref hom)))
    (when (and entry (= (length args) 3)
               (not (operator-english entry)) (not (operator-noun entry)))
      (notation! hom 'kind 'predicate 'arity 3
                 'english "$3 is a homomorphism from $1 to $2"))))

(define (install-hom-axiom! name slots)
  (call-with-values (lambda () (build-hom-axiom name slots))
    (lambda (hom args axiom)
      (fluid-let ((*current-provenance* 'definitional))
        (theory-add-axiom! *current-theory* (symbol-append hom '-def) axiom))
      (register-operator! hom 'predicate args)
      (declare-hom-english! hom args)
      hom)))

;;; A REFINEMENT shares its parent's shape, so a hom of X's is a hom of PARENTs
;;; between X's: IS-HOM-X(a,b,f...) <=> IS-X(a) and IS-X(b) and IS-HOM-PARENT(...).
(define (install-refinement-hom-axiom! name parent)
  (let* ((sd (find-shape-structure parent)))
    (and sd
         (let* ((carriers (map car (filter (lambda (s) (eq? (cadr s) 'carrier))
                                           (structure-def-slots sd))))
                (fvars    (if (= (length carriers) 1)
                              '(f)
                              (map (lambda (i)
                                     (symbol-append 'f (string->symbol (number->string i))))
                                   (iota (length carriers) 1))))
                (hom      (structure-hom-name name))
                (phom     (structure-hom-name parent))
                (is-name  (symbol-append 'IS- name))
                (args     (append '(a b) fvars))
                (body     (conjuncts->and
                            (list `(,is-name a) `(,is-name b) `(,phom ,@args)))))
           (fluid-let ((*current-provenance* 'definitional))
             (theory-add-axiom! *current-theory* (symbol-append hom '-def)
               `(FORALL a (FORALL b
                  ,(let loop ((fs fvars))
                     (if (null? fs)
                         `(IFF (,hom ,@args) ,body)
                         `(FORALL ,(car fs) ,(loop (cdr fs)))))))))
           (register-operator! hom 'predicate args)
           (declare-hom-english! hom args)   ; "f is a homomorphism from a to b"
           hom))))

;;; -----------------------------------------------------------------------
;;; TWO THINGS THE ALIST CANNOT DO
;;;
;;; def-functor's data is an accessor CORRESPONDENCE: select the source's slots,
;;; rename them into the target's.  That covers the forgetful functors and
;;; nothing else, and two gaps show up the moment TOP-SPACE (topological spaces)
;;; is on the table.
;;;
;;; (1) THE MORPHISMS OF A SPECIES MAY NOT BE ITS HOMOMORPHISMS.  build-hom-axiom
;;;     generates preservation-of-slots, which is right for algebra and right for
;;;     METRIC-SPACE (whose morphisms ARE the isometries).  It is WRONG for a
;;;     topological space: a topology slot would generate OPENS(a) = OPENS(b),
;;;     forcing the topologies literally equal.  Continuity is a PREIMAGE
;;;     condition, not a preservation law.  So a species may DECLARE its morphism
;;;     notion and override the generated one -- `declare-hom!', beside the
;;;     structure, like `notation!'.
;;;
;;; (2) A FUNCTOR'S OBJECT MAP MAY BE A CONSTRUCTION, NOT A SELECTION.  The
;;;     metric topology tau_d is not a SLOT of a metric space; it is COMPUTED
;;;     from DIST.  No correspondence of accessors yields it.  So the object map
;;;     may be an arbitrary TERM -- `def-constructed-functor'.
;;;
;;; And a constructed functor cannot have its typing and functoriality for free,
;;; the way an alist does: "an isometry is continuous" is a theorem with content.
;;; So the constructor ASSERTS NOTHING.  It records two OBLIGATIONS, and
;;; `functor-obligation-audit' reports any still undischarged.  A functor you
;;; have not proved is a functor you do not have.

;;; --- (1) a species may declare its morphisms ------------------------------
(define *hom-overrides* (make-equal-hash-table))   ; structure -> #t

(define (hom-overridden? name)
  (hash-table-ref/default *hom-overrides* name #f))

;;; (declare-hom! 'TOP-SPACE '(a b f) "forall([u in opens(b)], preimage(f, u) in opens(a))")
;;; The BODY says what it means for f to be a morphism a -> b, over and above
;;; a and b being objects and f being typed: IS-X(a), IS-X(b) and the carrier
;;; typing of each map are supplied here, so the body states only what is
;;; characteristic.  Replaces the generated IS-HOM-X definition.
(define (declare-hom! name args body)
  (let* ((sd       (find-shape-structure name))
         (_        (or sd (error "declare-hom!: unknown structure" name)))
         (carriers (map car (filter (lambda (s) (eq? (cadr s) 'carrier))
                                    (structure-def-slots sd))))
         (avar     (car args))
         (bvar     (cadr args))
         (fvars    (cddr args))
         (is-name  (symbol-append 'IS- name))
         (hom      (structure-hom-name name))
         (body*    (structure--law->formula body))
         (conjs    (append (list `(,is-name ,avar) `(,is-name ,bvar))
                           (map (lambda (c f) `(IN ,f (FUN (,c ,avar) (,c ,bvar))))
                                carriers fvars)
                           (list body*))))
    (unless (= (length fvars) (length carriers))
      (error "declare-hom!: one map per carrier expected" name carriers fvars))
    (fluid-let ((*current-provenance* 'definitional))
      (theory-add-axiom! *current-theory* (symbol-append hom '-def)
        `(FORALL ,avar (FORALL ,bvar
           ,(let loop ((fs fvars))
              (if (null? fs)
                  `(IFF (,hom ,avar ,bvar ,@fvars) ,(conjuncts->and conjs))
                  `(FORALL ,(car fs) ,(loop (cdr fs)))))))))
    (register-operator! hom 'predicate (append (list avar bvar) fvars))
    ;; An OVERRIDDEN hom is not preservation-of-slots, so "homomorphism" may be the
    ;; wrong word for it -- but it is not a WRONG default, and a `notation!' beside
    ;; the declare-hom! says the right one (METRIC-SPACE / TOP-SPACE: "continuous").
    (declare-hom-english! hom (append (list avar bvar) fvars))
    (hash-table-set! *hom-overrides* name #t)
    hom))

;;; --- (2) a functor whose object map is a constructed term -----------------
;;;
;;; PROJECTIONS OF A CONSTRUCTION, precomputed -- declare-instance!'s trick, one
;;; level up.  METRIC-TOP(md) is the literal pair [PTS(md), {U in POWER(PTS md) :
;;; IS-OPEN(md,U)}], so PTS(METRIC-TOP md) = PTS(md) is settled the moment the
;;; functor is declared, and no proof should have to rediscover it.
;;;
;;; Without this it is not merely tedious, it is a TRAP.  Reaching the projection
;;; by hand means unfolding the functoid and firing the accessor macete -- and a
;;; macete rewrites EVERY occurrence, so the (PTS md) sitting INSIDE the tuple is
;;; rewritten too, and the goal collapses to NTH form: `nth(1, [nth(1, md), ...])'
;;; where the supports it must meet (empty-is-open, carrier-is-open, ...) all say
;;; PTS(md).  Nothing matches, and `=' being partial, rfl will not even close
;;; nth(1,md) = nth(1,md) for an untyped md.  functoriality.scm:90 records this
;;; as the reason the projection equations "are not proved as standalone lemmas".
;;; With the projections precomputed, the tuple never enters the goal at all.
;;;
;;; PROVENANCE: definitional -- the functoid's unfold is definitional, the
;;; accessor macete is definitional, and NTH-reduction is a kernel rule.  Nothing
;;; asserted is being laundered (contrast declare-instance!, which INHERITS its
;;; tuple equation's provenance because that equation may be an axiom).
(define *functor-projections* (make-equal-hash-table))  ; functor -> ((acc mname term) ...)
(define *functor-info* (make-equal-hash-table))         ; functor -> (src tgt param)

(define (functor-info fn) (hash-table-ref/default *functor-info* fn #f))
(define (functor-names)
  (sort (hash-table-keys *functor-info*)
        (lambda (a b) (string<? (symbol->string a) (symbol->string b)))))

;;; The accessors this functor carries across ON THE NOSE: ACC(G r) = ACC(r), the
;;; projection being the SAME accessor of the parameter.  METRIC-TOP carries PTS
;;; (a metric space and its topology have the same points); it does NOT carry
;;; OPENS on the nose (a metric space has none -- the topology is CONSTRUCTED).
;;; NF-METRIC-SPACE carries nothing on the nose: its PTS is the source's CARR.
;;;
;;; This is the syntactic form of a strict commuting triangle: on these slots the
;;; functor is the identity, so anything defined THROUGH them alone cannot see it.
(define (functor-nose-accessors fn)
  (let ((info (functor-info fn)))
    (and info
         (let ((r (caddr info)))
           (map car
                (filter (lambda (p) (equal? (caddr p) (list (car p) r)))
                        (hash-table-ref/default *functor-projections* fn '())))))))

(define (functor-projection-macete fn acc)
  (let ((e (hash-table-ref/default *functor-projections* fn #f)))
    (and e (let ((hit (assq acc e))) (and hit (cadr hit))))))

(define (functor-projection-macete-name? name)
  (there-exists? (hash-table-values *functor-projections*)
    (lambda (e) (there-exists? e (lambda (p) (eq? (cadr p) name))))))

;;; ((FN (ACC . term) ...) ...) -- what each constructed functor's slots project to.
(define (functor-projection-audit)
  (map (lambda (fn)
         (cons fn (map (lambda (p) (cons (car p) (caddr p)))
                       (hash-table-ref/default *functor-projections* fn '()))))
       (sort (hash-table-keys *functor-projections*)
             (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

;;; TERM is the object map's body, in the parameter R.  If it is a literal LIST,
;;; install (ACC (NAME r)) -> component_k for each of the target's slots.  A
;;; non-LIST object map (none today) simply gets no projections: the proof can
;;; still unfold the functoid by hand.
(define (install-functor-projections! name tgt-sd r term)
  (when (and (pair? term) (eq? (car term) 'LIST))
    (let ((slots (structure-slot-names tgt-sd))
          (comps (cdr term)))
      (when (= (length slots) (length comps))
        (hash-table-set! *functor-projections* name
          (let loop ((accs slots) (ts comps) (acc '()))
            (if (null? accs)
                (reverse acc)
                (let ((mname (symbol-append name '@ (car accs))))
                  (if (hash-table-ref/default *macete-table* mname #f)
                      (error "def-constructed-functor: macete name already taken" mname))
                  (install-macete! mname
                    (make-elementary-macete
                      (list r) '()
                      `(,(car accs) (,name ,r))
                      (car ts)))
                  (register-provenance! mname 'definitional)
                  (loop (cdr accs) (cdr ts)
                        (cons (list (car accs) mname (car ts)) acc)))))))))
  name)

(define *functor-obligations* (make-equal-hash-table))  ; functor -> (name ...)

(define (functor-obligations name)
  (hash-table-ref/default *functor-obligations* name '()))

;;; (def-constructed-functor NAME SRC TGT (r) TERM)
;;;   -- the object map is the FUNCTOID (NAME r) = TERM, an arbitrary construction
;;;      (NF-METRIC-SPACE(nf) = [CARR(nf), lambda([x,y], FNRM(nf)(x - y))]);
;;;   -- the morphism action is the identity on the underlying maps, which is
;;;      what every construction of this kind does (it re-tops the same carrier).
;;; It installs the functoid and OWES two theorems.  Neither is asserted:
;;;      NAME-is-TGT     : IS-SRC(r) => IS-TGT(NAME r)
;;;      NAME-functorial : IS-HOM-SRC(a,b,f) => IS-HOM-TGT(NAME a, NAME b, f)
(define (def-constructed-functor name src tgt params term)
  (let* ((src-sd (find-shape-structure src))
         (tgt-sd (find-shape-structure tgt)))
    (unless src-sd (error "def-constructed-functor: unknown source" src))
    (unless tgt-sd (error "def-constructed-functor: unknown target" tgt))
    (let* ((ps       (if (pair? params) params (list params)))
           (r        (car ps))
           (is-src   (symbol-append 'IS- src))
           (is-tgt   (symbol-append 'IS- tgt))
           (hom-src  (structure-hom-name src))
           (hom-tgt  (structure-hom-name tgt))
           (carriers (lambda (sd) (map car (filter (lambda (s) (eq? (cadr s) 'carrier))
                                                   (structure-def-slots sd)))))
           (k        (length (carriers src-sd)))
           (fvars    (if (= k 1)
                         '(f)
                         (map (lambda (i)
                                (symbol-append 'f (string->symbol (number->string i))))
                              (iota k 1))))
           (typing   (symbol-append name '-is- tgt))
           (functl   (symbol-append name '-functorial)))
      (unless (= k (length (carriers tgt-sd)))
        (error "def-constructed-functor: source and target have different carrier counts"
               name src tgt))
      (def-functoid name ps term)
      (hash-table-set! *functor-info* name (list src tgt r))
      (install-functor-projections! name tgt-sd r term)
      (hash-table-set! *functor-obligations* name
        (list (cons typing
                    `(FORALL ,r (IMPLIES (,is-src ,r) (,is-tgt (,name ,r)))))
              (cons functl
                    `(FORALL a (FORALL b
                       ,(let loop ((fs fvars))
                          (if (null? fs)
                              `(IMPLIES (,hom-src a b ,@fvars)
                                        (,hom-tgt (,name a) (,name b) ,@fvars))
                              `(FORALL ,(car fs) ,(loop (cdr fs)))))))))) 
      name)))

;;; Every obligation of every constructed functor that is not yet a theorem.
;;; A functor you have not proved is a functor you do not have -- so this is
;;; reported at load, and the obligations are AVAILABLE as goals (the cdr is the
;;; statement, ready for `sp').
(define (functor-obligation-audit)
  (append-map
    (lambda (fn)
      (filter (lambda (ob)
                (not (hash-table-ref/default *theorem-table* (car ob) #f)))
              (functor-obligations fn)))
    (sort (hash-table-keys *functor-obligations*)
          (lambda (a b) (string<? (symbol->string a) (symbol->string b))))))

(define (functor-obligation name)
  (let loop ((fns (hash-table-keys *functor-obligations*)))
    (cond ((null? fns) #f)
          ((assq name (functor-obligations (car fns)))
           => (lambda (p) (make-wff (cdr p))))
          (else (loop (cdr fns))))))
