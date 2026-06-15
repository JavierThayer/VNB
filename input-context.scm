;;; input-context.scm -- generalized context-discharge + operator-remap engine.
;;;
;;; This GENERALIZES the ring-expression copilot (ring-term / ring-goal in
;;; interactive.scm) from the hardcoded commutative-ring to ANY registered
;;; structure kind.  You write algebra with ordinary  + * - ^  (and, later, the
;;; structure's own relations); the engine resolves each operator to the
;;; structure's OWN operation and discharges the whole formula into the guarded
;;; universal closure
;;;
;;;     forall s, IS-X(s) implies forall <elts> in <carrier>(s). <body>
;;;
;;; WHY THE PACKED ACCESSOR FORM.  A VNB structure IS a tuple (structures.scm:
;;; "the accessors are literally projections: (A ag) = (NTH 1 ag), (MUL ag) =
;;; (NTH 2 ag)").  So the flat presentation
;;;     let [X,plus,times,neg,zero,unity] be a commutative-ring
;;; and the library's packed  IS-COMMUTATIVE-RING(s)  are the SAME object: the
;;; tuple is s, the named components are its projections.  We EMIT the packed
;;; accessor heads (ADD s)/(MUL s)/... -- NOT bare component names -- because
;;; (crs) (comm-ring-simplify.scm) and the macetes pattern-match those accessor
;;; heads syntactically; bare names would not connect to the proven corpus.
;;;
;;; DIFFERENTIAL ANCHOR: with the commutative-ring profile, struct-goal must
;;; reproduce ring-goal byte-for-byte.  (run-context-tests) checks this against
;;; the live ring-goal, so any drift is caught at once.
;;;
;;; This file is the ENGINE.  The interactive surface -- (context "let [...] be
;;; a ...") / (nullify) reader state, and sort-directed operator overloading
;;; (vector space over a field: one `+' resolved to scalar vs vector addition by
;;; operand sort) -- layers on top in later increments.

;;; -----------------------------------------------------------------------
;;; Operation tables.  An OPS alist maps the abstract arithmetic roles the
;;; surface walker knows (add / mul / neg heads, the symbolic-power head, the
;;; one / zero constants) to a structure's accessor symbols.

(define (ops-ref ops role)
  (let ((p (assq role ops)))
    (if p (cdr p) (error "input-context: ops table lacks role" role))))

;;; -----------------------------------------------------------------------
;;; A NOTATION PROFILE for a structure kind.
;;;   predicate : the IS-X guard symbol            (e.g. IS-COMMUTATIVE-RING)
;;;   carrier   : the carrier accessor symbol       (e.g. A) -- elt membership
;;;   ops       : alist role->accessor              ((add . ADD) (mul . MUL) ...)
;;;   lits      : alist literal->role               ((0 . zero) (1 . one)) | ()
;;;
;;; `lits' is the LITERAL-PINNING knob.  Per the design, numerals denote
;;; built-in integers by default (lits = '()), so a literal passes through
;;; untouched.  A profile that WANTS the ring convention 0->(ZERO s),
;;; 1->(ONE s) opts in by listing those aliases -- which is exactly what
;;; ring-term hardcodes, and what keeps the differential anchor exact.

;;;   accessors : the structure's accessor symbols IN SLOT ORDER, e.g.
;;;               (A ADD MUL NEG ZERO ONE) -- used to bind the destructuring
;;;               names of  let [c1 c2 ...] be a <kind>  positionally.

(define (make-notation-profile predicate carrier ops lits accessors)
  (list 'notation-profile predicate carrier ops lits accessors))
(define (notation-profile? p) (and (pair? p) (eq? (car p) 'notation-profile)))
(define (np-predicate  p) (list-ref p 1))
(define (np-carrier    p) (list-ref p 2))
(define (np-ops        p) (list-ref p 3))
(define (np-lits       p) (list-ref p 4))
(define (np-accessors  p) (list-ref p 5))

;;; -----------------------------------------------------------------------
;;; struct-fold / struct-pow / struct-term : the operator-remap walk.
;;; Generalized verbatim from ring-term--fold / ring-term--pow / ring-term.

(define (struct-fold op args)            ; left-fold n-ary into the binary slot
  (cond ((null? args) (error "struct-term: empty + or *"))
        ((null? (cdr args)) (car args))
        (else (let loop ((acc (car args)) (rest (cdr args)))
                (if (null? rest) acc
                    (loop (list op acc (car rest)) (cdr rest)))))))

(define (struct-pow profile s base k)    ; literal k >= 0 -> k-fold structure MUL
  (let ((ops (np-ops profile)))
    (cond ((= k 0) (list (ops-ref ops 'one) s))
          ((= k 1) base)
          (else (let loop ((i (- k 1)) (acc base))
                  (if (= i 0) acc
                      (loop (- i 1) (list (list (ops-ref ops 'mul) s) acc base))))))))

(define (struct-term profile s e)
  (let ((ops  (np-ops  profile))
        (lits (np-lits profile)))
    (let recur ((e e))
      (let ((lit (and (not (pair? e)) (assv e lits))))
        (cond
          (lit (list (ops-ref ops (cdr lit)) s))   ; aliased literal -> (ZERO/ONE s)
          ((not (pair? e)) e)                       ; symbol / plain literal passes
          (else
           (case (car e)
             ((+) (struct-fold (list (ops-ref ops 'add) s)
                    (map recur (cdr e))))
             ((*) (struct-fold (list (ops-ref ops 'mul) s)
                    (map recur (cdr e))))
             ((-) (let ((as (map recur (cdr e))))
                    (cond ((null? as) (error "struct-term: empty -"))
                          ((null? (cdr as)) (list (list (ops-ref ops 'neg) s) (car as)))
                          (else (struct-fold (list (ops-ref ops 'add) s)
                                  (cons (car as)
                                        (map (lambda (a) (list (list (ops-ref ops 'neg) s) a))
                                             (cdr as))))))))
             ((^ expt)
              (let ((base (recur (cadr e))) (ex (caddr e)))
                (if (and (integer? ex) (>= ex 0))
                    (struct-pow profile s base ex)         ; literal power
                    (list (ops-ref ops 'pow) s base ex))))  ; symbolic power
             (else (cons (car e) (map recur (cdr e)))))))))))

;;; -----------------------------------------------------------------------
;;; struct-goal : the context-discharge wrapper.  Generalized verbatim from
;;; ring-goal-in -- forall s, IS-X(s) implies forall <elts> in carrier(s). body
;;; with BODY's operators resolved against s.

(define (struct-goal profile svar elt-vars body)
  (make-wff
   (list 'FORALL svar
     (list 'IMPLIES (list (np-predicate profile) svar)
       (let loop ((vs elt-vars))
         (if (null? vs)
             (struct-term profile svar body)
             (list 'FORALL (car vs)
               (list 'IMPLIES (list 'IN (car vs) (list (np-carrier profile) svar))
                 (loop (cdr vs))))))))))

;;; -----------------------------------------------------------------------
;;; Profile registry.  `let [...] be a <kind>' (next increment) looks the
;;; kind up here to find its predicate / carrier / operator map.

(define *notation-profiles* (make-equal-hash-table))

(define (register-notation-profile! kind profile)
  (hash-table-set! *notation-profiles* kind profile))

(define (notation-profile kind)
  (or (hash-table-ref/default *notation-profiles* kind #f)
      (error "input-context: no notation profile for structure kind" kind)))

;;; Seed: commutative-ring -- the exact table ring-term hardcodes, including
;;; the 0->ZERO / 1->ONE literal aliases (so the anchor is byte-exact).
(register-notation-profile! 'commutative-ring
  (make-notation-profile 'IS-COMMUTATIVE-RING 'A
    '((add . ADD) (mul . MUL) (neg . NEG) (pow . RING-POWER) (one . ONE) (zero . ZERO))
    '((0 . zero) (1 . one))
    '(A ADD MUL NEG ZERO ONE)))            ; ring.scm slot order: A.ADD.MUL.NEG.ZERO.ONE

;;; -----------------------------------------------------------------------
;;; Differential test: struct-goal (commutative-ring profile) vs the live
;;; ring-goal-in, on ring-goal's own documented examples plus a few edge cases.

(define (run-context-tests)
  (let ((cr (notation-profile 'commutative-ring)) (n 0) (bad 0))
    (define (chk vars body)
      (set! n (+ n 1))
      (let ((a (wff-formula (struct-goal cr 's vars body)))
            (b (wff-formula (ring-goal-in 's vars body))))
        (unless (equal? a b)
          (set! bad (+ bad 1))
          (display "  MISMATCH ") (write body) (newline)
          (display "    struct-goal: ") (write a) (newline)
          (display "    ring-goal:   ") (write b) (newline))))
    (chk '(x y z) '(= (* z (+ x y)) (+ (* z x) (* z y))))         ; distributivity
    (chk '(x y)   '(= (^ (+ x y) 2)                               ; literal power
                      (+ (^ x 2) (+ (* x y) (+ (* x y) (^ y 2))))))
    (chk '(x y)   '(= (- x y) (+ x (- y))))                       ; binary/unary minus
    (chk '(x)     '(= (* x 1) x))                                 ; 1 -> (ONE s)
    (chk '(x)     '(= (+ x 0) x))                                 ; 0 -> (ZERO s)
    (chk '(x n_)  '(= (^ x n_) (^ x n_)))                         ; symbolic -> RING-POWER
    (chk '(a b)   '(= (* a b) (* b a)))                           ; commutativity
    (chk '(x y z) '(- x y z))                                     ; n-ary minus
    (display "=== context-engine vs ring-goal: ") (display (- n bad))
    (display "/") (display n) (display " identical ===") (newline)
    bad))

;;; =======================================================================
;;; SURFACE.  Reader-state context + the `let ... ' declarations.
;;;
;;; A CONTEXT is a stack of FRAMES, outermost-first (= declaration order).  Two
;;; frame kinds:
;;;   (struct svar profile aliases)  from  let [c1 ... cn] be a <kind> [as v]
;;;       svar    : the (fresh) structure variable, default `s'
;;;       profile : the kind's notation profile
;;;       aliases : alist ci -> (accessor-i svar), positional by slot order
;;;   (elts vars class)              from  let v1, ..., vk in <class-expr>
;;;       vars  : the element variables
;;;       class : the membership class, ALREADY alias-resolved
;;;
;;; Input under a context (via the context-aware `wff') is: parse -> resolve
;;; aliases -> remap + * - ^ via the (single) structure frame's profile ->
;;; discharge through the frame closures, outermost wrapping inner.  The bracket
;;; names are surface aliases that vanish into accessor heads, so the output is
;;; the packed form (crs / macetes compatible).  `(nullify)' clears the stack;
;;; input is then tel-quel (no closure, no remap).

(define *current-context* '())           ; list of frames, outermost-first

;;; ---- alias substitution (symbol -> sexpr, everywhere in a tree) ----
(define (alias-subst e aliases)
  (cond ((symbol? e) (let ((p (assq e aliases))) (if p (cdr p) e)))
        ((pair? e) (cons (alias-subst (car e) aliases)
                         (alias-subst (cdr e) aliases)))
        (else e)))

(define (all-aliases ctx)
  (apply append (map (lambda (f) (if (eq? (car f) 'struct) (list-ref f 3) '())) ctx)))

;;; ---- declaration parser (works on the token stream) ----
(define (ctx-sym? t s) (and (pair? t) (eq? (car t) 'sym) (eq? (cdr t) s)))
(define (ctx-sym-tok? t) (and (pair? t) (memq (car t) '(sym funsym))))

(define (parse-context-decl str)
  (let ((toks (vnb-tokenize str)))
    (unless (and (pair? toks) (ctx-sym? (car toks) 'let))
      (error "context: declaration must begin with `let'" str))
    (let ((rest (cdr toks)))
      (cond
        ((null? rest) (error "context: empty declaration after `let'" str))
        ((eq? (car rest) 'lbracket) (parse-struct-decl (cdr rest) str))
        (else (parse-elts-decl rest str))))))

;;; let [ c1, ..., cn ] be a[n] <kind> [as <svar>]
(define (parse-struct-decl toks str)
  (let loop ((ts toks) (names '()))
    (cond
      ((null? ts) (error "context: missing `]' in structure declaration" str))
      ((eq? (car ts) 'rbracket) (finish-struct-decl (reverse names) (cdr ts) str))
      ((eq? (car ts) 'comma) (loop (cdr ts) names))
      ((ctx-sym-tok? (car ts)) (loop (cdr ts) (cons (cdar ts) names)))
      (else (error "context: bad component name in [...]" (car ts))))))

(define (finish-struct-decl names ts str)
  (unless (and (pair? ts) (ctx-sym? (car ts) 'be))
    (error "context: expected `be' after [...]" str))
  (let ((ts (cdr ts)))
    (when (and (pair? ts) (or (ctx-sym? (car ts) 'a) (ctx-sym? (car ts) 'an)))
      (set! ts (cdr ts)))
    (unless (and (pair? ts) (ctx-sym-tok? (car ts)))
      (error "context: expected a structure kind" str))
    (let ((kind (cdar ts)) (svar 's))
      (set! ts (cdr ts))
      (when (and (pair? ts) (ctx-sym? (car ts) 'as) (pair? (cdr ts)) (ctx-sym-tok? (cadr ts)))
        (set! svar (cdr (cadr ts)))
        (set! ts (cddr ts)))
      (unless (null? ts) (error "context: trailing tokens in structure declaration" ts))
      (let* ((profile (notation-profile kind))
             (accs (np-accessors profile)))
        (unless (= (length names) (length accs))
          (error "context:" kind "has" (length accs) "components; got" (length names) "in" str))
        (list 'struct svar profile
              (map (lambda (nm acc) (cons nm (list acc svar))) names accs))))))

;;; let v1, ..., vk in <class-expr>
(define (parse-elts-decl toks str)
  (let loop ((ts toks) (vars '()))
    (cond
      ((null? ts) (error "context: element declaration needs `in <class>'" str))
      ((ctx-sym? (car ts) 'in)
       (when (null? (cdr ts)) (error "context: missing class after `in'" str))
       (let ((class (alias-subst (vnb-parse-tokens (cdr ts)) (all-aliases *current-context*))))
         (list 'elts (reverse vars) class)))
      ((eq? (car ts) 'comma) (loop (cdr ts) vars))
      ((ctx-sym-tok? (car ts)) (loop (cdr ts) (cons (cdar ts) vars)))
      (else (error "context: bad element variable" (car ts))))))

;;; ---- collision guard (VNB case-folds: X and x are the SAME name) ----
(define (frame-names f)
  (case (car f)
    ((struct) (cons (cadr f) (map car (list-ref f 3))))   ; svar + alias names
    ((elts)   (cadr f))
    (else '())))

(define (check-context-collisions! frame)
  (let ((existing (apply append (map frame-names *current-context*)))
        (new (frame-names frame)))
    (for-each
     (lambda (n)
       (when (memq n existing)
         (error "context: name" n
                "is already bound -- VNB case-folds, so X and x are the same; pick another letter")))
     new)
    (let dup ((ns new))
      (unless (null? ns)
        (when (memq (car ns) (cdr ns)) (error "context: duplicate name" (car ns) "in declaration"))
        (dup (cdr ns))))))

;;; ---- discharge: resolve a parsed body through the current context ----
(define (frame-wrap f inner)
  (case (car f)
    ((struct) (list 'FORALL (cadr f)
                (list 'IMPLIES (list (np-predicate (caddr f)) (cadr f)) inner)))
    ((elts) (let loop ((vs (cadr f)))
              (if (null? vs) inner
                  (list 'FORALL (car vs)
                    (list 'IMPLIES (list 'IN (car vs) (caddr f)) (loop (cdr vs)))))))))

(define (context-discharge body)
  (let* ((b1 (alias-subst body (all-aliases *current-context*)))
         (sframes (filter (lambda (f) (eq? (car f) 'struct)) *current-context*))
         (b2 (cond ((null? sframes) b1)
                   ((null? (cdr sframes))
                    (struct-term (caddr (car sframes)) (cadr (car sframes)) b1))
                   (else
                    (display ";VNB note: multiple structures active -- + * - ^ left unresolved")
                    (newline)
                    (display ";  (use named operators; sort-directed overloading is the next increment)")
                    (newline)
                    b1))))
    (let loop ((fs *current-context*))
      (if (null? fs) b2 (frame-wrap (car fs) (loop (cdr fs)))))))

;;; ---- user-facing commands ----
(define (context str)
  (vnb-guard
   (lambda ()
     (let ((frame (parse-context-decl str)))
       (check-context-collisions! frame)
       (set! *current-context* (append *current-context* (list frame)))
       (show-context)))))

(define (nullify)
  (set! *current-context* '())
  (display ";VNB context nullified -- input is tel-quel (no closure, no remap)")
  (newline))

(define (show-context)
  (if (null? *current-context*)
      (begin (display ";VNB context: ()  -- tel-quel") (newline))
      (begin
        (display ";VNB context (outermost first):") (newline)
        (for-each
         (lambda (f)
           (case (car f)
             ((struct)
              (display ";  let ") (write (map car (list-ref f 3)))
              (display " be a ") (display (np-predicate (caddr f)))
              (display "  [var ") (display (cadr f)) (display "]") (newline))
             ((elts)
              (display ";  let ") (write (cadr f))
              (display " in ") (write (caddr f)) (newline))))
         *current-context*)))
  *current-context*)

;;; ---- context-aware wff: discharge when a context is active ----
;;; Overrides the plain alias in interactive.scm (loaded earlier).  With an
;;; empty context this is exactly make-wff-from-string, so existing use is
;;; unchanged; with a context it parses, resolves, remaps, and discharges.
(define (wff str)
  (if (null? *current-context*)
      (make-wff-from-string str)
      (vnb-guard
       (lambda () (make-wff (context-discharge (vnb-parse-tokens (vnb-tokenize str))))))))

;;; ---- surface differential test: (wff "...") under a ring context == ring-goal ----
(define (run-surface-tests)
  (nullify)
  (context "let [carr, plus, times, neg, zero, unity] be a commutative-ring")
  (context "let a, b, c in carr")
  (let ((got  (wff-formula (wff "c * (a + b) = times(c, a) + times(c, b)")))
        (got2 (wff-formula (wff "plus(a, zero) = a")))
        (want (wff-formula (ring-goal-in 's '(a b c)
                            '(= (* c (+ a b)) (+ (* c a) (* c b))))))
        ;; same active context (a,b,c in carr), so want2 must bind a,b,c too
        (want2 (wff-formula (ring-goal-in 's '(a b c) '(= (+ a 0) a)))))
    (nullify)
    (let ((ok1 (equal? got want)) (ok2 (equal? got2 want2)))
      (unless ok1
        (display "  SURFACE MISMATCH (distributivity)") (newline)
        (display "   got:  ") (write got)  (newline)
        (display "   want: ") (write want) (newline))
      (unless ok2
        (display "  SURFACE MISMATCH (named op + constant)") (newline)
        (display "   got:  ") (write got2)  (newline)
        (display "   want: ") (write want2) (newline))
      (display "=== surface vs ring-goal: ")
      (display (+ (if ok1 1 0) (if ok2 1 0))) (display "/2 identical ===") (newline)
      (+ (if ok1 0 1) (if ok2 0 1)))))
