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

(define (make-notation-profile predicate carrier ops lits)
  (list 'notation-profile predicate carrier ops lits))
(define (notation-profile? p) (and (pair? p) (eq? (car p) 'notation-profile)))
(define (np-predicate p) (list-ref p 1))
(define (np-carrier   p) (list-ref p 2))
(define (np-ops       p) (list-ref p 3))
(define (np-lits      p) (list-ref p 4))

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
    '((0 . zero) (1 . one))))

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
