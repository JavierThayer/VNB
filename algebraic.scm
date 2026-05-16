;;; algebraic.scm -- basic algebraic structures
;;;
;;; Defines: SEMIGROUP, MONOID, GROUP, RING, METRIC-SPACE
;;;
;;; Each declare-structure call installs:
;;;   - accessor macetes: OP(s) -> (NTH k s)
;;;   - IS-NAME definitional axiom (IFF expansion)
;;;
;;; Characteristic axioms are installed by the theory-add-axiom! calls below.
;;; Accessor notation in axiom formulas:
;;;   OP(s)       written as  (OP s)
;;;   OP(s)(a,b)  written as  ((OP s) a b)

;;; -----------------------------------------------------------------------
;;; SEMIGROUP: carrier A, binary operation MUL
;;;
;;; Accessor indices: A -> 1, MUL -> 2

(def-structure-from-clauses 'SEMIGROUP
  '((carriers A)
    (op MUL (A A) A)))

;;; forall s. IS-SEMIGROUP(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'semigroup-assoc
  '(FORALL s
     (IMPLIES (IS-SEMIGROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; -----------------------------------------------------------------------
;;; MONOID: carrier A, operation MUL, identity element E
;;;
;;; Accessor indices: A -> 1, MUL -> 2, E -> 3

(def-structure-from-clauses 'MONOID
  '((carriers A)
    (op MUL (A A) A)
    (constant E A)))

;;; forall s. IS-MONOID(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'monoid-assoc
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-MONOID(s) => forall a in A(s). E(s)*a = a
(theory-add-axiom! *current-theory* 'monoid-left-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) (E s) a) a))))))

;;; forall s. IS-MONOID(s) => forall a in A(s). a*E(s) = a
(theory-add-axiom! *current-theory* 'monoid-right-id
  '(FORALL s
     (IMPLIES (IS-MONOID s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) a (E s)) a))))))

;;; E(m) ∈ A(m) when IS-MONOID(m).
;;; DERIVED (REVIEW.md R-1): follows from the auto-generated IS-MONOID IFF
;;; (the `(constant E A)` clause in def-structure-from-clauses gives
;;; (IN (E m) (A m)) as a direct conjunct).  Kept as a named axiom for
;;; direct use; eventually demote to a proven lemma.
(theory-add-axiom! *current-theory* 'monoid-identity-in
  '(FORALL m (IMPLIES (IS-MONOID m) (IN (E m) (A m)))))

;;; Carrier closed under MUL: a,b ∈ A(m) => (MUL m)(a)(b) ∈ A(m).
;;; DERIVED (REVIEW.md R-4): IS-MONOID IFF gives (IN (MUL m) (FUN (CARTESIAN A A) A)),
;;; then fun-apply-type closes (MUL m)(a)(b).  Kept as a named axiom for
;;; direct use; eventually demote to a proven lemma.
(theory-add-axiom! *current-theory* 'monoid-carrier-closed-mul
  '(FORALL m (FORALL a (FORALL b
      (IMPLIES (AND (IS-MONOID m) (AND (IN a (A m)) (IN b (A m))))
               (IN ((MUL m) a b) (A m)))))))

;;; -----------------------------------------------------------------------
;;; GROUP: carrier A, operation MUL, identity E, inverse INV
;;;
;;; Accessor indices: A -> 1, MUL -> 2, E -> 3, INV -> 4
;;;
;;; Three axioms (left-only) suffice: assoc + left-id + left-inv.

(def-structure-from-clauses 'GROUP
  '((carriers A)
    (op MUL (A A) A)
    (constant E A)
    (op INV (A) A)))

;;; forall s. IS-GROUP(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'group-assoc
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). E(s)*a = a
(theory-add-axiom! *current-theory* 'group-left-id
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) (E s) a) a))))))

;;; forall s. IS-GROUP(s) => forall a in A(s). INV(s)(a)*a = E(s)
(theory-add-axiom! *current-theory* 'group-left-inv
  '(FORALL s
     (IMPLIES (IS-GROUP s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) ((INV s) a) a) (E s)))))))

;;; -----------------------------------------------------------------------
;;; RING: carrier A, addition ADD, multiplication MUL,
;;;       additive inverse NEG, zero ZERO, multiplicative identity ONE
;;;
;;; Accessor indices: A -> 1, ADD -> 2, MUL -> 3, NEG -> 4, ZERO -> 5, ONE -> 6
;;;
;;; (A, ADD, ZERO, NEG) is an abelian group; (A, MUL, ONE) is a monoid;
;;; MUL distributes over ADD.

(def-structure-from-clauses 'RING
  '((carriers A)
    (op ADD (A A) A)
    (op MUL (A A) A)
    (op NEG (A) A)
    (constant ZERO A)
    (constant ONE A)))

;;; forall s. IS-RING(s) => forall a,b,c in A(s). (a+b)+c = a+(b+c)
(theory-add-axiom! *current-theory* 'ring-add-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((ADD s) ((ADD s) a b) c)
                ((ADD s) a ((ADD s) b c))))))))))))

;;; forall s. IS-RING(s) => forall a,b in A(s). a+b = b+a
(theory-add-axiom! *current-theory* 'ring-add-comm
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (= ((ADD s) a b) ((ADD s) b a)))))))))

;;; forall s. IS-RING(s) => forall a in A(s). ZERO(s)+a = a
(theory-add-axiom! *current-theory* 'ring-add-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((ADD s) (ZERO s) a) a))))))

;;; forall s. IS-RING(s) => forall a in A(s). NEG(s)(a)+a = ZERO(s)
(theory-add-axiom! *current-theory* 'ring-add-left-inv
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((ADD s) ((NEG s) a) a) (ZERO s)))))))

;;; forall s. IS-RING(s) => forall a,b,c in A(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'ring-mul-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

;;; forall s. IS-RING(s) => forall a in A(s). ONE(s)*a = a
(theory-add-axiom! *current-theory* 'ring-mul-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) (ONE s) a) a))))))

;;; forall s. IS-RING(s) => forall a in A(s). a*ONE(s) = a
(theory-add-axiom! *current-theory* 'ring-mul-right-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (= ((MUL s) a (ONE s)) a))))))

;;; forall s. IS-RING(s) => forall a,b,c in A(s). a*(b+c) = a*b + a*c
(theory-add-axiom! *current-theory* 'ring-left-dist
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) a ((ADD s) b c))
                ((ADD s) ((MUL s) a b) ((MUL s) a c))))))))))))

;;; forall s. IS-RING(s) => forall a,b,c in A(s). (a+b)*c = a*c + b*c
(theory-add-axiom! *current-theory* 'ring-right-dist
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (A s))
         (FORALL b (IMPLIES (IN b (A s))
           (FORALL c (IMPLIES (IN c (A s))
             (= ((MUL s) ((ADD s) a b) c)
                ((ADD s) ((MUL s) a c) ((MUL s) b c))))))))))))

;;; ZERO(r) ∈ A(r) when IS-RING(r).
;;; DERIVED (REVIEW.md R-2): follows from the auto-generated IS-RING IFF
;;; (the `(constant ZERO A)` clause).  Kept for direct use.
(theory-add-axiom! *current-theory* 'ring-zero-in
  '(FORALL r (IMPLIES (IS-RING r) (IN (ZERO r) (A r)))))

;;; Carrier closed under ADD: a,b ∈ A(r) => (ADD r)(a)(b) ∈ A(r).
;;; DERIVED (REVIEW.md R-3): IS-RING IFF gives (IN (ADD r) (FUN (CARTESIAN A A) A)),
;;; then fun-apply-type closes (ADD r)(a)(b).  Kept for direct use.
(theory-add-axiom! *current-theory* 'ring-carrier-closed-add
  '(FORALL r (FORALL a (FORALL b
      (IMPLIES (AND (IS-RING r) (AND (IN a (A r)) (IN b (A r))))
               (IN ((ADD r) a b) (A r)))))))

;;; -----------------------------------------------------------------------
;;; RING-PROD: product of two rings
;;;
;;; RING-PROD(X, Y) is the product ring with carrier CARTESIAN(A(X), A(Y))
;;; and componentwise operations.  Total: defined for any X, Y.
;;; IS-RING(RING-PROD(X,Y)) holds when both IS-RING(X) and IS-RING(Y).
;;;
;;; Accessor layout (matches RING declaration):
;;;   NTH 1 = A    carrier CARTESIAN(A(X), A(Y))
;;;   NTH 2 = ADD  pointwise addition
;;;   NTH 3 = MUL  pointwise multiplication
;;;   NTH 4 = NEG  pointwise negation
;;;   NTH 5 = ZERO [ZERO(X), ZERO(Y)]
;;;   NTH 6 = ONE  [ONE(X), ONE(Y)]

(def-functoid 'RING-PROD '(X Y)
  '(LIST
     (CARTESIAN (A X) (A Y))
     (VNB-LAMBDA (LIST p q)
       (LIST ((ADD X) (NTH 1 p) (NTH 1 q))
             ((ADD Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p q)
       (LIST ((MUL X) (NTH 1 p) (NTH 1 q))
             ((MUL Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p)
       (LIST ((NEG X) (NTH 1 p))
             ((NEG Y) (NTH 2 p))))
     (LIST (ZERO X) (ZERO Y))
     (LIST (ONE X) (ONE Y))))

;;; IS-RING(X) ∧ IS-RING(Y) → IS-RING(RING-PROD(X,Y))
(theory-add-axiom! *current-theory* 'ring-prod-is-ring
  '(FORALL X (IMPLIES (IS-RING X)
      (FORALL Y (IMPLIES (IS-RING Y)
        (IS-RING (RING-PROD X Y)))))))

;;; -----------------------------------------------------------------------
;;; ZERO-RING: the terminal ring (carrier = {0}, all operations return 0)
;;;
;;; In the zero ring 0 = 1; all operations collapse to the constant 0.
;;; This is the 0-fold product: the identity for RING-PROD up to isomorphism.

(def-constant 'ZERO-RING
  (list 'zero-ring-def
        '(= ZERO-RING
            (LIST (MAKE-SET (LIST 0))
                  (VNB-LAMBDA (LIST p q) 0)
                  (VNB-LAMBDA (LIST p q) 0)
                  (VNB-LAMBDA (LIST p) 0)
                  0
                  0))))

(theory-add-axiom! *current-theory* 'zero-ring-is-ring
  '(IS-RING ZERO-RING))

;;; -----------------------------------------------------------------------
;;; METRIC-SPACE: carrier X, distance function D : X x X -> RR
;;;
;;; Accessor indices: X -> 1, D -> 2
;;;
;;; Real arithmetic uses the built-in <= and +.

(def-structure-from-clauses 'METRIC-SPACE
  '((carriers X)
    (op D (X X) RR)))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). 0 <= D(s)(x,y)
(theory-add-axiom! *current-theory* 'metric-pos
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (<= 0 ((D s) x y)))))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x in X(s). D(s)(x,x) = 0
(theory-add-axiom! *current-theory* 'metric-self-zero
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (= ((D s) x x) 0))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = 0 => x = y
(theory-add-axiom! *current-theory* 'metric-zero-eq
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (IMPLIES (= ((D s) x y) 0) (= x y)))))))))

;;; forall s. IS-METRIC-SPACE(s) => forall x,y in X(s). D(s)(x,y) = D(s)(y,x)
(theory-add-axiom! *current-theory* 'metric-sym
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (= ((D s) x y) ((D s) y x)))))))))

;;; forall s. IS-METRIC-SPACE(s) =>
;;;   forall x,y,z in X(s). D(s)(x,z) <= D(s)(x,y) + D(s)(y,z)
(theory-add-axiom! *current-theory* 'metric-triangle
  '(FORALL s
     (IMPLIES (IS-METRIC-SPACE s)
       (FORALL x (IMPLIES (IN x (X s))
         (FORALL y (IMPLIES (IN y (X s))
           (FORALL z (IMPLIES (IN z (X s))
             (<= ((D s) x z)
                 (+ ((D s) x y) ((D s) y z))))))))))))

;;; -----------------------------------------------------------------------
;;; Polynomial normal form -- ring identity decision procedure
;;;
;;; Represents elements of the free associative ZZ-algebra on a caller-
;;; supplied set of generators (non-commutative polynomial ring).
;;; Addition is commutative; multiplication respects generator order.
;;;
;;;   word = list of generator symbols  e.g. '(x y x) means x*y*x
;;;   term = (word . integer-coeff)     zero coefficients are dropped
;;;   poly = list of terms sorted by word<?
;;;
;;; Any symbol that arith-eval-term cannot reduce to a number is treated as
;;; a ring generator (non-commuting).  Known numeric constants (0, 1, PI …)
;;; are folded into coefficients.  Any sub-expression that is neither
;;; arithmetic nor +/-/* applied to such causes vnb->poly to return #f.

;;; Length-then-lex ordering on words.
(define (word<? w1 w2)
  (let ((l1 (length w1)) (l2 (length w2)))
    (cond ((< l1 l2) #t)
          ((> l1 l2) #f)
          (else (let lp ((a w1) (b w2))
                  (cond ((null? a) #f)
                        ((symbol<? (car a) (car b)) #t)
                        ((symbol<? (car b) (car a)) #f)
                        (else (lp (cdr a) (cdr b)))))))))

;;; Merge two sorted poly lists, combining coefficients for equal words.
(define (poly-add p q)
  (cond ((null? p) q)
        ((null? q) p)
        (else
         (let ((w1 (caar p)) (c1 (cdar p))
               (w2 (caar q)) (c2 (cdar q)))
           (cond ((word<? w1 w2) (cons (car p) (poly-add (cdr p) q)))
                 ((word<? w2 w1) (cons (car q) (poly-add p (cdr q))))
                 (else
                  (let ((c    (+ c1 c2))
                        (rest (poly-add (cdr p) (cdr q))))
                    (if (zero? c) rest (cons (cons w1 c) rest)))))))))

(define (poly-neg p)
  (map (lambda (t) (cons (car t) (- (cdr t)))) p))

;;; Non-commutative multiplication: p is on the left.
;;; Prepending a fixed word w to a sorted list of words preserves sort order
;;; (all results share the same prefix; relative order decided by suffix).
(define (poly-mul p q)
  (if (null? p) '()
      (poly-add
        (map (lambda (qt)
               (cons (append (caar p) (car qt))
                     (* (cdar p) (cdr qt))))
             q)
        (poly-mul (cdr p) q))))

;;; Convert a VNB ring expression to a poly.
;;; Symbols that arith-eval-term cannot reduce to a number are ring generators.
;;; Returns #f for any sub-expression that cannot be polynomialized.
(define (vnb->poly expr)
  (cond
    ((number? expr)
     (if (zero? expr) '() (list (cons '() expr))))
    ((symbol? expr)
     (let ((v (arith-eval-term expr)))
       (if (and v (number? v))
           (if (zero? v) '() (list (cons '() v)))
           (list (cons (list expr) 1)))))    ; unknown symbol → generator
    ((pair? expr)
     (case (car expr)
       ((+)
        (let lp ((args (cdr expr)) (acc '()))
          (if (null? args) acc
              (let ((p (vnb->poly (car args))))
                (and p (lp (cdr args) (poly-add acc p)))))))
       ((*)
        (let lp ((args (cdr expr)) (acc (list (cons '() 1))))
          (if (null? args) acc
              (let ((p (vnb->poly (car args))))
                (and p (lp (cdr args) (poly-mul acc p)))))))
       ((-)
        (cond
          ((null? (cdr expr)) #f)
          ((null? (cddr expr))
           (let ((p (vnb->poly (cadr expr))))
             (and p (poly-neg p))))
          (else
           (let ((head (vnb->poly (cadr expr))))
             (and head
                  (let lp ((args (cddr expr)) (acc head))
                    (if (null? args) acc
                        (let ((p (vnb->poly (car args))))
                          (and p (lp (cdr args)
                                     (poly-add acc (poly-neg p))))))))))))
       (else
        (let ((v (arith-eval-term expr)))
          (and v (number? v)
               (if (zero? v) '() (list (cons '() v))))))))
    (else #f)))

;;; Collect unique generator symbols from two polynomials.
;;; Generators are the symbols appearing in word positions (not coefficients).
(define (poly-generators p1 p2)
  (let loop ((terms (append p1 p2)) (seen '()))
    (if (null? terms)
        seen
        (let inner ((gs (caar terms)) (s seen))
          (if (null? gs)
              (loop (cdr terms) s)
              (inner (cdr gs)
                     (if (memq (car gs) s) s (cons (car gs) s))))))))

;;; Ring domains: the five standard number systems.
;;; string-downcase makes the check work on both case-folding (MIT 11.2)
;;; and case-sensitive (MIT 12.1) Scheme readers.
(define *ring-domain-names* '("nn" "zz" "qq" "rr" "cc"))

(define (ring-domain? set-expr)
  (and (symbol? set-expr)
       (member (string-downcase (symbol->string set-expr))
               *ring-domain-names*)))

;;; Peel a chain of (FORALL v (IMPLIES (IN v D) body)) where D is a ring
;;; domain, returning (cons inner-formula alist-of-(var . domain)).
;;; Stops and returns #f if a FORALL is found whose body is NOT a ring-typed
;;; IMPLIES.  For a non-FORALL input returns (cons input '()) so the
;;; post-di bare (= e1 e2) case works without special-casing.
(define (peel-ring-foralls raw)
  (let loop ((g raw) (qvars '()))
    (if (and (pair? g) (eq? (car g) 'FORALL))
        (let* ((v    (quantifier-var g))
               (body (quantifier-body g))
               (ante (and (pair? body) (eq? (car body) 'IMPLIES)
                          (binary-left body))))
          (if (and ante
                   (pair? ante) (= (length ante) 3)
                   (eq? (car ante) 'IN)
                   (eq? (cadr ante) v)
                   (ring-domain? (caddr ante)))
              (loop (binary-right body)
                    (cons (cons v (caddr ante)) qvars))
              #f))                       ; FORALL but not ring-typed → fail
        (cons g qvars))))               ; non-FORALL: inner formula reached

;;; Check that every generator has ring certification from one of two sources:
;;;   (a) it was peeled from a typed quantifier (in qvars alist), or
;;;   (b) there is an (IN v D) assumption in the sequent context.
(define (ring-vars-ok? gens qvars asms)
  (let check ((vs gens))
    (or (null? vs)
        (let ((v (car vs)))
          (and (or (let ((q (assq v qvars)))
                     (and q (ring-domain? (cdr q))))
                   (let find ((as asms))
                     (cond ((null? as) #f)
                           ((let ((f (wff-formula (car as))))
                              (and (pair? f) (= (length f) 3)
                                   (eq? (car f) 'IN)
                                   (eq? (cadr f) v)
                                   (ring-domain? (caddr f))))
                            #t)
                           (else (find (cdr as))))))
               (check (cdr vs)))))))

;;; Primitive inference: close a ring identity goal by polynomial normalization.
;;; Goal may be a bare (= e1 e2) — generators certified by sequent context — or
;;; a universally quantified (FORALL v (IMPLIES (IN v D) ...)) chain — generators
;;; certified by the quantifier typings themselves, no prior (di) needed.
(define (pi-ring-simplify! sqn)
  (let* ((goal   (sequent-node-assertion sqn))
         (g      (wff-formula goal))
         (dg     (sqn-dg sqn))
         (asms   (sequent-node-assumptions sqn))
         (peeled (peel-ring-foralls g)))
    (and peeled
         (let ((inner (car peeled))
               (qvars (cdr peeled)))
           (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
                (let ((p1 (vnb->poly (cadr inner)))
                      (p2 (vnb->poly (caddr inner))))
                  (and p1 p2
                       (equal? p1 p2)
                       (ring-vars-ok? (poly-generators p1 p2) qvars asms)
                       (dg-apply-rule! dg 'ring-simplify '() sqn))))))))
