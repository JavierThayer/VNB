;;; ring-simplify.scm -- polynomial-normal-form ring identity decision procedure
;;;
;;; Represents elements of the free associative ZZ-algebra on a caller-
;;; supplied set of generators (non-commutative polynomial ring).
;;; Addition is commutative; multiplication respects generator order.
;;;
;;;   word = list of generators       e.g. '(x y x) means x*y*x
;;;   term = (word . integer-coeff)    zero coefficients are dropped
;;;   poly = list of terms sorted by word<?
;;;
;;; A GENERATOR is any maximal sub-term arith-eval-term cannot reduce to a
;;; number: a bare symbol like x, OR a compound term like f(x) whose head is
;;; not one of +/-/*.  Generators do not commute.  Numeric constants
;;; (0, 1, PI …) fold into coefficients.  Only a genuinely malformed term (a
;;; non-symbol non-pair, or a degenerate (-) with no operands) makes
;;; vnb->poly return #f.
;;;
;;; SOUNDNESS for compound generators rests entirely on ring-vars-ok?: every
;;; generator must be certified (IN g D) for a ring domain D.  In VNB
;;; membership entails definedness, so the certification doubles as a
;;; definedness guarantee.  Hence 3 + f(x) = 1 + f(x) + 2 -- valid only when
;;; f(x) is defined -- fires exactly when (IN (f x) D) is in context, and the
;;; command does nothing otherwise.  No separate is-defined premise is needed:
;;; the ring-domain certification already supplies it.

;;; Total order on generators.  A generator is a symbol or a compound term,
;;; so symbol<? alone no longer suffices.  Order by a type rank
;;; (number < symbol < () < pair), then within a class: numbers by <, symbols
;;; by symbol<?, pairs lexicographically by car then cdr (recursively).  Total
;;; and deterministic, so monomial canonicalisation has a unique normal form.
;;; On two symbols it agrees with symbol<?, so symbol-only behaviour is
;;; unchanged.
(define (gen-rank x)
  (cond ((number? x) 0) ((symbol? x) 1) ((null? x) 2) ((pair? x) 3) (else 4)))
(define (gen<? a b)
  (let ((ra (gen-rank a)) (rb (gen-rank b)))
    (cond ((< ra rb) #t)
          ((> ra rb) #f)
          (else
           (case ra
             ((0) (< a b))
             ((1) (symbol<? a b))
             ((3) (cond ((gen<? (car a) (car b)) #t)
                        ((gen<? (car b) (car a)) #f)
                        (else (gen<? (cdr a) (cdr b)))))
             (else #f))))))      ; () vs (), or non-term atoms: not strictly <

;;; Length-then-lex ordering on words.
(define (word<? w1 w2)
  (let ((l1 (length w1)) (l2 (length w2)))
    (cond ((< l1 l2) #t)
          ((> l1 l2) #f)
          (else (let lp ((a w1) (b w2))
                  (cond ((null? a) #f)
                        ((gen<? (car a) (car b)) #t)
                        ((gen<? (car b) (car a)) #f)
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
        ;; A compound term whose head is not +/-/*.  If arith-eval can reduce
        ;; it to a number it is a constant; otherwise treat the whole term as
        ;; a single opaque generator (e.g. f(x)).  Soundness is guarded later
        ;; by ring-vars-ok? requiring (IN expr D).
        (let ((v (arith-eval-term expr)))
          (if (and v (number? v))
              (if (zero? v) '() (list (cons '() v)))
              (list (cons (list expr) 1)))))))
    (else #f)))

;;; Collect unique generators from two polynomials.  Generators may be
;;; compound terms, so dedup with member (equal?), not memq (eq?).
(define (poly-generators p1 p2)
  (let loop ((terms (append p1 p2)) (seen '()))
    (if (null? terms)
        seen
        (let inner ((gs (caar terms)) (s seen))
          (if (null? gs)
              (loop (cdr terms) s)
              (inner (cdr gs)
                     (if (member (car gs) s) s (cons (car gs) s))))))))

;;; Dedupe a list under equal? (generators may be compound terms).
(define (dedup-equal lst)
  (let loop ((xs lst) (seen '()))
    (cond ((null? xs) (reverse seen))
          ((member (car xs) seen) (loop (cdr xs) seen))
          (else (loop (cdr xs) (cons (car xs) seen))))))

;;; SOURCE generators of a concrete-surface expression: every maximal sub-term
;;; that (c)vnb->poly would treat as a generator, INCLUDING ones that later
;;; cancel.  poly-generators sees only the surviving normal-form monomials, so
;;; it misses a generator that cancels within a side (x in `x - x', y in
;;; `x + y - y').  Definedness must cover the vanished ones too: in VNB `=' is
;;; partial, so `e1 = e2' asserts e1, e2 DEFINED, and e_i is defined only if all
;;; its atoms lie in the ring carrier.  Mirrors (c)vnb->poly's case split exactly
;;; (same surface for the commutative and non-commutative simplifiers); a
;;; non-ring-op compound is one opaque generator (not recursed), as there.
(define (cvnb-source-generators expr)
  (cond
    ((number? expr) '())
    ((symbol? expr)
     (let ((v (arith-eval-term expr)))
       (if (and v (number? v)) '() (list expr))))
    ((pair? expr)
     (case (car expr)
       ((+ * -)            (apply append (map cvnb-source-generators (cdr expr))))
       ((binplus bintimes) (append (cvnb-source-generators (cadr expr))
                                   (cvnb-source-generators (caddr expr))))
       ((binneg)           (cvnb-source-generators (cadr expr)))
       (else
        (let ((v (arith-eval-term expr)))
          (if (and v (number? v)) '() (list expr))))))
    (else '())))

;;; The two source terms' generators, deduped — the set the definedness check
;;; must range over for a `(= e1 e2)' goal on the concrete surface.
(define (cvnb-eq-source-generators e1 e2)
  (dedup-equal (append (cvnb-source-generators e1) (cvnb-source-generators e2))))

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
          (and (or (let ((q (assoc v qvars)))   ; assoc: v may be a compound term
                     (and q (ring-domain? (cdr q))))
                   (let find ((as asms))
                     (cond ((null? as) #f)
                           ((let ((f (wff-formula (car as))))
                              (and (pair? f) (= (length f) 3)
                                   (eq? (car f) 'IN)
                                   (equal? (cadr f) v)   ; equal?: certify (IN (f x) D)
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
                       ;; certify SOURCE generators (incl. cancelled), not just
                       ;; survivors -- else `x - x = 0' closes for untyped x.
                       (ring-vars-ok? (cvnb-eq-source-generators
                                        (cadr inner) (caddr inner))
                                      qvars asms)
                       (dg-apply-rule! dg 'ring-simplify '() sqn))))))))
