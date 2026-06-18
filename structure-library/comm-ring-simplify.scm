;;; comm-ring-simplify.scm -- commutative-ring identity decision procedure.
;;;
;;; The commutative analogue of ring-simplify.scm.  That file works in the
;;; free *associative* ZZ-algebra (words = ordered generator lists, so x*y and
;;; y*x stay distinct); this one works in the free *commutative* ring
;;; ZZ[generators].  A monomial is a multiset of generators, canonicalised as a
;;; sorted generator list, so x*y and y*x share one normal form.  Two
;;; commutative-ring terms are equal in EVERY commutative ring iff their
;;; sum-of-monomials normal forms coincide; normal-form equality is therefore a
;;; sound and complete certificate -- a decision procedure, run as a trusted
;;; oracle rather than mechanised through the ring properties (warrant below,
;;; [[feedback-warrants]]).
;;;
;;; Reuses ring-simplify.scm's plumbing wholesale: word<? (length-then-lex
;;; still orders sorted words), poly-add / poly-neg (merge by word equality),
;;; poly-generators, ring-domain?, peel-ring-foralls, ring-vars-ok?.  Only
;;; multiplication changes -- the product monomial is the SORTED concatenation
;;; of the two factor monomials, so commutativity lives in the representation.
;;; Coefficients live in ZZ; any maximal sub-term arith-eval-term cannot reduce
;;; to a number is a generator -- a bare symbol or a compound term like f(x)
;;; (the ZZ-module / [[project-ag-are-zz-modules]] view of the additive group).
;;; As in ring-simplify.scm, a compound generator is sound only because
;;; cring-vars-ok? requires it certified (IN g D) / (IN g (A R)), which in VNB
;;; entails it is defined.
;;;
;;; Dependencies: ring-simplify.scm (loaded just before), arith-eval.scm.

;;; Canonicalise a monomial: sort its generators (multiset normal form).
;;; gen<? (ring-simplify.scm) totally orders symbols and compound terms alike.
(define (cmonomial-sort gens)
  (sort gens (lambda (a b) (gen<? a b))))

;;; Normalise an unsorted term list (each term a sorted-word . coeff): sort by
;;; word<?, combine equal monomials, drop zero-coefficient terms.
(define (cpoly-normalize terms)
  (let loop ((ts (sort terms (lambda (a b) (word<? (car a) (car b))))))
    (cond ((null? ts) '())
          ((null? (cdr ts))
           (if (zero? (cdar ts)) '() ts))
          ((equal? (caar ts) (caadr ts))
           (loop (cons (cons (caar ts) (+ (cdar ts) (cdadr ts)))
                       (cddr ts))))
          ((zero? (cdar ts)) (loop (cdr ts)))
          (else (cons (car ts) (loop (cdr ts)))))))

;;; Commutative product: each pair of monomials yields the sorted concatenation
;;; of their generators (coefficients multiply); renormalise the flat result.
(define (cpoly-mul p q)
  (cpoly-normalize
    (apply append
      (map (lambda (pt)
             (map (lambda (qt)
                    (cons (cmonomial-sort (append (car pt) (car qt)))
                          (* (cdr pt) (cdr qt))))
                  q))
           p))))

;;; Convert a VNB ring expression to a commutative poly (sorted-word terms).
;;; Identical to vnb->poly except multiplication is commutative (cpoly-mul).
;;; Returns #f for any sub-expression that cannot be polynomialized.
(define (cvnb->poly expr)
  (cond
    ((number? expr)
     (if (zero? expr) '() (list (cons '() expr))))
    ((symbol? expr)
     (let ((v (arith-eval-term expr)))
       (if (and v (number? v))
           (if (zero? v) '() (list (cons '() v)))
           (list (cons (list expr) 1)))))    ; unknown symbol -> generator
    ((pair? expr)
     (case (car expr)
       ((+)
        (let lp ((args (cdr expr)) (acc '()))
          (if (null? args) acc
              (let ((p (cvnb->poly (car args))))
                (and p (lp (cdr args) (poly-add acc p)))))))
       ((*)
        (let lp ((args (cdr expr)) (acc (list (cons '() 1))))
          (if (null? args) acc
              (let ((p (cvnb->poly (car args))))
                (and p (lp (cdr args) (cpoly-mul acc p)))))))
       ((-)
        (cond
          ((null? (cdr expr)) #f)
          ((null? (cddr expr))
           (let ((p (cvnb->poly (cadr expr))))
             (and p (poly-neg p))))
          (else
           (let ((head (cvnb->poly (cadr expr))))
             (and head
                  (let lp ((args (cddr expr)) (acc head))
                    (if (null? args) acc
                        (let ((p (cvnb->poly (car args))))
                          (and p (lp (cdr args)
                                     (poly-add acc (poly-neg p))))))))))))
       ;; binplus/bintimes/binneg: the binary structure-code surface, equal
       ;; to +/*/- extensionally (numeric-instances.scm).  Accepted here so a
       ;; concrete ring identity written with the structure operators
       ;; normalises just like the n-ary kid surface.
       ((binplus)
        (let ((p (cvnb->poly (cadr expr)))
              (q (cvnb->poly (caddr expr))))
          (and p q (poly-add p q))))
       ((bintimes)
        (let ((p (cvnb->poly (cadr expr)))
              (q (cvnb->poly (caddr expr))))
          (and p q (cpoly-mul p q))))
       ((binneg)
        (let ((p (cvnb->poly (cadr expr))))
          (and p (poly-neg p))))
       (else
        ;; Compound term, head not +/-/* or a binary structure alias: a number
        ;; if arith-eval reduces it, else an opaque generator (e.g. f(x)).
        ;; cring-vars-ok? backstops soundness via (IN expr D).
        (let ((v (arith-eval-term expr)))
          (if (and v (number? v))
              (if (zero? v) '() (list (cons '() v)))
              (list (cons (list expr) 1)))))))
    (else #f)))

;;; =======================================================================
;;; Symbolic normal form (the "simplify" / calculator surface).
;;;
;;; cvnb->poly already computes the sum-of-monomials canonical form of a
;;; concrete-surface expression; (crs) only ever uses it to COMPARE two sides
;;; and throws the polynomial away.  These two helpers expose the other half:
;;; take ONE free term and print its canonical commutative-ring form, so the
;;; calculator can turn (x+y)*(x+y) - x*y into x^2 + x*y + y^2.  No new math --
;;; just a literal-power pre-pass (cvnb->poly has no `^') and a poly->term
;;; printer (the inverse of the reader above), rendered via expression->string.
;;; =======================================================================

;;; Pre-expand a literal natural-number power (^ b k) / (expt b k) into the
;;; k-fold product cvnb->poly understands; recurse through every subterm.  A
;;; non-literal or negative exponent is left intact (becomes an opaque
;;; generator downstream, which is the honest thing to do).
(define (cvnb-expand-pow e)
  (cond
    ((not (pair? e)) e)
    ((and (memq (car e) '(power ^ expt))
          (pair? (cdr e)) (pair? (cddr e)) (null? (cdddr e))
          (integer? (caddr e)) (>= (caddr e) 0))
     ;; NB: VNB shadows Scheme's make-list (expressions.scm builds a LIST
     ;; term), so build the k-fold repeat by hand.
     (let ((base (cvnb-expand-pow (cadr e))) (k (caddr e)))
       (cond ((= k 0) 1)
             ((= k 1) base)
             (else (cons '* (let rep ((i k) (acc '()))
                              (if (= i 0) acc (rep (- i 1) (cons base acc)))))))))
    (else (cons (car e) (map cvnb-expand-pow (cdr e))))))

;;; Render one canonicalised monomial (a sorted generator multiset) as a VNB
;;; factor: run-length-encode repeats into (^ g n), join distinct generators
;;; with `*'.  The empty monomial is the unit, returned as #f so the caller
;;; can attach the bare coefficient.
(define (cmonomial->term gens)
  (if (null? gens) #f
      (let loop ((gs gens) (factors '()))
        (if (null? gs)
            (let ((fs (reverse factors)))
              (if (null? (cdr fs)) (car fs) (cons '* fs)))
            (let count ((rest (cdr gs)) (n 1))
              (if (and (pair? rest) (equal? (car rest) (car gs)))
                  (count (cdr rest) (+ n 1))
                  (loop rest
                        ;; head `power' so expression->string renders g^n infix
                        (cons (if (= n 1) (car gs) (list 'power (car gs) n))
                              factors))))))))

;;; Attach an integer coefficient to a monomial term, using the ABSOLUTE value
;;; (sign is handled by the +/- assembly in cpoly->term).  |c|=1 with a real
;;; monomial drops the coefficient; an empty monomial yields the bare |c|.
(define (cterm->term coeff mono)
  (let ((a (abs coeff)))
    (cond ((not mono) a)
          ((= a 1) mono)
          (else (list '* a mono)))))

;;; Inverse of cvnb->poly: a canonical poly (sorted (monomial . coeff) terms)
;;; back to a readable VNB term.  Positive terms are joined by `+'; negative
;;; terms are subtracted, so we print x^2 + y^2 - x*y rather than x^2 + y^2 +
;;; (-1)*x*y.  The empty poly is 0.
(define (cpoly->term poly)
  (if (null? poly) 0
      (let* ((pos (filter (lambda (t) (> (cdr t) 0)) poly))
             (neg (filter (lambda (t) (< (cdr t) 0)) poly))
             (->t (lambda (t) (cterm->term (cdr t) (cmonomial->term (car t)))))
             (pos-part
              (cond ((null? pos) #f)
                    ((null? (cdr pos)) (->t (car pos)))
                    (else (cons '+ (map ->t pos))))))
        (cond
          ((null? neg) (or pos-part 0))
          (pos-part (cons '- (cons pos-part (map ->t neg))))
          ;; all-negative: negate the sum of the magnitudes
          ((null? (cdr neg)) (list '- (->t (car neg))))
          (else (list '- (cons '+ (map ->t neg))))))))

;;; Top-level: a concrete-surface expression (string or s-expr) to its
;;; canonical commutative-ring term, or #f if it is not polynomializable
;;; (e.g. contains division).  Pure -- no proof state touched.
(define (cring-normal-form expr)
  (let ((poly (cvnb->poly (cvnb-expand-pow expr))))
    (and poly (cpoly->term poly))))

;;; ----- In-formula simplification: find a concrete ring redex in a goal -----
;;; The (simp) tactic rewrites a commutative-ring SUBTERM of the goal to its
;;; canonical form in place (the calculator's normal form, but as a sound proof
;;; step -- see cmd-cring-simp).  These helpers just LOCATE the subterm.

;;; A term is a concrete ring expression when its head is one of the
;;; number-surface ring operators (same set cvnb->poly walks, plus powers).
(define (concrete-ring-head? e)
  (and (pair? e)
       (memq (car e) '(+ * - binplus bintimes binneg power ^ expt))))

;;; Find the OUTERMOST ring subterm of g whose canonical form DIFFERS from it
;;; -- the redex (simp) will rewrite.  Returns (cons e e') or #f.  Never
;;; descends into FORALL/FORSOME bodies: a subterm whose variables are bound
;;; inside g cannot be lifted to a sequent-level equality without capture (the
;;; post-di idiom keeps the ring term at sequent level anyway).  With TARGET (a
;;; raw term) given, finds that exact subterm rather than the outermost.
(define (find-cring-redex g target)
  (define (redex-of e)            ; e' if e simplifies to something different
    (let ((nf (cring-normal-form e)))
      (and nf (not (equal? nf e)) nf)))
  (let walk ((e g))
    (cond
      ((not (pair? e)) #f)
      ((memq (car e) '(FORALL FORSOME)) #f)         ; never enter a binder
      (target
       (if (equal? e target)
           (let ((nf (redex-of e))) (and nf (cons e nf)))
           (let loop ((xs (cdr e)))
             (and (pair? xs) (or (walk (car xs)) (loop (cdr xs)))))))
      ((and (concrete-ring-head? e) (redex-of e))
       => (lambda (nf) (cons e nf)))
      (else
       (let loop ((xs (cdr e)))
         (and (pair? xs) (or (walk (car xs)) (loop (cdr xs)))))))))

;;; SOURCE generators of a concrete subterm with literal powers expanded -- the
;;; set whose carrier-membership (simp)/crs must certify (warrant 2).
(define (cring-redex-source-generators e)
  (dedup-equal (cvnb-source-generators (cvnb-expand-pow e))))

;;; =======================================================================
;;; Generic path: expressions in an ARBITRARY commutative ring R, written
;;; with the structure operators ((ADD R) x y), ((MUL R) x y), ((NEG R) x),
;;; (ZERO R), (ONE R) and carrier elements typed (IN v (A R)).  This is what
;;; "normalise in an arbitrary commutative ring" actually means: R is opaque
;;; (a variable satisfying IS-COMMUTATIVE-RING), its operators are treated
;;; structurally, ONE R is the unit monomial, ZERO R the zero poly, integer
;;; coefficients arise from repeated ADD / NEG.  Soundness is the same
;;; ZZ[generators] completeness theorem -- the concrete path is the special
;;; case where R is a number system and (ADD R) = binplus = +.

;;; Find the ring R named by the first structure operator in e: the R in an
;;; (ADD R)/(MUL R)/(NEG R) head, or in a (ZERO R)/(ONE R) constant.  #f if e
;;; carries no ring operator (e.g. a bare generator).
(define (find-cring e)
  (and (pair? e)
       (let ((h (car e)))
         (cond
           ((and (pair? h) (memq (car h) '(ADD MUL NEG)) (= (length h) 2))
            (cadr h))
           ((and (memq h '(ZERO ONE)) (= (length e) 2))
            (cadr e))
           (else (let loop ((xs e))
                   (and (pair? xs)
                        (or (find-cring (car xs)) (loop (cdr xs))))))))))

;;; Convert an expression over the fixed ring R to a commutative poly.
;;; Symbols are carrier elements (generators); R's ring operators recurse; any
;;; other compound term (a foreign function on the carrier, or a ring operator
;;; over a DIFFERENT ring) is taken as an opaque generator, certified later by
;;; cring-vars-ok? as (IN it (A R)).  Only a non-symbol non-pair returns #f.
(define (cring->poly e R)
  (cond
    ((symbol? e) (list (cons (list e) 1)))      ; carrier element -> generator
    ((pair? e)
     (let ((h (car e)))
       (cond
         ((and (pair? h) (eq? (car h) 'ADD) (equal? (cadr h) R) (= (length e) 3))
          (let ((p (cring->poly (cadr e) R)) (q (cring->poly (caddr e) R)))
            (and p q (poly-add p q))))
         ((and (pair? h) (eq? (car h) 'MUL) (equal? (cadr h) R) (= (length e) 3))
          (let ((p (cring->poly (cadr e) R)) (q (cring->poly (caddr e) R)))
            (and p q (cpoly-mul p q))))
         ((and (pair? h) (eq? (car h) 'NEG) (equal? (cadr h) R) (= (length e) 2))
          (let ((p (cring->poly (cadr e) R))) (and p (poly-neg p))))
         ((and (eq? h 'ZERO) (equal? (cadr e) R) (= (length e) 2)) '())
         ((and (eq? h 'ONE)  (equal? (cadr e) R) (= (length e) 2))
          (list (cons '() 1)))
         (else (list (cons (list e) 1))))))   ; opaque carrier element -> generator
    (else #f)))

;;; SOURCE generators of a generic-ring expression over R: mirrors cring->poly
;;; but keeps cancelled atoms, so the (IN g (A R)) definedness check covers a
;;; generator that vanishes (e.g. x in ((ADD R) x ((NEG R) x))).  ZERO/ONE are
;;; constants (no generator); any other compound is one opaque carrier element.
(define (cring-source-generators e R)
  (cond
    ((symbol? e) (list e))
    ((pair? e)
     (let ((h (car e)))
       (cond
         ((and (pair? h) (eq? (car h) 'ADD) (equal? (cadr h) R) (= (length e) 3))
          (append (cring-source-generators (cadr e) R)
                  (cring-source-generators (caddr e) R)))
         ((and (pair? h) (eq? (car h) 'MUL) (equal? (cadr h) R) (= (length e) 3))
          (append (cring-source-generators (cadr e) R)
                  (cring-source-generators (caddr e) R)))
         ((and (pair? h) (eq? (car h) 'NEG) (equal? (cadr h) R) (= (length e) 2))
          (cring-source-generators (cadr e) R))
         ((and (eq? h 'ZERO) (equal? (cadr e) R) (= (length e) 2)) '())
         ((and (eq? h 'ONE)  (equal? (cadr e) R) (= (length e) 2)) '())
         (else (list e)))))
    (else '())))

(define (cring-eq-source-generators e1 e2 R)
  (dedup-equal (append (cring-source-generators e1 R)
                       (cring-source-generators e2 R))))

;;; Peel (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R) <rest>)) and then a chain
;;; of (FORALL v (IMPLIES (IN v (A R)) ...)).  Returns (list R qvars inner)
;;; with qvars the element variables certified in (A R), or #f if the goal is
;;; not in that shape.
(define (peel-cring-foralls raw)
  (and (pair? raw) (eq? (car raw) 'FORALL)
       (let ((R (quantifier-var raw)) (body (quantifier-body raw)))
         (and (pair? body) (eq? (car body) 'IMPLIES)
              (let ((ante (binary-left body)))
                (and (pair? ante) (= (length ante) 2)
                     (eq? (car ante) 'IS-COMMUTATIVE-RING)
                     (eq? (cadr ante) R)
                     (let loop ((g (binary-right body)) (qvars '()))
                       (if (and (pair? g) (eq? (car g) 'FORALL))
                           (let ((v (quantifier-var g)) (b (quantifier-body g)))
                             (if (and (pair? b) (eq? (car b) 'IMPLIES)
                                      (let ((a (binary-left b)))
                                        (and (pair? a) (= (length a) 3)
                                             (eq? (car a) 'IN)
                                             (eq? (cadr a) v)
                                             (equal? (caddr a) (list 'A R)))))
                                 (loop (binary-right b) (cons v qvars))
                                 #f))
                           (list R qvars g)))))))))

;;; R is certified a commutative ring either by the peeled quantifier or by an
;;; (IS-COMMUTATIVE-RING R) assumption in the sequent context (the post-di case).
(define (cring-certified? R from-quantifier? asms)
  (or from-quantifier?
      (let find ((as asms))
        (and (pair? as)
             (or (let ((f (wff-formula (car as))))
                   (and (pair? f) (= (length f) 2)
                        (eq? (car f) 'IS-COMMUTATIVE-RING)
                        (equal? (cadr f) R)))
                 (find (cdr as)))))))

;;; Every generator is certified in the carrier (A R) by a peeled typing or an
;;; (IN v (A R)) assumption.
(define (cring-vars-ok? gens R qvars asms)
  (let ((carrier (list 'A R)))
    (let check ((vs gens))
      (or (null? vs)
          (let ((v (car vs)))
            (and (or (member v qvars)   ; member: v may be a compound term
                     (let find ((as asms))
                       (and (pair? as)
                            (or (let ((f (wff-formula (car as))))
                                  (and (pair? f) (= (length f) 3)
                                       (eq? (car f) 'IN)
                                       (equal? (cadr f) v)   ; equal?: certify (IN (f x) (A R))
                                       (equal? (caddr f) carrier)))
                                (find (cdr as))))))
                 (check (cdr vs))))))))

;;; Primitive inference: close a commutative-ring identity goal by normal-form
;;; equality.  Tries two parsings, both closing via the 'comm-ring-simplify
;;; rule:
;;;   (1) CONCRETE -- +/*/-/binplus/bintimes/binneg over a number domain
;;;       (NN/ZZ/QQ/RR/CC), generators certified by ring-domain typings or
;;;       context (no prior di needed for the typed-forall form).
;;;   (2) GENERIC  -- ((ADD R) ..)/((MUL R) ..)/((NEG R) ..)/(ZERO R)/(ONE R)
;;;       for an arbitrary R with IS-COMMUTATIVE-RING(R), certified by the
;;;       (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R) ...)) form or, post-di,
;;;       by sequent assumptions.
(define (pi-comm-ring-simplify! sqn)
  (let* ((goal (sequent-node-assertion sqn))
         (g    (wff-formula goal))
         (dg   (sqn-dg sqn))
         (asms (sequent-node-assumptions sqn)))
    (or
     ;; (1) Concrete number-domain path.  Expand literal powers first so
     ;; `(x+y)^2 = ...' closes directly (cvnb->poly has no power case); source
     ;; generators are then read off the expanded sides (x, not (power x 2)).
     (let ((peeled (peel-ring-foralls g)))
       (and peeled
            (let ((inner (car peeled)) (qvars (cdr peeled)))
              (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
                   (let ((e1 (cvnb-expand-pow (cadr inner)))
                         (e2 (cvnb-expand-pow (caddr inner))))
                     (let ((p1 (cvnb->poly e1)) (p2 (cvnb->poly e2)))
                       (and p1 p2 (equal? p1 p2)
                            ;; SOURCE generators (incl. cancelled), not survivors
                            (ring-vars-ok? (cvnb-eq-source-generators e1 e2)
                                           qvars asms)
                            (dg-apply-rule! dg 'comm-ring-simplify '() sqn))))))))
     ;; (2) Generic arbitrary-commutative-ring path.
     (let* ((cpeeled (peel-cring-foralls g))
            (inner   (if cpeeled (caddr cpeeled) g))
            (qvars   (if cpeeled (cadr cpeeled) '())))
       (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
            (let ((R (or (and cpeeled (car cpeeled))
                         (find-cring (cadr inner))
                         (find-cring (caddr inner)))))
              (and R
                   (cring-certified? R (and cpeeled #t) asms)
                   (let ((p1 (cring->poly (cadr inner) R))
                         (p2 (cring->poly (caddr inner) R)))
                     (and p1 p2 (equal? p1 p2)
                          ;; SOURCE generators (incl. cancelled), not survivors
                          (cring-vars-ok? (cring-eq-source-generators
                                            (cadr inner) (caddr inner) R)
                                          R qvars asms)
                          (dg-apply-rule! dg 'comm-ring-simplify '() sqn))))))))))

;;; The procedure is a trusted oracle; the warrant records the grounds.
(warrant! 'comm-ring-simplify 'well-known
  "Decision procedure for commutative-ring identities, on two surfaces: the concrete number-domain operators (+/*/- and their binary aliases binplus/bintimes/binneg) and the generic structure operators ((ADD R) (MUL R) (NEG R) (ZERO R) (ONE R)) of an arbitrary R satisfying IS-COMMUTATIVE-RING. Each side is normalised to its sum-of-monomials form in the free commutative ring ZZ[generators] (monomial = sorted multiset of generators, coefficient in ZZ); two terms are equal in every commutative ring iff these normal forms coincide. Sound and complete by the standard normal-form theorem for commutative-ring equational logic; computed in Scheme rather than mechanised through the ring properties.")
