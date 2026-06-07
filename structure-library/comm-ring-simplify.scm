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
;;; oracle rather than mechanised through the ring axioms (warrant below,
;;; [[feedback-warrants]]).
;;;
;;; Reuses ring-simplify.scm's plumbing wholesale: word<? (length-then-lex
;;; still orders sorted words), poly-add / poly-neg (merge by word equality),
;;; poly-generators, ring-domain?, peel-ring-foralls, ring-vars-ok?.  Only
;;; multiplication changes -- the product monomial is the SORTED concatenation
;;; of the two factor monomials, so commutativity lives in the representation.
;;; Coefficients live in ZZ; symbols arith-eval-term cannot reduce to a number
;;; are generators (the ZZ-module / [[project-ag-are-zz-modules]] view of the
;;; additive group).
;;;
;;; Dependencies: ring-simplify.scm (loaded just before), arith-eval.scm.

;;; Canonicalise a monomial: sort its generator symbols (multiset normal form).
(define (cmonomial-sort gens)
  (sort gens (lambda (a b) (symbol<? a b))))

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
        (let ((v (arith-eval-term expr)))
          (and v (number? v)
               (if (zero? v) '() (list (cons '() v))))))))
    (else #f)))

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
;;; Symbols are carrier elements (generators); ring operators recurse; any
;;; foreign operator or a ring operator over a DIFFERENT ring returns #f.
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
         (else #f))))
    (else #f)))

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
            (and (or (memq v qvars)
                     (let find ((as asms))
                       (and (pair? as)
                            (or (let ((f (wff-formula (car as))))
                                  (and (pair? f) (= (length f) 3)
                                       (eq? (car f) 'IN)
                                       (eq? (cadr f) v)
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
     ;; (1) Concrete number-domain path.
     (let ((peeled (peel-ring-foralls g)))
       (and peeled
            (let ((inner (car peeled)) (qvars (cdr peeled)))
              (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
                   (let ((p1 (cvnb->poly (cadr inner)))
                         (p2 (cvnb->poly (caddr inner))))
                     (and p1 p2 (equal? p1 p2)
                          (ring-vars-ok? (poly-generators p1 p2) qvars asms)
                          (dg-apply-rule! dg 'comm-ring-simplify '() sqn)))))))
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
                          (cring-vars-ok? (poly-generators p1 p2) R qvars asms)
                          (dg-apply-rule! dg 'comm-ring-simplify '() sqn))))))))))

;;; The procedure is a trusted oracle; the warrant records the grounds.
(warrant! 'comm-ring-simplify 'well-known
  "Decision procedure for commutative-ring identities, on two surfaces: the concrete number-domain operators (+/*/- and their binary aliases binplus/bintimes/binneg) and the generic structure operators ((ADD R) (MUL R) (NEG R) (ZERO R) (ONE R)) of an arbitrary R satisfying IS-COMMUTATIVE-RING. Each side is normalised to its sum-of-monomials form in the free commutative ring ZZ[generators] (monomial = sorted multiset of generators, coefficient in ZZ); two terms are equal in every commutative ring iff these normal forms coincide. Sound and complete by the standard normal-form theorem for commutative-ring equational logic; computed in Scheme rather than mechanised through the ring axioms.")
