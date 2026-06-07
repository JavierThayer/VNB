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
       (else
        (let ((v (arith-eval-term expr)))
          (and v (number? v)
               (if (zero? v) '() (list (cons '() v))))))))
    (else #f)))

;;; Primitive inference: close a commutative-ring identity goal by normal-form
;;; equality.  Goal may be a bare (= e1 e2) -- generators certified by sequent
;;; context -- or a typed (FORALL v (IMPLIES (IN v D) ...)) chain over ring
;;; domains, certified by the quantifier typings themselves (no prior di
;;; needed).  Mirrors pi-ring-simplify! exactly, with cvnb->poly in place of
;;; vnb->poly and rule name 'comm-ring-simplify.
(define (pi-comm-ring-simplify! sqn)
  (let* ((goal   (sequent-node-assertion sqn))
         (g      (wff-formula goal))
         (dg     (sqn-dg sqn))
         (asms   (sequent-node-assumptions sqn))
         (peeled (peel-ring-foralls g)))
    (and peeled
         (let ((inner (car peeled))
               (qvars (cdr peeled)))
           (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
                (let ((p1 (cvnb->poly (cadr inner)))
                      (p2 (cvnb->poly (caddr inner))))
                  (and p1 p2
                       (equal? p1 p2)
                       (ring-vars-ok? (poly-generators p1 p2) qvars asms)
                       (dg-apply-rule! dg 'comm-ring-simplify '() sqn))))))))

;;; The procedure is a trusted oracle; the warrant records the grounds.
(warrant! 'comm-ring-simplify 'well-known
  "Decision procedure for commutative-ring identities. Each side is normalised to its sum-of-monomials form in the free commutative ring ZZ[generators] (monomial = sorted multiset of generators, coefficient in ZZ); two terms are equal in every commutative ring iff these normal forms coincide. Sound and complete by the standard normal-form theorem for commutative-ring equational logic; computed in Scheme rather than mechanised through the ring axioms.")
