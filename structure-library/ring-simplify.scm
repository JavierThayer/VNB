;;; ring-simplify.scm -- polynomial-normal-form ring identity decision procedure
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
