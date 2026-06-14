;;; ineq-oracle.scm -- the (ineq) decision procedure: close a linear-inequality
;;; goal over RR from NAMED assumptions, crs-style, via the Fourier-Motzkin /
;;; Farkas engine in linear-arith.scm.
;;;
;;; Usage (post-di, so the linear premises are assumptions):
;;;   (ineq i j k ...)   ; i,j,k = 1-based indices of the assumptions to use as
;;;                      ;         linear premises (predictable: no auto-scan).
;;; Goal and premises must be <=, <, or = between linear RR expressions.
;;;
;;; ATOM ABSTRACTION (decision #2): a term is linearized over +, -, * (and the
;;; binplus/binneg/bintimes aliases) and numeric literals; every MAXIMAL non-
;;; arithmetic subterm is treated as an opaque real variable -- exactly how crs
;;; treats compound generators.  So  d(x,y) <= d(x,z) + d(z,y)  is linear in the
;;; three distance atoms, and  3 + f(x) <= 1 + f(x) + 2  is linear in f(x).
;;;
;;; SOUNDNESS: linear-combination + positive-rational scaling is valid only over
;;; an ordered field, so every atom must be certified in RR (an (IN atom RR)
;;; assumption, an abs(.) term by rr-abs-closed, or an RR-typed goal binder).
;;; Uncertified atoms => refuse.  Trusted oracle; warrant 'ineq below, and each
;;; success prints its Farkas certificate (the nonneg combo that yields 0<0).
;;;
;;; Dependencies: linear-arith.scm (make-con, la-*, fm-prove), kernel
;;; (sequent-node-*, dg-apply-rule!, sqn-dg, wff-formula), warrants.

;;; -----------------------------------------------------------------------
;;; Linear forms over RR atoms:  (coeffs . const), coeffs an alist (atom . rat).

(define (lin-zero)        (cons '() 0))
(define (lin-const k)     (cons '() k))
(define (lin-atom t)      (cons (list (cons t 1)) 0))
(define (lin-coeffs L)    (car L))
(define (lin-const-of L)  (cdr L))
(define (lin-pure-const? L) (null? (car L)))
(define (lin-add L1 L2)   (cons (la-add (car L1) (car L2)) (+ (cdr L1) (cdr L2))))
(define (lin-scale L k)   (cons (la-scale (car L) k) (* k (cdr L))))
(define (lin-neg L)       (lin-scale L -1))

(define (lin-mul L1 L2)   ; product is linear only if a factor is constant; else #f
  (cond ((lin-pure-const? L1) (lin-scale L2 (lin-const-of L1)))
        ((lin-pure-const? L2) (lin-scale L1 (lin-const-of L2)))
        (else #f)))

(define la-plus-ops  '(+ binplus))
(define la-minus-ops '(- binneg))
(define la-times-ops '(* bintimes))

;; vnb->linear : VNB term -> linear form.  Non-arithmetic subterms become atoms.
(define (vnb->linear t)
  (cond
    ((number? t) (lin-const t))
    ((not (pair? t)) (lin-atom t))                 ; bare symbol = variable atom
    (else
     (let ((op (car t)) (args (cdr t)))
       (cond
         ((and (memq op la-plus-ops) (pair? args))
          (fold-left lin-add (lin-zero) (map vnb->linear args)))
         ((and (memq op la-minus-ops) (= (length args) 1))
          (lin-neg (vnb->linear (car args))))
         ((and (memq op la-minus-ops) (= (length args) 2))
          (lin-add (vnb->linear (car args)) (lin-neg (vnb->linear (cadr args)))))
         ((and (memq op la-times-ops) (pair? args))
          (let loop ((as (cdr args)) (acc (vnb->linear (car args))))
            (cond ((not acc) (lin-atom t))         ; nonlinear product => atom
                  ((null? as) acc)
                  (else (loop (cdr as) (lin-mul acc (vnb->linear (car as))))))))
         (else (lin-atom t)))))))                  ; any other head => maximal atom

;;; -----------------------------------------------------------------------
;;; Formula -> (linform . rel), where linform is lhs-rhs and rel in {le,lt,eq}.

(define (ineq-rel-of head)
  (cond ((eq? head '<=) 'le) ((eq? head '<) 'lt) ((eq? head '=) 'eq) (else #f)))

(define (formula->lin+rel f)
  (and (pair? f) (= (length f) 3)
       (let ((rel (ineq-rel-of (car f))))
         (and rel
              (cons (lin-add (vnb->linear (cadr f))
                             (lin-neg (vnb->linear (caddr f))))
                    rel)))))

;; A hypothesis at index i -> engine constraint(s).  Equality splits into the
;; two <= directions, with ids hI and hI-rev so the certificate distinguishes
;; them; le/lt give one constraint with id hI.
(define (ineq-hyp-constraints i L rel)
  (let ((hid (string->symbol (string-append "h" (number->string i)))))
    (cond
      ((eq? rel 'eq)
       (let ((hidr (string->symbol (string-append "h" (number->string i) "-rev"))))
         (list (make-con (lin-coeffs L) (lin-const-of L) 'le (list (cons hid 1)))
               (make-con (la-scale (lin-coeffs L) -1) (- (lin-const-of L)) 'le
                         (list (cons hidr 1))))))
      (else
       (list (make-con (lin-coeffs L) (lin-const-of L) rel (list (cons hid 1))))))))

;;; -----------------------------------------------------------------------
;;; RR certification of atoms.

;; Peel RR-typed universal binders off a goal: (FORALL v (IMPLIES (IN v RR) ..)).
(define (ineq-peel-rr-foralls g)
  (let loop ((g g) (vs '()))
    (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3))
        (let ((v (cadr g)) (body (caddr g)))
          (if (and (pair? body) (eq? (car body) 'IMPLIES)
                   (let ((a (cadr body)))
                     (and (pair? a) (eq? (car a) 'IN)
                          (eq? (cadr a) v) (equal? (caddr a) 'RR))))
              (loop (caddr body) (cons v vs))
              (cons g vs)))
        (cons g vs))))

(define (ineq-atom-rr-ok? v asms rr-qvars)
  (or (member v rr-qvars)
      (and (pair? v) (eq? (car v) 'abs))           ; rr-abs-closed: abs(.) in RR
      (let scan ((as asms))
        (and (pair? as)
             (or (let ((f (wff-formula (car as))))
                   (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                        (equal? (cadr f) v) (equal? (caddr f) 'RR)))
                 (scan (cdr as)))))))

;;; -----------------------------------------------------------------------
;;; The primitive inference.

(define (ineq-report cert)
  (display ";; ineq: closed by Farkas certificate ") (write cert) (newline))

(define (pi-ineq! sqn idxs)
  (let* ((goal0 (wff-formula (sequent-node-assertion sqn)))
         (peel  (ineq-peel-rr-foralls goal0))
         (goal  (car peel))
         (rrqv  (cdr peel))
         (asms  (sequent-node-assumptions sqn))
         (dg    (sqn-dg sqn))
         (nasm  (length asms))
         (gpr   (formula->lin+rel goal)))
    (and gpr
         (let ((hyp-cons '()) (ok #t))
           (for-each
             (lambda (i)
               (if (and (integer? i) (>= i 1) (<= i nasm))
                   (let ((hpr (formula->lin+rel (wff-formula (list-ref asms (- i 1))))))
                     (if hpr
                         (set! hyp-cons
                           (append hyp-cons
                             (ineq-hyp-constraints i (car hpr) (cdr hpr))))
                         (set! ok #f)))
                   (set! ok #f)))
             idxs)
           (and ok
                (let* ((gcoeffs (lin-coeffs (car gpr)))
                       (atoms (la-uniq
                               (append (map car gcoeffs)
                                       (apply append
                                         (map (lambda (c) (map car (con-coeffs c)))
                                              hyp-cons))))))
                  (and (let allok ((vs atoms))
                         (or (null? vs)
                             (and (ineq-atom-rr-ok? (car vs) asms rrqv)
                                  (allok (cdr vs)))))
                       (let ((cert (fm-prove hyp-cons gcoeffs
                                             (lin-const-of (car gpr)) (cdr gpr))))
                         (and cert
                              (begin (ineq-report cert)
                                     (dg-apply-rule! dg 'ineq '() sqn)))))))))))

(warrant! 'ineq 'well-known
  "Decision procedure for linear arithmetic over the ordered field RR.  The goal
   and the named premise assumptions are each read as a linear (in)equality in
   their maximal non-arithmetic subterms (atoms, all certified in RR); Fourier-
   Motzkin elimination on premises + negated goal seeks an infeasibility, whose
   Farkas certificate is a nonnegative combination of the premises and the
   negated goal summing to 0<0.  Sound and complete for linear real arithmetic;
   computed in Scheme.  Each closure prints its certificate.")
