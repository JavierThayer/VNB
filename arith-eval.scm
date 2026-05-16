;;; arith-eval.scm -- ground arithmetic decision procedure
;;;
;;; Evaluates closed VNB arithmetic terms and formulas using Scheme's
;;; exact arithmetic.  All arithmetic is exact (integers and rationals).
;;;
;;; Public API:
;;;   (vnb-do-arith formula)  =>  #t | #f | error if not decidable
;;;   (pi-arith! sqn)         =>  inference node | #f

;;; -----------------------------------------------------------------------
;;; Term evaluator
;;;
;;; Returns a Scheme number, or #f if unevaluable (free variable,
;;; unknown operator, division by zero, etc.).

(define (arith-eval-term e)
  (cond
    ((number? e) e)
    ((functoid? e) #f)            ; functoids are not ground arithmetic values
    ((pair? e)
     (case (car e)
       ((+)
        (and (= (length e) 3)
             (let ((a (arith-eval-term (cadr e)))
                   (b (arith-eval-term (caddr e))))
               (and a b (+ a b)))))
       ((*)
        (and (= (length e) 3)
             (let ((a (arith-eval-term (cadr e)))
                   (b (arith-eval-term (caddr e))))
               (and a b (* a b)))))
       ((-) ; unary negation only in VNB
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (- a)))))
       ((recip)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (not (zero? a)) (/ 1 a)))))
       ((abs)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (abs a)))))
       ((succ)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (+ a 1)))))
       ((conjugate)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (conjugate a)))))
       ((exp)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (exp a)))))
       ((sin)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (sin a)))))
       ((cos)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (cos a)))))
       ((real-part)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (real-part a)))))
       ((imag-part)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (imag-part a)))))
       ((magnitude)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (magnitude a)))))
       ((power)
        (and (= (length e) 3)
             (let ((x (arith-eval-term (cadr e)))
                   (n (arith-eval-term (caddr e))))
               (and (number? x) (exact? n) (integer? n)
                    (cond
                      ((zero? n) 1)
                      ((positive? n) (expt x n))
                      (else (and (not (zero? x)) (expt x n))))))))
       (else #f)))
    (else #f)))  ; symbol (free variable) or anything else => unevaluable

;;; -----------------------------------------------------------------------
;;; Membership check for number system classes

(define (arith-membership-check val-expr class)
  (let ((v (arith-eval-term val-expr)))
    (and v
         (case class
           ((NN)     (and (exact? v) (integer? v) (>= v 0)))
           ((ZZ)     (and (exact? v) (integer? v)))
           ((QQ)     (and (exact? v) (rational? v)))
           ((RR)     (real? v))
           ((CC)     (number? v))
           (else #f)))))

;;; -----------------------------------------------------------------------
;;; Formula evaluator
;;;
;;; Returns:
;;;   #t    — formula is true (decidably)
;;;   #f    — formula is false (decidably)
;;;   'UNDEF — cannot decide (free variables, unknown predicates, etc.)

(define (arith-eval-formula e)
  (cond
    ((eq? e 'TRUTH)   #t)
    ((eq? e 'FALSITY) #f)
    ((pair? e)
     (case (car e)
       ((=)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((a (arith-eval-term (cadr e)))
                  (b (arith-eval-term (caddr e))))
              (if (and (number? a) (number? b))
                  (= a b)
                  'UNDEF))))
       ((<=)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((a (arith-eval-term (cadr e)))
                  (b (arith-eval-term (caddr e))))
              (if (and (real? a) (real? b))
                  (<= a b)
                  'UNDEF))))
       ((IN)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((result (arith-membership-check (cadr e) (caddr e))))
              (if (boolean? result)
                  result
                  'UNDEF))))
       ((NOT)
        (if (not (= (length e) 2))
            'UNDEF
            (let ((v (arith-eval-formula (cadr e))))
              (if (boolean? v) (not v) 'UNDEF))))
       ((AND)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((a (arith-eval-formula (cadr e))))
              (cond
                ((eq? a #f) #f)           ; short-circuit: false AND anything = false
                ((eq? a #t)
                 (let ((b (arith-eval-formula (caddr e))))
                   (if (boolean? b) b 'UNDEF)))
                (else 'UNDEF)))))
       ((OR)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((a (arith-eval-formula (cadr e))))
              (cond
                ((eq? a #t) #t)           ; short-circuit: true OR anything = true
                ((eq? a #f)
                 (let ((b (arith-eval-formula (caddr e))))
                   (if (boolean? b) b 'UNDEF)))
                (else 'UNDEF)))))
       ((IMPLIES)
        (if (not (= (length e) 3))
            'UNDEF
            (let ((a (arith-eval-formula (cadr e))))
              (cond
                ((eq? a #f) #t)           ; false implies anything = true
                ((eq? a #t)
                 (let ((b (arith-eval-formula (caddr e))))
                   (if (boolean? b) b 'UNDEF)))
                (else 'UNDEF)))))
       (else 'UNDEF)))
    (else 'UNDEF)))

;;; -----------------------------------------------------------------------
;;; Public standalone predicate

(define (vnb-do-arith formula)
  (vnb-guard
    (lambda ()
      (let ((result (arith-eval-formula formula)))
        (cond
          ((eq? result #t)     #t)
          ((eq? result #f)     #f)
          ((eq? result 'UNDEF)
           (error "vnb-do-arith: not a decidable closed arithmetic sentence" formula))
          (else #f))))))

;;; -----------------------------------------------------------------------
;;; vnb-create-num-theorem
;;;
;;; Given a wff (or raw formula) that decides to #t under ground arithmetic
;;; evaluation, install it as a named theorem in the current theory.
;;; Use for facts of the form P(n, params) where n is a numeric literal
;;; (integer or rational) and the formula reduces to a true closed
;;; sentence under arith-eval-formula.

(define (vnb-create-num-theorem name wic-or-formula)
  (vnb-guard
    (lambda ()
      (let ((formula (cond ((wff? wic-or-formula)    (wff-formula wic-or-formula))
                           ((string? wic-or-formula) (parse-string wic-or-formula))
                           (else                     wic-or-formula))))
        (case (arith-eval-formula formula)
          ((#t)
           (theory-add-theorem! *current-theory* name formula)
           name)
          ((#f)
           (error "vnb-create-num-theorem: formula evaluates to FALSE" formula))
          (else
           (error "vnb-create-num-theorem: formula is not a decidable closed arithmetic sentence"
                  formula)))))))

;;; -----------------------------------------------------------------------
;;; Term simplifier: reduce ground numeric subterms to their values

(define (arith-simplify-term e)
  (let ((v (arith-eval-term e)))
    (cond
      ((and (number? v) (not (equal? e v))) v)
      ((pair? e)
       (let ((new-args (map arith-simplify-term (cdr e))))
         (if (equal? new-args (cdr e)) e (cons (car e) new-args))))
      (else e))))

;;; Formula simplifier: apply arith-simplify-term at every term position

(define (arith-simplify-formula e)
  (if (not (pair? e))
      e
      (case (car e)
        ((= <=)
         (let ((new-args (map arith-simplify-term (cdr e))))
           (if (equal? new-args (cdr e)) e (cons (car e) new-args))))
        ((IN)
         (let ((new-val (arith-simplify-term (cadr e))))
           (if (equal? new-val (cadr e)) e
               (list 'IN new-val (caddr e)))))
        ((NOT)
         (let ((new-sub (arith-simplify-formula (cadr e))))
           (if (equal? new-sub (cadr e)) e (list 'NOT new-sub))))
        ((AND OR IMPLIES IFF)
         (let* ((l (cadr e))
                (r (caddr e))
                (new-l (arith-simplify-formula l))
                (new-r (arith-simplify-formula r)))
           (if (and (equal? new-l l) (equal? new-r r)) e
               (list (car e) new-l new-r))))
        ((FORALL FORSOME)
         (let* ((body (caddr e))
                (new-body (arith-simplify-formula body)))
           (if (equal? new-body body) e
               (list (car e) (cadr e) new-body))))
        (else e))))

;;; -----------------------------------------------------------------------
;;; Calculator pattern detector
;;;
;;; Recognises (FORSOME x (AND (IN x CLASS) (= EXPR x)))
;;; and the symmetric (= x EXPR) variant.  Returns the numeric witness
;;; if EXPR is ground-evaluable and the value is in CLASS; else #f.

(define (arith-forsome-witness f)
  (and (pair? f) (eq? (car f) 'FORSOME)
       (let ((x    (cadr f))
             (body (caddr f)))
         (and (pair? body) (eq? (car body) 'AND)
              (let ((in-clause (cadr body))
                    (eq-clause (caddr body)))
                (and (pair? in-clause) (eq? (car in-clause) 'IN)
                     (eq? (cadr in-clause) x)
                     (pair? eq-clause) (eq? (car eq-clause) '=)
                     (let ((lhs (cadr eq-clause))
                           (rhs (caddr eq-clause))
                           (cls (caddr in-clause)))
                       (define (try expr)
                         (let ((v (arith-eval-term expr)))
                           (and (number? v)
                                (arith-membership-check v cls)
                                v)))
                       (cond
                         ((and (eq? rhs x) (not (eq? lhs x))) (try lhs))
                         ((and (eq? lhs x) (not (eq? rhs x))) (try rhs))
                         (else #f)))))))))

;;; -----------------------------------------------------------------------
;;; Primitive inference: close a goal that is a true arithmetic sentence,
;;; or recognise the calculator pattern, or reduce ground numeric subterms.

(define (pi-arith! sqn)
  (let* ((goal (sequent-node-assertion sqn))
         (dg   (sqn-dg sqn))
         (f    (wff-formula goal))
         (f*   (arith-simplify-formula f)))
    (cond
      ((eq? (arith-eval-formula f) #t)
       (dg-apply-rule! dg 'arith-ground '() sqn))
      ((arith-forsome-witness f)
       (dg-apply-rule! dg 'arith-forsome '() sqn))
      ((not (equal? f* f))
       (let ((new-sqn (make-sequent (sequent-node-assumptions sqn)
                                    (wff-child goal f*))))
         (dg-apply-rule! dg 'arith-simplify (list new-sqn) sqn)))
      (else #f))))
