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

;;; SOUND-ARITH GATE.  arith-eval-term must NEVER hand back an INEXACT flonum.
;;; Every downstream decision -- `=' / `<=' comparison, membership, the
;;; forsome-witness search, and the term simplifier -- is sound only over EXACT
;;; values.  An inexact result is either a decimal literal (2.5) or a
;;; transcendental rounding (exp/sin/cos/magnitude), and treating it as a decided
;;; value forges false facts: `(exp 1) = 2.718...' (e is irrational), a natural
;;; number `= 2.5', membership of a rounded double.  The recent membership fix
;;; hardened only the IN branch and, by returning a truthy 'UNDEF, actually
;;; RE-OPENED the forsome path (arith-forsome-witness's `(and ... 'UNDEF v)').
;;; Rejecting inexact at this one choke point closes all of it, and -- since the
;;; recursive descent goes through this wrapper -- at every subterm too.
;;; REVISED 2026-08-01.  The parenthesis that used to close this comment read
;;; "decimal literals become UNEVALUABLE, not unsound; parsing them as exact
;;; rationals is a separate, larger change in parser.scm" -- that change has now
;;; been made (parser.scm's `p--exact-num' reads every literal with the "#e"
;;; prefix, so 0.1 enters the theory as 1/10).  What remains of the gate is its
;;; other and permanent job: rejecting inexactness that arithmetic PRODUCED
;;; rather than read -- exp, sin, cos, magnitude below all return flonums, and
;;; `(exp 1) = 2.718...' is a false fact about an irrational number.  So the
;;; gate stays exactly as it was; only its input changed.
;;;
;;; A stray flonum can still reach the LEAF case -- a wff built in Scheme source
;;; rather than parsed, e.g. '(<= 2.5 x).  `arith--exactify' converts it there,
;;; so the descent stays exact.  Note the two conversions are NOT the same and
;;; must not be confused: the parser exactifies the DECIMAL AS WRITTEN (0.1 ->
;;; 1/10), while `inexact->exact' on an existing double gives that double's
;;; dyadic value (0.1 -> 3602879701896397/36028797018963968).  The parser's
;;; reading is what a reader means; this one is the honest value of an object
;;; that is already a double, and it is a fallback, not the intended path.
(define (arith--exactify v)
  (cond ((exact? v) v)
        ((and (real? v) (rational? v)) (inexact->exact v))
        ;; Complex flonum: exactify both parts, or give up (inf/nan in either).
        ((and (rational? (real-part v)) (rational? (imag-part v)))
         (make-rectangular (inexact->exact (real-part v))
                           (inexact->exact (imag-part v))))
        (else #f)))                   ; +inf.0, -inf.0, nan -- no exact value

(define (arith-eval-term e)
  (let ((v (arith-eval-term--core e)))
    (if (and (number? v) (inexact? v)) #f v)))

(define (arith-eval-term--core e)
  (cond
    ((number? e) (arith--exactify e))
    ((functoid? e) #f)            ; functoids are not ground arithmetic values
    ((pair? e)
     (case (car e)
       ((+)
        ;; n-ary sum.  The kiddie surface emits flat (+ a b c ...); the
        ;; binary case (+ a b) is just the two-operand instance.
        (let ((vs (map arith-eval-term (cdr e))))
          (and (pair? vs) (every number? vs) (apply + vs))))
       ((*)
        ;; n-ary product: flat (* a b c ...).
        (let ((vs (map arith-eval-term (cdr e))))
          (and (pair? vs) (every number? vs) (apply * vs))))
       ((-)
        ;; (- a) is unary negation; (- a b c ...) is left-folded
        ;; subtraction a - b - c - ... (chained minus left-associates,
        ;; which is exactly Scheme's n-ary -).
        (let ((vs (map arith-eval-term (cdr e))))
          (and (pair? vs) (every number? vs) (apply - vs))))
       ((recip)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (not (zero? a)) (/ 1 a)))))
       ((abs)
        (and (= (length e) 2)
             (let ((a (arith-eval-term (cadr e))))
               (and a (abs a)))))
       ((succ succ_ORD)
        ;; succ is the NN successor, succ_ORD the ordinal successor; on a
        ;; ground natural number both are n+1.  card-insert emits succ_ORD,
        ;; so handling it here lets (arith) close e.g. (= (succ_ORD 0) 1)
        ;; without a manual succ_ORD->succ bridge.
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

;;; Decide t in {NN,ZZ,QQ,RR,CC} ONLY when the decision is sound.  A boolean
;;; result is a decided membership; 'UNDEF means "cannot decide" and MUST be
;;; returned whenever the term does not reduce to an exact value -- otherwise a
;;; non-reducing term (sqrt(5)) reads as "not exact-rational" = #f, and NOT
;;; flips it to a bogus `modulo 0' proof of `not(sqrt(5) in qq)' (and, worse,
;;; of the FALSE `not(sqrt(4) in qq)').  Negation-as-failure is unsound here.
;;;   * term does not reduce to a number  -> UNDEF (e.g. sqrt, a free var)
;;;   * reduces to an INEXACT float        -> UNDEF for NN/ZZ/QQ (a float cannot
;;;     witness exact-rationality: 2.0 might be 2 or a rounding), sound only for
;;;     RR/CC.
;;;   * reduces to an EXACT number         -> fully decidable, both directions
;;;     (exact & real => rational, so QQ is #t; 1/2 is provably not in ZZ => #f).
(define (arith-membership-check val-expr class)
  (let ((v (arith-eval-term val-expr)))
    (cond
      ((not (number? v)) 'UNDEF)                 ; term did not reduce -> undecidable
      ;; There is no inexact case.  arith-eval-term exactifies literals and
      ;; rejects computed flonums outright (the sound-arith gate at the head of
      ;; this file), so a value reaching here is exact or is not a number at all.
      ;; The branch that used to sit here -- admitting an inexact v to RR and CC
      ;; and answering 'UNDEF elsewhere -- had been unreachable since that gate
      ;; was installed, and it encoded the OLD reading of a decimal literal, in
      ;; which 2.5 was a real but not a rational.  Under exact parsing 2.5 is
      ;; 5/2 and lands in QQ, which is the user's 2026-08-01 decision: a literal
      ;; the reader accepts denotes the exact rational it names.
      (else                                      ; exact: decidable both ways
       (case class
         ((NN)     (and (real? v) (integer? v) (>= v 0)))
         ((ZZ)     (and (real? v) (integer? v)))
         ((QQ)     (real? v))                    ; every exact real is rational
         ((RR)     (real? v))
         ((CC)     #t)
         (else     'UNDEF))))))

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
           ;; A REAL PROOF since 2026-09-20: state the sentence, close it with the `arith'
           ;; oracle, install with `qed'.  Until then this procedure installed the formula
           ;; directly, stamped `proven', with no deduction graph: the evaluation was trusted
           ;; twice over and appeared on no bill.  Now the inference is recorded, checked by
           ;; the arith rule checker, billed `[oracles: arith]', and the proof has a page.
           (let ((saved *ps*))
             (sp (make-wff formula))
             (arith)
             (let ((done (proof-done? *ps*)))
               (if done (qed name))
               (set! *ps* saved)
               (if (not done)
                   (error "vnb-create-num-theorem: `arith' did not close the sentence it evaluated true"
                          formula))))
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
