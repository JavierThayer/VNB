;;; rule-checkers-oracle.scm -- inference checkers for the seven ORACLE rules.
;;;
;;; A checker VERIFIES a finished inference.  `dg-apply-rule!' hands it the rule
;;; tag, the hypothesis sequents and the conclusion sequent; it returns #t to
;;; accept, or #f / a string (the reason) to refuse, and refusing aborts the
;;; write.  A checker never rebuilds the inference: it states the rule as a
;;; relation between the conclusion and the hypotheses and tests that relation.
;;; Nothing here calls the pi-* procedure it guards, and nothing here calls the
;;; oracle it guards -- "run the oracle again" is not a check.  The arithmetic
;;; below (exact evaluation, linear forms, polynomials) is written out in this
;;; file from the mathematics, not borrowed from arith-eval.scm, ineq-oracle.scm,
;;; linear-arith.scm, ring-simplify.scm or comm-ring-simplify.scm.  What is
;;; shared with them is the expression layer only: `wff-formula', the sequent
;;; accessors, `free-vars', `alpha-equiv?', `car'/`cdr'.
;;;
;;; CONVENTIONS (the same in the four rule-checker files)
;;;   * Assumption lists are compared as SETS, up to alpha-equivalence: the order
;;;     of a context is not part of a sequent's meaning here.
;;;   * A checker is handed either a raw <sequent> or a <sequent-node>; the two
;;;     accessors below take both.
;;;   * A refusal returns a STRING.  A checker never signals an error itself.
;;;
;;; THE SEVEN OPERATIONS AND WHAT IS CHECKED
;;;
;;;   ineq                (ineq-oracle.scm)  CHECKED.  The tag carries the Farkas
;;;     certificate the oracle computed.  The checker re-reads the goal and the
;;;     named premises as linear forms over their maximal non-arithmetic
;;;     subterms, multiplies by the certificate's multipliers and verifies, term
;;;     by term, that the result is an absurd constant inequality.  Plain
;;;     arithmetic over the exact rationals; no elimination, no search.
;;;   arith-ground        (arith-eval.scm)   CHECKED, by independent exact
;;;     evaluation of the closed goal.
;;;   arith-forsome       (arith-eval.scm)   CHECKED.  The witness is read off
;;;     the goal's equation and the BODY is then evaluated at it.
;;;   arith-simplify      (arith-eval.scm)   CHECKED.  The hypothesis' goal must
;;;     differ from the conclusion's only where a ground subterm has been
;;;     replaced by its exact value, and the contexts must agree.
;;;   comm-ring-simplify  (comm-ring-simplify.scm)  CHECKED, by independent
;;;     expansion of both sides to the sum-of-monomials normal form of the free
;;;     commutative ring ZZ[generators], on both surfaces (the number operators
;;;     and the structure operators of an arbitrary commutative ring).
;;;   ring-simplify       (ring-simplify.scm) CHECKED, the same way in the free
;;;     ASSOCIATIVE algebra (monomials are words, not multisets).
;;;   sos                 (sos-oracle.scm)   CHECKED.  The tag carries the
;;;     squares and their weights; the checker verifies the polynomial identity
;;;     b - a = sum lambda_i c_i^2 monomial by monomial and lambda_i >= 0.
;;;
;;; Heads NOT checked here are registered under the accepting checker
;;; `trusted-oracle' and listed by `(trusted-oracle-rules)', so a load can print
;;; what is still taken on trust.  Today that list is empty.
;;;
;;; WHAT A CHECKER OF AN ORACLE CANNOT DO.  A decision procedure has no proof to
;;; replay, so the checker's strength is exactly the strength of the certificate
;;; the oracle was made to record.  Where the oracle records a certificate
;;; (ineq, sos) the check is a verification in the proper sense: an independent
;;; procedure, with no shared code, either confirms the arithmetic or the
;;; inference is refused.  Where it records none (arith-*, crs, rs) the check is
;;; an independent RE-DECISION by a second implementation of the same
;;; mathematics; that catches a bug in the oracle's plumbing (a mis-read atom, a
;;; missing typing certificate, a dropped premise) but not an error shared by
;;; both implementations of, say, polynomial normalisation.  The comments on
;;; each checker say which of the two it is.

;;; =======================================================================
;;; 0.  Plumbing
;;; =======================================================================

;;; The assumptions / the goal of a hypothesis or conclusion, as raw formulas.
(define (rco--asms s)
  (map wff-formula
       (if (sequent-node? s) (sequent-node-assumptions s) (sequent-assumptions s))))

(define (rco--goal s)
  (wff-formula
   (if (sequent-node? s) (sequent-node-assertion s) (sequent-assertion s))))

(define (rco--all? p lst)
  (or (null? lst) (and (p (car lst)) (rco--all? p (cdr lst)))))

(define (rco--any? p lst)
  (and (pair? lst) (or (p (car lst)) (rco--any? p (cdr lst)))))

;;; Context equality as SETS up to alpha-equivalence.  ONE helper for the four
;;; checker files: `chk-set=?' (rule-checkers-logic.scm, which loads first).
(define (rco--ctx-same? a b) (chk-set=? a b))

;;; The argument of a tag (ineq CERT) / (sos CERT); #f for a bare symbol.
(define (rco--tag-arg rule)
  (and (pair? rule) (pair? (cdr rule)) (cadr rule)))

(define (rco--exact-nonneg? x)
  (and (number? x) (exact? x) (real? x) (rational? x) (>= x 0)))

;;; =======================================================================
;;; 1.  Exact arithmetic  (for arith-ground / arith-forsome / arith-simplify,
;;;     and for the numeric constants of the ring checkers)
;;; =======================================================================
;;;
;;; EXACTNESS IS THE SOUNDNESS CONDITION.  A value that is not an exact rational
;;; (or an exact complex) is not a value the theory names: `exp(1)' is
;;; irrational, and a float that stands for it would forge the false fact
;;; exp(1) = 2.718...  So every operation's RESULT is required to be exact, at
;;; every subterm, and an inexact one makes the whole term unevaluable.  A leaf
;;; literal that is an inexact rational is converted to the rational it names --
;;; the VNB reader produces exact literals, so this is a fallback for a wff built
;;; in Scheme source.
(define (rco--exactify v)
  (cond ((not (number? v)) #f)
        ((exact? v) v)
        ((and (real? v) (rational? v)) (inexact->exact v))
        ((and (rational? (real-part v)) (rational? (imag-part v)))
         (make-rectangular (inexact->exact (real-part v))
                           (inexact->exact (imag-part v))))
        (else #f)))                       ; inf / nan: no exact value

;;; ENV is an alist (variable . exact value); it is empty everywhere except
;;; under the existential of arith-forsome.  Returns an exact number or #f.
(define (rco--ev e env)
  (let ((v (rco--ev-raw e env)))
    (and (number? v) (exact? v) v)))

(define (rco--ev1 e env f)                ; unary: evaluate, then apply f
  (and (= (length e) 2)
       (let ((a (rco--ev (cadr e) env)))
         (and a (f a)))))

(define (rco--ev-raw e env)
  (cond
    ((number? e) (rco--exactify e))
    ((symbol? e) (let ((p (assq e env))) (and p (cdr p))))
    ((not (pair? e)) #f)
    (else
     (case (car e)
       ;; n-ary sum / product / (left-folded) difference, as the surface writes
       ;; them.  A unary (- a) is negation.  (-) with no operand is malformed.
       ((+) (let ((vs (map (lambda (x) (rco--ev x env)) (cdr e))))
              (and (pair? vs) (rco--all? number? vs) (apply + vs))))
       ((*) (let ((vs (map (lambda (x) (rco--ev x env)) (cdr e))))
              (and (pair? vs) (rco--all? number? vs) (apply * vs))))
       ((-) (let ((vs (map (lambda (x) (rco--ev x env)) (cdr e))))
              (and (pair? vs) (rco--all? number? vs) (apply - vs))))
       ((recip) (rco--ev1 e env (lambda (a) (and (not (zero? a)) (/ 1 a)))))
       ((abs)   (rco--ev1 e env (lambda (a) (and (real? a) (abs a)))))
       ;; succ is the successor of a NATURAL number and succ_ORD of an ordinal.
       ;; Off those domains the symbol is uninterpreted, so -- unlike the oracle,
       ;; which adds 1 to whatever it evaluated -- a non-natural argument makes
       ;; the term unevaluable here.  See the report: no library proof needs the
       ;; wider reading.
       ((succ succ_ORD)
        (rco--ev1 e env (lambda (a) (and (real? a) (integer? a) (>= a 0) (+ a 1)))))
       ((conjugate)  (rco--ev1 e env conjugate))
       ((real-part)  (rco--ev1 e env real-part))
       ((imag-part)  (rco--ev1 e env imag-part))
       ((magnitude)  (rco--ev1 e env magnitude))
       ;; exp / sin / cos are exact only at the point where their value is
       ;; rational; anywhere else the exactness gate above rejects the flonum.
       ((exp) (rco--ev1 e env exp))
       ((sin) (rco--ev1 e env sin))
       ((cos) (rco--ev1 e env cos))
       ;; power: an exact integer exponent; a negative one needs a nonzero base.
       ((power)
        (and (= (length e) 3)
             (let ((x (rco--ev (cadr e) env))
                   (n (rco--ev (caddr e) env)))
               (and (number? x) (number? n) (integer? n)
                    (cond ((zero? n) 1)
                          ((positive? n) (expt x n))
                          (else (and (not (zero? x)) (expt x n))))))))
       (else #f)))))

;;; Membership of an EXACT value in a number class.  Decided in both directions:
;;; an exact real is a rational, so QQ and RR hold of it; 1/2 is provably not an
;;; integer.  A class this does not know gives 'undef.
(define (rco--in-class v cls)
  (case cls
    ((NN) (and (real? v) (integer? v) (>= v 0)))
    ((ZZ) (and (real? v) (integer? v)))
    ((QQ) (real? v))
    ((RR) (real? v))
    ((CC) #t)
    (else 'undef)))

;;; Truth of a ground formula: #t, #f, or 'undef when some part does not reduce.
(define (rco--true f env)
  (define (bool x) (if (boolean? x) x 'undef))
  (cond
    ((eq? f 'TRUTH)   #t)
    ((eq? f 'FALSITY) #f)
    ((not (pair? f))  'undef)
    (else
     (case (car f)
       ((=)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--ev (cadr f) env)) (b (rco--ev (caddr f) env)))
              (if (and (number? a) (number? b)) (= a b) 'undef))))
       ((<=)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--ev (cadr f) env)) (b (rco--ev (caddr f) env)))
              (if (and (real? a) (real? b)) (<= a b) 'undef))))
       ((<)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--ev (cadr f) env)) (b (rco--ev (caddr f) env)))
              (if (and (real? a) (real? b)) (< a b) 'undef))))
       ((IN)
        (if (not (= (length f) 3)) 'undef
            (let ((v (rco--ev (cadr f) env)))
              (if (number? v) (bool (rco--in-class v (caddr f))) 'undef))))
       ((NOT)
        (if (not (= (length f) 2)) 'undef
            (let ((v (rco--true (cadr f) env)))
              (if (boolean? v) (not v) 'undef))))
       ((AND)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--true (cadr f) env)))
              (cond ((eq? a #f) #f)
                    ((eq? a #t) (bool (rco--true (caddr f) env)))
                    (else 'undef)))))
       ((OR)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--true (cadr f) env)))
              (cond ((eq? a #t) #t)
                    ((eq? a #f) (bool (rco--true (caddr f) env)))
                    (else 'undef)))))
       ((IMPLIES)
        (if (not (= (length f) 3)) 'undef
            (let ((a (rco--true (cadr f) env)))
              (cond ((eq? a #f) #t)
                    ((eq? a #t) (bool (rco--true (caddr f) env)))
                    (else 'undef)))))
       (else 'undef)))))

;;; =======================================================================
;;; 2.  arith-ground, arith-forsome, arith-simplify
;;; =======================================================================

;;; RULE (arith-ground).  No hypotheses; the conclusion's goal is a closed
;;; arithmetic sentence that is TRUE under exact evaluation.  The context is
;;; irrelevant -- a true sentence follows from any context.
;;;
;;; This is an independent RE-DECISION, not a certificate check: the second
;;; evaluator above either agrees with the oracle or the inference is refused.
(define (rco--check-arith-ground rule hyps concl)
  (cond
    ((pair? hyps) "arith-ground takes no hypotheses")
    ((eq? (rco--true (rco--goal concl) '()) #t) #t)
    (else "goal is not a closed arithmetic sentence that evaluates to TRUE")))

;;; RULE (arith-forsome).  No hypotheses; the goal is (FORSOME x BODY) and some
;;; exact rational makes BODY true.  The witness is FOUND by matching the shape
;;; the oracle recognises -- (AND (IN x CLASS) (= EXPR x)), either way round --
;;; and is then CHECKED by evaluating the whole body at it.  Finding the witness
;;; by matching is allowed (it is what "there exists" means); the acceptance
;;; rests on the evaluation, so a witness found by a wrong match is refused.
(define (rco--forsome-candidates f)
  ;; the ground terms worth trying as witnesses for (FORSOME x BODY)
  (and (pair? f) (eq? (car f) 'FORSOME) (= (length f) 3)
       (let ((x (cadr f)) (body (caddr f)))
         (and (pair? body) (eq? (car body) 'AND) (= (length body) 3)
              (let ((c1 (cadr body)) (c2 (caddr body)))
                (and (pair? c2) (eq? (car c2) '=) (= (length c2) 3)
                     (cond ((eq? (caddr c2) x) (list (cadr c2)))
                           ((eq? (cadr c2) x)  (list (caddr c2)))
                           (else '()))))))))

(define (rco--check-arith-forsome rule hyps concl)
  (let* ((f (rco--goal concl))
         (cands (rco--forsome-candidates f)))
    (cond
      ((pair? hyps) "arith-forsome takes no hypotheses")
      ((not cands) "goal is not (FORSOME x (AND (IN x CLASS) (= EXPR x)))")
      ((rco--any?
        (lambda (t)
          (let ((v (rco--ev t '())))
            (and v (eq? #t (rco--true (caddr f) (list (cons (cadr f) v)))))))
        cands)
       #t)
      (else "no ground witness: the equation's other side does not evaluate, or the body is false at it"))))

;;; RULE (arith-simplify).  ONE hypothesis, same context (as a set, up to alpha);
;;; its goal is the conclusion's goal with some ground subterms replaced by their
;;; exact values.  Verified by walking the two formulas in parallel: where they
;;; differ, the hypothesis must carry a NUMBER and the conclusion a term that
;;; evaluates to exactly that number.  Replacing a ground term by its value is
;;; sound because evaluation is exact and total where it succeeds (it fails on
;;; recip 0 and on anything with a free variable), so the two terms denote the
;;; same defined object.
(define (rco--simplification? before after)
  (cond
    ((equal? before after) #t)
    ((and (number? after) (let ((v (rco--ev before '()))) (and v (= v after)))) #t)
    ((and (pair? before) (pair? after)
          (eq? (car before) (car after))
          (= (length before) (length after)))
     (rco--all? (lambda (p) (rco--simplification? (car p) (cdr p)))
                (map cons (cdr before) (cdr after))))
    (else #f)))

(define (rco--check-arith-simplify rule hyps concl)
  (cond
    ((not (= (length hyps) 1)) "arith-simplify takes exactly one hypothesis")
    ((not (rco--ctx-same? (rco--asms (car hyps)) (rco--asms concl)))
     "the hypothesis does not have the conclusion's context")
    ((not (rco--simplification? (rco--goal concl) (rco--goal (car hyps))))
     "the hypothesis' goal is not the goal with ground subterms replaced by their values")
    (#t #t)))

;;; =======================================================================
;;; 3.  Linear forms over opaque atoms  (for ineq)
;;; =======================================================================
;;;
;;; A LINEAR FORM is (constant . ((atom . coefficient) ...)), the coefficients
;;; exact rationals, atoms compared with equal?, zero coefficients dropped.  An
;;; ATOM is a maximal subterm the reading below does not decompose: a variable, a
;;; function application, an accessor -- anything that is not a sum, a difference,
;;; a product by a constant, or a numeral.  Reading a term this way is sound in
;;; any ordered field once each atom denotes a real number, which is what the
;;; certification in section 4 establishes.
;;;
;;; WHAT IS DECOMPOSED, and why exactly this much.  Sums and differences and
;;; products where one side is constant are linear operations, so they must be
;;; decomposed or no certificate would ever check.  Division and `recip' by a
;;; NONZERO EXACT RATIONAL LITERAL are also folded, because in a field
;;; c * recip(c) = 1 determines recip(c) = 1/c uniquely: the term denotes the
;;; rational it looks like, and folding it changes no denotation.  recip of
;;; anything else -- a variable, a compound, zero -- stays an ATOM: nothing is
;;; assumed about its sign or its definedness.

(define (rco--l-const k)   (cons k '()))
(define (rco--l-atom t)    (cons 0 (list (cons t 1))))
(define (rco--l-zero)      (cons 0 '()))
(define (rco--l-k L)       (car L))
(define (rco--l-terms L)   (cdr L))

(define (rco--l-scale L k)
  (if (= k 0)
      (rco--l-zero)
      (cons (* k (car L))
            (map (lambda (p) (cons (car p) (* k (cdr p)))) (cdr L)))))

(define (rco--l-add L1 L2)
  (let loop ((ts (cdr L2)) (acc (cdr L1)))
    (if (null? ts)
        (cons (+ (car L1) (car L2))
              (filter (lambda (p) (not (= 0 (cdr p)))) acc))
        (let* ((a (caar ts))
               (c (cdar ts))
               (old (assoc a acc)))
          (loop (cdr ts)
                (if old
                    (map (lambda (p) (if (equal? (car p) a) (cons a (+ (cdr p) c)) p))
                         acc)
                    (append acc (list (cons a c)))))))))

(define (rco--l-neg L) (rco--l-scale L -1))

(define (rco--rational-literal? c)
  (and (number? c) (exact? c) (real? c) (rational? c) (not (= c 0))))

;;; The linear reading of a term.  Never fails: what it cannot decompose is an
;;; atom.
(define (rco--lin t)
  (cond
    ;; a REAL numeral is the constant it names (an inexact one is read as the
    ;; rational it is written as, the reader's convention); a complex numeral
    ;; has no place in an order formula, so it stays an opaque atom and the
    ;; certificate will not check.
    ((number? t) (let ((v (rco--exactify t)))
                   (if (and v (real? v)) (rco--l-const v) (rco--l-atom t))))
    ((not (pair? t)) (rco--l-atom t))
    (else
     (let ((op (car t)) (args (cdr t)))
       (cond
         ((and (memq op '(+ binplus)) (pair? args))
          (let loop ((as (cdr args)) (acc (rco--lin (car args))))
            (if (null? as) acc (loop (cdr as) (rco--l-add acc (rco--lin (car as)))))))
         ((and (memq op '(- binneg)) (= (length args) 1))
          (rco--l-neg (rco--lin (car args))))
         ((and (memq op '(- binneg)) (= (length args) 2))
          (rco--l-add (rco--lin (car args)) (rco--l-neg (rco--lin (cadr args)))))
         ((and (memq op '(* bintimes)) (pair? args))
          ;; a product is linear only while at most one factor is non-constant;
          ;; as soon as two are, the WHOLE product is one atom.
          (let loop ((as (cdr args)) (acc (rco--lin (car args))))
            (cond ((not acc) (rco--l-atom t))
                  ((null? as) acc)
                  (#t (let ((b (rco--lin (car as))))
                        (loop (cdr as)
                              (cond ((null? (rco--l-terms acc))
                                     (rco--l-scale b (rco--l-k acc)))
                                    ((null? (rco--l-terms b))
                                     (rco--l-scale acc (rco--l-k b)))
                                    (#t #f))))))))
         ((and (eq? op 'recip) (= (length args) 1)
               (rco--rational-literal? (car args)))
          (rco--l-const (/ 1 (car args))))
         ((and (eq? op '/) (= (length args) 2)
               (rco--rational-literal? (cadr args)))
          (rco--l-scale (rco--lin (car args)) (/ 1 (cadr args))))
         (#t (rco--l-atom t)))))))

;;; An order formula as (linear form . relation), the form being lhs - rhs and
;;; the relation what it stands in to 0.  #f for anything else.
(define (rco--lin-rel f)
  (and (pair? f) (= (length f) 3)
       (let ((rel (case (car f) ((<=) 'le) ((<) 'lt) ((=) 'eq) (else #f))))
         (and rel
              (cons (rco--l-add (rco--lin (cadr f)) (rco--l-neg (rco--lin (caddr f))))
                    rel)))))

;;; =======================================================================
;;; 4.  ineq  --  verifying a Farkas certificate
;;; =======================================================================
;;;
;;; THE RULE.  The tag is (ineq CERT).  CERT is a nonnegative rational
;;; combination of constraints, given as an alist of (id . multiplier), where
;;;   goal     the NEGATION of the conclusion's goal,
;;;   hI       the I-th assumption of the conclusion (1-based) read as `L <= 0'
;;;            or `L < 0', or -- if that assumption is an equation -- as `L <= 0',
;;;   hI-rev   the same equation read as `-L <= 0'.
;;; For a goal that is an EQUATION, CERT is a PAIR of two such combinations, one
;;; for each direction.
;;;
;;; WHAT IS VERIFIED, for each combination:
;;;   (a) every multiplier is an exact nonnegative rational;
;;;   (b) every id names an assumption that really is an order formula, in the
;;;       direction the id claims;
;;;   (c) the sum of the multiples, computed atom by atom, has NO atoms left --
;;;       every coefficient cancels -- and its constant k is absurd: k > 0 when
;;;       the combination is nonstrict, k >= 0 when some strictly-used premise
;;;       makes it strict;
;;;   (d) every atom occurring in the goal or in a premise used with a positive
;;;       multiplier is certified REAL by the context: a standalone (IN a RR)
;;;       assumption, or a leading RR-restricted universal of the goal, or an
;;;       abs(.) of a term all of whose atoms are certified.  Scaling by a
;;;       positive rational and adding are order-preserving in an ordered FIELD;
;;;       over an uncertified atom the combination means nothing.
;;;   (e) no variable of a leading RR-restricted universal of the goal occurs
;;;       free in a premise used.  The oracle strips `forall x in RR' and treats
;;;       the bound x as a real atom; if an assumption mentions a DIFFERENT x
;;;       that happens to share the name, identifying the two would prove
;;;       `forall x in RR. x <= 0' from the single assumption `x <= 0'.
;;;
;;; That is a verification in the proper sense: the certificate is data, and the
;;; arithmetic above decides it without elimination, search, or any code of the
;;; oracle's.

;;; (FORALL v (IMPLIES (IN v RR) body)) ... -> (body . (v ...))
(define (rco--peel-rr g)
  (let loop ((g g) (vs '()))
    (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)
             (let ((b (caddr g)))
               (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
                    (let ((a (cadr b)))
                      (and (pair? a) (= (length a) 3) (eq? (car a) 'IN)
                           (equal? (cadr a) (cadr g)) (eq? (caddr a) 'RR))))))
        (loop (caddr (caddr g)) (cons (cadr g) vs))
        (cons g vs))))

(define (rco--in-rr? t asms)
  (rco--any? (lambda (f)
               (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                    (equal? (cadr f) t) (eq? (caddr f) 'RR)))
             asms))

(define (rco--real-atom? a asms rrvars)
  (or (and (symbol? a) (memq a rrvars))
      (rco--in-rr? a asms)
      ;; abs(t) is real as soon as t is (rr-abs-closed); t is read linearly and
      ;; every atom of it must itself be certified.
      (and (pair? a) (eq? (car a) 'abs) (= (length a) 2)
           (rco--all? (lambda (p) (rco--real-atom? (car p) asms rrvars))
                      (rco--l-terms (rco--lin (cadr a)))))))

;;; An id -> (index . direction) | 'goal | #f.  hI / hI-rev, I a positive
;;; decimal numeral.
(define (rco--ineq-id id)
  (and (symbol? id)
       (if (eq? id 'goal)
           'goal
           (let* ((s (symbol->string id))
                  (n (string-length s))
                  (rev (and (> n 4) (string=? (substring s (- n 4) n) "-rev")))
                  (digits (and (> n 1) (char=? (string-ref s 0) #\h)
                               (substring s 1 (if rev (- n 4) n)))))
             (and digits (> (string-length digits) 0)
                  (rco--all? char-numeric? (string->list digits))
                  (let ((i (string->number digits)))
                    (and (exact? i) (integer? i) (> i 0)
                         (cons i (if rev 'rev 'fwd)))))))))

;;; The constraint an id stands for, as (linear form . strict?), meaning
;;; `form <= 0' or `form < 0'.  A string is a refusal reason.
;;; NEGATED-GOAL is what `goal' stands for in this combination.
(define (rco--ineq-constraint id asms negated-goal)
  (let ((k (rco--ineq-id id)))
    (cond
      ((not k) "certificate names an id that is neither `goal' nor an assumption")
      ((eq? k 'goal) negated-goal)
      (#t
       (let ((i (car k)) (dir (cdr k)))
         (if (> i (length asms))
             "certificate names an assumption index that is not in the context"
             (let ((pr (rco--lin-rel (list-ref asms (- i 1)))))
               (cond
                 ((not pr) "a premise named by the certificate is not an order formula")
                 ((eq? (cdr pr) 'eq)
                  (if (eq? dir 'rev)
                      (cons (rco--l-neg (car pr)) #f)
                      (cons (car pr) #f)))
                 ((eq? dir 'rev)
                  "certificate uses the reverse of a premise that is not an equation")
                 (#t (cons (car pr) (eq? (cdr pr) 'lt)))))))))))

;;; Verify ONE combination.  ASMS are the raw assumption formulas.
(define (rco--farkas-ok? cert asms negated-goal rrvars)
  (let loop ((cs cert) (acc (rco--l-zero)) (strict #f) (atoms '()))
    (cond
      ((not (list? cs)) "certificate is not a list of (id . multiplier)")
      ((null? cs)
       (cond
         ((pair? (rco--l-terms acc))
          "the certificate's combination does not cancel: atoms remain")
         ((not (if strict (>= (rco--l-k acc) 0) (> (rco--l-k acc) 0)))
          "the certificate's combination is not an absurd constant inequality")
         ;; every atom that entered the combination must denote a real number
         ((rco--any? (lambda (a) (not (rco--real-atom? a asms rrvars))) atoms)
          "an atom of the goal or of a premise used is not certified real by the context")
         (#t #t)))
      ((not (and (pair? (car cs)) (rco--exact-nonneg? (cdar cs))))
       "a certificate multiplier is missing or is not an exact nonnegative rational")
      (#t
       (let ((id (caar cs)) (m (cdar cs)))
         (let ((c (rco--ineq-constraint id asms negated-goal)))
           (cond
             ((string? c) c)
             ((= m 0) (loop (cdr cs) acc strict atoms))   ; contributes nothing
             (#t
              (loop (cdr cs)
                    (rco--l-add acc (rco--l-scale (car c) m))
                    (or strict (cdr c))
                    (append atoms (map car (rco--l-terms (car c)))))))))))))

;;; The variables a certificate's premises must not mention: the eigenvariables
;;; the goal's leading RR-universals bound.
(define (rco--ineq-capture-ok? cert asms rrvars)
  (or (null? rrvars)
      (rco--all?
       (lambda (c)
         (let ((k (rco--ineq-id (car c))))
           (or (not (pair? k))
               (> (car k) (length asms))
               (let ((f (list-ref asms (- (car k) 1))))
                 (rco--all? (lambda (v) (not (memq v (free-vars f)))) rrvars)))))
       cert)))

(define (rco--check-ineq rule hyps concl)
  (let* ((cert (rco--tag-arg rule))
         (asms (rco--asms concl))
         (peel (rco--peel-rr (rco--goal concl)))
         (gpr  (rco--lin-rel (car peel)))
         (rrvars (cdr peel)))
    (cond
      ((pair? hyps) "ineq takes no hypotheses")
      ((not cert) "the ineq tag carries no Farkas certificate")
      ((not gpr) "the goal is not an order formula between linear terms")
      (#t
       (let* ((L (car gpr))
              (rel (cdr gpr)))
         (if (eq? rel 'eq)
             ;; an equation needs both directions: L <= 0 and -L <= 0.
             (if (not (and (pair? cert) (list? (car cert))))
                 "an equation goal needs a PAIR of certificates"
                 (let ((a (rco--farkas-ok? (car cert) asms (cons (rco--l-neg L) #t) rrvars))
                       (b (rco--farkas-ok? (cdr cert) asms (cons L #t) rrvars)))
                   (cond ((string? a) (string-append "first direction: " a))
                         ((string? b) (string-append "second direction: " b))
                         ((not (and (rco--ineq-capture-ok? (car cert) asms rrvars)
                                    (rco--ineq-capture-ok? (cdr cert) asms rrvars)))
                          "a premise mentions a variable the goal's RR-universal binds")
                         (#t #t))))
             ;; goal `L <= 0': its negation is `-L < 0'.
             ;; goal `L <  0': its negation is `-L <= 0'.
             (let ((neg (if (eq? rel 'le)
                            (cons (rco--l-neg L) #t)
                            (cons (rco--l-neg L) #f))))
               (let ((r (rco--farkas-ok? cert asms neg rrvars)))
                 (cond ((string? r) r)
                       ((not (rco--ineq-capture-ok? cert asms rrvars))
                        "a premise mentions a variable the goal's RR-universal binds")
                       (#t #t))))))))))

;;; =======================================================================
;;; 5.  Polynomials  (for comm-ring-simplify, ring-simplify, sos)
;;; =======================================================================
;;;
;;; A POLYNOMIAL is a list of (monomial . integer or rational coefficient) with
;;; no repeated monomial and no zero coefficient.  Two readings of a monomial:
;;;
;;;   COMMUTATIVE  an alist (generator . exponent), exponents positive: the
;;;                multiset of its factors.  Two monomials are equal when they
;;;                have the same generators with the same exponents, whatever
;;;                order they were written in.  This is the free commutative
;;;                ring ZZ[generators].
;;;   ASSOCIATIVE  a WORD, the list of its factors in order.  Equal only as
;;;                lists.  This is the free associative ZZ-algebra.
;;;
;;; Two terms denote the same element of every commutative ring (resp. of every
;;; ring) exactly when these normal forms agree -- the standard normal-form
;;; theorem for equational logic over those theories.  So comparing normal forms
;;; is a decision, and the checker is an independent RE-DECISION: it does the
;;; same mathematics with its own code (no shared order on generators, no shared
;;; representation: monomials are compared as multisets, not as sorted lists).

(define (rco--mono-comm-eq? m1 m2)
  (and (= (length m1) (length m2))
       (rco--all? (lambda (p)
                    (let ((q (assoc (car p) m2)))
                      (and q (= (cdr p) (cdr q)))))
                  m1)))

(define (rco--mono-comm-mul m1 m2)             ; multiset union
  (let loop ((ts m2) (acc m1))
    (if (null? ts)
        acc
        (let* ((g (caar ts)) (e (cdar ts)) (old (assoc g acc)))
          (loop (cdr ts)
                (if old
                    (map (lambda (p) (if (equal? (car p) g) (cons g (+ (cdr p) e)) p)) acc)
                    (append acc (list (cons g e)))))))))

(define (rco--mono-word-eq? w1 w2) (equal? w1 w2))
(define (rco--mono-word-mul w1 w2) (append w1 w2))

;;; The two monomial algebras, as (equality multiplication generator-as-monomial).
;;; Everything below is written once and reads its algebra from OPS.
(define rco--comm-ops
  (list rco--mono-comm-eq? rco--mono-comm-mul (lambda (g) (list (cons g 1)))))
(define rco--word-ops
  (list rco--mono-word-eq? rco--mono-word-mul (lambda (g) (list g))))

(define (rco--m-eq  ops) (car ops))
(define (rco--m-mul ops) (cadr ops))
(define (rco--m-gen ops) (caddr ops))

(define (rco--p-one ops) (list (cons '() 1)))   ; the empty monomial, coefficient 1
(define (rco--p-zero)    '())

(define (rco--p-const k) (if (= k 0) '() (list (cons '() k))))

(define (rco--p-gen ops g) (list (cons ((rco--m-gen ops) g) 1)))

(define (rco--p-find ops p m)
  (let loop ((ts p))
    (cond ((null? ts) #f)
          (((rco--m-eq ops) (caar ts) m) (car ts))
          (#t (loop (cdr ts))))))

(define (rco--p-add ops p q)
  (let loop ((ts q) (acc p))
    (if (null? ts)
        (filter (lambda (t) (not (= 0 (cdr t)))) acc)
        (let* ((m (caar ts)) (c (cdar ts))
               (old (rco--p-find ops acc m)))
          (loop (cdr ts)
                (if old
                    (map (lambda (t)
                           (if ((rco--m-eq ops) (car t) m) (cons (car t) (+ (cdr t) c)) t))
                         acc)
                    (append acc (list (cons m c)))))))))

(define (rco--p-neg p) (map (lambda (t) (cons (car t) (- (cdr t)))) p))

(define (rco--p-mul ops p q)
  (let loop ((ts p) (acc '()))
    (if (null? ts)
        acc
        (loop (cdr ts)
              (rco--p-add ops acc
                          (map (lambda (u)
                                 (cons ((rco--m-mul ops) (caar ts) (car u))
                                       (* (cdar ts) (cdr u))))
                               q))))))

(define (rco--p-eq? ops p q)
  (and (= (length p) (length q))
       (rco--all? (lambda (t)
                    (let ((u (rco--p-find ops q (car t))))
                      (and u (= (cdr t) (cdr u)))))
                  p)))

;;; ----- the ring surfaces --------------------------------------------------

;;; Expand a literal natural power into a product before reading a term: the
;;; polynomial reading has no exponent case, and (x+y)^2 is (x+y)*(x+y).
(define (rco--expand-pow e)
  (cond
    ((not (pair? e)) e)
    ((and (memq (car e) '(power ^ expt)) (= (length e) 3)
          (integer? (caddr e)) (exact? (caddr e)) (>= (caddr e) 0))
     (let ((b (rco--expand-pow (cadr e))) (k (caddr e)))
       (cond ((= k 0) 1)
             ((= k 1) b)
             (#t (cons '* (let rep ((i k) (acc '()))
                            (if (= i 0) acc (rep (- i 1) (cons b acc)))))))))
    (#t (cons (car e) (map rco--expand-pow (cdr e))))))

;;; THE NUMBER SURFACE: +, *, - and their binary aliases over NN/ZZ/QQ/RR/CC.
;;; Anything else is a generator, unless it evaluates to an exact number, in
;;; which case it is that constant.
(define (rco--num-poly e ops)
  (cond
    ((number? e) (let ((v (rco--exactify e))) (and v (rco--p-const v))))
    ((symbol? e) (rco--p-gen ops e))
    ((not (pair? e)) #f)
    (#t
     (case (car e)
       ((+ binplus)
        (let loop ((as (cdr e)) (acc (rco--p-zero)))
          (if (null? as) acc
              (let ((p (rco--num-poly (car as) ops)))
                (and p (loop (cdr as) (rco--p-add ops acc p)))))))
       ((* bintimes)
        (let loop ((as (cdr e)) (acc (rco--p-one ops)))
          (if (null? as) acc
              (let ((p (rco--num-poly (car as) ops)))
                (and p (loop (cdr as) (rco--p-mul ops acc p)))))))
       ((- binneg)
        (cond
          ((null? (cdr e)) #f)
          ((null? (cddr e)) (let ((p (rco--num-poly (cadr e) ops)))
                              (and p (rco--p-neg p))))
          (#t (let loop ((as (cddr e)) (acc (rco--num-poly (cadr e) ops)))
                (if (or (not acc) (null? as)) acc
                    (let ((p (rco--num-poly (car as) ops)))
                      (and p (loop (cdr as) (rco--p-add ops acc (rco--p-neg p))))))))))
       (else (let ((v (rco--ev e '())))
               (if v (rco--p-const v) (rco--p-gen ops e))))))))

;;; The generators of a number-surface term, INCLUDING the ones that cancel: in
;;; VNB `=' is partial, so `e1 = e2' asserts both sides DEFINED, and a side is
;;; defined only if every one of its atoms lies in the carrier.  x cancels in
;;; x - x but x - x = 0 is not a theorem about an undefined x.
(define (rco--num-gens e)
  (cond
    ((number? e) '())
    ((symbol? e) (list e))
    ((not (pair? e)) '())
    (#t
     (case (car e)
       ((+ * - binplus bintimes binneg)
        (apply append (map rco--num-gens (cdr e))))
       (else (if (rco--ev e '()) '() (list e)))))))

;;; THE STRUCTURE SURFACE: the operations of an arbitrary ring R.
(define (rco--ring-op? h name R)
  (and (pair? h) (eq? (car h) name) (= (length h) 2) (equal? (cadr h) R)))

(define (rco--ring-poly e R ops)
  (cond
    ((symbol? e) (rco--p-gen ops e))
    ((not (pair? e)) #f)
    (#t
     (let ((h (car e)))
       (cond
         ((and (rco--ring-op? h 'ADD R) (= (length e) 3))
          (let ((p (rco--ring-poly (cadr e) R ops)) (q (rco--ring-poly (caddr e) R ops)))
            (and p q (rco--p-add ops p q))))
         ((and (rco--ring-op? h 'MUL R) (= (length e) 3))
          (let ((p (rco--ring-poly (cadr e) R ops)) (q (rco--ring-poly (caddr e) R ops)))
            (and p q (rco--p-mul ops p q))))
         ((and (rco--ring-op? h 'NEG R) (= (length e) 2))
          (let ((p (rco--ring-poly (cadr e) R ops))) (and p (rco--p-neg p))))
         ((and (eq? h 'ZERO) (= (length e) 2) (equal? (cadr e) R)) (rco--p-zero))
         ((and (eq? h 'ONE)  (= (length e) 2) (equal? (cadr e) R)) (rco--p-one ops))
         (#t (rco--p-gen ops e)))))))     ; any other term: one opaque element

(define (rco--ring-gens e R)
  (cond
    ((symbol? e) (list e))
    ((not (pair? e)) '())
    (#t
     (let ((h (car e)))
       (cond
         ((and (rco--ring-op? h 'ADD R) (= (length e) 3))
          (append (rco--ring-gens (cadr e) R) (rco--ring-gens (caddr e) R)))
         ((and (rco--ring-op? h 'MUL R) (= (length e) 3))
          (append (rco--ring-gens (cadr e) R) (rco--ring-gens (caddr e) R)))
         ((and (rco--ring-op? h 'NEG R) (= (length e) 2))
          (rco--ring-gens (cadr e) R))
         ((and (eq? h 'ZERO) (= (length e) 2) (equal? (cadr e) R)) '())
         ((and (eq? h 'ONE)  (= (length e) 2) (equal? (cadr e) R)) '())
         (#t (list e)))))))

;;; ----- certification of the generators ------------------------------------
;;;
;;; NN, ZZ, QQ, RR, CC are nested subsets of CC and their +, * and - are the
;;; restrictions of CC's, so a polynomial identity over generators certified in
;;; ANY of the five holds of them: the identity is evaluated in the commutative
;;; ring CC.  (NN is not a ring, but nothing here needs it to be: the terms
;;; denote in CC.)  Membership in VNB also entails definedness, so certifying a
;;; compound generator covers the definedness the equation asserts.
(define (rco--number-class? d)
  (and (symbol? d) (memq d '(NN ZZ QQ RR CC))))

;;; Peel (FORALL v (IMPLIES (IN v D) ...)) with D a number class -- the typed
;;; universal form the oracle may close without a prior `di'.  Returns
;;; (inner . ((v . D) ...)), or #f if a leading FORALL is not of that shape.
(define (rco--peel-num-foralls g)
  (let loop ((g g) (qs '()))
    (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3))
        (let ((v (cadr g)) (b (caddr g)))
          (if (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
                   (let ((a (cadr b)))
                     (and (pair? a) (= (length a) 3) (eq? (car a) 'IN)
                          (equal? (cadr a) v) (rco--number-class? (caddr a)))))
              (loop (caddr b) (cons (cons v (caddr (cadr b))) qs))
              #f))
        (cons g qs))))

;;; Peel (FORALL R (IMPLIES (IS-COMMUTATIVE-RING R) (FORALL v (IMPLIES (IN v
;;; (CARR R)) ...)))) -> (list R (v ...) inner), or #f.
(define (rco--peel-cring-foralls g)
  (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)
       (let ((R (cadr g)) (b (caddr g)))
         (and (pair? b) (eq? (car b) 'IMPLIES) (= (length b) 3)
              (let ((a (cadr b)))
                (and (pair? a) (= (length a) 2)
                     (eq? (car a) 'IS-COMMUTATIVE-RING) (equal? (cadr a) R)
                     (let loop ((g (caddr b)) (vs '()))
                       (if (and (pair? g) (eq? (car g) 'FORALL) (= (length g) 3)
                                (let ((c (caddr g)))
                                  (and (pair? c) (eq? (car c) 'IMPLIES) (= (length c) 3)
                                       (let ((t (cadr c)))
                                         (and (pair? t) (= (length t) 3) (eq? (car t) 'IN)
                                              (equal? (cadr t) (cadr g))
                                              (equal? (caddr t) (list 'CARR R)))))))
                           (loop (caddr (caddr g)) (cons (cadr g) vs))
                           (list R vs g)))))))))

(define (rco--typed-in? g cls asms)
  (rco--any? (lambda (f)
               (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                    (equal? (cadr f) g) (equal? (caddr f) cls)))
             asms))

(define (rco--num-gens-ok? gens qs asms)
  (rco--all?
   (lambda (g)
     (or (let ((q (assoc g qs))) (and q (rco--number-class? (cdr q))))
         (rco--any? (lambda (f)
                      (and (pair? f) (= (length f) 3) (eq? (car f) 'IN)
                           (equal? (cadr f) g) (rco--number-class? (caddr f))))
                    asms)))
   gens))

(define (rco--ring-gens-ok? gens R qvars asms)
  (let ((carrier (list 'CARR R)))
    (rco--all? (lambda (g)
                 (or (member g qvars) (rco--typed-in? g carrier asms)))
               gens)))

(define (rco--dedup lst)
  (let loop ((xs lst) (acc '()))
    (cond ((null? xs) (reverse acc))
          ((member (car xs) acc) (loop (cdr xs) acc))
          (#t (loop (cdr xs) (cons (car xs) acc))))))

;;; =======================================================================
;;; 6.  comm-ring-simplify, ring-simplify, sos
;;; =======================================================================

;;; RULE (comm-ring-simplify).  No hypotheses.  The conclusion's goal, after
;;; peeling typed universals, is an equation whose two sides have the same
;;; commutative normal form over generators all certified in a carrier -- on one
;;; of the two surfaces:
;;;   NUMBER SURFACE   generators typed (IN g D), D one of NN ZZ QQ RR CC, by a
;;;                    peeled universal or by a standalone assumption;
;;;   STRUCTURE SURFACE  a ring R certified IS-COMMUTATIVE-RING by a peeled
;;;                    universal or by an assumption, generators typed
;;;                    (IN g (CARR R)) the same way.
(define (rco--crs-number-ok? g asms ops)
  (let ((peeled (rco--peel-num-foralls g)))
    (and peeled
         (let ((inner (car peeled)) (qs (cdr peeled)))
           (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
                (let ((e1 (rco--expand-pow (cadr inner)))
                      (e2 (rco--expand-pow (caddr inner))))
                  (let ((p1 (rco--num-poly e1 ops)) (p2 (rco--num-poly e2 ops)))
                    (and p1 p2 (rco--p-eq? ops p1 p2)
                         (rco--num-gens-ok?
                          (rco--dedup (append (rco--num-gens e1) (rco--num-gens e2)))
                          qs asms)))))))))

(define (rco--crs-structure-ok? g asms)
  (let* ((peeled (rco--peel-cring-foralls g))
         (inner  (if peeled (caddr peeled) g))
         (qvars  (if peeled (cadr peeled) '())))
    (and (pair? inner) (eq? (car inner) '=) (= (length inner) 3)
         (let ((R (or (and peeled (car peeled))
                      (rco--find-ring (cadr inner))
                      (rco--find-ring (caddr inner)))))
           (and R
                (or (and peeled #t)
                    (rco--any? (lambda (f)
                                 (and (pair? f) (= (length f) 2)
                                      (eq? (car f) 'IS-COMMUTATIVE-RING)
                                      (equal? (cadr f) R)))
                               asms))
                (let ((p1 (rco--ring-poly (cadr inner) R rco--comm-ops))
                      (p2 (rco--ring-poly (caddr inner) R rco--comm-ops)))
                  (and p1 p2 (rco--p-eq? rco--comm-ops p1 p2)
                       (rco--ring-gens-ok?
                        (rco--dedup (append (rco--ring-gens (cadr inner) R)
                                            (rco--ring-gens (caddr inner) R)))
                        R qvars asms))))))))

;;; The ring a structure-surface term is written over: the R of the first
;;; (ADD R) / (MUL R) / (NEG R) head or (ZERO R) / (ONE R) constant.
(define (rco--find-ring e)
  (and (pair? e)
       (let ((h (car e)))
         (cond
           ((and (pair? h) (memq (car h) '(ADD MUL NEG)) (= (length h) 2)) (cadr h))
           ((and (memq h '(ZERO ONE)) (= (length e) 2)) (cadr e))
           (#t (let loop ((xs e))
                 (and (pair? xs)
                      (or (rco--find-ring (car xs)) (loop (cdr xs))))))))))

(define (rco--check-crs rule hyps concl)
  (let ((g (rco--goal concl)) (asms (rco--asms concl)))
    (cond
      ((pair? hyps) "comm-ring-simplify takes no hypotheses")
      ((rco--crs-number-ok? g asms rco--comm-ops) #t)
      ((rco--crs-structure-ok? g asms) #t)
      (#t "not an equation whose sides share a commutative normal form over certified generators"))))

;;; RULE (ring-simplify).  As above, on the number surface only, in the free
;;; ASSOCIATIVE algebra: x*y and y*x are different monomials.
(define (rco--check-rs rule hyps concl)
  (cond
    ((pair? hyps) "ring-simplify takes no hypotheses")
    ((rco--crs-number-ok? (rco--goal concl) (rco--asms concl) rco--word-ops) #t)
    (#t "not an equation whose sides share an associative normal form over certified generators")))

;;; RULE (sos).  The tag is (sos ((term . lambda) ...)).  No hypotheses.  The
;;; goal, after peeling RR-universals, is a NONSTRICT inequality a <= b (or
;;; b >= a) over RR-certified generators, and
;;;      b - a  =  sum lambda_i * (term_i)^2   with every lambda_i >= 0,
;;; as polynomials -- monomial by monomial, in the free commutative ring.  Each
;;; square is >= 0 over RR and each weight is >= 0, so 0 <= b - a.  A STRICT
;;; goal is refused: a square may vanish.
;;;
;;; A verification in the proper sense: the squares and their weights are data
;;; the oracle recorded, and the identity is decided here by polynomial
;;; arithmetic that shares nothing with the oracle's simplex.
(define (rco--check-sos rule hyps concl)
  (let* ((cert (rco--tag-arg rule))
         (asms (rco--asms concl))
         (peel (rco--peel-rr (rco--goal concl)))
         (goal (car peel))
         (rrvars (cdr peel)))
    (cond
      ((pair? hyps) "sos takes no hypotheses")
      ((not (list? cert)) "the sos tag carries no ((term . lambda) ...) certificate")
      ((not (and (pair? goal) (= (length goal) 3) (memq (car goal) '(<= >=))))
       "the goal is not a nonstrict inequality")
      ((not (rco--all? (lambda (c) (and (pair? c) (rco--exact-nonneg? (cdr c)))) cert))
       "a sos weight is missing or is not an exact nonnegative rational")
      (#t
       (let* ((flip (eq? (car goal) '>=))
              (a (rco--expand-pow (if flip (caddr goal) (cadr goal))))
              (b (rco--expand-pow (if flip (cadr goal) (caddr goal))))
              (pa (rco--num-poly a rco--comm-ops))
              (pb (rco--num-poly b rco--comm-ops))
              (squares (map (lambda (c)
                              (let ((p (rco--num-poly (rco--expand-pow (car c))
                                                      rco--comm-ops)))
                                (and p (rco--p-mul rco--comm-ops p p))))
                            cert))
              (gens (rco--dedup
                     (append (rco--num-gens a) (rco--num-gens b)
                             (apply append
                                    (map (lambda (c)
                                           (rco--num-gens (rco--expand-pow (car c))))
                                         cert))))))
         (cond
           ((not (and pa pb (rco--all? (lambda (s) s) squares)))
            "a side or a certificate term is not a polynomial")
           ((not (rco--all? (lambda (v) (rco--real-atom? v asms rrvars)) gens))
            "a generator of the goal or of a certificate term is not certified real")
           (#t
            (let ((D (rco--p-add rco--comm-ops pb (rco--p-neg pa)))
                  (S (let loop ((cs cert) (ss squares) (acc '()))
                       (if (null? cs) acc
                           (loop (cdr cs) (cdr ss)
                                 (rco--p-add rco--comm-ops acc
                                             (map (lambda (t)
                                                    (cons (car t) (* (cdr t) (cdar cs))))
                                                  (car ss))))))))
              (if (rco--p-eq? rco--comm-ops D S)
                  #t
                  "b - a is not the certificate's nonnegative combination of squares")))))))))

;;; =======================================================================
;;; 7.  Registration, and what is still taken on trust
;;; =======================================================================

;;; A head registered here is accepted WITHOUT a check.  `(trusted-oracle-rules)'
;;; reports the list, so a load can print what the kernel is still believing.
(define *rco-trusted* '())

(define (rco--check-trusted-oracle rule hyps concl) #t)

(define (rco-trust-oracle! head why)
  (set! *rco-trusted* (append *rco-trusted* (list (cons head why))))
  (register-rule-checker! head rco--check-trusted-oracle))

(define (trusted-oracle-rules) (map car *rco-trusted*))

(define (trusted-oracle-report)
  (if (null? *rco-trusted*)
      (display ";; rule checkers: every oracle operation is checked.\n")
      (begin
        (display ";; rule checkers: accepted on TRUST (no check): ")
        (for-each (lambda (p)
                    (display (car p)) (display " (") (display (cdr p)) (display ") "))
                  *rco-trusted*)
        (newline))))

(register-rule-checker! 'ineq               rco--check-ineq)
(register-rule-checker! 'arith-ground       rco--check-arith-ground)
(register-rule-checker! 'arith-forsome      rco--check-arith-forsome)
(register-rule-checker! 'arith-simplify     rco--check-arith-simplify)
(register-rule-checker! 'comm-ring-simplify rco--check-crs)
(register-rule-checker! 'ring-simplify      rco--check-rs)
(register-rule-checker! 'sos                rco--check-sos)
