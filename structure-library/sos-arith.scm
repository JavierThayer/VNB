;;; sos-arith.scm -- exact-rational LP feasibility with witness extraction.
;;;
;;; The linear core of the (sos) sum-of-squares oracle (sos-oracle.scm, kernel
;;; side).  It decides one question:
;;;
;;;   given vectors  S_1 .. S_n  and a target vector  D  (all over a shared,
;;;   finite set of monomial keys, entries exact rationals), do there exist
;;;   NONNEGATIVE rationals  lambda_1 .. lambda_n  with  Sum_i lambda_i S_i = D ?
;;;
;;; and, when the answer is yes, RETURNS the witness (lambda_1 .. lambda_n).
;;; In the oracle the S_i are the monomial vectors of the certificate squares
;;; (cert_i)^2 and D is the monomial vector of (b - a); a feasible lambda
;;; certifies  b - a = Sum_i lambda_i (cert_i)^2 >= 0,  hence  a <= b.
;;;
;;; Method: Phase-I simplex over EXACT rationals.  We minimise the sum of one
;;; artificial variable per equation; the system is feasible iff that minimum
;;; is 0, and the basic lambda values at optimum are the witness.  Bland's rule
;;; (smallest-index entering / smallest-basis-index leaving) guarantees
;;; termination with no cycling.  Pure Scheme, no kernel coupling; the alist
;;; helpers (la-uniq, la-get-style assoc) are shared with linear-arith.scm,
;;; which loads first.  Unit-tested by (run-sos-tests).
;;;
;;; Soundness of the oracle that calls this is external (each (cert_i)^2 >= 0
;;; over RR, lambda_i >= 0); this file only certifies the exact linear identity
;;; Sum lambda_i S_i = D, so a wrong witness can never be returned -- the
;;; equality is enforced on every monomial key.

;;; -----------------------------------------------------------------------
;;; Sparse vectors: alists (key . rational), keys compared with equal? (a key
;;; is a sorted monomial = generator list, possibly compound -- see crs).

(define (sv-get v k) (let ((p (assoc k v))) (if p (cdr p) 0)))

(define (sv-keys vs)                     ; union of keys across a list of vectors
  (la-uniq (apply append (map (lambda (v) (map car v)) vs))))

;;; -----------------------------------------------------------------------
;;; Dense rational row helpers (Scheme vectors of exact rationals).

(define (row-scale! row k)
  (let ((w (vector-length row)))
    (let loop ((j 0))
      (when (< j w) (vector-set! row j (* k (vector-ref row j))) (loop (+ j 1))))))

;; row <- row - f * piv   (elementwise, over all columns)
(define (row-axpy! row piv f)
  (if (not (= f 0))
      (let ((w (vector-length row)))
        (let loop ((j 0))
          (when (< j w)
            (vector-set! row j (- (vector-ref row j) (* f (vector-ref piv j))))
            (loop (+ j 1)))))))

;;; -----------------------------------------------------------------------
;;; sos-nonneg-combo : (list-of-vector) vector -> (list rational) | #f
;;;
;;; targets = (S_1 .. S_n), D the target.  Returns a length-n nonnegative
;;; rational list lambda with Sum lambda_i S_i = D, or #f if none exists.

(define (sos-nonneg-combo targets D)
  (let* ((keys (sv-keys (cons D targets)))
         (n    (length targets))
         (m    (length keys)))
    (cond
      ((= m 0)                                  ; no equations: 0 = 0
       (map (lambda (ignore) 0) targets))
      (else (sos-phase1 keys targets n m D)))))

;;; Build the Phase-I tableau and run simplex.  Columns 0..n-1 are the lambdas,
;;; n..n+m-1 the artificials, column W=n+m is the right-hand side.  The cost
;;; row (rc) carries reduced costs in cols 0..W-1 and -objective in col W.
(define (sos-phase1 keys targets n m D)
  (let* ((W      (+ n m))
         (ncol   (+ W 1))
         (T      (make-vector m))
         (basis  (make-vector m)))
    ;; one constraint row per monomial key
    (let rowloop ((ks keys) (r 0))
      (when (pair? ks)
        (let ((row (make-vector ncol 0))
              (dk  (sv-get D (car ks))))
          (let cloop ((ts targets) (j 0))   ; lambda coefficients = S_i(key)
            (when (pair? ts)
              (vector-set! row j (sv-get (car ts) (car ks)))
              (cloop (cdr ts) (+ j 1))))
          (vector-set! row W dk)
          (when (< dk 0) (row-scale! row -1)) ; keep rhs >= 0
          (vector-set! row (+ n r) 1)         ; artificial column
          (vector-set! basis r (+ n r))
          (vector-set! T r row)
          (rowloop (cdr ks) (+ r 1)))))
    ;; reduced-cost row: all artificials basic with cost 1, lambdas cost 0, so
    ;; rc[j] = cost[j] - Sum_r T[r][j];  rc[W] = -Sum_r rhs_r = -objective.
    (let ((rc (make-vector ncol 0)))
      (let jloop ((j 0))
        (when (< j ncol)
          (let ((cj (if (and (>= j n) (< j W)) 1 0)))
            (vector-set! rc j
              (let sumr ((r 0) (acc cj))
                (if (< r m) (sumr (+ r 1) (- acc (vector-ref (vector-ref T r) j)))
                    acc))))
          (jloop (+ j 1))))
      ;; simplex iterations (Bland); cap as a paranoia backstop.
      (let iterate ((guard (* 4 (+ (* (+ n m) (+ n m)) 1))))
        (let ((enter (sos-entering rc W)))
          (cond
            ((not enter)                           ; optimal
             (if (= 0 (vector-ref rc W))           ; objective 0 => feasible
                 (sos-extract T basis n m W)
                 #f))
            ((<= guard 0) #f)                      ; should never trigger
            (else
             (let ((leave (sos-leaving T basis enter m W)))
               (if (not leave) #f                  ; unbounded (cannot happen, >=0)
                   (begin (sos-pivot! T rc basis leave enter m ncol)
                          (iterate (- guard 1))))))))))))

;;; Bland entering rule: smallest structural/artificial column with rc < 0.
(define (sos-entering rc W)
  (let loop ((j 0))
    (cond ((>= j W) #f)
          ((< (vector-ref rc j) 0) j)
          (else (loop (+ j 1))))))

;;; Min-ratio leaving rule; ties broken by smallest basis index (Bland).
(define (sos-leaving T basis enter m W)
  (let loop ((r 0) (best #f) (bestratio #f))
    (if (>= r m)
        best
        (let ((a (vector-ref (vector-ref T r) enter)))
          (if (> a 0)
              (let ((ratio (/ (vector-ref (vector-ref T r) W) a)))
                (if (or (not best)
                        (< ratio bestratio)
                        (and (= ratio bestratio)
                             (< (vector-ref basis r) (vector-ref basis best))))
                    (loop (+ r 1) r ratio)
                    (loop (+ r 1) best bestratio)))
              (loop (+ r 1) best bestratio))))))

;;; Pivot on (leave, enter): normalise the pivot row, clear the entering column
;;; from every other constraint row and from the reduced-cost row.
(define (sos-pivot! T rc basis leave enter m ncol)
  (let* ((prow (vector-ref T leave))
         (piv  (vector-ref prow enter)))
    (row-scale! prow (/ 1 piv))
    (let loop ((r 0))
      (when (< r m)
        (if (not (= r leave))
            (row-axpy! (vector-ref T r) prow (vector-ref (vector-ref T r) enter)))
        (loop (+ r 1))))
    (row-axpy! rc prow (vector-ref rc enter))
    (vector-set! basis leave enter)))

;;; Read the witness: lambda_j is its basic value if basic, else 0 (nonbasic).
(define (sos-extract T basis n m W)
  (let ((lam (make-vector n 0)))
    (let loop ((r 0))
      (when (< r m)
        (let ((b (vector-ref basis r)))
          (if (< b n) (vector-set! lam b (vector-ref (vector-ref T r) W))))
        (loop (+ r 1))))
    (let build ((j (- n 1)) (acc '()))
      (if (< j 0) acc (build (- j 1) (cons (vector-ref lam j) acc))))))

;;; -----------------------------------------------------------------------
;;; Standalone unit tests.  (run-sos-tests) prints PASS/FAIL per case and
;;; returns the failure count.  Vectors written as alists (key . rat).

(define sos-pass 0)
(define sos-fail 0)
(define (sos-check name got expect)
  (let ((ok (if (eq? expect #f) (not got)
                (and got (equal? got expect)))))
    (set! sos-pass (+ sos-pass (if ok 1 0)))
    (set! sos-fail (+ sos-fail (if ok 0 1)))
    (display (if ok "  PASS  " "  FAIL  ")) (display name)
    (if (not ok) (begin (display "   got=") (write got)
                        (display " want=") (write expect)))
    (newline)))

(define (run-sos-tests)
  (set! sos-pass 0) (set! sos-fail 0)
  ;; 1. x*y <= x^2+y^2 : D = x^2 - x*y + y^2, squares (x-y)^2, x^2, y^2.
  ;;    (x-y)^2 = x^2 - 2x*y + y^2.  Unique witness (1/2,1/2,1/2).
  (sos-check "x*y<=x^2+y^2 via (x-y)^2,x^2,y^2"
    (sos-nonneg-combo
      (list '(((x x) . 1) ((x y) . -2) ((y y) . 1))   ; (x-y)^2
            '(((x x) . 1))                              ; x^2
            '(((y y) . 1)))                             ; y^2
      '(((x x) . 1) ((x y) . -1) ((y y) . 1)))          ; D
    (list 1/2 1/2 1/2))
  ;; 2. exact single square: D = (x-y)^2 itself => lambda = (1).
  (sos-check "D = (x-y)^2 => (1)"
    (sos-nonneg-combo (list '(((x x) . 1) ((x y) . -2) ((y y) . 1)))
                      '(((x x) . 1) ((x y) . -2) ((y y) . 1)))
    (list 1))
  ;; 3. scaling: D = 3*x^2, square x^2 => lambda = (3).
  (sos-check "D = 3 x^2 => (3)"
    (sos-nonneg-combo (list '(((x x) . 1))) '(((x x) . 3)))
    (list 3))
  ;; 4. INFEASIBLE: a square cannot produce a bare negative monomial.
  (sos-check "D = -x^2 infeasible"
    (sos-nonneg-combo (list '(((x x) . 1))) '(((x x) . -1)))
    #f)
  ;; 5. INFEASIBLE: D needs an x*y term no nonneg square combo can match.
  (sos-check "D = x*y alone infeasible from x^2,y^2"
    (sos-nonneg-combo (list '(((x x) . 1)) '(((y y) . 1)))
                      '(((x y) . 1)))
    #f)
  ;; 6. redundant squares (underdetermined): D=x^2, squares x^2 and x^2.
  ;;    Feasible; Phase-I picks a nonneg witness summing the right total.
  (sos-check "underdetermined x^2 from {x^2,x^2} feasible"
    (let ((w (sos-nonneg-combo (list '(((x x) . 1)) '(((x x) . 1)))
                               '(((x x) . 1)))))
      (and w (= 2 (length w)) (every-nonneg? w)
           (= 1 (+ (car w) (cadr w)))))
    #t)
  ;; 7. empty target (D=0) => all-zero witness.
  (sos-check "D = 0 => (0 0)"
    (sos-nonneg-combo (list '(((x x) . 1)) '(((y y) . 1))) '())
    (list 0 0))
  ;; 8. two-variable AM-GM-ish: D = x^2 + 4 y^2 - 4 x y = (x-2y)^2.
  (sos-check "x^2+4y^2-4xy = (x-2y)^2 => (1)"
    (sos-nonneg-combo (list '(((x x) . 1) ((x y) . -4) ((y y) . 4)))
                      '(((x x) . 1) ((x y) . -4) ((y y) . 4)))
    (list 1))
  (display "=== SOS-ARITH SUMMARY: ") (display sos-pass) (display " passed, ")
  (display sos-fail) (display " failed ===") (newline)
  sos-fail)

(define (every-nonneg? xs)
  (or (null? xs) (and (>= (car xs) 0) (every-nonneg? (cdr xs)))))
