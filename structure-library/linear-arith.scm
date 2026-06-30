;;; linear-arith.scm -- standalone linear-arithmetic decision core.
;;;
;;; Fourier-Motzkin refutation with Farkas certificates, over EXACT RATIONALS.
;;; Pure Scheme, NO kernel coupling: this file decides feasibility of a finite
;;; conjunction of linear constraints over an ordered field (RR), and when the
;;; conjunction is infeasible returns the Farkas certificate -- the nonnegative
;;; combination of the input constraints that sums to a manifest contradiction
;;; (a positive constant <= 0, or any constant < 0 that is actually >= 0).
;;;
;;; The (ineq) oracle (kernel side, separate file) will:
;;;   1. parse a goal `g REL 0` and linear hypotheses into constraints,
;;;   2. negate the goal, hand the lot to fm-refute,
;;;   3. on success, discharge the goal carrying the returned certificate.
;;; This file is the engine only; it is unit-tested standalone (run-la-tests).
;;;
;;; CONSTRAINT representation (a tagged list):
;;;   (con coeffs const rel prov)
;;;     coeffs : alist (var . rational)         -- the linear part, Sum coeff*var
;;;     const  : rational                       -- the constant term
;;;     rel    : 'le | 'lt                      -- meaning (Sum coeff*var)+const REL 0
;;;     prov   : alist (id . rational>=0)        -- the nonneg combination of the
;;;                                                ORIGINAL constraints (by id) that
;;;                                                produced this one  [the certificate]
;;; Variables are symbols; ids are anything eqv?-comparable.

;;; -----------------------------------------------------------------------
;;; Tiny alist arithmetic (keys are symbols/atoms; values rationals).

;; Keys are atoms -- symbols OR COMPOUND TERMS (e.g. (f x), ((DIST s) x y)) -- so
;; comparison must be equal?, not eqv? (two distinct (f x) list objects are not
;; eqv?).  This is what lets compound atoms cancel/combine, mirroring how crs
;; compares generators.
(define (la-uniq lst)                       ; dedup, equal?
  (let loop ((l lst) (acc '()))
    (cond ((null? l) (reverse acc))
          ((member (car l) acc) (loop (cdr l) acc))
          (else (loop (cdr l) (cons (car l) acc))))))

(define (la-get al k) (let ((p (assoc k al))) (if p (cdr p) 0)))

(define (la-scale al k)                     ; multiply every value by k
  (map (lambda (p) (cons (car p) (* k (cdr p)))) al))

(define (la-clean al)                        ; drop zero entries
  (filter (lambda (p) (not (= 0 (cdr p)))) al))

(define (la-add a b)                         ; sum two alists key-wise
  (let ((keys (la-uniq (append (map car a) (map car b)))))
    (la-clean (map (lambda (k) (cons k (+ (la-get a k) (la-get b k)))) keys))))

;;; -----------------------------------------------------------------------
;;; Constraint constructors / accessors.

(define (make-con coeffs const rel prov) (list 'con coeffs const rel prov))
(define (con-coeffs c) (list-ref c 1))
(define (con-const  c) (list-ref c 2))
(define (con-rel    c) (list-ref c 3))
(define (con-prov   c) (list-ref c 4))

(define (rel-join r1 r2) (if (or (eq? r1 'lt) (eq? r2 'lt)) 'lt 'le))

(define (con-scale c k)                      ; k must be > 0 (keeps rel, prov nonneg)
  (make-con (la-scale (con-coeffs c) k)
            (* k (con-const c))
            (con-rel c)
            (la-scale (con-prov c) k)))

(define (con-add c1 c2)
  (make-con (la-add (con-coeffs c1) (con-coeffs c2))
            (+ (con-const c1) (con-const c2))
            (rel-join (con-rel c1) (con-rel c2))
            (la-add (con-prov c1) (con-prov c2))))

(define (la-all-vars cstrs)
  (la-uniq (apply append (map (lambda (c) (map car (con-coeffs c))) cstrs))))

;;; A *constant* constraint (no variables) is contradictory when it asserts
;;; something false about its constant: (const <= 0) with const > 0, or
;;; (const < 0) with const >= 0.
(define (con-contradictory? c)
  (and (null? (con-coeffs c))
       (let ((k (con-const c)))
         (if (eq? (con-rel c) 'lt) (>= k 0) (> k 0)))))

(define (la-find pred lst)                   ; first element satisfying pred, or #f
  (cond ((null? lst) #f)
        ((pred (car lst)) (car lst))
        (else (la-find pred (cdr lst)))))

;;; -----------------------------------------------------------------------
;;; Fourier-Motzkin: eliminate one variable v from a constraint list.
;;; Each (positive-on-v, negative-on-v) pair is combined into a v-free
;;; constraint by a NONNEGATIVE combination (so provenance stays a valid
;;; Farkas multiplier); v-free constraints pass through; one-sided
;;; constraints (only positive, or only negative, on v) are dropped -- they
;;; bound v from a single side and constrain nothing else.
(define (fm-eliminate v cstrs)
  (let loop ((cs cstrs) (pos '()) (neg '()) (zero '()))
    (if (null? cs)
        (append zero
          (apply append
            (map (lambda (p)
                   (map (lambda (n)
                          (let ((cp (la-get (con-coeffs p) v))    ; > 0
                                (cn (la-get (con-coeffs n) v)))   ; < 0
                            ;; (-cn)*p + cp*n  cancels v; both weights > 0
                            (con-add (con-scale p (- cn))
                                     (con-scale n cp))))
                        neg))
                 pos)))
        (let ((cv (la-get (con-coeffs (car cs)) v)))
          (cond ((> cv 0) (loop (cdr cs) (cons (car cs) pos) neg zero))
                ((< cv 0) (loop (cdr cs) pos (cons (car cs) neg) zero))
                (else     (loop (cdr cs) pos neg (cons (car cs) zero))))))))

;;; fm-refute : list of constraints -> Farkas certificate (prov alist) | #f
;;; Eliminate all variables; if any surviving constant constraint is
;;; contradictory, its provenance is the certificate.
(define (fm-refute cstrs)
  (let loop ((cs cstrs) (vs (la-all-vars cstrs)))
    (if (null? vs)
        (let ((bad (la-find con-contradictory? cs)))
          (and bad (la-clean (con-prov bad))))
        (loop (fm-eliminate (car vs) cs) (cdr vs)))))

;;; -----------------------------------------------------------------------
;;; Goal negation + the prove wrapper.
;;;
;;; To PROVE  g REL 0  from hyps, assume its negation and refute:
;;;   goal (g <= 0)  -> assume  g > 0  i.e.  -g < 0   (negate, rel 'lt)
;;;   goal (g <  0)  -> assume  g >= 0 i.e.  -g <= 0  (negate, rel 'le)
;;;   goal (g =  0)  -> prove g <= 0 AND -g <= 0 separately (two refutations).
;;; The negated goal carries id 'goal so it appears in the certificate.

(define (con-negate-as-goal coeffs const rel)
  (make-con (la-scale coeffs -1) (- const)
            (if (eq? rel 'lt) 'le 'lt)
            '((goal . 1))))

;;; fm-prove : hyps (list of con, each with its own id in prov) ,
;;;            goal-coeffs, goal-const, goal-rel ('le|'lt|'eq)
;;;          -> certificate | (cons cert1 cert2) for 'eq | #f
(define (fm-prove hyps gcoeffs gconst grel)
  (if (eq? grel 'eq)
      (let ((c1 (fm-prove hyps gcoeffs gconst 'le))
            (c2 (fm-prove hyps (la-scale gcoeffs -1) (- gconst) 'le)))
        (and c1 c2 (cons c1 c2)))
      (fm-refute (cons (con-negate-as-goal gcoeffs gconst grel) hyps))))

;;; convenience: build a hypothesis constraint with a single-id provenance.
(define (la-hyp id coeffs const rel) (make-con coeffs const rel (list (cons id 1))))

;;; -----------------------------------------------------------------------
;;; Standalone unit tests.  (run-la-tests) prints PASS/FAIL per case.

(define la-pass 0)
(define la-fail 0)
(define (la-check name got expect-true?)
  (let ((ok (if expect-true? (and got #t) (not got))))
    (set! la-pass (+ la-pass (if ok 1 0)))
    (set! la-fail (+ la-fail (if ok 0 1)))
    (display (if ok "  PASS  " "  FAIL  ")) (display name)
    (if (and ok got (not (eq? got #t))) (begin (display "   cert=") (write got)))
    (newline)))

(define (run-la-tests)
  (set! la-pass 0) (set! la-fail 0)
  ;; 1. transitivity: x<=y, y<=z  |-  x<=z
  (la-check "transitivity x<=y,y<=z => x<=z"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'le)
                    (la-hyp 1 '((y . 1) (z . -1)) 0 'le))
              '((x . 1) (z . -1)) 0 'le) #t)
  ;; 2. add inequalities: x<=y, u<=v |- x+u <= y+v
  (la-check "add x<=y,u<=v => x+u<=y+v"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'le)
                    (la-hyp 1 '((u . 1) (v . -1)) 0 'le))
              '((x . 1) (u . 1) (y . -1) (v . -1)) 0 'le) #t)
  ;; 3. strict chaining: x<y, y<z |- x<z
  (la-check "strict x<y,y<z => x<z"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'lt)
                    (la-hyp 1 '((y . 1) (z . -1)) 0 'lt))
              '((x . 1) (z . -1)) 0 'lt) #t)
  ;; 4. mixed: x<y, y<=z |- x<z
  (la-check "mixed x<y,y<=z => x<z"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'lt)
                    (la-hyp 1 '((y . 1) (z . -1)) 0 'le))
              '((x . 1) (z . -1)) 0 'lt) #t)
  ;; 5. scaling certificate uses rationals: 2x<=2y |- x<=y  (cert multiplier 1/2)
  (la-check "halving 2x<=2y => x<=y (rational cert)"
    (fm-prove (list (la-hyp 0 '((x . 2) (y . -2)) 0 'le))
              '((x . 1) (y . -1)) 0 'le) #t)
  ;; 6. equality goal: x<=y, y<=x |- x=y
  (la-check "antisymmetry x<=y,y<=x => x=y"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'le)
                    (la-hyp 1 '((y . 1) (x . -1)) 0 'le))
              '((x . 1) (y . -1)) 0 'eq) #t)
  ;; 7. UNPROVABLE (should fail): x<=0 |- x<=-1
  (la-check "FALSE x<=0 => x<=-1  (must reject)"
    (fm-prove (list (la-hyp 0 '((x . 1)) 0 'le))
              '((x . 1)) 1 'le) #f)
  ;; 8. UNPROVABLE strict from non-strict: x<=y |- x<y
  (la-check "FALSE x<=y => x<y  (must reject)"
    (fm-prove (list (la-hyp 0 '((x . 1) (y . -1)) 0 'le))
              '((x . 1) (y . -1)) 0 'lt) #f)
  ;; 9. constant arithmetic with no vars: 3 + g <= 1 + g + 2  (i.e. 0<=0), trivially
  (la-check "trivial 0<=0"
    (fm-prove '() '() 0 'le) #t)
  ;; 10. contradiction in hyps alone proves anything: x<0, x>0 |- 0<0 via goal y<=y? use false hyps to prove x<=-5
  (la-check "inconsistent hyps prove anything"
    (fm-prove (list (la-hyp 0 '((x . 1)) 0 'lt)       ; x<0
                    (la-hyp 1 '((x . -1)) 0 'lt))      ; -x<0 i.e. x>0
              '((x . 1)) 5 'le) #t)                 ; x<=-5, arbitrary
  (display "=== LA SUMMARY: ") (display la-pass) (display " passed, ")
  (display la-fail) (display " failed ===") (newline)
  la-fail)
