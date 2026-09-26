;;; series-abs-triangle.scm -- |Sum_{n<k} f(n)| <= Sum_{n<k} |f(n)|, PROVEN, and
;;; `abs(0) = 0', which the tree did not state.
;;;
;;; THE TRIANGLE INEQUALITY FOR A FINITE REAL SUM.  analysis-inequalities.scm
;;; describes it in a warrant ("the triangle inequality for finite sums") and
;;; nothing in the library proved it: `rr-abs-triangle' is the two-term case and
;;; `series-block-le' compares two NONNEGATIVE series, which is a different
;;; statement.  It is the rung under `ps-absolute-implies-convergent' -- an
;;; asserted support -- and so under the ratio test.
;;;
;;; A STRAIGHT TRANSPLANT of theorem-library/cc-series.scm's
;;; `cc-series-partial-sum-magnitude-le' (2026-09-02), six names swapped:
;;; magnitude -> abs, cc-magnitude-triangle -> rr-abs-triangle,
;;; cc-magnitude-closed -> rr-abs-closed, cc-add-closed -> rr-add-closed,
;;; cc-series-partial-sum-* -> series-partial-sum-*, cc-magnitude-zero ->
;;; rr-abs-zero-value.  It went through on the first run, which is the argument
;;; for having done the complex case in transfer form: the shape moved.
;;;
;;; STATED IN TRANSFER FORM -- `g' is any sequence agreeing pointwise with the
;;; absolute values, not the literal lambda j |-> |f(j)|.  A conclusion about a
;;; literal VNB-LAMBDA can only be applied to that lambda, and every use then
;;; owes a beta-reduction under a binder.
;;;
;;; `rr-abs-zero-value' is `abs(0) = 0'.  `rr-abs-zero' is the IFF
;;; (|a| = 0 iff a = 0) and does not give the value without an instance; the
;;; value is one citation of `rr-abs-of-nonneg' at 0.
;;;
;;; WHAT IT DOES NOT YET REACH.  `ps-absolute-implies-convergent' needs the
;;; BLOCK form -- |S(f,k) - S(f,m)| <= S(g,k) - S(g,m) for m <= k -- which is an
;;; induction on the GAP rather than on k, and so carries the m + d arithmetic
;;; this file has none of.  That is the next rung.
;;;
;;; Loads after comparison-test-proof (series-partial-sum-zero/-succ/-in-rr) and
;;; rr-abs-basics (rr-abs-triangle, rr-abs-closed, rr-abs-of-nonneg).

;;; |S(f,k)| <= S(|f|,k)  -- the RR twin of cc-series-partial-sum-magnitude-le.
(define (sat-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "sat-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (sat-ineq . fs) (apply ineq (map sat-idx fs)))
(define (sat-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "sat-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

;;; abs(0) = 0 first: the base case needs it.
(sp (make-wff '(= (abs 0) 0)))
(fact 'rr-zero-in)
(have! '(<= 0 0) (lambda () (arith)))
(fact 'rr-abs-of-nonneg 0)
(ass)
(qed 'rr-abs-zero-value)

(sp (make-wff
     '(FORALL k (IMPLIES (IN k NN)
        (FORALL f (IMPLIES (IN f (FUN NN RR))
          (FORALL g (IMPLIES (IN g (FUN NN RR))
            (IMPLIES (FORALL j (IMPLIES (IN j NN) (= (g j) (abs (f j)))))
              (<= (abs (SERIES-PARTIAL-SUM f k))
                  (SERIES-PARTIAL-SUM g k)))))))))))
(define sat-br (use-induction))

;;; BASE
(dk-focus! (cdr (assq 'base sat-br)))
(sat-peel-to! '<=)
(mac 'series-partial-sum-zero)
(mac 'rr-abs-zero-value)
(arith)

;;; STEP
(dk-focus! (cdr (assq 'step sat-br)))
(define sat-ih (cdr (assq 'ih sat-br)))
(sat-peel-to! '<=)
(define sat-S  '(SERIES-PARTIAL-SUM f k))
(define sat-fk '(f k))
(define sat-ag
  (let loop ((l (dk-asms)))
    (cond ((null? l) (error "no agreement hypothesis"))
          ((and (pair? (car l)) (eq? (caar l) 'FORALL) (dk-contains? (car l) 'abs)) (car l))
          (else (loop (cdr l))))))
(fact 'series-partial-sum-in-rr 'k 'f)
(fact 'fun-apply-type-c 'f 'NN 'RR 'k)
(fact 'series-partial-sum-in-rr 'k 'g)
(fact 'fun-apply-type-c 'g 'NN 'RR 'k)
(mac 'series-partial-sum-succ)
(have! (list 'AND (list 'IN sat-S 'RR) (list 'IN sat-fk 'RR)))
(fact 'rr-abs-triangle sat-S sat-fk)
(fact 'rr-add-closed sat-S sat-fk)
(dk-deepest (lambda () (inst+ (dk-deepest (lambda () (inst+ sat-ih 'f))) 'g)))
(inst+ sat-ag 'k)
(fact 'rr-abs-closed sat-S)
(fact 'rr-abs-closed sat-fk)
(fact 'rr-abs-closed (list '+ sat-S sat-fk))
(sat-ineq (list '<= (list 'abs (list '+ sat-S sat-fk))
                (list '+ (list 'abs sat-S) (list 'abs sat-fk)))
          (list '<= (list 'abs sat-S) '(SERIES-PARTIAL-SUM g k))
          (list '= (list 'g 'k) (list 'abs sat-fk)))
(qed 'series-abs-triangle)

(topic! 'rr-abs-zero-value 'inequalities)
(alias! 'rr-abs-zero-value "the absolute value of 0 is 0")
(topic! 'series-abs-triangle 'analysis)
(alias! 'series-abs-triangle
        "the absolute value of a partial sum is at most the partial sum of the absolute values")
