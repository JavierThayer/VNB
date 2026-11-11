;;; ccr-adj-unit.scm -- wave of 2026-11-09/10 (agent CCR-1109-B4), wired 2026-11-10 from scratchpad/ccr1109b4/ccr-adj-unit.scm.
;;; Library: linear-algebra.

;;; ccr-adj-unit.scm -- a square matrix over a COMMUTATIVE ring is invertible iff its determinant is a
;;; unit (Cramer's rule, general form).  Agent CCR-1109-B4, wave 2026-11-09.
;;; Destination: theorem-library/ccr-adj-unit.scm.  Library: linear-algebra.  Helper prefix cu1-.
;;;
;;; The adjugate itself and Cramer's rule are ALREADY in the tree: structure-library/la-det-vocab.scm
;;; defines ADJ(R, n, A) (the transposed cofactor matrix of an (n+1)-square A), and
;;; theorem-library/la-det-adjoint.scm (LA-DET, 2026-10-18) proves adj-mul / mul-adj
;;; (adj(A) A = det(A) I = A adj(A)), cramer-inverse (det(A) b = 1 => b adj(A) is a two-sided inverse)
;;; and invertible-iff-det-nonzero (over a field).  determinant.scm's comment "DEFERRED seeds:
;;; det-cramer / adjugate, det-nonzero-iff-invertible" is stale.  What is added here:
;;;
;;;   det-unit-iff-invertible   R commutative, A n-by-n:  A invertible  iff  det A b = 1 for some b in R.
;;;
;;; Route: => det(A) det(V) = det(A V) = det(I) = 1 (det-multiplicative, det-identity-ind);
;;;        <= n = 0: A = I_0 (matrix-entry-extensionality, the index range is empty), invertible;
;;;           n = succ m: cramer-inverse at b, then inverse-is-invertible.
;;;
;;; LOAD WINDOW: after theorem-library/la-det-adjoint (cramer-inverse, adj-type, matscale-type), which is
;;; the latest citation; det-multiplicative, det-identity-ind, identmat-invertible, inverse-is-invertible,
;;; matrix-entry-extensionality load earlier.  Nothing cites it outside this wave.

(define (cu1-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display ";; cu1: OPEN LEAVES before qed ") (display name) (newline)
        (for-each (lambda (l)
                    (display ";;   GOAL ") (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

(define (cu1-absurd! prems)
  (dk-have! '(<= 1 0) (lambda () (apply dk-nn! prems)))
  (dk-focus-having! '(<= 1 0))
  (have! '(NOT (<= 1 0)) (lambda () (arith)))
  (dk-focus-having! '(NOT (<= 1 0)))
  (pbc)
  (ai '(NOT (<= 1 0))))

(sp (make-wff
  (forall-guarded '(R n A) '((IS-COMMUTATIVE-RING R) (IN n NN) (IN A (MAT n n (CARR R))))
    '(IFF (IS-INVERTIBLE-MAT R n A)
          (FORSOME cub_ (AND (IN cub_ (CARR R)) (= ((MUL R) (DET R n A) cub_) (ONE R))))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'det-in-carrier 'R 'n 'A)
(dk-iff! (dk-head? 'FORSOME)
  ;; invertible => det A det V = 1
  (lambda ()
    (let* ((u (dk-landed-1 (lambda () (mac-h 'IS-INVERTIBLE-MAT '(IS-INVERTIBLE-MAT R n A)))))
           (V (dk-skolem! u)))
      (dk-split-all!)
      (let* ((dV (list 'DET 'R 'n V))
             (e1 (dk-fact! 'det-multiplicative 'R 'n 'A V)))
        (fact 'det-identity-ind 'R 'n)
        (fact 'det-in-carrier 'R 'n V)
        (let* ((e2 (dk-rewrite-h! e1 (list 'MATMUL 'R 'A V) '(IDENTMAT R n)))
               (e3 (dk-rewrite-h! e2 '(DET R n (IDENTMAT R n)) '(ONE R))))
          (ew dV)
          (dk-conj-close! (lambda ()
            (if (dk-asm? (dk-goal)) (dk-ass!) (begin (subst e3) (rfl)))))))))
  ;; det A b = 1 => invertible
  (lambda ()
    (let* ((ex (dk-pick (dk-head? 'FORSOME) "the unit hypothesis"))
           (b (dk-skolem! ex #t)))
      (use-em '(= n 0)
        (lambda ()
          (dk-rewrite-h! '(IN A (MAT n n (CARR R))) 'n 0)
          (subst '(= n 0))
          (fact 'nn-zero-in)
          (fact 'identmat-type 'R 0)
          (dk-have! '(= A (IDENTMAT R 0))
            (lambda ()
              (detach-with! (dk-fact! 'matrix-entry-extensionality 0 0 '(CARR R) 'A '(IDENTMAT R 0))
                (lambda ()
                  (dk-peel!)
                  (let* ((g (dk-goal)) (ei (caddr (cadr g))))
                    (fact 'interval-elt-in-nn 1 0 ei)
                    (fact 'interval-lo 1 0 ei)
                    (fact 'interval-hi 1 0 ei)
                    (cu1-absurd! (list (list '<= 1 ei) (list '<= ei 0))))))
              (ass)))
          (fact 'identmat-invertible 'R 0)
          (subst '(= A (IDENTMAT R 0)))
          (ass))
        (lambda ()
          (let* ((m (dk-skolem! (dk-fact! 'nn-nonzero-is-succ 'n)))
                 (sm (list 'succ m)))
            (dk-rewrite-h! '(IN A (MAT n n (CARR R))) 'n sm)
            (dk-rewrite-h! (list '= (list '(MUL R) '(DET R n A) b) '(ONE R)) 'n sm)
            (subst (list '= 'n sm))
            (fact 'nn-succ-closed m)
            (let ((both (dk-fact! 'cramer-inverse 'R m 'A b)))
              (dk-split! both)
              (fact 'adj-type 'R m 'A)
              (fact 'matscale-type 'R sm sm b (list 'ADJ 'R m 'A))
              (fact 'inverse-is-invertible 'R sm (list 'MATSCALE 'R b (list 'ADJ 'R m 'A)) 'A)
              (ass))))))))
(cu1-done! 'det-unit-iff-invertible)
(topic! 'det-unit-iff-invertible 'algebra)
(gloss! 'det-unit-iff-invertible
  "Over a commutative ring, a square matrix is invertible iff its determinant is a unit (Cramer's rule).")
