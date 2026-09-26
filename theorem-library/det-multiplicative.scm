;;; det-multiplicative.scm -- det(P Q) = det(P) det(Q) over a commutative ring
;;; (Hoffman-Kunze 5.3 Theorem 3; the notes' proposition "det is multiplicative"),
;;; and the notes' corollary 3.20 (R a field, V invertible: det(A V) = det A det V).
;;; Batch 26-B, 2026-09-24.
;;;
;;; HK's proof, verbatim: for fixed Q, D(P) = det(P Q) is alternating n-linear in the
;;; rows of P (daf-det-rm-fun/-lin/-alt, theorem-library/det-alternating-form.scm), so
;;; by HK 5.3 Theorem 2 (det-alternating-form) D(P) = det(P) D(I), and
;;; D(I) = det(I Q) = det(Q).
;;;
;;; det-multiplicative is stated EXACTLY as the support of
;;; structure-library/determinant.scm (retire it there).  Helper prefix: dml-.

(define (dml-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** det-multiplicative: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

(sp (make-wff
  (forall-guarded '(R n P Q)
    (list '(IS-COMMUTATIVE-RING R) '(IN n NN)
          '(IN P (MAT n n (CARR R))) '(IN Q (MAT n n (CARR R))))
    '(= (DET R n (MATMUL R P Q)) ((MUL R) (DET R n P) (DET R n Q))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'identmat-type 'R 'n)
(define dml-D '(VNB-LAMBDA dql_ (MAT n n (CARR R)) (DET R n (MATMUL R dql_ Q))))
(define dml-I '(IDENTMAT R n))
(fact 'daf-det-rm-fun 'R 'n 'Q)
(fact 'daf-det-rm-lin 'R 'n 'Q)
(fact 'daf-det-rm-alt 'R 'n 'Q)
(dk-lam-b-h! (dk-fact! 'det-alternating-form 'R 'n dml-D 'P))
(define dml-res
  (list '= '(DET R n (MATMUL R P Q)) (list '(MUL R) '(DET R n P) (list 'DET 'R 'n (list 'MATMUL 'R dml-I 'Q)))))
(if (not (dk-asm? dml-res)) (error "det-multiplicative: the beta-reduced instance did not land"))
(fact 'identmat-left-identity 'R 'n 'n 'Q)
(fact 'det-in-carrier 'R 'n 'P)
(fact 'det-in-carrier 'R 'n 'Q)
(fact 'ring-carrier-closed-mul 'R '(DET R n P) '(DET R n Q))
(subst dml-res)
(subst (list '= (list 'MATMUL 'R dml-I 'Q) 'Q))
(rfl)
(dml-done! 'det-multiplicative)
(topic! 'det-multiplicative 'algebra)

;;; the notes' 3.20: R a field, V invertible  =>  det(A V) = det A det V
(sp (make-wff
  (forall-guarded '(R n A V)
    (list '(IS-FIELD-RING R) '(IN n NN) '(IN A (MAT n n (CARR R))) '(IS-INVERTIBLE-MAT R n V))
    '(= (DET R n (MATMUL R A V)) ((MUL R) (DET R n A) (DET R n V))))))
(dk-peel!)
(dk-project! '(IS-COMMUTATIVE-RING R) 'is-field-ring-def '(IS-FIELD-RING R))
(fact 'invertible-mat-is-mat 'R 'n 'V)
(fact 'det-multiplicative 'R 'n 'A 'V)
(ass)
(dml-done! 'det-mul-invertible)
(topic! 'det-mul-invertible 'algebra)
