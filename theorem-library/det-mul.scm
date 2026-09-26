;;; det-mul.scm -- det(E A) = det(E) det(A) for an ELEMENTARY matrix E (batch 25-C,
;;; 2026-09-24).  The multiplicativity of the determinant as far as the tree
;;; carries it; see the report (scratchpad/triage/BATCH25-REPORTS.md, 25-C) for
;;; what stands between this and linear-algebra 3.20 / 3.27.
;;;
;;; WHAT IS HERE (all over a commutative ring R, E of size n):
;;;   det-elem-h        det H[sc,k]   = sc
;;;   det-elem-g        det G[sc,k,l] = 1          (k /= l)
;;;   det-elem-f        det F[k,l]    = -1         (k /= l)
;;;   det-mul-elem-h / -g / -f        det(E A) = det E det A
;;; Each value is det(E I) = (the row operation's factor) det I, with
;;; E I = E (identmat-right-identity) and det I = 1 (det-identity-ind); the
;;; products then combine that value with det-elem-{h,g,f}-row of det-rows.scm.
;;;
;;; Helper prefix: dtm-.

(define (dtm-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** det-mul: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

;; det E = (factor) for E typed n-square: rewrite E as E I, apply the row law
;; ROW at A := I (ROW-ARGS are its arguments after R n A), then det I = 1.
(define (dtm-value! E row row-args)
  (fact 'commutative-ring-is-ring 'R)
  (fact 'identmat-type 'R 'n)
  (fact 'ring-one-in 'R)
  (let ((ei (dk-fact! 'identmat-right-identity 'R 'n 'n E)))
    (subst (list '= E (list 'MATMUL 'R E '(IDENTMAT R n))))
    (subst (apply dk-fact! row 'R 'n '(IDENTMAT R n) row-args))
    (fact 'det-identity-ind 'R 'n)
    (subst '(= (DET R n (IDENTMAT R n)) (ONE R)))))

(sp (make-wff
  (forall-guarded '(R n sc k)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN sc (CARR R)) (IN k (INTERVAL 1 n)))
    '(= (DET R n (ELEM-H R n sc k)) sc))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'elem-h-type 'R 'n 'sc 'k)
(dtm-value! '(ELEM-H R n sc k) 'det-elem-h-row '(sc k))
(fact 'ring-mul-right-id 'R 'sc)
(subst '(= ((MUL R) sc (ONE R)) sc))
(rfl)
(dtm-done! 'det-elem-h)
(topic! 'det-elem-h 'algebra)

(sp (make-wff
  (forall-guarded '(R n sc k l)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN sc (CARR R)) (IN k (INTERVAL 1 n))
      (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(= (DET R n (ELEM-G R n sc k l)) (ONE R)))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'elem-g-type 'R 'n 'sc 'k 'l)
(dtm-value! '(ELEM-G R n sc k l) 'det-elem-g-row '(sc k l))
(rfl)
(dtm-done! 'det-elem-g)
(topic! 'det-elem-g 'algebra)

(sp (make-wff
  (forall-guarded '(R n k l)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN k (INTERVAL 1 n))
      (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(= (DET R n (ELEM-F R n k l)) ((NEG R) (ONE R))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(fact 'elem-f-type 'R 'n 'k 'l)
(dtm-value! '(ELEM-F R n k l) 'det-elem-f-row '(k l))
(fact 'ring-neg-in-carr 'R '(ONE R))
(rfl)
(dtm-done! 'det-elem-f)
(topic! 'det-elem-f 'algebra)

;;; det(E A) = det E det A
(sp (make-wff
  (forall-guarded '(R n A sc k)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN A (MAT n n (CARR R))) (IN sc (CARR R))
      (IN k (INTERVAL 1 n)))
    '(= (DET R n (MATMUL R (ELEM-H R n sc k) A))
        ((MUL R) (DET R n (ELEM-H R n sc k)) (DET R n A))))))
(dk-peel!)
(subst (dk-fact! 'det-elem-h 'R 'n 'sc 'k))
(fact 'det-elem-h-row 'R 'n 'A 'sc 'k)
(ass)
(dtm-done! 'det-mul-elem-h)
(topic! 'det-mul-elem-h 'algebra)

(sp (make-wff
  (forall-guarded '(R n A sc k l)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN A (MAT n n (CARR R))) (IN sc (CARR R))
      (IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(= (DET R n (MATMUL R (ELEM-G R n sc k l) A))
        ((MUL R) (DET R n (ELEM-G R n sc k l)) (DET R n A))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(subst (dk-fact! 'det-elem-g 'R 'n 'sc 'k 'l))
(fact 'det-in-carrier 'R 'n 'A)
(fact 'ring-mul-left-id 'R '(DET R n A))
(subst '(= ((MUL R) (ONE R) (DET R n A)) (DET R n A)))
(fact 'det-elem-g-row 'R 'n 'A 'sc 'k 'l)
(ass)
(dtm-done! 'det-mul-elem-g)
(topic! 'det-mul-elem-g 'algebra)

(sp (make-wff
  (forall-guarded '(R n A k l)
    '((IS-COMMUTATIVE-RING R) (IN n NN) (IN A (MAT n n (CARR R)))
      (IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(= (DET R n (MATMUL R (ELEM-F R n k l) A))
        ((MUL R) (DET R n (ELEM-F R n k l)) (DET R n A))))))
(dk-peel!)
(fact 'commutative-ring-is-ring 'R)
(subst (dk-fact! 'det-elem-f 'R 'n 'k 'l))
(fact 'det-in-carrier 'R 'n 'A)
(fact 'ring-one-in 'R)
(fact 'ring-neg-mul-left 'R '(ONE R) '(DET R n A))
(subst '(= ((MUL R) ((NEG R) (ONE R)) (DET R n A)) ((NEG R) ((MUL R) (ONE R) (DET R n A)))))
(fact 'ring-mul-left-id 'R '(DET R n A))
(subst '(= ((MUL R) (ONE R) (DET R n A)) (DET R n A)))
(fact 'det-elem-f-row 'R 'n 'A 'k 'l)
(ass)
(dtm-done! 'det-mul-elem-f)
(topic! 'det-mul-elem-f 'algebra)
