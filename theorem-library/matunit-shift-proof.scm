;;; matunit-shift-proof.scm -- Lemma 3.3 (algebraic-numbers.pdf ch.3): the
;;; column-shift formula for right-multiplication by a matrix unit.
;;;
;;;   IS-RING A, P : MAT(m,n), k,l in [1,n], i in [1,m], c in [1,n]
;;;      |-  (P . E[k,l])_{ic} = P_{ik}  if c = l,  else 0
;;;
;;; The engine behind every elementary column operation (Prop 3.5).  Route
;;; (the same finsum-collapse shape as the IDENTMAT identities):
;;;   * matmul-entry expands (P.E[k,l])_{ic} to FINSUM_{j in [1,n]}
;;;     P_{ij} . E[k,l]_{jc};
;;;   * VANISH: off j=k the summand is P_{ij}.0 = 0 (matunit-entry-off-row +
;;;     ring-mul-zero-right + ras-id), so finsum-single-support at j0=k collapses
;;;     the sum to the single term P_{ik} . E[k,l]_{kc};
;;;   * matunit-entry-k-row rewrites E[k,l]_{kc} = (1 if c=l else 0), and an
;;;     excluded-middle case-split on (c=l) closes both branches by
;;;     ring-mul-right-id / ring-mul-zero-right.
;;;
;;; Was an asserted support (warrant 'proof) in elementary-matrix.scm; now genuine.

;; --- local proof helpers ---
(define (mu-last)  (car (reverse (dg-sequent-nodes (proof-state-dg *ps*)))))
(define (mu-focus! n) (set-proof-state-focus! *ps* n))
(define (mu-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mu-di*)
  (let lp () (let* ((g (mu-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

;; excluded-middle case split on a proposition P (inline pbc proof of
;; (OR P (NOT P)), then or-elim); returns the (NOT P) branch node.
(define (mu-em P)
  (cut `(OR ,P (NOT ,P)))
  (let ((use-or (mu-last)))
    (pbc)
    (cut `(NOT ,P))
    (let ((use-notp (mu-last)))
      (di)
      (cut `(OR ,P (NOT ,P)))
      (let ((use-or2 (mu-last))) (oi-l) (ass) (mu-focus! use-or2))
      (ai `(NOT (OR ,P (NOT ,P))))
      (mu-focus! use-notp))
    (cut `(OR ,P (NOT ,P)))
    (let ((use-or3 (mu-last))) (oi-r) (ass) (mu-focus! use-or3))
    (ai `(NOT (OR ,P (NOT ,P))))
    (mu-focus! use-or)))
(define (mu-cases P) (mu-em P) (ai `(OR ,P (NOT ,P))) (mu-last))

;; term abbreviations
(define MU-RAG '(RING-ADDITIVE-AG A))
(define MU-FF  '(VNB-LAMBDA j (INTERVAL 1 n) ((MUL A) (ENTRY P i j) (ENTRY (MATUNIT A n k l) j c))))
(define MU-INT '(INTERVAL 1 n))

(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A)
     (FORALL m (FORALL n (FORALL P (FORALL k (FORALL l
       (IMPLIES (IN P (MAT m n (CARR A)))
       (IMPLIES (IN k (INTERVAL 1 n))
       (IMPLIES (IN l (INTERVAL 1 n))
       (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
       (FORALL c (IMPLIES (IN c (INTERVAL 1 n))
         (= (ENTRY (MATMUL A P (MATUNIT A n k l)) i c)
            (IF (= c l) (ENTRY P i k) (ZERO A)))))))))))))))))))
(mu-di*)

;; expand the product entry to a FINSUM
(fact 'matunit-type 'A 'n 'k 'l)     ; (IN (MATUNIT A n k l) (MAT n n (CARR A)))
(fact 'matmul-entry 'A 'm 'n 'n 'P '(MATUNIT A n k l) 'i 'c)
(subst `(= (ENTRY (MATMUL A P (MATUNIT A n k l)) i c)
           (FINSUM ,MU-RAG ,MU-FF ,MU-INT)))

;; the four non-VANISH antecedents of finsum-single-support
(fact 'ring-additive-ag-is-abelian-group 'A)
(fact 'interval-in-set 1 'n)
;; interval-card-in-nn's guard: n is the row count of the n-by-n unit matrix
;; just typed (the statement types no dimension).
(fact 'mat-rows-in-nn 'n 'n '(CARR A) '(MATUNIT A n k l))
(fact 'interval-card-in-nn 1 'n)
(fact 'matunit-summand-type 'A 'm 'n 'P 'k 'l 'i 'c)

;; VANISH: off the k-row the summand is the additive identity
(cut `(FORALL jz (IMPLIES (IN jz ,MU-INT)
        (IMPLIES (NOT (= jz k))
          (= (,MU-FF jz) (IDEN ,MU-RAG))))))
(define mu-main (mu-last))
  (di) (di) (di)
  (lam-b)
  (fact 'matunit-entry-off-row 'A 'n 'k 'l 'jz 'c)
  (subst `(= (ENTRY (MATUNIT A n k l) jz c) (ZERO A)))
  (fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'i 'jz)
  (fact 'ring-mul-zero-right 'A '(ENTRY P i jz))
  (subst `(= ((MUL A) (ENTRY P i jz) (ZERO A)) (ZERO A)))
  (fact 'ras-id 'A)
  (subst `(= (IDEN (RING-ADDITIVE-AG A)) (ZERO A)))
  (rfl)
(mu-focus! mu-main)

;; collapse the sum to its single surviving term, then beta-reduce
(fact 'finsum-single-support MU-RAG MU-INT MU-FF 'k)
(subst `(= (FINSUM ,MU-RAG ,MU-FF ,MU-INT) (,MU-FF k)))
(lam-b)

;; resolve the matrix-unit entry on the k-row
(fact 'matunit-entry-k-row 'A 'n 'k 'l 'c)
(subst `(= (ENTRY (MATUNIT A n k l) k c) (IF (= c l) (ONE A) (ZERO A))))
(fact 'entry-in-carrier 'm 'n '(CARR A) 'P 'i 'k)

;; case split on (c = l): both IF terms resolve together in each branch
(define mu-notcl (mu-cases '(= c l)))
;; ---- (= c l) branch ----
(if-true '(IF (= c l) (ONE A) (ZERO A)))
(define mu-pl (mu-last)) (ass) (mu-focus! mu-pl)
(subst '(= (IF (= c l) (ONE A) (ZERO A)) (ONE A)))
(if-true '(IF (= c l) (ENTRY P i k) (ZERO A)))
(define mu-pr (mu-last)) (ass) (mu-focus! mu-pr)
(subst '(= (IF (= c l) (ENTRY P i k) (ZERO A)) (ENTRY P i k)))
(fact 'ring-mul-right-id 'A '(ENTRY P i k))
(subst '(= ((MUL A) (ENTRY P i k) (ONE A)) (ENTRY P i k)))
(rfl)
;; ---- (NOT (= c l)) branch ----
(mu-focus! mu-notcl)
(if-false '(IF (= c l) (ONE A) (ZERO A)))
(define mu-nl (mu-last)) (ass) (mu-focus! mu-nl)
(subst '(= (IF (= c l) (ONE A) (ZERO A)) (ZERO A)))
(if-false '(IF (= c l) (ENTRY P i k) (ZERO A)))
(define mu-nr (mu-last)) (ass) (mu-focus! mu-nr)
(subst '(= (IF (= c l) (ENTRY P i k) (ZERO A)) (ZERO A)))
(fact 'ring-mul-zero-right 'A '(ENTRY P i k))
(subst '(= ((MUL A) (ENTRY P i k) (ZERO A)) (ZERO A)))
(rfl)

(qed 'matunit-col-shift)
(topic! 'matunit-col-shift 'algebra)
