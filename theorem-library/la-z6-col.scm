;;; la-z6-col.scm -- linear algebra Lemma 3.8 over a field, in column equivalence (LA-Z6, 2026-10-25).
;;;
;;; THE SOURCE.  The user's linear-algebra notes, Lemma 3.8: "Suppose R is a field.  Any m x n matrix A is
;;; column equivalent to a matrix B such that all entries b_1j = 0 for 2 <= j <= n and b_11 is either 0 or 1."
;;; Proposition 3.10 (the column-step proposition) is ALREADY in the tree as column-step-exists
;;; (theorem-library/la-elem-gen, LA-DET2): over IS-FIELD-RING, every m-by-n matrix is COL-EQUIV to an
;;; IS-COLUMN-STEP matrix (b_ij = 0 for i < j, b_ii in {0, 1}), which is the notes' statement word for word.
;;; The tree proves it by running down the rows (the notes' lemma at each row), so 3.8 is the case "row 1" of
;;; that proposition: it is derived here from column-step-exists in a few lines.
;;;
;;; THE STATEMENT.  col-reduce-first-row: R a field ring, m, n in NN, 1 <= m, 1 <= n, A in MAT(m, n, CARR R)
;;; => exists B, COL-EQUIV(R, n, A, B), ENTRY(B, 1, j) = ZERO(R) for j in INTERVAL(2, n), and ENTRY(B, 1, 1) is
;;; ZERO(R) or ONE(R).  The guards 1 <= m, 1 <= n are what makes b_11 an entry.
;;;
;;; LOAD WINDOW: after "theorem-library/la-elem-gen" (load.scm:2178, primary tree of 2026-10-25; column-step-exists) and the interval laws
;;; (interval-lo, interval-hi, interval-elt-in-nn, interval-mem-intro: core, early).  Nothing cites it.
;;; Library: linear-algebra.  No axiom, support or stamp.  Helper prefix: lz6c-.  Binders: clj_ (the column),
;;; crb_ (the witness).

(define (lz6c-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-z6-col: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

(define (lz6c-above c)
  (list 'FORALL 'csi_ (list 'IMPLIES '(IN csi_ (INTERVAL 1 m))
    (list 'FORALL 'csj_ (list 'IMPLIES '(IN csj_ (INTERVAL 1 n))
      (list 'IMPLIES '(< csi_ csj_) (list '= (list 'ENTRY c 'csi_ 'csj_) '(ZERO R))))))))
(define (lz6c-diag c)
  (list 'FORALL 'csi_ (list 'IMPLIES '(IN csi_ (INTERVAL 1 m))
    (list 'IMPLIES '(IN csi_ (INTERVAL 1 n))
      (list 'OR (list '= (list 'ENTRY c 'csi_ 'csi_) '(ZERO R))
                (list '= (list 'ENTRY c 'csi_ 'csi_) '(ONE R)))))))
(define (lz6c-part! f c)
  (dk-project! f (lambda () (mac-h 'IS-COLUMN-STEP (list 'IS-COLUMN-STEP 'R 'm 'n c)))))

(sp (make-wff (forall-guarded '(R m n A)
  (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) '(<= 1 m) '(<= 1 n) '(IN A (MAT m n (CARR R))))
  '(FORSOME crb_ (AND (COL-EQUIV R n A crb_)
                 (AND (FORALL clj_ (IMPLIES (IN clj_ (INTERVAL 2 n)) (= (ENTRY crb_ 1 clj_) (ZERO R))))
                      (OR (= (ENTRY crb_ 1 1) (ZERO R)) (= (ENTRY crb_ 1 1) (ONE R)))))))))
(dk-peel!)
(let* ((c (dk-skolem! (dk-cite! 'column-step-exists 'R 'm 'n 'A))))
  (dk-have! '(IN 1 NN) (lambda () (arith)))
  (dk-have! '(IN 1 (INTERVAL 1 m)) (lambda () (fact 'interval-mem-intro 1 'm 1) (ass)))
  (dk-have! '(IN 1 (INTERVAL 1 n)) (lambda () (fact 'interval-mem-intro 1 'n 1) (ass)))
  (ew c)
  (dk-conj-close!
    (lambda ()
      (let ((g (dk-goal)))
        (cond
          ((eq? (car g) 'COL-EQUIV) (ass))
          ((eq? (car g) 'FORALL)
           (let ((j (dk-di-var!)))
             (fact 'interval-elt-in-nn 2 'n j)
             (fact 'interval-lo 2 'n j)
             (fact 'interval-hi 2 'n j)
             (dk-have! (list '<= 1 j) (lambda () (dk-nn! (list '<= 2 j))))
             (dk-have! (list '< 1 j) (lambda () (dk-nn! (list '<= 2 j))))
             (dk-have! (list 'IN j '(INTERVAL 1 n)) (lambda () (fact 'interval-mem-intro 1 'n j) (ass)))
             (dk-apply! (lz6c-part! (lz6c-above c) c) 1 j)
             (ass)))
          (#t
           (dk-apply! (lz6c-part! (lz6c-diag c) c) 1)
           (ass)))))))
(lz6c-done! 'col-reduce-first-row)
(topic! 'col-reduce-first-row 'algebra)
(gloss! 'col-reduce-first-row
  "Over a field, every m-by-n matrix (m, n >= 1) is column equivalent to a matrix whose first row is zero
   except possibly for the entry b_11, which is 0 or 1 (linear algebra, Lemma 3.8).")
