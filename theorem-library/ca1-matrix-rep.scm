;;; ca1-matrix-rep.scm -- THE COMPLEX NUMBERS AS 2-BY-2 REAL MATRICES
;;; (complex-analysis.pdf, Proposition 1.3).  Agent CA-1, 2026-10-19.
;;;
;;; PROPOSITION 1.3 (the notes).  The mapping Phi : a + b i |-> [[a, b], [-b, a]] is an
;;; algebraic isomorphism from C onto the set of 2 x 2 real matrices of that form.
;;;
;;; THE STATEMENT PROVEN (cc-matrix-representation).  With R the ring of reals as the tree
;;; has it, NORMED-FIELD-AS-COMMUTATIVE-RING(RR-NORMED-FIELD), and the vocabulary of
;;; structure-library/ca1-vocab.scm (CC-MATRIX-OF, CC-MATRICES, CC-MATRIX-REP = Phi):
;;;     Phi in BIJECTION(CC, CC-MATRICES),
;;;     Phi(z + w) = MATADD(R, Phi z, Phi w),   Phi(z w) = MATMUL(R, Phi z, Phi w),
;;;     Phi(1) = IDENTMAT(R, 2),                Phi(c z) = MATSCALE(R, c, Phi z) (c real).
;;; "Algebraic isomorphism" is read as: a bijection onto the set that preserves sum,
;;; product and unit (a ring isomorphism) and real multiples (an R-algebra isomorphism).
;;; The set CC-MATRICES is not given a RING structure of its own (it is a subring of
;;; MAT-RING(R, 2)); see the report for what an IS-HOM-RING form would take.
;;;
;;; THE NOTES' PROOF is the product computation [[a,b],[-b,a]] [[c,d],[-d,c]] =
;;; [[ac - bd, ad + bc], [-(ad + bc), ac - bd]] (cc-matrix-of-mul here), the sum being
;;; "even simpler and omitted" (cc-matrix-of-add).  The notes take bijectivity onto the
;;; set for granted: here cc-matrix-of-injective (the matrix determines a and b) and
;;; cc-re-im-of (a + b i has real part a and imaginary part b).
;;;
;;; CONTENTS.
;;;  mat22-literal-in-mat     [[a, b], [c, d]] in MAT(2, 2, X) for a, b, c, d in X
;;;  mat22-ext                two 2-by-2 matrices with the same four entries are equal
;;;  cc-matrix-of-entries     the four entries of [[a, b], [-b, a]]
;;;  cc-matrix-of-in-mat      [[a, b], [-b, a]] in MAT(2, 2, RR)
;;;  rr-matmul-2x2-type, rr-matadd-2x2-type      closure of MAT(2, 2, RR) under R's MATMUL / MATADD
;;;  rr-matmul-2x2-entry      (P Q)_{ik} = P_{i1} Q_{1k} + P_{i2} Q_{2k} over R
;;;  rr-matadd-2x2-entry      (P + Q)_{ik} = P_{ik} + Q_{ik} over R
;;;  cc-matrix-of-mul, cc-matrix-of-add, cc-matrix-of-scale    the notes' computation
;;;  cc-matrix-of-injective   [[a, b], [-b, a]] = [[c, d], [-d, c]] implies a = c, b = d
;;;  cc-matrix-rep-apply      Phi(z) == [[re z, im z], [-im z, re z]]
;;;  cc-matrix-rep-add / -mul / -real-mul / -one   Phi preserves +, *, real multiples, 1
;;;  cc-matrix-rep-in-fun, cc-matrix-rep-bijection
;;;  cc-matrix-representation PROPOSITION 1.3
;;;
;;; THE ROUTE.  A matrix in the tree is the literal list of its rows, so [[a, b], [-b, a]]
;;; is a LIST of two LISTs, and its entries are `mac ENTRY' plus `nth-r'.  Membership in
;;; MAT(2, 2, X) goes through mat-intro (tuples by `ti', the row lengths by `len-r' and a
;;; two-case split of the row index, ms-index-2).  Matrix identities go through mat22-ext
;;; (matrix-entry-extensionality with the index box split into its four points); the product
;;; entry is a FINSUM over INTERVAL(1, 2), evaluated by finsum-two-support; R's ADD / MUL
;;; slots are read off by rr-scalar-ring-add / -mul and `lam-b'; the remaining identities
;;; in RR are `crs'.
;;;
;;; NOTHING asserted, no definition here (the vocabulary is structure-library/ca1-vocab.scm).
;;; LOAD WINDOW: lo = theorem-library/cc-coords-laws (load.scm 3472: apply-congruence-1,
;;; cc-re-add / cc-im-add / cc-re-mul / cc-im-mul / cc-re-real-mul / cc-im-real-mul), the
;;; latest citation; the next are elem-entry-readoffs (2001: identmat-entry-diag / -off,
;;; matadd-entry, matscale-entry) and lam-fun-bricks (1707: matprod-summand-type).  It needs
;;; structure-library/ca1-vocab before it.  hi: none (nothing cites this file).
;;; Library: complex-analysis.  Tactics: the early kit only (dk-*, use-cases, crs, arith, prop).
;;; Helper prefix cmr-.

;;; =====================================================================
;;; File-local driver helpers (prefix cmr-).
;;; =====================================================================

(define cmr-rring '(NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD))

;;; Recursive tuple introduction on a literal LIST goal (IN (LIST ...) (TUPLES ...)).
(define (cmr-ti!)
  (for-each (lambda (leaf)
              (if (not (sequent-node-grounded? leaf))
                  (begin (dk-focus! leaf)
                         (let ((g (dk-goal)))
                           (if (and (pair? g) (eq? (car g) 'IN) (pair? (cadr g)) (eq? (car (cadr g)) 'LIST))
                               (cmr-ti!)
                               (from-context!))))))
            (dk-opened (lambda () (ti)))))

;;; v in NN, 1 <= v, v <= 2 in context: land v = 1 or v = 2 (ms-index-2).
(define (cmr-index-cases! v) (fact 'ms-index-2 v))

;;; LENGTH(NTH v M) = 2 for an index v in {1, 2} and M a literal list of two 2-lists.
(define (cmr-len2! v m)
  (cmr-index-cases! v)
  (dk-have! (list '= (list 'LENGTH (list 'NTH v m)) 2)
    (lambda ()
      (use-cases (list (list '= v 1) (list '= v 2))
        (lambda () (subst (list '= v 1)) (nth-r) (len-r) (rfl))
        (lambda () (subst (list '= v 2)) (nth-r) (len-r) (rfl))))))

;;; v in INTERVAL(1, 2) in context: land v in NN, 1 <= v, v <= 2.
(define (cmr-interval-parts! v)
  (fact 'interval-elt-in-nn 1 2 v)
  (fact 'interval-lo 1 2 v)
  (fact 'interval-hi 1 2 v))

;;; k in INTERVAL(1, 2) for the literal k = 1, 2.
(define (cmr-in-12! k)
  (let ((f (list 'IN k '(INTERVAL 1 2))))
    (if (not (dk-asm? f))
        (dk-have! f (lambda ()
                      (dk-have! (list 'IN k 'NN) (lambda () (arith)))
                      (dk-have! (list '<= 1 k) (lambda () (arith)))
                      (dk-have! (list '<= k 2) (lambda () (arith)))
                      (dk-cite! 'interval-mem-intro 1 2 k)
                      (from-context!))))
    f))

;;; nth-r until no NTH of a literal list is left in the goal.
(define (cmr-has-lit-nth? t)
  (and (pair? t)
       (or (and (eq? (car t) 'NTH) (pair? (cdr t)) (pair? (cddr t)) (pair? (caddr t)) (eq? (car (caddr t)) 'LIST))
           (any-pred cmr-has-lit-nth? t))))
(define (cmr-nth-r*!)
  (let loop ((fuel 6))
    (if (and (> fuel 0) (cmr-has-lit-nth? (dk-goal)))
        (begin (nth-r) (loop (- fuel 1))))))

;;; Close (= (ENTRY <literal> i j) t) by unfolding ENTRY and reducing the NTHs; the
;;; reduced goal may land on a node an earlier conjunct already grounded (hash-consing),
;;; and then the focus has moved: every step is guarded by the leaf we started on.
(define (cmr-entry-literal!)
  (let ((leaf (proof-state-focus *ps*)))
    (mac 'ENTRY)
    (let loop ((n 4))
      (if (and (> n 0) (not (sequent-node-grounded? leaf)) (cmr-has-lit-nth? (dk-goal)))
          (begin (nth-r) (loop (- n 1)))))
    (if (not (sequent-node-grounded? leaf)) (rfl))))

;;; The ring of reals is a ring.
(define (cmr-ring!)
  (fact 'rr-is-normed-field)
  (dk-cite! 'normed-field-as-commutative-ring-is-commutative-ring 'RR-NORMED-FIELD)
  (dk-cite! 'commutative-ring-is-ring cmr-rring))

;;; (IN t (MAT 2 2 RR)) in context  |-  (IN t (MAT 2 2 (CARR R))).
(define (cmr-mat-carr! t)
  (let ((f (list 'IN t (list 'MAT 2 2 (list 'CARR cmr-rring)))))
    (dk-have! f (lambda () (mac 'rr-scalar-ring-carr) (from-context!)))
    f))

;;; =====================================================================
;;; 1.  A LITERAL 2-BY-2 MATRIX, ITS ENTRIES, 2-BY-2 EXTENSIONALITY.
;;; =====================================================================

(define cmr-m22 '(LIST (LIST a b) (LIST c d)))

(sp (make-wff '(FORALL x (FORALL a (IMPLIES (IN a x) (FORALL b (IMPLIES (IN b x)
      (FORALL c (IMPLIES (IN c x) (FORALL d (IMPLIES (IN d x)
        (IN (LIST (LIST a b) (LIST c d)) (MAT 2 2 x)))))))))))))
(dk-peel!)
(for-each (lambda (v) (fact 'membership-implies-sethood v 'x)) '(a b c d))
(dk-have! (list 'IN cmr-m22 '(MATRIX x))
  (lambda ()
    (mac 'matrix-membership)
    (len-r)
    (dk-conj-close!
      (lambda ()
        (let ((g (dk-goal)))
          (if (eq? (car g) 'IN)
              (cmr-ti!)
              (let* ((lk (dk-peel!))
                     (sp1 (dk-split-all! lk))
                     (vs (map cadr (filter (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) 'NN)))
                                           (append lk sp1)))))
                (for-each (lambda (v) (cmr-len2! v cmr-m22)) vs)
                (for-each (lambda (v) (subst (list '= (list 'LENGTH (list 'NTH v cmr-m22)) 2))) vs)
                (rfl))))))))
(dk-have! '(IN 2 NN) (lambda () (arith)))
(dk-have! '(<= 1 2) (lambda () (arith)))
(dk-have! (list '= (list 'LENGTH cmr-m22) 2) (lambda () (len-r) (rfl)))
(dk-have! (list '= (list 'LENGTH (list 'NTH 1 cmr-m22)) 2) (lambda () (nth-r) (len-r) (rfl)))
(dk-cite! 'mat-intro 2 2 'x cmr-m22)
(ass)
(qed 'mat22-literal-in-mat)

;;; Two 2-by-2 matrices with the same four entries are equal.
(sp (make-wff '(FORALL x (FORALL p (IMPLIES (IN p (MAT 2 2 x)) (FORALL q (IMPLIES (IN q (MAT 2 2 x))
      (IMPLIES (= (ENTRY p 1 1) (ENTRY q 1 1))
      (IMPLIES (= (ENTRY p 1 2) (ENTRY q 1 2))
      (IMPLIES (= (ENTRY p 2 1) (ENTRY q 2 1))
      (IMPLIES (= (ENTRY p 2 2) (ENTRY q 2 2))
        (= p q))))))))))))
(dk-peel!)
(let* ((inst (dk-cite! 'matrix-entry-extensionality 2 2 'x 'p 'q))
       (imp (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES) (equal? (caddr f) '(= p q))
                                         (pair? (cadr f)) (eq? (car (cadr f)) 'FORALL)))
                        (dk-asms)))
       (clause (if imp (cadr imp) (error "mat22-ext: no extensionality implication landed"))))
  (dk-have! clause
    (lambda ()
      (let* ((lk (dk-peel!))
             (vs (map cadr (filter (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) '(INTERVAL 1 2)))) lk))))
        (for-each cmr-interval-parts! vs)
        (for-each cmr-index-cases! vs)
        (let ((i_ (car vs)) (j_ (cadr vs)))
          (use-cases (list (list '= i_ 1) (list '= i_ 2))
            (lambda ()
              (subst (list '= i_ 1))
              (use-cases (list (list '= j_ 1) (list '= j_ 2))
                (lambda () (subst (list '= j_ 1)) (from-context!))
                (lambda () (subst (list '= j_ 2)) (from-context!))))
            (lambda ()
              (subst (list '= i_ 2))
              (use-cases (list (list '= j_ 1) (list '= j_ 2))
                (lambda () (subst (list '= j_ 1)) (from-context!))
                (lambda () (subst (list '= j_ 2)) (from-context!)))))))))
  (detach! imp)
  (from-context!))
(qed 'mat22-ext)

;;; =====================================================================
;;; 2.  CC-MATRIX-OF: TYPING AND ENTRIES.
;;; =====================================================================

(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
      (AND (= (ENTRY (CC-MATRIX-OF a b) 1 1) a)
      (AND (= (ENTRY (CC-MATRIX-OF a b) 1 2) b)
      (AND (= (ENTRY (CC-MATRIX-OF a b) 2 1) (- b))
           (= (ENTRY (CC-MATRIX-OF a b) 2 2) a))))))))))
(dk-peel!)
(fact 'rr-neg-closed 'b)
(for-each (lambda (v) (fact 'membership-implies-sethood v 'RR)) '(a b (- b)))
(mac 'CC-MATRIX-OF)
(dk-conj-close! (lambda () (cmr-entry-literal!)))
(qed 'cc-matrix-of-entries)

(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
      (IN (CC-MATRIX-OF a b) (MAT 2 2 RR))))))))
(dk-peel!)
(fact 'rr-neg-closed 'b)
(mac 'CC-MATRIX-OF)
(dk-cite! 'mat22-literal-in-mat 'RR 'a 'b '(- b) 'a)
(ass)
(qed 'cc-matrix-of-in-mat)

;;; =====================================================================
;;; 3.  2-BY-2 PRODUCTS AND SUMS OVER THE RING OF REALS.
;;; =====================================================================

(sp (make-wff `(FORALL p (IMPLIES (IN p (MAT 2 2 RR)) (FORALL q (IMPLIES (IN q (MAT 2 2 RR))
      (IN (MATMUL ,cmr-rring p q) (MAT 2 2 RR))))))))
(dk-peel!)
(cmr-ring!)
(cmr-mat-carr! 'p)
(cmr-mat-carr! 'q)
(dk-have! '(NOT (= 2 0)) (lambda () (arith)))
(dk-have! '(IMPLIES (= 2 0) (OR (= 2 0) (= 2 0))) (lambda () (prop)))
(dk-cite! 'matmul-type cmr-rring 2 2 2 'p 'q)
(fact 'rr-scalar-ring-carr)
(subst (list '= 'RR (list 'CARR cmr-rring)))
(from-context!)
(qed 'rr-matmul-2x2-type)

(sp (make-wff `(FORALL p (IMPLIES (IN p (MAT 2 2 RR)) (FORALL q (IMPLIES (IN q (MAT 2 2 RR))
      (IN (MATADD ,cmr-rring p q) (MAT 2 2 RR))))))))
(dk-peel!)
(cmr-ring!)
(cmr-mat-carr! 'p)
(cmr-mat-carr! 'q)
(dk-cite! 'matadd-type cmr-rring 2 2 'p 'q)
(fact 'rr-scalar-ring-carr)
(subst (list '= 'RR (list 'CARR cmr-rring)))
(from-context!)
(qed 'rr-matadd-2x2-type)

;;; Type a real term built from typed atoms by + - * and unary -.
(define (cmr-rr! t)
  (let ((typ (list 'IN t 'RR)))
    (cond ((dk-asm? typ) typ)
          ((eqv? t 0) (fact 'rr-zero-in) typ)
          ((eqv? t 1) (fact 'rr-one-in) typ)
          ((and (pair? t) (eq? (car t) 'real-part)) (fact 'real-part-in-rr (cadr t)) typ)
          ((and (pair? t) (eq? (car t) 'imag-part)) (fact 'imag-part-in-rr (cadr t)) typ)
          ((and (pair? t) (eq? (car t) '-) (= (length t) 2))
           (cmr-rr! (cadr t)) (fact 'rr-neg-closed (cadr t)) typ)
          ((and (pair? t) (memq (car t) '(+ * -)) (= (length t) 3))
           (cmr-rr! (cadr t)) (cmr-rr! (caddr t))
           (fact (cdr (assq (car t) '((+ . rr-add-in-rr) (* . rr-mul-in-rr) (- . rr-sub-in-rr))))
                 (cadr t) (caddr t))
           typ)
          (#t (dk-real! t) typ))))

;;; Land the four entries of CC-MATRIX-OF(a, b), a and b real.
(define (cmr-entries! a b)
  (cmr-rr! a) (cmr-rr! b)
  (dk-split-all! (list (dk-cite! 'cc-matrix-of-entries a b))))

;;; Rewrite every (ENTRY ...) of the goal for which the context holds (= (ENTRY ...) t).
(define (cmr-subterm? s t) (or (equal? s t) (and (pair? t) (any-pred (lambda (u) (cmr-subterm? s u)) t))))
(define (cmr-subst-entries!)
  (let loop ((fuel 40))
    (let ((eq (find-first (lambda (h) (and (pair? h) (eq? (car h) '=) (pair? (cadr h)) (eq? (car (cadr h)) 'ENTRY)
                                           (cmr-subterm? (cadr h) (dk-goal))))
                          (dk-asms))))
      (if (and eq (> fuel 0))
          (begin (subst eq) (loop (- fuel 1)))))))

;;; The product entry over the ring of reals: (P Q)_{ik} = P_{i1} Q_{1k} + P_{i2} Q_{2k}.
(sp (make-wff `(FORALL p (IMPLIES (IN p (MAT 2 2 RR)) (FORALL q (IMPLIES (IN q (MAT 2 2 RR))
      (FORALL i (IMPLIES (IN i (INTERVAL 1 2)) (FORALL k (IMPLIES (IN k (INTERVAL 1 2))
        (= (ENTRY (MATMUL ,cmr-rring p q) i k)
           (+ (* (ENTRY p i 1) (ENTRY q 1 k)) (* (ENTRY p i 2) (ENTRY q 2 k))))))))))))))
(dk-peel!)
(cmr-ring!)
(cmr-mat-carr! 'p)
(cmr-mat-carr! 'q)
(dk-have! '(<= 1 2) (lambda () (arith)))
(dk-have! '(IN 1 NN) (lambda () (arith)))
(dk-have! '(IN 2 NN) (lambda () (arith)))
(cmr-in-12! 1)
(cmr-in-12! 2)
(define cmr-me (dk-cite! 'matmul-entry cmr-rring 2 2 2 'p 'q 'i 'k))
(subst cmr-me)
(define cmr-ag (list 'RING-ADDITIVE-AG cmr-rring))
(define cmr-f (caddr (caddr cmr-me)))
(dk-cite! 'matprod-summand-type cmr-rring 2 2 2 'p 'q 'i 'k)
(dk-cite! 'ring-additive-ag-is-abelian-group cmr-rring)
(fact 'interval-in-set 1 2)
(dk-cite! 'interval-card-in-nn 1 2)
(dk-have! '(NOT (= 1 2)) (lambda () (arith)))
(dk-cite! 'finsum-two-support cmr-ag '(INTERVAL 1 2) cmr-f 1 2)
(let* ((imp (find-first (lambda (f) (and (pair? f) (eq? (car f) 'IMPLIES) (pair? (caddr f)) (eq? (car (caddr f)) '=)
                                         (pair? (cadr (caddr f))) (eq? (car (cadr (caddr f))) 'FINSUM)
                                         (pair? (cadr f)) (eq? (car (cadr f)) 'FORALL)))
                        (dk-asms)))
       (clause (if imp (cadr imp) (error "rr-matmul-2x2-entry: finsum-two-support did not land"))))
  (dk-have! clause
    (lambda ()
      (let* ((lk (dk-peel!))
             (v (cadr (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) '(INTERVAL 1 2)))) lk))))
        (cmr-interval-parts! v)
        (cmr-index-cases! v)
        (keep (list 'OR (list '= v 1) (list '= v 2)) (list 'NOT (list '= v 1)) (list 'NOT (list '= v 2)))
        (prop))))
  (detach! imp)
  (subst (caddr imp)))
(subst (dk-cite! 'ras-op cmr-rring))
(dk-lam-b!)
(for-each (lambda (e) (dk-cite! 'entry-in-carrier 2 2 'RR (car e) (cadr e) (caddr e)))
          '((p i 1) (q 1 k) (p i 2) (q 2 k)))
(cmr-rr! '(* (ENTRY p i 1) (ENTRY q 1 k)))
(cmr-rr! '(* (ENTRY p i 2) (ENTRY q 2 k)))
(mac 'rr-scalar-ring-add)
(mac 'rr-scalar-ring-mul)
(dk-lam-b!)
(rfl)
(qed 'rr-matmul-2x2-entry)

;;; The sum entry over the ring of reals: (P + Q)_{ij} = P_{ij} + Q_{ij}.
(sp (make-wff `(FORALL p (IMPLIES (IN p (MAT 2 2 RR)) (FORALL q (IMPLIES (IN q (MAT 2 2 RR))
      (FORALL i (IMPLIES (IN i (INTERVAL 1 2)) (FORALL k (IMPLIES (IN k (INTERVAL 1 2))
        (= (ENTRY (MATADD ,cmr-rring p q) i k)
           (+ (ENTRY p i k) (ENTRY q i k)))))))))))))
(dk-peel!)
(cmr-ring!)
(cmr-mat-carr! 'p)
(cmr-mat-carr! 'q)
(subst (dk-cite! 'matadd-entry cmr-rring 2 2 'p 'q 'i 'k))
(dk-cite! 'entry-in-carrier 2 2 'RR 'p 'i 'k)
(dk-cite! 'entry-in-carrier 2 2 'RR 'q 'i 'k)
(mac 'rr-scalar-ring-add)
(dk-lam-b!)
(rfl)
(qed 'rr-matadd-2x2-entry)

;;; =====================================================================
;;; 4.  THE NOTES' COMPUTATION: PRODUCTS AND SUMS OF MATRICES OF THE FORM [[a,b],[-b,a]].
;;; =====================================================================

;;; Prove (= P Q) for two 2-by-2 real matrices given as terms, entrywise: each entry
;;; equation is rewritten by every ENTRY equation the context holds, then closed by crs.
(define (cmr-entrywise! pm qm)
  (for-each
    (lambda (ij)
      (let ((i (car ij)) (j (cadr ij)))
        (dk-have! (list '= (list 'ENTRY pm i j) (list 'ENTRY qm i j))
          (lambda () (cmr-subst-entries!) (crs)))))
    '((1 1) (1 2) (2 1) (2 2)))
  (dk-cite! 'mat22-ext 'RR pm qm)
  (from-context!))

;;; the entries of the product P Q, P and Q real 2-by-2 matrices in context, at literal indices
(define (cmr-matmul-entries! pm qm)
  (cmr-in-12! 1) (cmr-in-12! 2)
  (for-each (lambda (ij) (dk-cite! 'rr-matmul-2x2-entry pm qm (car ij) (cadr ij)))
            '((1 1) (1 2) (2 1) (2 2))))
(define (cmr-matadd-entries! pm qm)
  (cmr-in-12! 1) (cmr-in-12! 2)
  (for-each (lambda (ij) (dk-cite! 'rr-matadd-2x2-entry pm qm (car ij) (cadr ij)))
            '((1 1) (1 2) (2 1) (2 2))))

(sp (make-wff `(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
      (FORALL c (IMPLIES (IN c RR) (FORALL d (IMPLIES (IN d RR)
        (= (MATMUL ,cmr-rring (CC-MATRIX-OF a b) (CC-MATRIX-OF c d))
           (CC-MATRIX-OF (- (* a c) (* b d)) (+ (* a d) (* b c))))))))))))))
(dk-peel!)
(define cmr-ma '(CC-MATRIX-OF a b))
(define cmr-mc '(CC-MATRIX-OF c d))
(define cmr-mq '(CC-MATRIX-OF (- (* a c) (* b d)) (+ (* a d) (* b c))))
(cmr-entries! 'a 'b)
(cmr-entries! 'c 'd)
(cmr-entries! '(- (* a c) (* b d)) '(+ (* a d) (* b c)))
(dk-cite! 'cc-matrix-of-in-mat 'a 'b)
(dk-cite! 'cc-matrix-of-in-mat 'c 'd)
(dk-cite! 'cc-matrix-of-in-mat '(- (* a c) (* b d)) '(+ (* a d) (* b c)))
(dk-cite! 'rr-matmul-2x2-type cmr-ma cmr-mc)
(cmr-matmul-entries! cmr-ma cmr-mc)
(cmr-entrywise! (list 'MATMUL cmr-rring cmr-ma cmr-mc) cmr-mq)
(qed 'cc-matrix-of-mul)

(sp (make-wff `(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
      (FORALL c (IMPLIES (IN c RR) (FORALL d (IMPLIES (IN d RR)
        (= (MATADD ,cmr-rring (CC-MATRIX-OF a b) (CC-MATRIX-OF c d))
           (CC-MATRIX-OF (+ a c) (+ b d)))))))))))))
(dk-peel!)
(define cmr-mq2 '(CC-MATRIX-OF (+ a c) (+ b d)))
(cmr-entries! 'a 'b)
(cmr-entries! 'c 'd)
(cmr-entries! '(+ a c) '(+ b d))
(dk-cite! 'cc-matrix-of-in-mat 'a 'b)
(dk-cite! 'cc-matrix-of-in-mat 'c 'd)
(dk-cite! 'cc-matrix-of-in-mat '(+ a c) '(+ b d))
(dk-cite! 'rr-matadd-2x2-type cmr-ma cmr-mc)
(cmr-matadd-entries! cmr-ma cmr-mc)
(cmr-entrywise! (list 'MATADD cmr-rring cmr-ma cmr-mc) cmr-mq2)
(qed 'cc-matrix-of-add)

;;; Real multiples: MATSCALE(R, c, [[a, b], [-b, a]]) = [[c a, c b], [-(c b), c a]].
(sp (make-wff `(FORALL c (IMPLIES (IN c RR) (FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
        (= (MATSCALE ,cmr-rring c (CC-MATRIX-OF a b))
           (CC-MATRIX-OF (* c a) (* c b)))))))))))
(dk-peel!)
(define cmr-msc (list 'MATSCALE cmr-rring 'c cmr-ma))
(cmr-ring!)
(cmr-entries! 'a 'b)
(cmr-entries! '(* c a) '(* c b))
(dk-cite! 'cc-matrix-of-in-mat 'a 'b)
(dk-cite! 'cc-matrix-of-in-mat '(* c a) '(* c b))
(cmr-mat-carr! cmr-ma)
(dk-have! (list 'IN 'c (list 'CARR cmr-rring)) (lambda () (mac 'rr-scalar-ring-carr) (from-context!)))
(let ((ty (dk-cite! 'matscale-type cmr-rring 2 2 'c cmr-ma)))
  (fact 'rr-scalar-ring-carr)
  (dk-rewrite-h! ty (list 'CARR cmr-rring) 'RR))
(cmr-in-12! 1) (cmr-in-12! 2)
(for-each
  (lambda (ij)
    (let* ((i (car ij)) (j (cadr ij))
           (e (dk-cite! 'matscale-entry cmr-rring 2 2 'c cmr-ma i j)))
      (dk-cite! 'entry-in-carrier 2 2 'RR cmr-ma i j)
      (dk-have! (list '= (list 'ENTRY cmr-msc i j) (list '* 'c (list 'ENTRY cmr-ma i j)))
        (lambda () (subst e) (mac 'rr-scalar-ring-mul) (dk-lam-b!) (rfl)))))
  '((1 1) (1 2) (2 1) (2 2)))
(cmr-entrywise! cmr-msc '(CC-MATRIX-OF (* c a) (* c b)))
(qed 'cc-matrix-of-scale)

;;; Two matrices of the form [[a, b], [-b, a]] are equal only when their a's and b's are.
(sp (make-wff '(FORALL a (IMPLIES (IN a RR) (FORALL b (IMPLIES (IN b RR)
      (FORALL c (IMPLIES (IN c RR) (FORALL d (IMPLIES (IN d RR)
        (IMPLIES (= (CC-MATRIX-OF a b) (CC-MATRIX-OF c d))
          (AND (= a c) (= b d)))))))))))))
(dk-peel!)
(cmr-entries! 'a 'b)
(cmr-entries! 'c 'd)
(dk-conj-close!
  (lambda ()
    (let* ((g (dk-goal)) (u (cadr g)) (v (caddr g))
           (ij (if (eq? u 'a) '(1 1) '(1 2)))
           (eu (list 'ENTRY cmr-ma (car ij) (cadr ij)))
           (ev (list 'ENTRY cmr-mc (car ij) (cadr ij))))
      (subst (list '= u eu))
      (subst (list '= cmr-ma cmr-mc))
      (subst (list '= ev v))
      (rfl))))
(qed 'cc-matrix-of-injective)

;;; =====================================================================
;;; 5.  THE MAP PHI = CC-MATRIX-REP.
;;; =====================================================================

(define cmr-rep-body '(VNB-LAMBDA cmz_ CC (CC-MATRIX-OF (real-part cmz_) (imag-part cmz_))))

(sp (make-wff '(FORALL z (IMPLIES (IN z CC)
      (== (CC-MATRIX-REP z) (CC-MATRIX-OF (real-part z) (imag-part z)))))))
(dk-peel!)
(fact 'cc-matrix-rep-def)
(subst (dk-fact! 'apply-congruence-1 'CC-MATRIX-REP cmr-rep-body 'z))
(dk-lam-b!)
(qrfl)
(qed 'cc-matrix-rep-apply)

;;; Phi(z) rewritten to [[re z, im z], [-im z, re z]], with the coordinates typed.
(define (cmr-unfold-rep! t)
  (cmr-rr! (list 'real-part t))
  (cmr-rr! (list 'imag-part t))
  (subst (dk-cite! 'cc-matrix-rep-apply t)))

(define (cmr-cc-and! u v)
  (let ((f (list 'AND (list 'IN u 'CC) (list 'IN v 'CC))))
    (if (not (dk-asm? f)) (dk-have! f (lambda () (dk-conj-close! from-context!))))
    f))

;;; Phi preserves sums.
(sp (make-wff `(FORALL z (IMPLIES (IN z CC) (FORALL w (IMPLIES (IN w CC)
      (= (CC-MATRIX-REP (+ z w))
         (MATADD ,cmr-rring (CC-MATRIX-REP z) (CC-MATRIX-REP w)))))))))
(dk-peel!)
(cmr-cc-and! 'z 'w)
(fact 'cc-add-closed 'z 'w)
(cmr-unfold-rep! '(+ z w))
(cmr-unfold-rep! 'z)
(cmr-unfold-rep! 'w)
(subst (dk-cite! 'cc-re-add 'z 'w))
(subst (dk-cite! 'cc-im-add 'z 'w))
(subst (dk-cite! 'cc-matrix-of-add '(real-part z) '(imag-part z) '(real-part w) '(imag-part w)))
(dk-cite! 'cc-matrix-of-in-mat '(+ (real-part z) (real-part w)) '(+ (imag-part z) (imag-part w)))
(rfl)
(qed 'cc-matrix-rep-add)

;;; Phi preserves products.
(sp (make-wff `(FORALL z (IMPLIES (IN z CC) (FORALL w (IMPLIES (IN w CC)
      (= (CC-MATRIX-REP (* z w))
         (MATMUL ,cmr-rring (CC-MATRIX-REP z) (CC-MATRIX-REP w)))))))))
(dk-peel!)
(cmr-cc-and! 'z 'w)
(fact 'cc-mul-closed 'z 'w)
(cmr-unfold-rep! '(* z w))
(cmr-unfold-rep! 'z)
(cmr-unfold-rep! 'w)
(subst (dk-cite! 'cc-re-mul 'z 'w))
(subst (dk-cite! 'cc-im-mul 'z 'w))
(subst (dk-cite! 'cc-matrix-of-mul '(real-part z) '(imag-part z) '(real-part w) '(imag-part w)))
(cmr-rr! '(- (* (real-part z) (real-part w)) (* (imag-part z) (imag-part w))))
(cmr-rr! '(+ (* (real-part z) (imag-part w)) (* (imag-part z) (real-part w))))
(dk-cite! 'cc-matrix-of-in-mat '(- (* (real-part z) (real-part w)) (* (imag-part z) (imag-part w)))
                               '(+ (* (real-part z) (imag-part w)) (* (imag-part z) (real-part w))))
(rfl)
(qed 'cc-matrix-rep-mul)

;;; Phi preserves real multiples.
(sp (make-wff `(FORALL c (IMPLIES (IN c RR) (FORALL z (IMPLIES (IN z CC)
      (= (CC-MATRIX-REP (* c z))
         (MATSCALE ,cmr-rring c (CC-MATRIX-REP z)))))))))
(dk-peel!)
(fact 'rr-subset-cc 'c)
(cmr-cc-and! 'c 'z)
(fact 'cc-mul-closed 'c 'z)
(cmr-unfold-rep! '(* c z))
(cmr-unfold-rep! 'z)
(subst (dk-cite! 'cc-re-real-mul 'c 'z))
(subst (dk-cite! 'cc-im-real-mul 'c 'z))
(subst (dk-cite! 'cc-matrix-of-scale 'c '(real-part z) '(imag-part z)))
(cmr-rr! '(* c (real-part z)))
(cmr-rr! '(* c (imag-part z)))
(dk-cite! 'cc-matrix-of-in-mat '(* c (real-part z)) '(* c (imag-part z)))
(rfl)
(qed 'cc-matrix-rep-real-mul)

;;; Phi(1) is the identity matrix.
(sp (make-wff `(= (CC-MATRIX-REP 1) (IDENTMAT ,cmr-rring 2))))
(fact 'cc-one-in)
(fact 'cc-i-in)
(fact 'rr-one-in)
(fact 'rr-zero-in)
(cmr-unfold-rep! 1)
(dk-have! '(= 1 (+ 1 (* 0 +i))) (lambda () (crs)))
(dk-split-all! (list (dk-cite! 'cc-re-im-of 1 1 0)))
(subst '(= (real-part 1) 1))
(subst '(= (imag-part 1) 0))
(cmr-ring!)
(define cmr-id (list 'IDENTMAT cmr-rring 2))
(dk-have! '(IN 2 NN) (lambda () (arith)))
(let ((ty (dk-cite! 'identmat-type cmr-rring 2)))
  (fact 'rr-scalar-ring-carr)
  (dk-rewrite-h! ty (list 'CARR cmr-rring) 'RR))
(cmr-entries! 1 0)
(dk-cite! 'cc-matrix-of-in-mat 1 0)
(cmr-in-12! 1) (cmr-in-12! 2)
(dk-have! '(NOT (= 1 2)) (lambda () (arith)))
(dk-have! '(NOT (= 2 1)) (lambda () (arith)))
(for-each
  (lambda (ij)
    (let* ((i (car ij)) (j (cadr ij))
           (e (if (= i j)
                  (dk-cite! 'identmat-entry-diag cmr-rring 2 i)
                  (dk-cite! 'identmat-entry-off cmr-rring 2 i j))))
      (dk-have! (list '= (list 'ENTRY cmr-id i j) (if (= i j) 1 0))
        (lambda () (subst e) (mac (if (= i j) 'rr-scalar-ring-one 'rr-scalar-ring-zero)) (rfl)))))
  '((1 1) (1 2) (2 1) (2 2)))
(cmr-entrywise! '(CC-MATRIX-OF 1 0) cmr-id)
(qed 'cc-matrix-rep-one)

;;; =====================================================================
;;; 6.  PHI IS A BIJECTION OF CC ONTO CC-MATRICES.
;;; =====================================================================

(define cmr-matrices-body
  '(SEP cmq_ (MAT 2 2 RR)
     (FORSOME cma_ (AND (IN cma_ RR)
       (FORSOME cmb_ (AND (IN cmb_ RR)
         (= cmq_ (CC-MATRIX-OF cma_ cmb_))))))))

;;; Phi maps CC into CC-MATRICES.
(sp (make-wff '(IN CC-MATRIX-REP (FUN CC CC-MATRICES))))
(fact 'cc-matrix-rep-def)
(subst (list '= 'CC-MATRIX-REP cmr-rep-body))
(fact 'cc-matrices-def)
(subst (list '= 'CC-MATRICES cmr-matrices-body))
(fact 'cc-is-set)
(dk-lam-type!
  (lambda ()
    (let* ((lk (dk-peel!))
           (v (cadr (find-first (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'CC))) lk))))
      (cmr-rr! (list 'real-part v))
      (cmr-rr! (list 'imag-part v))
      (dk-cite! 'cc-matrix-of-in-mat (list 'real-part v) (list 'imag-part v))
      (in-sep!
        (lambda ()
          (ew (list 'real-part v))
          (dk-conj-close!
            (lambda ()
              (if (eq? (car (dk-goal)) 'FORSOME)
                  (begin (ew (list 'imag-part v))
                         (dk-conj-close! (lambda () (if (dk-asm? (dk-goal)) (ass) (rfl)))))
                  (from-context!)))))))))
(qed 'cc-matrix-rep-in-fun)

(sp (make-wff '(IN CC-MATRIX-REP (BIJECTION CC CC-MATRICES))))
(dk-cite! 'cc-matrix-rep-in-fun)
(mac 'bijection-membership-iff)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond
        ((eq? (car g) 'IN) (from-context!))
        ;; injective: Phi(a) = Phi(b) implies a = b
        ((let loop ((t g)) (and (pair? t) (or (eq? (car t) 'FORSOME) (and (memq (car t) '(FORALL IMPLIES)) (loop (caddr t))))))
         ;; surjective
         (let* ((lk (dk-peel!))
                (w (cadr (find-first (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'CC-MATRICES))) lk))))
           (fact 'cc-matrices-def)
           (let* ((h (dk-rewrite-h! (list 'IN w 'CC-MATRICES) 'CC-MATRICES cmr-matrices-body))
                  (landed (dk-landed* (lambda () (sep-me h))))
                  (ex (find-first (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) landed))
                  (av (dk-skolem! ex))
                  (ex2 (find-first (lambda (f) (and (pair? f) (eq? (car f) 'FORSOME))) (dk-asms)))
                  (bv (dk-skolem! ex2))
                  (z0 (list '+ av (list '* bv +i))))
             (fact 'rr-subset-cc av)
             (fact 'rr-subset-cc bv)
             (fact 'cc-i-in)
             (cmr-cc-and! bv +i)
             (fact 'cc-mul-closed bv +i)
             (cmr-cc-and! av (list '* bv +i))
             (fact 'cc-add-closed av (list '* bv +i))
             (dk-have! (list '= z0 z0) (lambda () (rfl)))
             (dk-split-all! (list (dk-cite! 'cc-re-im-of z0 av bv)))
             (ew z0)
             (dk-conj-close!
               (lambda ()
                 (if (eq? (car (dk-goal)) 'IN)
                     (from-context!)
                     (begin
                       (cmr-unfold-rep! z0)
                       (subst (list '= (list 'real-part z0) av))
                       (subst (list '= (list 'imag-part z0) bv))
                       (subst (list '= w (list 'CC-MATRIX-OF av bv)))
                       (dk-cite! 'cc-matrix-of-in-mat av bv)
                       (rfl))))))))
        (#t
         (let* ((lk (dk-peel!))
                (vs (map cadr (filter (lambda (f) (and (eq? (car f) 'IN) (eq? (caddr f) 'CC))) lk)))
                (h (find-first (lambda (f) (eq? (car f) '=)) lk))
                (u (car vs)) (v (cadr vs)))
           (for-each (lambda (t) (cmr-rr! (list 'real-part t)) (cmr-rr! (list 'imag-part t))) vs)
           (dk-cite! 'cc-matrix-rep-apply u)
           (dk-cite! 'cc-matrix-rep-apply v)
           (let* ((h1 (dk-rewrite-h! h (list 'CC-MATRIX-REP u)
                                     (list 'CC-MATRIX-OF (list 'real-part u) (list 'imag-part u))))
                  (h2 (dk-rewrite-h! h1 (list 'CC-MATRIX-REP v)
                                     (list 'CC-MATRIX-OF (list 'real-part v) (list 'imag-part v)))))
             (dk-split-all! (list (dk-cite! 'cc-matrix-of-injective (list 'real-part u) (list 'imag-part u)
                                                                    (list 'real-part v) (list 'imag-part v))))
             (let ((du (dk-cite! 'cc-re-im-decompose u))
                   (dv (dk-cite! 'cc-re-im-decompose v)))
               (subst du)
               (subst (list '= (list 'real-part u) (list 'real-part v)))
               (subst (list '= (list 'imag-part u) (list 'imag-part v)))
               (subst (list '= (caddr dv) v))
               (rfl)))))))))
(qed 'cc-matrix-rep-bijection)

;;; =====================================================================
;;; 7.  PROPOSITION 1.3.
;;; =====================================================================

(sp (make-wff `(AND (IN CC-MATRIX-REP (BIJECTION CC CC-MATRICES))
               (AND (FORALL z (IMPLIES (IN z CC) (FORALL w (IMPLIES (IN w CC)
                      (= (CC-MATRIX-REP (+ z w))
                         (MATADD ,cmr-rring (CC-MATRIX-REP z) (CC-MATRIX-REP w)))))))
               (AND (FORALL z (IMPLIES (IN z CC) (FORALL w (IMPLIES (IN w CC)
                      (= (CC-MATRIX-REP (* z w))
                         (MATMUL ,cmr-rring (CC-MATRIX-REP z) (CC-MATRIX-REP w)))))))
               (AND (= (CC-MATRIX-REP 1) (IDENTMAT ,cmr-rring 2))
                    (FORALL c (IMPLIES (IN c RR) (FORALL z (IMPLIES (IN z CC)
                      (= (CC-MATRIX-REP (* c z))
                         (MATSCALE ,cmr-rring c (CC-MATRIX-REP z)))))))))))))
(for-each dk-cite! '(cc-matrix-rep-bijection cc-matrix-rep-add cc-matrix-rep-mul cc-matrix-rep-one
                     cc-matrix-rep-real-mul))
(dk-conj-close! from-context!)
(qed 'cc-matrix-representation)

(for-each (lambda (n) (topic! n 'algebra))
  '(cc-matrix-of-entries cc-matrix-of-in-mat cc-matrix-of-mul cc-matrix-of-add cc-matrix-of-scale
    cc-matrix-of-injective cc-matrix-rep-apply cc-matrix-rep-add cc-matrix-rep-mul cc-matrix-rep-real-mul
    cc-matrix-rep-one cc-matrix-rep-in-fun cc-matrix-rep-bijection cc-matrix-representation))
(for-each (lambda (n) (topic! n 'plumbing))
  '(mat22-literal-in-mat mat22-ext rr-matmul-2x2-type rr-matadd-2x2-type rr-matmul-2x2-entry rr-matadd-2x2-entry))
(alias! 'cc-matrix-representation
  "the complex numbers are the 2-by-2 real matrices [[a, b], [-b, a]]: a + b i |-> [[a, b], [-b, a]] is an algebra isomorphism onto them (Proposition 1.3)")
