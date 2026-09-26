;;; class-min-pivot-proof.scm -- the minimal-degree pivot over the whole
;;; ~-equivalence class, and the typing lemma it needs.
;;;
;;;   mat-equiv-target-is-mat   C ~ D and C an m-by-n matrix  =>  so is D
;;;   class-min-pivot           P has a nonzero entry  =>  some B ~ P has a
;;;                             nonzero (1,1) entry whose degree is <= the
;;;                             degree of EVERY nonzero entry of EVERY C ~ P
;;;
;;; class-min-pivot is the Smith descent invariant: division-with-remainder
;;; against B_{1,1} produces a remainder of strictly smaller degree, which would
;;; sit in a matrix equivalent to P -- so the remainder must vanish, and the
;;; pivot cross clears in one step (clear-pivot-cross-proof.scm).
;;;
;;; It was an ASSERTED support in structure-library/mat-equiv.scm, warranted
;;; 'well-known.  The warrant swallowed four separate things: the well-ordering
;;; of NN, the formation of the class-degree set, swap-to-corner-gen (which is
;;; PROVEN, smith-proof.scm), and the reflexivity/transitivity of ~ (also
;;; proven).  Only the first two were ever "well known" in the sense the warrant
;;; claimed, and minimize! discharges both.  What is left here is the
;;; mathematics that is actually specific to matrices: put the minimizer at
;;; (1,1), and transport minimality along the equality of entries.
;;;
;;; Needs: minimize.scm + theorem-library/nn-least-element (minimize!),
;;; mat-equiv-proof (refl / trans / invertible-mat-is-mat), smith-proof
;;; (swap-to-corner-gen), matrix.scm (entry-in-carrier, matmul-type),
;;; euclidean-ring.scm (gauge-is-degree), order-lemmas.scm (fun-apply-type-c).

;;; ---- driver helpers (cmp- prefix)
(define (cmp-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (cmp-asms) (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*))))
(define (cmp-foc! n) (dk-focus! n))
(define (cmp-leaves)
  (filter (lambda (n) (and (not (sequent-node-grounded? n))
                           (null? (sequent-node-in-arrows n))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
(define (cmp-foc-goal! g)                ; ERRORS on a miss, by design
  (let loop ((ls (cmp-leaves)))
    (cond ((null? ls) (error "cmp-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (cmp-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (cmp-find pred)
  (let lp ((as (cmp-asms)))
    (cond ((null? as) (error "cmp-find: no such assumption"))
          ((pred (car as)) (car as))
          (else (lp (cdr as))))))
(define (cmp-di*)
  (let lp () (let* ((g (cmp-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

;;; ===================================================================
;;; mat-equiv-target-is-mat: D = U.C.V is an m-by-n matrix.
;;; The minimality clause of class-min-pivot quantifies over every C ~ P with
;;; no typing hypothesis on C, so the typing has to be RECOVERED from ~.
;;; ===================================================================
(sp (make-wff
  '(FORALL A (IMPLIES (IS-RING A) (FORALL m (FORALL n (FORALL C (FORALL D
     (IMPLIES (IN C (MAT m n (CARR A)))
       (IMPLIES (MAT-EQUIV A m n C D) (IN D (MAT m n (CARR A)))))))))))))
(cmp-di*)
(mac-h 'MAT-EQUIV '(MAT-EQUIV A m n C D))
(let* ((f1 (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME))))))
  (ai f1))                                          ; U
(let* ((f2 (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'AND))))))
  (ai f2))                                          ; IS-INVERTIBLE-MAT A m U | FORSOME V ...
(let* ((f3 (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME))))))
  (ai f3))                                          ; V
(let* ((f4 (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'AND))))))
  (ai f4))                                          ; IS-INVERTIBLE-MAT A n V | (= D ...)
(let* ((eqd (cmp-find (lambda (z) (and (pair? z) (eq? (car z) '=) (eq? (cadr z) 'D)))))
       (rhs (caddr eqd))                            ; (MATMUL A (MATMUL A U C) V)
       (uc  (caddr rhs))                            ; (MATMUL A U C)
       (uu  (caddr uc))
       (vv  (cadddr rhs)))
  (fact 'invertible-mat-is-mat 'A 'm uu)
  (fact 'invertible-mat-is-mat 'A 'n vv)
  ;; product guards (SIZE/MAT surgery, 2026-09-16): tautologies here
  (dk-have-prop! '(IMPLIES (= m 0) (OR (= m 0) (= n 0))))
  (dk-have-prop! '(IMPLIES (= n 0) (OR (= m 0) (= n 0))))
  (fact 'matmul-type 'A 'm 'm 'n uu 'C)
  (fact 'matmul-type 'A 'm 'n 'n uc vv)
  (subst eqd)
  (ass))
(qed 'mat-equiv-target-is-mat)
(topic! 'mat-equiv-target-is-mat 'algebra)

;;; ===================================================================
;;; class-min-pivot
;;; ===================================================================
(define cmp-rows '(INTERVAL 1 m))
(define cmp-cols '(INTERVAL 1 n))
(define (cmp-nz c i j) (list 'NOT (list '= (list 'ENTRY c i j) '(ZERO A))))
(define (cmp-deg c i j) (list (list 'GAUGE 'A) (list 'ENTRY c i j)))
(define (cmp-eqv c) (list 'MAT-EQUIV 'A 'm 'n 'P c))
(define (cmp-typed c) (list 'IN c '(MAT m n (CARR A))))

;; The guard minimize! ranges over: an equivalent, correctly typed matrix C
;; together with a position (i,j) at which it is nonzero.  The typing conjunct
;; is not decoration -- entry-in-carrier needs it to type the measure.
(define (cmp-guard c i j)
  (list 'AND (cmp-typed c)
    (list 'AND (cmp-eqv c)
      (list 'AND (list 'IN i cmp-rows)
        (list 'AND (list 'IN j cmp-cols) (cmp-nz c i j))))))

;; The minimality clause of the CONCLUSION: curried guards, and no typing
;; hypothesis on C (mat-equiv-target-is-mat supplies it).  Verbatim the shape
;; clear-pivot-cross-proof.scm consumes -- do not "tidy" it.
(define (cmp-curried b)
  (list 'FORALL 'C
    (list 'IMPLIES (cmp-eqv 'C)
      (list 'FORALL 'i (list 'FORALL 'j
        (list 'IMPLIES (list 'IN 'i cmp-rows)
          (list 'IMPLIES (list 'IN 'j cmp-cols)
            (list 'IMPLIES (cmp-nz 'C 'i 'j)
              (list '<= (cmp-deg b 1 1) (cmp-deg 'C 'i 'j))))))))))

(define cmp-concl
  (list 'FORSOME 'B
    (list 'AND (cmp-eqv 'B)
      (list 'AND (cmp-nz 'B 1 1) (cmp-curried 'B)))))

(sp (make-wff
  (list 'FORALL 'A (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
    (list 'FORALL 'm (list 'FORALL 'n (list 'FORALL 'P
      (list 'IMPLIES '(IN P (MAT m n (CARR A)))
        (list 'IMPLIES (list 'IN 1 cmp-rows)
          (list 'IMPLIES (list 'IN 1 cmp-cols)
            (list 'IMPLIES
              (list 'FORSOME 'i0 (list 'FORSOME 'j0
                (list 'AND (list 'IN 'i0 cmp-rows)
                  (list 'AND (list 'IN 'j0 cmp-cols) (cmp-nz 'P 'i0 'j0)))))
              cmp-concl)))))))))))
(cmp-di*)
(fact 'euclidean-ring-is-integral-domain 'A)
(fact 'integral-domain-is-commutative-ring 'A)
(fact 'commutative-ring-is-ring 'A)

;;; ---- Choose C ~ P and a position (i,j) minimizing the degree of C_ij.
(define cmp-r (minimize! '(C i j) (cmp-guard 'C 'i 'j) (cmp-deg 'C 'i 'j)))
(define cmp-c0 (car   (car cmp-r)))
(define cmp-i0 (cadr  (car cmp-r)))
(define cmp-j0 (caddr (car cmp-r)))
;; Both obligations are genuinely new here: the guard carries a typing conjunct
;; and MAT-EQUIV, so NONEMPTY is not an alpha-variant of the nonzero-entry
;; hypothesis (contrast min-degree-entry-proof.scm, where it is, and minimize!
;; returns #f).
(define cmp-type (or (cadr  cmp-r) (error "class-min-pivot: TYPE not opened")))
(define cmp-ne   (or (caddr cmp-r) (error "class-min-pivot: NONEMPTY not opened")))

;;; ---- obligation 1: the degree of an entry is a natural number.
(cmp-foc! cmp-type)
(di) (di)                                ; peel C,i,j ; assume the guard
(let* ((ent (cadr (cadr (cmp-goal))))    ; goal (IN ((GAUGE A) (ENTRY C i j)) NN)
       (cc  (cadr ent)) (ii (caddr ent)) (jj (cadddr ent)))
  (ai (cmp-guard cc ii jj))
  (ai (list 'AND (cmp-eqv cc)
        (list 'AND (list 'IN ii cmp-rows)
          (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj)))))
  (ai (list 'AND (list 'IN ii cmp-rows)
        (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj))))
  (ai (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj)))
  (fact 'entry-in-carrier 'm 'n '(CARR A) cc ii jj)
  (fact 'gauge-is-degree 'A)
  (ai '(AND (IN (GAUGE A) (FUN (CARR A) NN)) (HAS-DIV-REMAINDER A (GAUGE A))))
  (fact 'fun-apply-type-c '(GAUGE A) '(CARR A) 'NN (list 'ENTRY cc ii jj))
  (ass))

;;; ---- obligation 2: the guard is satisfiable.  Take C = P (mat-equiv-refl)
;;; at the nonzero position the hypothesis provides.
(cmp-foc! cmp-ne)
;; peel the two existentials of the nonzero-entry hypothesis
(define (cmp-forsome!)
  (let ((f (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME)))))) (ai f)))
(cmp-forsome!) (cmp-forsome!)
(fact 'mat-equiv-refl 'A 'm 'n 'P)
;; the surviving conjunction is (AND (IN i* rows) (AND (IN j* cols) (NOT ...)))
(let* ((conj (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'AND)
                                        (pair? (cadr z)) (eq? (car (cadr z)) 'IN)
                                        (equal? (caddr (cadr z)) cmp-rows)))))
       (ii   (cadr (cadr conj)))
       (tail (caddr conj))                ; (AND (IN j* cols) (NOT ...))
       (jj   (cadr (cadr tail))))
  (ai conj) (ai tail)
  (ew 'P) (ew ii) (ew jj)
  (di) (cmp-foc-goal! (cmp-typed 'P)) (ass)
  (cmp-foc-goal! (list 'AND (cmp-eqv 'P)
                   (list 'AND (list 'IN ii cmp-rows)
                     (list 'AND (list 'IN jj cmp-cols) (cmp-nz 'P ii jj)))))
  (di) (cmp-foc-goal! (cmp-eqv 'P)) (ass)
  (cmp-foc-goal! (list 'AND (list 'IN ii cmp-rows)
                   (list 'AND (list 'IN jj cmp-cols) (cmp-nz 'P ii jj))))
  (di) (cmp-foc-goal! (list 'IN ii cmp-rows)) (ass)
  (cmp-foc-goal! (list 'AND (list 'IN jj cmp-cols) (cmp-nz 'P ii jj)))
  (di) (cmp-foc-goal! (list 'IN jj cmp-cols)) (ass)
  (cmp-foc-goal! (cmp-nz 'P ii jj)) (ass))

;;; ===================================================================
;;; Assemble: bring the minimizing entry to the (1,1) corner.
;;; ===================================================================
(cmp-foc-goal! cmp-concl)
(ai (cmp-guard cmp-c0 cmp-i0 cmp-j0))
(ai (list 'AND (cmp-eqv cmp-c0)
      (list 'AND (list 'IN cmp-i0 cmp-rows)
        (list 'AND (list 'IN cmp-j0 cmp-cols) (cmp-nz cmp-c0 cmp-i0 cmp-j0)))))
(ai (list 'AND (list 'IN cmp-i0 cmp-rows)
      (list 'AND (list 'IN cmp-j0 cmp-cols) (cmp-nz cmp-c0 cmp-i0 cmp-j0))))
(ai (list 'AND (list 'IN cmp-j0 cmp-cols) (cmp-nz cmp-c0 cmp-i0 cmp-j0)))

;; the minimality assumption minimize! landed (AND-guarded, over C,i,j)
(define cmp-minim
  (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'FORALL)
                             (pair? (caddr z)) (eq? (car (caddr z)) 'FORALL)))))

;; swap-to-corner-gen brings C0's minimizing entry to the (1,1) corner.
(fact 'swap-to-corner-gen 'A 'm 'n cmp-c0 cmp-i0 cmp-j0)
(define cmp-swap
  (cmp-find (lambda (z) (and (pair? z) (eq? (car z) 'FORSOME)
                             (pair? (caddr z)) (eq? (car (caddr z)) 'AND)
                             (pair? (cadr (caddr z)))
                             (eq? (car (cadr (caddr z))) 'MAT-EQUIV)))))
(define cmp-swap-body
  (let ((before (cmp-asms)))
    (ai cmp-swap)                        ; forsome-elim: mints the eigenconstant
    (car (filter (lambda (f) (not (member f before))) (cmp-asms)))))
(define cmp-b (list-ref (cadr cmp-swap-body) 5))   ; from (MAT-EQUIV A m n C0 B)
(define cmp-val (caddr cmp-swap-body))             ; (= (ENTRY B 1 1) (ENTRY C0 i* j*))
(ai cmp-swap-body)

;; P ~ B, by transitivity through C0
(fact 'mat-equiv-trans 'A 'm 'n 'P cmp-c0 cmp-b)

(ew cmp-b)
(di) (cmp-foc-goal! (cmp-eqv cmp-b)) (ass)
(cmp-foc-goal! (list 'AND (cmp-nz cmp-b 1 1) (cmp-curried cmp-b)))
(di)
;; B_{1,1} /= 0, because it IS C0's minimizing entry
(cmp-foc-goal! (cmp-nz cmp-b 1 1))
(subst cmp-val) (ass)

;;; ---- the minimality clause, re-curried and with C's typing recovered.
(cmp-foc-goal! (cmp-curried cmp-b))
(di)                                     ; peel C
(di)                                     ; assume P ~ C
(di)                                     ; peel i, j
(di) (di) (di)                           ; assume the three index guards
(let* ((g  (cmp-goal))                   ; (<= (deg B 1 1) (deg C i j))
       (e  (cadr (caddr g)))             ; (ENTRY C i j)
       (cc (cadr e)) (ii (caddr e)) (jj (cadddr e))
       (gd (cmp-guard cc ii jj)))
  (subst cmp-val)                        ; deg(B_11) -> deg(C0_{i0,j0})
  (fact 'mat-equiv-target-is-mat 'A 'm 'n 'P cc)
  (cut gd)
  ;; the AND-guard, from its curried pieces
  (di) (cmp-foc-goal! (cmp-typed cc)) (ass)
  (cmp-foc-goal! (list 'AND (cmp-eqv cc)
                   (list 'AND (list 'IN ii cmp-rows)
                     (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj)))))
  (di) (cmp-foc-goal! (cmp-eqv cc)) (ass)
  (cmp-foc-goal! (list 'AND (list 'IN ii cmp-rows)
                   (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj))))
  (di) (cmp-foc-goal! (list 'IN ii cmp-rows)) (ass)
  (cmp-foc-goal! (list 'AND (list 'IN jj cmp-cols) (cmp-nz cc ii jj)))
  (di) (cmp-foc-goal! (list 'IN jj cmp-cols)) (ass)
  (cmp-foc-goal! (cmp-nz cc ii jj)) (ass)
  ;; ... and minimality applies at (C,i,j)
  (let ((target (list '<= (cmp-deg cmp-c0 cmp-i0 cmp-j0) (cmp-deg cc ii jj))))
    (cmp-foc-goal! target)
    (let* ((m1 (begin (inst cmp-minim cc)
                      (subst-free (cadr cmp-minim) cc (caddr cmp-minim))))
           (m2 (begin (inst m1 ii) (subst-free (cadr m1) ii (caddr m1)))))
      (inst m2 jj)
      (detach! (list 'IMPLIES gd target))
      (ass))))

(qed 'class-min-pivot)
(topic! 'class-min-pivot 'algebra)
