;;; la-elem-gen.scm -- elementary column matrices, column equivalence, the column-step
;;; proposition and linear-algebra 3.12 / 3.13 (LA-DET2, 2026-10-18).
;;;
;;; Vocabulary: structure-library/la-elem-vocab.scm (IS-ELEMENTARY, ELEM-GEN, COL-EQUIV,
;;; IS-COLUMN-STEP, COL-STEP-ROW).  Determinants: theorem-library/la-det-adjoint.scm
;;; (det-lower-triangular, invertible-iff-det-nonzero), vocabulary la-det-vocab.scm.
;;;
;;; PART A (closure of ELEM-GEN).  The elementary matrices are typed and two-sided
;;; invertible with elementary inverses (elementary-type, elementary-inverse);
;;; ELEM-GEN contains I, is closed under X |-> X E (elem-gen-step), satisfies
;;; induction (elem-gen-induction), is closed under products (elem-gen-mul), contains
;;; every elementary matrix (elementary-in-elem-gen), and each of its members has an
;;; inverse in it (elem-gen-inverse), hence is invertible (elem-gen-invertible); a left
;;; inverse equals a right inverse (mat-left-inverse-eq-right).
;;;
;;; PART B (the column-step proposition, over a field: IS-FIELD-RING).  Column
;;; equivalence is reflexive, typed, transitive and contains one elementary step
;;; (col-equiv-refl / -mat / -trans / -elem).  The proof runs down the rows: after t
;;; steps every row 1..t of the matrix is a row of a REDUCED column step matrix
;;; (COL-STEP-ROW); step t+1 (laeg-row-step) is the notes' lemma on row r = t+1: bring a
;;; nonzero entry of row r in a column >= r to (r, r) by ELEM-F (laeg-step-pivot), scale it
;;; to 1 by ELEM-H at its inverse (laeg-step-norm), clear the rest of row r by ELEM-G,
;;; one column at a time (laeg-clear-ind, an induction over the columns).  None of these
;;; changes rows 1..t, whose entries in the columns >= r vanish (laeg-op-*-agree).
;;; HEADLINES: column-step-reduced, column-step-exists (the proposition before 3.12).
;;; PART C.  col-equiv-identity-in-elem-gen (I = A P gives A = P^-1 in ELEM-GEN);
;;; laeg-reduced-invertible-identity (an invertible reduced column step matrix is I:
;;; det = product of the diagonal /= 0 -- the notes' test vector eta replaced by
;;; det-lower-triangular, invertible-iff-det-nonzero and prod-ring-zero-factor);
;;; invertible-iff-col-equiv-identity (3.12), invertible-iff-elem-gen (3.13).
;;;
;;; LOAD WINDOW: after "theorem-library/la-det-adjoint" (unwired; it is the latest
;;; citation: ladet-field-one-ne, ladet-field-inverse, det-lower-triangular,
;;; invertible-iff-det-nonzero), and after "structure-library/la-elem-vocab".  The latest
;;; wired citation is interval-widen (load.scm:2078); then product-of-invertibles-is-
;;; invertible (mat-equiv-proof, 2051), elem-*-inverse (2018), elem-*-action (2014),
;;; matmul-assoc (1985).  Nothing in the tree cites this file.  Library: linear-algebra.
;;; No axiom, support or stamp.
;;;
;;; Helper prefix: laeg-.  Binders the driver builds or states: egs_ egx_ ege_ (the
;;; family, as the vocabulary spells it), egy_ egf_ egp_ (the induction statement), egt_
;;; egq_ egv_ (the classes the inductions use), eiv_ (the inverse); agi_ agj_ (rows
;;; agreeing), csa_ clj_ (the clearing), pvc_ pvj_ nmc_ clc_ rsc_ mnc_ csc_ cse_ (the
;;; existential witnesses of part B), exi_ exj_ dgq_ (part C).

;;; =====================================================================
;;; The file's kit.
;;; =====================================================================
(define (laeg-done! name)
  (if (not (proof-done? *ps*))
      (begin
        (display "\n*** la-elem-gen: ") (display name) (display " did NOT close.\n")
        (for-each (lambda (l)
                    (display ";;   leaf: ")
                    (display (expression->string (dk-goal-of l))) (newline))
                  (dk-open-leaves))))
  (qed name))

(define (laeg-iv n) (list 'INTERVAL 1 n))
(define (laeg-mat n) (list 'MAT n n '(CARR R)))
(define laeg-I '(IDENTMAT R n))
(define laeg-gen '(ELEM-GEN R n))
(define (laeg-mm a b) (list 'MATMUL 'R a b))

;; the family ELEM-GEN(R, n) intersects, spelled exactly as the vocabulary spells it
(define (laeg-fam rr nn)
  (list 'SEP 'egs_ (list 'POWER (list 'MAT nn nn (list 'CARR rr)))
        (list 'AND (list 'IN (list 'IDENTMAT rr nn) 'egs_)
              (list 'FORALL 'egx_ (list 'IMPLIES '(IN egx_ egs_)
                (list 'FORALL 'ege_ (list 'IMPLIES (list 'IS-ELEMENTARY rr nn 'ege_)
                  (list 'IN (list 'MATMUL rr 'egx_ 'ege_) 'egs_))))))))
(define laeg-F (laeg-fam 'R 'n))
(define laeg-int (list 'INTERSECTION-OF laeg-F))
(define (laeg-all-of t)
  (list 'FORALL 'iou_ (list 'IMPLIES (list 'IN 'iou_ laeg-F) (list 'IN t 'iou_))))

;; every typing goal goes through the kit's typing chain
(define (laeg-typ! t cls)
  (if (not (dk-asm? (list 'IN t cls)))
      (dk-have! (list 'IN t cls) dk-typ-close!)))

;; skolemise a (possibly nested) existential in context; return its witnesses in order
(define (laeg-skolem-all! ex)
  (let loop ((ex ex) (acc '()))
    (let* ((v #f)
           (landed (dk-landed (lambda () (set! v (dk-skolem! ex)))))
           (nxt (find-first (dk-head? 'FORSOME) landed)))
      (if nxt (loop nxt (append acc (list v))) (append acc (list v))))))

;; NOT (b = a) from NOT (a = b)
(define (laeg-ne-sym! a b)
  (let ((goal (list 'NOT (list '= b a))))
    (if (not (dk-asm? goal))
        (dk-have! goal
          (lambda ()
            (di)
            (dk-have! (list '= a b) (lambda () (subst (list '= b a)) (rfl)))
            (ai (list 'NOT (list '= a b))))))))

;; the sizes guards of matmul-assoc at square n-by-n matrices, landed by prop
(define (laeg-assoc-guards!)
  (dk-have! '(IMPLIES (= n 0) (OR (= n 0) (AND (= n 0) (= n 0)))) (lambda () (prop))))

;; (P Q) E = P (Q E), all n-by-n and typed in context; returns the equation
(define (laeg-assoc! p q e)
  (laeg-assoc-guards!)
  (dk-cite! 'matmul-assoc 'R 'n 'n 'n 'n p q e))

;; land (IN P (MAT n n (CARR R))) from (IN P (ELEM-GEN R n))
(define (laeg-gen-mat! p)
  (if (not (dk-asm? (list 'IN p (laeg-mat 'n))))
      (fact 'elem-gen-mat 'R 'n p)))

;;; =====================================================================
;;; (A1) The elementary matrices.
;;; =====================================================================
;; the three introduction rules
(sp (make-wff
  (forall-guarded '(R n k l)
    '((IS-RING R) (IN n NN) (IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(IS-ELEMENTARY R n (ELEM-F R n k l)))))
(dk-peel!)
(laeg-typ! '(ELEM-F R n k l) (laeg-mat 'n))
(mac 'IS-ELEMENTARY)
(oi-l)
(ew 'k)
(ew 'l)
(dk-conj-close! (lambda () (let ((g (dk-goal))) (if (and (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl) (ass)))))
(laeg-done! 'elem-f-is-elementary)
(topic! 'elem-f-is-elementary 'algebra)

(sp (make-wff
  (forall-guarded '(R n sc k l)
    '((IS-RING R) (IN n NN) (IN sc (CARR R)) (IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)))
    '(IS-ELEMENTARY R n (ELEM-G R n sc k l)))))
(dk-peel!)
(laeg-typ! '(ELEM-G R n sc k l) (laeg-mat 'n))
(mac 'IS-ELEMENTARY)
(oi-r)
(oi-l)
(ew 'sc)
(ew 'k)
(ew 'l)
(dk-conj-close! (lambda () (let ((g (dk-goal))) (if (and (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl) (ass)))))
(laeg-done! 'elem-g-is-elementary)
(topic! 'elem-g-is-elementary 'algebra)

(sp (make-wff
  (forall-guarded '(R n sc su k)
    '((IS-RING R) (IN n NN) (IN sc (CARR R)) (IN su (CARR R))
      (= ((MUL R) sc su) (ONE R)) (= ((MUL R) su sc) (ONE R)) (IN k (INTERVAL 1 n)))
    '(IS-ELEMENTARY R n (ELEM-H R n sc k)))))
(dk-peel!)
(laeg-typ! '(ELEM-H R n sc k) (laeg-mat 'n))
(mac 'IS-ELEMENTARY)
(oi-r)
(oi-r)
(ew 'sc)
(ew 'k)
(define (laeg-h-closer)
  (let ((g (dk-goal)))
    (cond ((eq? (car g) 'FORSOME) (ew 'su) (dk-conj-close! laeg-h-closer))
          ((and (eq? (car g) '=) (equal? (cadr g) (caddr g))) (rfl))
          (#t (ass)))))
(dk-conj-close! laeg-h-closer)
(laeg-done! 'elem-h-is-elementary)
(topic! 'elem-h-is-elementary 'algebra)

;; the case analysis on IS-ELEMENTARY(R, n, E): F-THUNK, G-THUNK, H-THUNK are called with
;; the witnesses (k l), (r k l), (r k s) and the equation E = ... in context
(define (laeg-elem-cases! e f-thunk g-thunk h-thunk)
  (let* ((hyp (list 'IS-ELEMENTARY 'R 'n e))
         (ignore (fact 'IS-ELEMENTARY 'R 'n e))
         (iff (iff-for hyp))
         (disj (caddr iff))
         (d1 (cadr disj)) (d2 (cadr (caddr disj))) (d3 (caddr (caddr disj))))
    (dk-have! disj (lambda () (dk-only! iff hyp) (prop)))
    (use-cases disj
      (lambda () (f-thunk (laeg-skolem-all! (dk-ctx-form d1))))
      (lambda () (g-thunk (laeg-skolem-all! (dk-ctx-form d2))))
      (lambda () (h-thunk (laeg-skolem-all! (dk-ctx-form d3)))))))

;; typing
(sp (make-wff
  (forall-guarded '(R n E) '((IS-RING R) (IN n NN) (IS-ELEMENTARY R n E))
    '(IN E (MAT n n (CARR R))))))
(dk-peel!)
(laeg-elem-cases! 'E
  (lambda (ws) (let ((k (car ws)) (l (cadr ws)))
                 (subst (list '= 'E (list 'ELEM-F 'R 'n k l))) (dk-typ-close!)))
  (lambda (ws) (let ((r (car ws)) (k (cadr ws)) (l (caddr ws)))
                 (subst (list '= 'E (list 'ELEM-G 'R 'n r k l))) (dk-typ-close!)))
  (lambda (ws) (let ((r (car ws)) (k (cadr ws)))
                 (subst (list '= 'E (list 'ELEM-H 'R 'n r k))) (dk-typ-close!))))
(laeg-done! 'elementary-type)
(topic! 'elementary-type 'algebra)

;; two-sided inverse, itself elementary (the notes' corollary on F^-1, G^-1, H^-1)
(define laeg-inv-body
  '(FORSOME eiv_ (AND (IS-ELEMENTARY R n eiv_)
                      (AND (= (MATMUL R E eiv_) (IDENTMAT R n))
                           (= (MATMUL R eiv_ E) (IDENTMAT R n))))))
(sp (make-wff
  (forall-guarded '(R n E) '((IS-RING R) (IN n NN) (IS-ELEMENTARY R n E)) laeg-inv-body)))
(dk-peel!)
(define (laeg-inv-finish! eq v)
  (subst eq)
  (ew v)
  (dk-conj-close! (lambda () (ass))))
(laeg-elem-cases! 'E
  (lambda (ws)
    (let* ((k (car ws)) (l (cadr ws)) (Fkl (list 'ELEM-F 'R 'n k l)) (Flk (list 'ELEM-F 'R 'n l k)))
      (laeg-ne-sym! k l)
      (laeg-typ! Flk (laeg-mat 'n))
      (fact 'elem-f-is-elementary 'R 'n l k)
      (fact 'elem-f-inverse 'R 'n k l)
      (fact 'elem-f-inverse 'R 'n l k)
      (laeg-inv-finish! (list '= 'E Fkl) Flk)))
  (lambda (ws)
    (let* ((r (car ws)) (k (cadr ws)) (l (caddr ws)) (nr (list '(NEG R) r))
           (G1 (list 'ELEM-G 'R 'n r k l)) (G2 (list 'ELEM-G 'R 'n nr k l)))
      (fact 'ring-neg-in-carr 'R r)
      (laeg-typ! G2 (laeg-mat 'n))
      (fact 'elem-g-is-elementary 'R 'n nr k l)
      (fact 'elem-g-inverse 'R 'n r k l)
      (let ((e2 (dk-fact! 'elem-g-inverse 'R 'n nr k l)))
        (fact 'ring-neg-neg 'R r)
        (dk-rewrite-h! e2 (list '(NEG R) nr) r))
      (laeg-inv-finish! (list '= 'E G1) G2)))
  (lambda (ws)
    (let* ((r (car ws)) (k (cadr ws)) (s (caddr ws))
           (H1 (list 'ELEM-H 'R 'n r k)) (H2 (list 'ELEM-H 'R 'n s k)))
      (laeg-typ! H2 (laeg-mat 'n))
      (fact 'elem-h-is-elementary 'R 'n s r k)
      (fact 'elem-h-inverse 'R 'n r s k)
      (fact 'elem-h-inverse 'R 'n s r k)
      (laeg-inv-finish! (list '= 'E H1) H2))))
(laeg-done! 'elementary-inverse)
(topic! 'elementary-inverse 'algebra)

;;; =====================================================================
;;; (A2) ELEM-GEN: membership, the minimal-set induction, products, inverses.
;;; =====================================================================
(sp (make-wff (list 'FORALL 'R (list 'FORALL 'n (list '== laeg-gen laeg-int)))))
(dk-peel!)
(mac 'ELEM-GEN)
(qrfl)
(laeg-done! 'elem-gen-unfold)
(topic! 'elem-gen-unfold 'algebra)

;; MAT(n, n, CARR R) is a member of the family
(sp (make-wff (forall-guarded '(R n) '((IS-RING R) (IN n NN)) (list 'IN (laeg-mat 'n) laeg-F))))
(dk-peel!)
(fact 'ring-carr-in-set 'R)
(fact 'mat-is-set '(CARR R) 'n 'n)
(fact 'power-whole-in (laeg-mat 'n))
(in-sep! (lambda () (ass))
  (lambda ()
    (dk-conj-close!
      (lambda ()
        (if (eq? (car (dk-goal)) 'IN)
            (dk-typ-close!)
            (let* ((landed (dk-peel!))
                   (ef (find-first (dk-head? 'IS-ELEMENTARY) landed))
                   (e (cadddr ef)))
              (fact 'elementary-type 'R 'n e)
              (dk-typ-close!)))))))
(laeg-done! 'laeg-fam-has-mat)
(topic! 'laeg-fam-has-mat 'plumbing)

;; with (IN P (ELEM-GEN R n)) in context, land (and return) forall u in F. P in u
(define (laeg-gen-all! p)
  (let ((mem (list 'IN p laeg-gen)) (all (laeg-all-of p)))
    (if (not (dk-asm? all))
        (begin
          (fact 'elem-gen-unfold 'R 'n)
          (let* ((m2 (dk-rewrite-h! mem laeg-gen laeg-int))
                 (ignore (fact 'intersection-of-membership laeg-F p))
                 (iff (iff-for m2)))
            (dk-have! all (lambda () (dk-only! iff m2) (prop))))))
    (dk-ctx-form all)))

;; prove the goal (IN P (ELEM-GEN R n)) from a thunk proving, on the focus leaf,
;; (IN P U) with (IN U F) in context; U is passed to the thunk
(define (laeg-gen-intro! p body)
  (fact 'elem-gen-unfold 'R 'n)
  (subst (list '= laeg-gen laeg-int))
  (fact 'laeg-fam-has-mat 'R 'n)
  (fact 'intersection-of-membership laeg-F p)
  (let* ((iff (iff-for (list 'IN p laeg-int)))
         (inh (cadr (caddr iff)))
         (all (caddr (caddr iff))))
    (dk-have! inh (lambda () (ew (laeg-mat 'n)) (ass)))
    (dk-have! all
      (lambda ()
        (let* ((landed (dk-peel!))
               (uf (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) laeg-F))) landed)))
          (body (cadr uf)))))
    (dk-only! iff inh all)
    (prop)))

(sp (make-wff (forall-guarded '(R n P) (list '(IS-RING R) '(IN n NN) (list 'IN 'P laeg-gen))
                (list 'IN 'P (laeg-mat 'n)))))
(dk-peel!)
(fact 'laeg-fam-has-mat 'R 'n)
(dk-apply! (laeg-gen-all! 'P) (laeg-mat 'n))
(ass)
(laeg-done! 'elem-gen-mat)
(topic! 'elem-gen-mat 'algebra)

(sp (make-wff (forall-guarded '(R n) '((IS-RING R) (IN n NN)) (list 'IN laeg-I laeg-gen))))
(dk-peel!)
(laeg-typ! laeg-I (laeg-mat 'n))
(laeg-gen-intro! laeg-I
  (lambda (u)
    (let* ((landed (dk-landed (lambda () (sep-me (list 'IN u laeg-F)))))
           (cj (find-first (dk-head? 'AND) landed)))
      (dk-split! cj)
      (ass))))
(laeg-done! 'elem-gen-identity)
(topic! 'elem-gen-identity 'algebra)

(sp (make-wff (forall-guarded '(R n P E)
                (list '(IS-RING R) '(IN n NN) (list 'IN 'P laeg-gen) '(IS-ELEMENTARY R n E))
                (list 'IN (laeg-mm 'P 'E) laeg-gen))))
(dk-peel!)
(laeg-gen-mat! 'P)
(fact 'elementary-type 'R 'n 'E)
(laeg-typ! (laeg-mm 'P 'E) (laeg-mat 'n))
(let ((allp (laeg-gen-all! 'P)))
  (laeg-gen-intro! (laeg-mm 'P 'E)
    (lambda (u)
      (dk-apply! allp u)
      (let* ((landed (dk-landed (lambda () (sep-me (list 'IN u laeg-F)))))
             (cj (find-first (dk-head? 'AND) landed))
             (parts (dk-split! cj))
             (cl (find-first (dk-head? 'FORALL) parts)))
        (dk-apply! cl 'P 'E)
        (ass)))))
(laeg-done! 'elem-gen-step)
(topic! 'elem-gen-step 'algebra)

;; the minimal-set induction, over any class S
(define laeg-closed-S
  '(FORALL egy_ (IMPLIES (IN egy_ S)
     (FORALL egf_ (IMPLIES (IS-ELEMENTARY R n egf_) (IN (MATMUL R egy_ egf_) S))))))
(sp (make-wff (forall-guarded '(R n S)
                (list '(IS-RING R) '(IN n NN) (list 'IN laeg-I 'S) laeg-closed-S)
                (list 'FORALL 'egp_ (list 'IMPLIES (list 'IN 'egp_ laeg-gen) '(IN egp_ S))))))
(let* ((landed (dk-peel!))
       (pm (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) laeg-gen))) landed))
       (p (cadr pm))
       (allp (laeg-gen-all! p))
       (tcl (list 'SEP 'egt_ (laeg-mat 'n) '(IN egt_ S))))
  (fact 'ring-carr-in-set 'R)
  (fact 'mat-is-set '(CARR R) 'n 'n)
  (laeg-typ! laeg-I (laeg-mat 'n))
  (dk-have! (list 'IN tcl 'SET) (lambda () (sep-set) (ass)))
  (dk-have! (list 'IN tcl laeg-F)
    (lambda ()
      (in-sep!
        (lambda ()
          (dk-have! (list 'FORALL 'egz_ (list 'IMPLIES (list 'IN 'egz_ tcl) (list 'IN 'egz_ (laeg-mat 'n))))
            (lambda ()
              (let* ((l2 (dk-peel!)) (zm (car l2)))
                (sep-me zm)
                (ass))))
          (fact 'power-mem-intro (laeg-mat 'n) tcl)
          (ass))
        (lambda ()
          (dk-conj-close!
            (lambda ()
              (if (eq? (car (dk-goal)) 'IN)
                  (in-sep! (lambda () (ass)) (lambda () (ass)))
                  (let* ((l3 (dk-peel!))
                         (xm (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) tcl))) l3))
                         (ef (find-first (dk-head? 'IS-ELEMENTARY) l3))
                         (x (cadr xm)) (e (cadddr ef)))
                    (sep-me xm)
                    (fact 'elementary-type 'R 'n e)
                    (laeg-typ! (laeg-mm x e) (laeg-mat 'n))
                    (in-sep! (lambda () (ass))
                      (lambda () (dk-apply! (dk-ctx-form laeg-closed-S) x e) (ass)))))))))))
  (dk-apply! allp tcl)
  (sep-me (list 'IN p tcl))
  (ass))
(laeg-done! 'elem-gen-induction)
(topic! 'elem-gen-induction 'algebra)

;; run the induction on the class (SEP egq_ MAT BODY): IDENT-THUNK proves BODY[I] (focus
;; on that leaf), STEP-THUNK is called with X, E and proves BODY[X E] with X in MAT,
;; BODY[X] and IS-ELEMENTARY(R, n, E) in context; then for P in ELEM-GEN BODY[P] lands
(define (laeg-induct! body p ident-thunk step-thunk)
  (let* ((S (list 'SEP 'egq_ (laeg-mat 'n) body))
         (cl (list 'FORALL 'egy_ (list 'IMPLIES (list 'IN 'egy_ S)
               (list 'FORALL 'egf_ (list 'IMPLIES '(IS-ELEMENTARY R n egf_)
                 (list 'IN '(MATMUL R egy_ egf_) S)))))))
    (laeg-typ! laeg-I (laeg-mat 'n))
    (dk-have! (list 'IN laeg-I S) (lambda () (in-sep! (lambda () (ass)) ident-thunk)))
    (dk-have! cl
      (lambda ()
        (let* ((l3 (dk-peel!))
               (xm (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) S))) l3))
               (ef (find-first (dk-head? 'IS-ELEMENTARY) l3))
               (x (cadr xm)) (e (cadddr ef)))
          (sep-me xm)
          (fact 'elementary-type 'R 'n e)
          (laeg-typ! (laeg-mm x e) (laeg-mat 'n))
          (in-sep! (lambda () (ass)) (lambda () (step-thunk x e))))))
    (let ((all (dk-fact! 'elem-gen-induction 'R 'n S)))
      (dk-apply! all p)
      (sep-me (list 'IN p S)))))

(sp (make-wff (forall-guarded '(R n P Q)
                (list '(IS-RING R) '(IN n NN) (list 'IN 'P laeg-gen) (list 'IN 'Q laeg-gen))
                (list 'IN (laeg-mm 'P 'Q) laeg-gen))))
(dk-peel!)
(laeg-gen-mat! 'P)
(laeg-induct! (list 'IN '(MATMUL R P egq_) laeg-gen) 'Q
  (lambda ()
    (fact 'identmat-right-identity 'R 'n 'n 'P)
    (subst (list '= (laeg-mm 'P laeg-I) 'P))
    (ass))
  (lambda (x e)
    (laeg-typ! (laeg-mm 'P x) (laeg-mat 'n))
    (laeg-assoc! 'P x e)
    (subst (list '= (laeg-mm 'P (laeg-mm x e)) (laeg-mm (laeg-mm 'P x) e)))
    (fact 'elem-gen-step 'R 'n (laeg-mm 'P x) e)
    (ass)))
(ass)
(laeg-done! 'elem-gen-mul)
(topic! 'elem-gen-mul 'algebra)

(sp (make-wff (forall-guarded '(R n E) '((IS-RING R) (IN n NN) (IS-ELEMENTARY R n E))
                (list 'IN 'E laeg-gen))))
(dk-peel!)
(fact 'elementary-type 'R 'n 'E)
(fact 'elem-gen-identity 'R 'n)
(let ((st (dk-fact! 'elem-gen-step 'R 'n laeg-I 'E)))
  (fact 'identmat-left-identity 'R 'n 'n 'E)
  (dk-rewrite-h! st (laeg-mm laeg-I 'E) 'E))
(ass)
(laeg-done! 'elementary-in-elem-gen)
(topic! 'elementary-in-elem-gen 'algebra)

;; every member of ELEM-GEN has a two-sided inverse in ELEM-GEN
(define (laeg-inv-in-gen x)
  (list 'FORSOME 'egv_ (list 'AND (list 'IN 'egv_ laeg-gen)
    (list 'AND (list '= (laeg-mm x 'egv_) laeg-I) (list '= (laeg-mm 'egv_ x) laeg-I)))))
(sp (make-wff (forall-guarded '(R n P) (list '(IS-RING R) '(IN n NN) (list 'IN 'P laeg-gen))
                (laeg-inv-in-gen 'P))))
(dk-peel!)
(laeg-induct! (laeg-inv-in-gen 'egq_) 'P
  (lambda ()
    (fact 'elem-gen-identity 'R 'n)
    (fact 'identmat-left-identity 'R 'n 'n laeg-I)
    (ew laeg-I)
    (dk-conj-close! (lambda () (ass))))
  (lambda (x e)
    (let* ((v (dk-skolem! (dk-ctx-form (laeg-inv-in-gen x))))
           (w (dk-skolem! (dk-fact! 'elementary-inverse 'R 'n e)))
           (wv (laeg-mm w v)) (xe (laeg-mm x e)))
      (laeg-gen-mat! v)
      (fact 'elementary-type 'R 'n w)
      (fact 'elementary-in-elem-gen 'R 'n w)
      (fact 'elem-gen-mul 'R 'n w v)
      (laeg-typ! wv (laeg-mat 'n))
      (ew wv)
      (dk-conj-close!
        (lambda ()
          (let ((g (dk-goal)))
            (cond ((eq? (car g) 'IN) (ass))
                  ((equal? (cadr g) (laeg-mm xe wv))
                   ;; (X E)(W V) = X (E (W V)) = X ((E W) V) = X (I V) = X V = I
                   (subst (laeg-assoc! x e wv))
                   (laeg-assoc! e w v)
                   (subst (list '= (laeg-mm e wv) (laeg-mm (laeg-mm e w) v)))
                   (subst (list '= (laeg-mm e w) laeg-I))
                   (fact 'identmat-left-identity 'R 'n 'n v)
                   (subst (list '= (laeg-mm laeg-I v) v))
                   (subst (list '= (laeg-mm x v) laeg-I))
                   (rfl))
                  (#t
                   ;; (W V)(X E) = W (V (X E)) = W ((V X) E) = W (I E) = W E = I
                   (subst (laeg-assoc! w v xe))
                   (laeg-assoc! v x e)
                   (subst (list '= (laeg-mm v xe) (laeg-mm (laeg-mm v x) e)))
                   (subst (list '= (laeg-mm v x) laeg-I))
                   (fact 'identmat-left-identity 'R 'n 'n e)
                   (subst (list '= (laeg-mm laeg-I e) e))
                   (subst (list '= (laeg-mm w e) laeg-I))
                   (rfl)))))))))
(ass)
(laeg-done! 'elem-gen-inverse)
(topic! 'elem-gen-inverse 'algebra)

(sp (make-wff (forall-guarded '(R n P) (list '(IS-RING R) '(IN n NN) (list 'IN 'P laeg-gen))
                '(IS-INVERTIBLE-MAT R n P))))
(dk-peel!)
(laeg-gen-mat! 'P)
(let ((v (dk-skolem! (dk-fact! 'elem-gen-inverse 'R 'n 'P))))
  (laeg-gen-mat! v)
  (mac 'IS-INVERTIBLE-MAT)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'FORSOME)
          (begin (ew v) (dk-conj-close! (lambda () (ass))))
          (ass)))))
(laeg-done! 'elem-gen-invertible)
(topic! 'elem-gen-invertible 'algebra)

;; a left inverse equals a right inverse: A P = I and P V = I give A = V
(sp (make-wff (forall-guarded '(R n A P V)
                '((IS-RING R) (IN n NN) (IN A (MAT n n (CARR R))) (IN P (MAT n n (CARR R)))
                  (IN V (MAT n n (CARR R))) (= (MATMUL R A P) (IDENTMAT R n)) (= (MATMUL R P V) (IDENTMAT R n)))
                '(= A V))))
(dk-peel!)
(let* ((e1 (laeg-assoc! 'A 'P 'V))
       (e2 (dk-rewrite-h! e1 (laeg-mm 'A 'P) laeg-I))
       (e3 (dk-rewrite-h! e2 (laeg-mm 'P 'V) laeg-I)))
  (fact 'identmat-left-identity 'R 'n 'n 'V)
  (fact 'identmat-right-identity 'R 'n 'n 'A)
  (let* ((e4 (dk-rewrite-h! e3 (laeg-mm laeg-I 'V) 'V))
         (e5 (dk-rewrite-h! e4 (laeg-mm 'A laeg-I) 'A)))
    (subst '(= A V))
    (rfl)))
(laeg-done! 'mat-left-inverse-eq-right)
(topic! 'mat-left-inverse-eq-right 'algebra)

;;; =====================================================================
;;; (A3) A finite product with a zero factor is zero (over [1, n]).
;;; =====================================================================
;; close ANY goal from contradictory NN facts PREMS
(define (laeg-absurd! prems)
  (dk-have! '(<= 1 0) (lambda () (apply dk-nn! prems)))
  (dk-focus-having! '(<= 1 0))
  (have! '(NOT (<= 1 0)) (lambda () (arith)))
  (dk-focus-having! '(NOT (<= 1 0)))
  (pbc)
  (ai '(NOT (<= 1 0))))

(define (laeg-ptw-typ f dom)
  (list 'FORALL 'pzz_ (list 'IMPLIES (list 'IN 'pzz_ dom) (list 'IN (list f 'pzz_) '(CARR R)))))
(define (laeg-pz-body nv)
  (list 'FORALL 'pzf_ (list 'IMPLIES (laeg-ptw-typ 'pzf_ (laeg-iv nv))
    (list 'FORALL 'pzk_ (list 'IMPLIES (list 'IN 'pzk_ (laeg-iv nv))
      (list 'IMPLIES '(= (pzf_ pzk_) (ZERO R))
        (list '= (list 'PROD-RING 'R 'pzf_ (laeg-iv nv)) '(ZERO R))))))))

(sp (make-wff (list 'FORALL 'pzn_ (list 'IMPLIES '(IN pzn_ NN)
                (forall-guarded '(R) '((IS-COMMUTATIVE-RING R)) (laeg-pz-body 'pzn_))))))
(define laeg-pz-ind (use-induction))
(dk-focus! (cdr (assq 'base laeg-pz-ind)))
(let* ((landed (dk-peel!))
       (km (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) (laeg-iv 0)))) landed))
       (k (cadr km)))
  (fact 'interval-elt-in-nn 1 0 k)
  (fact 'interval-lo 1 0 k)
  (fact 'interval-hi 1 0 k)
  (laeg-absurd! (list (list '<= 1 k) (list '<= k 0))))
(dk-focus! (cdr (assq 'step laeg-pz-ind)))
(let* ((ih (cdr (assq 'ih laeg-pz-ind)))
       (v (cdr (assq 'var laeg-pz-ind)))
       (sv (list 'succ v))
       (I0 (laeg-iv v)) (I1 (laeg-iv sv))
       (U (list 'UNION I0 (list 'PAIR sv sv)))
       (landed (dk-peel!))
       (tf (find-first (dk-head? 'FORALL) landed))
       (fv (car (cadr (caddr (caddr tf)))))
       (km (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) I1))) landed))
       (k (cadr km))
       (P0 (list 'PROD-RING 'R fv I0)))
  (fact 'commutative-ring-is-ring 'R)
  (fact 'nn-succ-closed v)
  (dk-have! (list '<= v sv) (lambda () (dk-nn!)))
  ;; the typing restricted to [1, n]
  (dk-have! (laeg-ptw-typ fv I0)
    (lambda ()
      (let* ((l2 (dk-peel!)) (z (cadr (car l2))))
        (fact 'interval-widen v sv 1 z)
        (dk-apply! tf z)
        (ass))))
  ;; f(n+1) is typed
  (dk-have! (list 'IN sv I1)
    (lambda () (dk-have! (list '<= 1 sv) (lambda () (dk-nn!)))
               (dk-have! (list '<= sv sv) (lambda () (dk-nn!)))
               (fact 'interval-mem-intro 1 sv sv) (ass)))
  (dk-apply! tf sv)
  ;; peel the last factor
  (fact 'interval-in-set 1 v)
  (fact 'interval-card-in-nn 1 v)
  (fact 'membership-implies-sethood sv 'NN)
  (fact 'interval-succ-insert v)
  (dk-have! (list 'NOT (list 'IN sv I0))
    (lambda ()
      (di)
      (fact 'interval-hi 1 v sv)
      (laeg-absurd! (list (list '<= sv v)))))
  (let* ((tu (dk-rewrite-h! tf I1 U))
         (pins (dk-fact! 'prod-ring-insert-ptwise 'R I0 sv fv))
         (pins1 (dk-rewrite-h! pins U I1)))
    (subst pins1))
  (fact 'prod-ring-type-ptwise 'R I0 fv)
  (use-em (list '= k sv)
    (lambda ()
      (subst (list '= sv k))
      (subst (list '= (list fv k) '(ZERO R)))
      (subst (dk-fact! 'ring-mul-zero-right 'R P0))
      (rfl))
    (lambda ()
      (fact 'interval-lo 1 sv k)
      (fact 'interval-hi 1 sv k)
      (fact 'interval-elt-in-nn 1 sv k)
      (dk-have! (list '<= k v) (lambda () (fact 'nn-le-succ-cases v k) (dk-have! (list 'OR (list '<= k v) (list '= k sv)) (lambda () (ass))) (prop)))
      (fact 'interval-mem-intro 1 v k)
      (subst (dk-apply! ih 'R fv k))
      (subst (dk-fact! 'ring-mul-zero-left 'R (list fv sv)))
      (rfl))))
(laeg-done! 'laeg-prod-zero-ind)
(topic! 'laeg-prod-zero-ind 'plumbing)

(sp (make-wff (forall-guarded '(R pzn_) '((IS-COMMUTATIVE-RING R) (IN pzn_ NN)) (laeg-pz-body 'pzn_))))
(let* ((landed (dk-peel!))
       (tf (find-first (dk-head? 'FORALL) landed))
       (fv (car (cadr (caddr (caddr tf)))))
       (km (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) (laeg-iv 'pzn_)))) landed))
       (k (cadr km)))
  (dk-apply! (dk-fact! 'laeg-prod-zero-ind 'pzn_ 'R) fv k)
  (ass))
(laeg-done! 'prod-ring-zero-factor)
(topic! 'prod-ring-zero-factor 'algebra)

;;; =====================================================================
;;; PART B.  The column-step proposition.  The proof runs down the rows: after t
;;; steps the rows 1..t of A P are rows of a REDUCED column step matrix
;;; (COL-STEP-ROW), so in particular they vanish in the columns > t.  Step t+1 works
;;; on row r = t+1 with column operations that touch only columns >= r except for
;;; adding multiples of column r (whose rows 1..t vanish): a swap of two columns >= r
;;; (ELEM-F), scaling column r (ELEM-H), adding a multiple of column r to another
;;; column (ELEM-G).  None of them changes rows 1..t ("AGREE" below), and the pivot
;;; row r is cleared on BOTH sides of the pivot, so that 3.12 needs no second
;;; elimination below the diagonal.
;;; =====================================================================
;; rows 1..t of CX equal those of BX
(define (laeg-agree bx cx t)
  (list 'FORALL 'agi_ (list 'IMPLIES (list 'IN 'agi_ (laeg-iv t))
    (list 'FORALL 'agj_ (list 'IMPLIES (list 'IN 'agj_ (laeg-iv 'n))
      (list '= (list 'ENTRY cx 'agi_ 'agj_) (list 'ENTRY bx 'agi_ 'agj_)))))))
;; rows 1..t of BX vanish in the columns >= t+1
(define (laeg-zr bx t)
  (list 'FORALL 'agi_ (list 'IMPLIES (list 'IN 'agi_ (laeg-iv t))
    (list 'FORALL 'agj_ (list 'IMPLIES (list 'IN 'agj_ (laeg-iv 'n))
      (list 'IMPLIES (list '<= (list 'succ t) 'agj_)
        (list '= (list 'ENTRY bx 'agi_ 'agj_) '(ZERO R))))))))
;; rows 1..t of BX are rows of a reduced column step matrix
(define (laeg-rows bx t)
  (list 'FORALL 'agi_ (list 'IMPLIES (list 'IN 'agi_ (laeg-iv t)) (list 'COL-STEP-ROW 'R 'n bx 'agi_))))
(define laeg-mmn '(MAT m n (CARR R)))

;; the first IF of the goal (preorder)
(define (laeg-find-if e)
  (cond ((not (pair? e)) #f)
        ((and (eq? (car e) 'IF) (= (length e) 4)) e)
        (#t (let loop ((l e))
              (cond ((not (pair? l)) #f)
                    ((laeg-find-if (car l)))
                    (#t (loop (cdr l))))))))
;; resolve the goal's first IF: on the side the context decides, else split on it
(define (laeg-split-if! kt kf)
  (let* ((ift (or (laeg-find-if (dk-goal)) (error "laeg-split-if!: no IF in the goal")))
         (c (cadr ift)))
    (cond ((dk-asm? c) (dk-if-branch! #t ift #f kt))
          ((dk-asm? (list 'NOT c)) (dk-if-branch! #f ift #f kf))
          (#t (use-em c (lambda () (dk-if-branch! #t ift #f kt))
                        (lambda () (dk-if-branch! #f ift #f kf)))))))

;; land (IN i (INTERVAL 1 m)) from (IN i (INTERVAL 1 t)) and t <= m
(define (laeg-widen! i t m)
  (if (not (dk-asm? (list 'IN i (laeg-iv m))))
      (fact 'interval-widen t m 1 i)))
;; land (IN x (INTERVAL a b)) for x, a, b in NN with a <= x <= b decided by dk-nn!
(define (laeg-in-iv! x a b)
  (if (not (dk-asm? (list 'IN x (list 'INTERVAL a b))))
      (dk-have! (list 'IN x (list 'INTERVAL a b))
        (lambda ()
          (dk-have! (list '<= a x) (lambda () (dk-nn!)))
          (dk-have! (list '<= x b) (lambda () (dk-nn!)))
          (fact 'interval-mem-intro a b x)
          (ass)))))
;; the bounds of an interval element, as NN facts
(define (laeg-iv-facts! i a b)
  (fact 'interval-elt-in-nn a b i)
  (fact 'interval-lo a b i)
  (fact 'interval-hi a b i))
;; type an entry of a matrix typed m-by-n in context, i in [1,m], j in [1,n]
(define (laeg-entry-typ! mx i j)
  (laeg-typ! (list 'ENTRY mx i j) '(CARR R)))

;; instantiate the in-context universal F at TERMS, detaching each guard in context;
;; a partial instance ALREADY in context is reused (dk-apply! errors there: inst+ lands
;; nothing).  Returns the final instance.
(define (laeg-app! f . terms)
  (let loop ((f (or (dk-ctx-form f) f)) (ts terms))
    (cond ((and (pair? f) (eq? (car f) 'IMPLIES) (dk-asm? (cadr f)))
           (let ((c (caddr f)))
             (if (dk-asm? c)
                 (loop (dk-ctx-form c) ts)
                 (loop (dk-landed-1 (lambda () (detach! f))) ts))))
          ((null? ts) f)
          (#t
           (let* ((inst (subst-free (quantifier-var f) (car ts) (quantifier-body f)))
                  (have (dk-ctx-form inst)))
             (loop (or have (dk-deepest (lambda () (inst+ f (car ts))))) (cdr ts)))))))
;; the agreement and zero instances at (i, j)
(define (laeg-ag! bx cx t i j)
  (laeg-app! (laeg-agree bx cx t) i j))
(define (laeg-z! bx t i j)
  (laeg-app! (laeg-zr bx t) i j))

;; the common guards of the operation lemmas
(define laeg-op-guards
  (list '(IS-RING R) '(IN m NN) '(IN n NN) '(IN t NN) '(<= t m)
        (list 'IN 'bx laeg-mmn) (list 'IN 'cx laeg-mmn)
        (laeg-agree 'bx 'cx 't) (laeg-zr 'bx 't)))
;; peel an operation lemma down to its entry (i, j); return (i j)
(define (laeg-op-peel!)
  (let* ((landed (dk-peel!))
         (im (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) (laeg-iv 't)))) landed))
         (jm (find-first (lambda (f) (and (eq? (car f) 'IN) (equal? (caddr f) (laeg-iv 'n))
                                          (not (memq (cadr f) '(k l))))) landed)))
    (list (cadr im) (cadr jm))))

;; ---- ELEM-F(k, l), k, l >= t+1: rows 1..t unchanged
(sp (make-wff (forall-guarded '(R m n t bx cx k l)
  (append laeg-op-guards
    '((IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)) (<= (succ t) k) (<= (succ t) l)))
  (laeg-agree 'bx '(MATMUL R cx (ELEM-F R n k l)) 't))))
(let* ((ij (laeg-op-peel!)) (i (car ij)) (j (cadr ij)))
  (laeg-widen! i 't 'm)
  (subst (dk-apply! (dk-fact! 'elem-f-action 'R 'm 'n 'cx 'k 'l) i j))
  (laeg-ag! 'bx 'cx 't i 'k)
  (laeg-ag! 'bx 'cx 't i 'l)
  (laeg-z! 'bx 't i 'k) (laeg-z! 'bx 't i 'l)
  (fact 'ring-zero-in 'R)
  (laeg-split-if!
    (lambda ()                              ; j = k
      (subst (list '= j 'k))
      (subst (list '= (list 'ENTRY 'cx i 'l) (list 'ENTRY 'bx i 'l)))
      (subst (list '= (list 'ENTRY 'bx i 'l) '(ZERO R)))
      (subst (list '= (list 'ENTRY 'bx i 'k) '(ZERO R)))
      (rfl))
    (lambda ()
      (laeg-split-if!
        (lambda ()                          ; j = l
          (subst (list '= j 'l))
          (subst (list '= (list 'ENTRY 'cx i 'k) (list 'ENTRY 'bx i 'k)))
          (subst (list '= (list 'ENTRY 'bx i 'k) '(ZERO R)))
          (subst (list '= (list 'ENTRY 'bx i 'l) '(ZERO R)))
          (rfl))
        (lambda ()
          (laeg-ag! 'bx 'cx 't i j)
          (ass))))))
(laeg-done! 'laeg-op-f-agree)
(topic! 'laeg-op-f-agree 'plumbing)

;; ---- ELEM-H(sc, k), k >= t+1
(sp (make-wff (forall-guarded '(R m n t bx cx sc k)
  (append laeg-op-guards '((IN sc (CARR R)) (IN k (INTERVAL 1 n)) (<= (succ t) k)))
  (laeg-agree 'bx '(MATMUL R cx (ELEM-H R n sc k)) 't))))
(let* ((ij (laeg-op-peel!)) (i (car ij)) (j (cadr ij)))
  (laeg-widen! i 't 'm)
  (subst (dk-apply! (dk-fact! 'elem-h-action 'R 'm 'n 'cx 'sc 'k) i j))
  (laeg-ag! 'bx 'cx 't i 'k)
  (laeg-z! 'bx 't i 'k)
  (fact 'ring-zero-in 'R)
  (laeg-split-if!
    (lambda ()
      (subst (list '= j 'k))
      (subst (list '= (list 'ENTRY 'cx i 'k) (list 'ENTRY 'bx i 'k)))
      (subst (list '= (list 'ENTRY 'bx i 'k) '(ZERO R)))
      (subst (dk-fact! 'ring-mul-zero-left 'R 'sc))
      (rfl))
    (lambda ()
      (laeg-ag! 'bx 'cx 't i j)
      (ass))))
(laeg-done! 'laeg-op-h-agree)
(topic! 'laeg-op-h-agree 'plumbing)

;; ---- ELEM-G(sc, k, l): column l += sc column k, k >= t+1
(sp (make-wff (forall-guarded '(R m n t bx cx sc k l)
  (append laeg-op-guards
    '((IN sc (CARR R)) (IN k (INTERVAL 1 n)) (IN l (INTERVAL 1 n)) (NOT (= k l)) (<= (succ t) k)))
  (laeg-agree 'bx '(MATMUL R cx (ELEM-G R n sc k l)) 't))))
(let* ((ij (laeg-op-peel!)) (i (car ij)) (j (cadr ij)))
  (laeg-widen! i 't 'm)
  (subst (dk-apply! (dk-fact! 'elem-g-action 'R 'm 'n 'cx 'sc 'k 'l) i j))
  (laeg-ag! 'bx 'cx 't i 'k) (laeg-ag! 'bx 'cx 't i 'l)
  (laeg-z! 'bx 't i 'k)
  (fact 'ring-zero-in 'R)
  (laeg-entry-typ! 'bx i 'l)
  (laeg-split-if!
    (lambda ()                              ; j = l
      (subst (list '= j 'l))
      (subst (list '= (list 'ENTRY 'cx i 'k) (list 'ENTRY 'bx i 'k)))
      (subst (list '= (list 'ENTRY 'bx i 'k) '(ZERO R)))
      (subst (list '= (list 'ENTRY 'cx i 'l) (list 'ENTRY 'bx i 'l)))
      (subst (dk-fact! 'ring-mul-zero-left 'R 'sc))
      (subst (dk-fact! 'ring-add-right-id 'R (list 'ENTRY 'bx i 'l)))
      (rfl))
    (lambda ()
      (laeg-ag! 'bx 'cx 't i j)
      (ass))))
(laeg-done! 'laeg-op-g-agree)
(topic! 'laeg-op-g-agree 'plumbing)

;;; =====================================================================
;;; (B1) Column equivalence: reflexive, typed, transitive, one elementary step.
;;; =====================================================================
(define (laeg-ce a b) (list 'COL-EQUIV 'R 'n a b))
(define (laeg-ce-body a b)
  (list 'FORSOME 'cep_ (list 'AND (list 'IN 'cep_ laeg-gen) (list '= b (list 'MATMUL 'R a 'cep_)))))
;; open COL-EQUIV(A, B) in context (it survives); return the witness P, with
;; (IN P (ELEM-GEN R n)) and (= B (MATMUL R A P)) landed
(define (laeg-ce-open! a b)
  (dk-skolem! (dk-project! (laeg-ce-body a b) 'COL-EQUIV (laeg-ce a b))))
;; the field facts every part-B proof wants
(define (laeg-field!)
  (dk-project! '(IS-COMMUTATIVE-RING R) 'is-field-ring-def '(IS-FIELD-RING R))
  (if (not (dk-asm? '(IS-RING R))) (fact 'commutative-ring-is-ring 'R)))
;; close any goal from F and (NOT F) in context; NOTF is the negation
(define (laeg-contra! notf)
  (if (not (eq? (dk-goal) 'FALSITY)) (pbc))
  (ai notf))
;; (<= J (succ V)) in context: split into J <= V (K1) and J = succ V (K2)
(define (laeg-le-succ-cases! j v k1 k2)
  (let ((d (dk-cite! 'nn-le-succ-cases v j)))
    (use-cases d k1 k2)))
;; (A P) Q = A (P Q) for A m-by-n, P, Q n-by-n
(define (laeg-assoc3! a p q)
  (dk-have! '(IMPLIES (= n 0) (OR (= m 0) (AND (= n 0) (= n 0)))) (lambda () (prop)))
  (dk-have! '(IMPLIES (= n 0) (OR (= n 0) (AND (= n 0) (= m 0)))) (lambda () (prop)))
  (dk-cite! 'matmul-assoc 'R 'm 'n 'n 'n a p q))

(sp (make-wff (forall-guarded '(R m n A) (list '(IS-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn))
                (laeg-ce 'A 'A))))
(dk-peel!)
(fact 'elem-gen-identity 'R 'n)
(fact 'identmat-right-identity 'R 'm 'n 'A)
(mac 'COL-EQUIV)
(ew laeg-I)
(dk-conj-close!
  (lambda ()
    (if (eq? (car (dk-goal)) 'IN)
        (ass)
        (begin (subst (list '= (laeg-mm 'A laeg-I) 'A)) (rfl)))))
(laeg-done! 'col-equiv-refl)
(topic! 'col-equiv-refl 'algebra)

(sp (make-wff (forall-guarded '(R m n A B)
                (list '(IS-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn) (laeg-ce 'A 'B))
                (list 'IN 'B laeg-mmn))))
(dk-peel!)
(let ((p (laeg-ce-open! 'A 'B)))
  (laeg-gen-mat! p)
  (subst (list '= 'B (laeg-mm 'A p)))
  (dk-typ-close!))
(laeg-done! 'col-equiv-mat)
(topic! 'col-equiv-mat 'algebra)

(sp (make-wff (forall-guarded '(R m n A B C)
                (list '(IS-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn) (laeg-ce 'A 'B) (laeg-ce 'B 'C))
                (laeg-ce 'A 'C))))
(dk-peel!)
(let* ((p (laeg-ce-open! 'A 'B))
       (q (laeg-ce-open! 'B 'C))
       (pq (laeg-mm p q)))
  (laeg-gen-mat! p)
  (laeg-gen-mat! q)
  (fact 'elem-gen-mul 'R 'n p q)
  (laeg-typ! pq (laeg-mat 'n))
  (laeg-typ! (laeg-mm 'A pq) laeg-mmn)
  (laeg-assoc3! 'A p q)
  (mac 'COL-EQUIV)
  (ew pq)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'IN)
          (ass)
          (begin
            (subst (list '= 'C (laeg-mm 'B q)))
            (subst (list '= 'B (laeg-mm 'A p)))
            (ass))))))
(laeg-done! 'col-equiv-trans)
(topic! 'col-equiv-trans 'algebra)

(sp (make-wff (forall-guarded '(R m n A E)
                (list '(IS-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn) '(IS-ELEMENTARY R n E))
                (laeg-ce 'A '(MATMUL R A E)))))
(dk-peel!)
(fact 'elementary-type 'R 'n 'E)
(fact 'elementary-in-elem-gen 'R 'n 'E)
(laeg-typ! (laeg-mm 'A 'E) laeg-mmn)
(mac 'COL-EQUIV)
(ew 'E)
(dk-conj-close! (lambda () (if (eq? (car (dk-goal)) 'IN) (ass) (rfl))))
(laeg-done! 'col-equiv-elem)
(topic! 'col-equiv-elem 'algebra)

;;; =====================================================================
;;; (B2) Rows of a reduced column step matrix: the invariant's plumbing.
;;; =====================================================================
(define (laeg-csr i x) (list 'COL-STEP-ROW 'R 'n x i))
;; the unfolded COL-STEP-ROW(R, n, X, I), as the vocabulary states it
(define (laeg-csr-parts x i)
  (list 'AND
    (list 'FORALL 'csj_ (list 'IMPLIES '(IN csj_ (INTERVAL 1 n))
      (list 'IMPLIES (list '< i 'csj_) (list '= (list 'ENTRY x i 'csj_) '(ZERO R)))))
    (list 'IMPLIES (list 'IN i '(INTERVAL 1 n))
      (list 'AND (list 'OR (list '= (list 'ENTRY x i i) '(ZERO R)) (list '= (list 'ENTRY x i i) '(ONE R)))
        (list 'IMPLIES (list '= (list 'ENTRY x i i) '(ONE R))
          (list 'FORALL 'csj_ (list 'IMPLIES '(IN csj_ (INTERVAL 1 n))
            (list 'IMPLIES (list 'NOT (list '= 'csj_ i)) (list '= (list 'ENTRY x i 'csj_) '(ZERO R))))))))))
;; with COL-STEP-ROW(R, n, X, I) in context, land its two conjuncts (it survives);
;; return the list (ABOVE REST) of the formulas as the context holds them
(define (laeg-csr-open! x i)
  (let ((body (laeg-csr-parts x i)))
    (if (not (and (dk-asm? (cadr body)) (dk-asm? (caddr body))))
        (dk-split! (dk-project! body 'COL-STEP-ROW (laeg-csr i x))))
    (list (dk-ctx-form (cadr body)) (dk-ctx-form (caddr body)))))

(sp (make-wff (forall-guarded '(R m n t bx)
                (list '(IS-RING R) '(IN m NN) '(IN n NN) '(IN t NN) '(<= t m) (list 'IN 'bx laeg-mmn))
                (laeg-agree 'bx 'bx 't))))
(dk-peel!)
(let* ((g (dk-goal)) (i (caddr (cadr g))) (j (cadddr (cadr g))))
  (laeg-widen! i 't 'm)
  (laeg-entry-typ! 'bx i j)
  (rfl))
(laeg-done! 'laeg-agree-refl)
(topic! 'laeg-agree-refl 'plumbing)

(sp (make-wff (forall-guarded '(R n t bx) (list '(IN n NN) '(IN t NN) (laeg-rows 'bx 't)) (laeg-zr 'bx 't))))
(dk-peel!)
(let* ((g (dk-goal)) (i (caddr (cadr g))) (j (cadddr (cadr g))))
  (laeg-iv-facts! i 1 't)
  (laeg-iv-facts! j 1 'n)
  (fact 'nn-succ-closed 't)
  (dk-have! (list '< i j) (lambda () (dk-nn! (list '<= i 't) (list '<= '(succ t) j))))
  (laeg-app! (laeg-rows 'bx 't) i)
  (let ((parts (laeg-csr-open! 'bx i)))
    (laeg-app! (car parts) j)
    (ass)))
(laeg-done! 'laeg-rows-zr)
(topic! 'laeg-rows-zr 'plumbing)

;; a row of a reduced column step matrix stays one when the row does not change
(sp (make-wff (forall-guarded '(R m n t bx cx i)
                (list '(IS-RING R) '(IN m NN) '(IN n NN) '(IN t NN) '(<= t m)
                      (list 'IN 'bx laeg-mmn) (list 'IN 'cx laeg-mmn) (laeg-agree 'bx 'cx 't)
                      '(IN i (INTERVAL 1 t)) (laeg-csr 'i 'bx))
                (laeg-csr 'i 'cx))))
(dk-peel!)
(laeg-widen! 'i 't 'm)
(let* ((parts (laeg-csr-open! 'bx 'i)) (h1 (car parts)) (h2 (cadr parts)))
  (mac 'COL-STEP-ROW)
  (dk-conj-close!
    (lambda ()
      (if (eq? (car (dk-goal)) 'FORALL)
          (begin
            (dk-peel!)
            (let ((j (cadddr (cadr (dk-goal)))))
              (subst (laeg-ag! 'bx 'cx 't 'i j))
              (laeg-app! h1 j)
              (ass)))
          (begin
            (di)
            (subst (laeg-ag! 'bx 'cx 't 'i 'i))
            (let* ((p (laeg-app! h2)) (ps (dk-split! p))
                   (h2b (find-first (dk-head? 'IMPLIES) ps)))
              (dk-conj-close!
                (lambda ()
                  (if (eq? (car (dk-goal)) 'OR)
                      (ass)
                      (begin
                        (dk-peel!)
                        (let ((j (cadddr (cadr (dk-goal))))
                              (h3 (laeg-app! h2b)))
                          (subst (laeg-ag! 'bx 'cx 't 'i j))
                          (laeg-app! h3 j)
                          (ass))))))))))))
(laeg-done! 'laeg-csr-transfer)
(topic! 'laeg-csr-transfer 'plumbing)

;;; =====================================================================
;;; (B3) The three moves on the pivot row r = t+1 (the notes' lemma): bring a
;;; nonzero entry to the diagonal (ELEM-F), scale it to 1 (ELEM-H), clear the rest
;;; of the row by adding multiples of column r (ELEM-G, an induction over the
;;; columns).  Throughout, BX is the matrix the step started from, whose rows 1..t
;;; vanish in the columns >= r (laeg-zr), and every move keeps rows 1..t of BX.
;;; =====================================================================
(define laeg-r '(succ t))
(define laeg-fr-guards
  (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) '(IN t NN) '(<= (succ t) m) '(<= (succ t) n)
        (list 'IN 'bx laeg-mmn) (laeg-zr 'bx 't)))
(define (laeg-fr-setup!)
  (laeg-field!)
  (fact 'ladet-field-one-ne 'R)
  (fact 'ring-zero-in 'R)
  (fact 'ring-one-in 'R)
  (fact 'nn-succ-closed 't)
  (dk-have! '(<= t m) (lambda () (dk-nn! '(<= (succ t) m))))
  (laeg-in-iv! laeg-r 1 'n)
  (laeg-in-iv! laeg-r 1 'm)
  (dk-have! (list '<= laeg-r laeg-r) (lambda () (dk-nn!)))
  (dk-have! (list '= laeg-r laeg-r) (lambda () (rfl))))
;; column r of D equals column r of CX
(define (laeg-colsame cx d)
  (list 'FORALL 'csa_ (list 'IMPLIES '(IN csa_ (INTERVAL 1 m))
    (list '= (list 'ENTRY d 'csa_ laeg-r) (list 'ENTRY cx 'csa_ laeg-r)))))
;; row r of D vanishes in the columns j <= S other than r
(define (laeg-cleared d s)
  (list 'FORALL 'clj_ (list 'IMPLIES '(IN clj_ (INTERVAL 1 n))
    (list 'IMPLIES (list '<= 'clj_ s)
      (list 'IMPLIES (list 'NOT (list '= 'clj_ laeg-r))
        (list '= (list 'ENTRY d laeg-r 'clj_) '(ZERO R)))))))

;; ---- the pivot: a nonzero entry of row r in a column >= r is brought to (r, r)
(sp (make-wff (forall-guarded '(R m n t bx jz)
  (append laeg-fr-guards
    (list '(IN jz (INTERVAL 1 n)) '(<= (succ t) jz) '(NOT (= (ENTRY bx (succ t) jz) (ZERO R)))))
  (list 'FORSOME 'pvc_ (list 'AND (laeg-ce 'bx 'pvc_) (list 'AND (laeg-agree 'bx 'pvc_ 't)
    (list 'NOT (list '= (list 'ENTRY 'pvc_ laeg-r laeg-r) '(ZERO R)))))))))
(dk-peel!)
(laeg-fr-setup!)
(fact 'col-equiv-refl 'R 'm 'n 'bx)
(fact 'laeg-agree-refl 'R 'm 'n 't 'bx)
(use-em (list '= 'jz laeg-r)
  (lambda ()
    (dk-rewrite-h! '(NOT (= (ENTRY bx (succ t) jz) (ZERO R))) 'jz laeg-r)
    (ew 'bx)
    (dk-conj-close! (lambda () (ass))))
  (lambda ()
    (let* ((E (list 'ELEM-F 'R 'n laeg-r 'jz)) (C (laeg-mm 'bx E)))
      (laeg-ne-sym! 'jz laeg-r)
      (laeg-typ! E (laeg-mat 'n))
      (fact 'elem-f-is-elementary 'R 'n laeg-r 'jz)
      (fact 'col-equiv-elem 'R 'm 'n 'bx E)
      (fact 'laeg-op-f-agree 'R 'm 'n 't 'bx 'bx laeg-r 'jz)
      (laeg-typ! C laeg-mmn)
      (let ((eq (laeg-app! (dk-cite! 'elem-f-action 'R 'm 'n 'bx laeg-r 'jz) laeg-r laeg-r)))
        (ew C)
        (dk-conj-close!
          (lambda ()
            (if (eq? (car (dk-goal)) 'NOT)
                (begin
                  (subst eq)
                  (laeg-split-if! (lambda () (ass)) (lambda () (error "laeg: the pivot IF went false"))))
                (ass))))))))
(laeg-done! 'laeg-step-pivot)
(topic! 'laeg-step-pivot 'plumbing)

;; ---- the scaling: a nonzero (r, r) entry becomes 1
(sp (make-wff (forall-guarded '(R m n t bx cx)
  (append laeg-fr-guards
    (list (list 'IN 'cx laeg-mmn) (laeg-agree 'bx 'cx 't) '(NOT (= (ENTRY cx (succ t) (succ t)) (ZERO R)))))
  (list 'FORSOME 'nmc_ (list 'AND (laeg-ce 'cx 'nmc_) (list 'AND (laeg-agree 'bx 'nmc_ 't)
    (list '= (list 'ENTRY 'nmc_ laeg-r laeg-r) '(ONE R))))))))
(dk-peel!)
(laeg-fr-setup!)
(let ((cv (list 'ENTRY 'cx laeg-r laeg-r)))
  (laeg-entry-typ! 'cx laeg-r laeg-r)
  (let* ((b (dk-skolem! (laeg-app! (dk-cite! 'ladet-field-inverse 'R) cv)))
         (cb (list '(MUL R) cv b))
         (comm (dk-cite! 'commutative-ring-mul-comm 'R b cv))
         (E (list 'ELEM-H 'R 'n b laeg-r))
         (cmat (laeg-mm 'cx E)))
    (dk-rewrite-h! comm cb '(ONE R))
    (fact 'elem-h-is-elementary 'R 'n b cv laeg-r)
    (laeg-typ! E (laeg-mat 'n))
    (laeg-typ! cmat laeg-mmn)
    (fact 'col-equiv-elem 'R 'm 'n 'cx E)
    (fact 'laeg-op-h-agree 'R 'm 'n 't 'bx 'cx b laeg-r)
    (let ((eq (laeg-app! (dk-cite! 'elem-h-action 'R 'm 'n 'cx b laeg-r) laeg-r laeg-r)))
      (ew cmat)
      (dk-conj-close!
        (lambda ()
          (if (eq? (car (dk-goal)) '=)
              (begin
                (subst eq)
                (laeg-split-if! (lambda () (ass)) (lambda () (error "laeg: the scaling IF went false"))))
              (ass)))))))
(laeg-done! 'laeg-step-norm)
(topic! 'laeg-step-norm 'plumbing)

;; ---- the clearing, by induction on the number s of columns treated
(define (laeg-clear-body s)
  (forall-guarded '(R m n t bx cx)
    (append laeg-fr-guards
      (list (list 'IN 'cx laeg-mmn) (laeg-agree 'bx 'cx 't)
            '(= (ENTRY cx (succ t) (succ t)) (ONE R)) (list '<= s 'n)))
    (list 'FORSOME 'clc_ (list 'AND (laeg-ce 'cx 'clc_) (list 'AND (laeg-agree 'bx 'clc_ 't)
      (list 'AND (laeg-colsame 'cx 'clc_) (laeg-cleared 'clc_ s)))))))
(sp (make-wff (list 'FORALL 's (list 'IMPLIES '(IN s NN) (laeg-clear-body 's)))))
(define laeg-cl-ind (use-induction))
(dk-focus! (cdr (assq 'base laeg-cl-ind)))
(dk-peel!)
(laeg-fr-setup!)
(fact 'col-equiv-refl 'R 'm 'n 'cx)
(ew 'cx)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond ((dk-asm? g) (ass))
            ((alpha-equiv? g (laeg-colsame 'cx 'cx))
             (dk-peel!)
             (let ((i (caddr (cadr (dk-goal)))))
               (laeg-entry-typ! 'cx i laeg-r)
               (rfl)))
            (#t
             (dk-peel!)
             (let ((j (cadddr (cadr (dk-goal)))))
               (laeg-iv-facts! j 1 'n)
               (laeg-absurd! (list (list '<= 1 j) (list '<= j 0)))))))))
(dk-focus! (cdr (assq 'step laeg-cl-ind)))
(let* ((ih (cdr (assq 'ih laeg-cl-ind)))
       (v (cdr (assq 'var laeg-cl-ind)))
       (sv (list 'succ v)))
  (dk-peel!)
  (laeg-fr-setup!)
  (fact 'nn-succ-closed v)
  (dk-have! (list '<= v 'n) (lambda () (dk-nn! (list '<= sv 'n))))
  (let ((D (dk-skolem! (laeg-app! ih 'R 'm 'n 't 'bx 'cx))))
    (fact 'col-equiv-mat 'R 'm 'n 'cx D)
    (use-em (list '= sv laeg-r)
      (lambda ()                            ; column s+1 is the pivot column: nothing to do
        (ew D)
        (dk-conj-close!
          (lambda ()
            (if (dk-asm? (dk-goal))
                (ass)
                (begin
                  (dk-peel!)
                  (let ((j (cadddr (cadr (dk-goal)))))
                    (laeg-iv-facts! j 1 'n)
                    (laeg-le-succ-cases! j v
                      (lambda () (laeg-app! (laeg-cleared D v) j) (ass))
                      (lambda ()
                        (dk-rewrite-h! (list '= j sv) sv laeg-r)
                        (laeg-contra! (list 'NOT (list '= j laeg-r)))))))))))
      (lambda ()                            ; column s+1 += (- d_{r,s+1}) column r
        (let* ((x (list 'ENTRY D laeg-r sv)) (nx (list '(NEG R) x))
               (E (list 'ELEM-G 'R 'n nx laeg-r sv)) (C (laeg-mm D E)))
          (laeg-in-iv! sv 1 'n)
          (laeg-entry-typ! D laeg-r sv)
          (fact 'ring-neg-in-carr 'R x)
          (laeg-ne-sym! sv laeg-r)
          (fact 'elem-g-is-elementary 'R 'n nx laeg-r sv)
          (laeg-typ! E (laeg-mat 'n))
          (laeg-typ! C laeg-mmn)
          (fact 'col-equiv-elem 'R 'm 'n D E)
          (fact 'col-equiv-trans 'R 'm 'n 'cx D C)
          (fact 'laeg-op-g-agree 'R 'm 'n 't 'bx D nx laeg-r sv)
          (let ((act (dk-cite! 'elem-g-action 'R 'm 'n D nx laeg-r sv)))
            (ew C)
            (dk-conj-close!
              (lambda ()
                (let ((g (dk-goal)))
                  (cond
                    ((dk-asm? g) (ass))
                    ((alpha-equiv? g (laeg-colsame 'cx C))
                     (dk-peel!)
                     (let ((i (caddr (cadr (dk-goal)))))
                       (subst (laeg-app! act i laeg-r))
                       (laeg-split-if!
                         (lambda () (error "laeg: the clearing IF went true on column r"))
                         (lambda () (laeg-app! (laeg-colsame 'cx D) i) (ass)))))
                    (#t
                     (dk-peel!)
                     (let ((j (cadddr (cadr (dk-goal)))))
                       (laeg-iv-facts! j 1 'n)
                       (subst (laeg-app! act laeg-r j))
                       (laeg-split-if!
                         (lambda ()                ; j = s+1: d + 1 (-d) = 0
                           (laeg-app! (laeg-colsame 'cx D) laeg-r)
                           (subst (list '= (list 'ENTRY D laeg-r laeg-r) (list 'ENTRY 'cx laeg-r laeg-r)))
                           (subst (list '= (list 'ENTRY 'cx laeg-r laeg-r) '(ONE R)))
                           (subst (dk-cite! 'ring-mul-left-id 'R nx))
                           (subst (dk-cite! 'ring-add-right-inv 'R x))
                           (rfl))
                         (lambda ()                ; j /= s+1: untouched, cleared before
                           (laeg-le-succ-cases! j v
                             (lambda () (laeg-app! (laeg-cleared D v) j) (ass))
                             (lambda () (laeg-contra! (list 'NOT (list '= j sv)))))))))))))))))))
(laeg-done! 'laeg-clear-ind)
(topic! 'laeg-clear-ind 'plumbing)

;;; =====================================================================
;;; (B4) One row: rows 1..t of a reduced column step matrix become rows 1..t+1.
;;; =====================================================================
;; some entry of row r in a column >= r is nonzero
(define laeg-piv
  (list 'FORSOME 'pvj_ (list 'AND '(IN pvj_ (INTERVAL 1 n)) (list 'AND (list '<= laeg-r 'pvj_)
    (list 'NOT (list '= (list 'ENTRY 'bx laeg-r 'pvj_) '(ZERO R)))))))
;; goal rows(X, succ t): OLD (called with i) proves COL-STEP-ROW at i in [1, t],
;; LAST proves it at succ t
(define (laeg-rows-succ! x old last)
  (dk-peel!)
  (let ((i (list-ref (dk-goal) 4)))
    (laeg-iv-facts! i 1 laeg-r)
    (laeg-le-succ-cases! i 't
      (lambda () (laeg-in-iv! i 1 't) (old i))
      (lambda () (subst (list '= i laeg-r)) (last)))))
(define (laeg-old-row! x)
  (lambda (i) (laeg-app! (laeg-rows x 't) i) (ass)))

(sp (make-wff (forall-guarded '(R m n t bx)
  (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) '(IN t NN) '(<= (succ t) m)
        (list 'IN 'bx laeg-mmn) (laeg-rows 'bx 't))
  (list 'FORSOME 'rsc_ (list 'AND (laeg-ce 'bx 'rsc_) (laeg-rows 'rsc_ laeg-r))))))
(dk-peel!)
(laeg-field!)
(fact 'ladet-field-one-ne 'R)
(fact 'ring-zero-in 'R)
(fact 'ring-one-in 'R)
(fact 'nn-succ-closed 't)
(dk-have! '(<= t m) (lambda () (dk-nn! '(<= (succ t) m))))
(laeg-in-iv! laeg-r 1 'm)
(fact 'laeg-rows-zr 'R 'n 't 'bx)
(fact 'col-equiv-refl 'R 'm 'n 'bx)
(use-em (list '<= laeg-r 'n)
  (lambda ()
    (laeg-in-iv! laeg-r 1 'n)
    (dk-have! (list '<= laeg-r laeg-r) (lambda () (dk-nn!)))
    (dk-have! '(<= n n) (lambda () (dk-nn!)))
    (use-em laeg-piv
      (lambda ()                            ; a pivot: swap, scale, clear
        (let* ((jz (dk-skolem! (dk-ctx-form laeg-piv)))
               (c1 (dk-skolem! (dk-cite! 'laeg-step-pivot 'R 'm 'n 't 'bx jz))))
          (fact 'col-equiv-mat 'R 'm 'n 'bx c1)
          (let ((c2 (dk-skolem! (dk-cite! 'laeg-step-norm 'R 'm 'n 't 'bx c1))))
            (fact 'col-equiv-mat 'R 'm 'n c1 c2)
            (fact 'col-equiv-trans 'R 'm 'n 'bx c1 c2)
            (let ((c3 (dk-skolem! (laeg-app! (dk-cite! 'laeg-clear-ind 'n) 'R 'm 'n 't 'bx c2))))
              (fact 'col-equiv-mat 'R 'm 'n c2 c3)
              (fact 'col-equiv-trans 'R 'm 'n 'bx c2 c3)
              (ew c3)
              (dk-conj-close!
                (lambda ()
                  (if (dk-asm? (dk-goal))
                      (ass)
                      (laeg-rows-succ! c3
                        (lambda (i)
                          (laeg-app! (laeg-rows 'bx 't) i)
                          (fact 'laeg-csr-transfer 'R 'm 'n 't 'bx c3 i)
                          (ass))
                        (lambda ()
                          (let ((e33 (list 'ENTRY c3 laeg-r laeg-r)) (e22 (list 'ENTRY c2 laeg-r laeg-r)))
                            (laeg-app! (laeg-colsame c2 c3) laeg-r)
                            (dk-rewrite-h! (list '= e33 e22) e22 '(ONE R))
                            (mac 'COL-STEP-ROW)
                            (dk-conj-close!
                              (lambda ()
                                (if (eq? (car (dk-goal)) 'FORALL)
                                    (begin
                                      (dk-peel!)
                                      (let ((j (cadddr (cadr (dk-goal)))))
                                        (laeg-iv-facts! j 1 'n)
                                        (dk-have! (list 'NOT (list '= j laeg-r)) (lambda () (dk-nn! (list '< laeg-r j))))
                                        (laeg-app! (laeg-cleared c3 'n) j)
                                        (ass)))
                                    (begin
                                      (di)
                                      (dk-conj-close!
                                        (lambda ()
                                          (if (eq? (car (dk-goal)) 'OR)
                                              (begin (oi-r) (ass))
                                              (begin
                                                (dk-peel!)
                                                (let ((j (cadddr (cadr (dk-goal)))))
                                                  (laeg-iv-facts! j 1 'n)
                                                  (laeg-app! (laeg-cleared c3 'n) j)
                                                  (ass))))))))))))))))))))
      (lambda ()                            ; no pivot: row r already vanishes from r on
        (let ((zero-at
                (lambda (j)
                  (pbc)
                  (dk-have! laeg-piv (lambda () (ew j) (dk-conj-close! (lambda () (ass)))))
                  (laeg-contra! (list 'NOT laeg-piv)))))
          (ew 'bx)
          (dk-conj-close!
            (lambda ()
              (if (dk-asm? (dk-goal))
                  (ass)
                  (laeg-rows-succ! 'bx (laeg-old-row! 'bx)
                    (lambda ()
                      (mac 'COL-STEP-ROW)
                      (dk-conj-close!
                        (lambda ()
                          (if (eq? (car (dk-goal)) 'FORALL)
                              (begin
                                (dk-peel!)
                                (let ((j (cadddr (cadr (dk-goal)))))
                                  (laeg-iv-facts! j 1 'n)
                                  (dk-have! (list '<= laeg-r j) (lambda () (dk-nn! (list '< laeg-r j))))
                                  (zero-at j)))
                              (let ((err (list 'ENTRY 'bx laeg-r laeg-r)))
                                (di)
                                (dk-have! (list '= err '(ZERO R)) (lambda () (zero-at laeg-r)))
                                (dk-conj-close!
                                  (lambda ()
                                    (if (eq? (car (dk-goal)) 'OR)
                                        (begin (oi-l) (ass))
                                        (begin
                                          (dk-peel!)
                                          (dk-rewrite-h! (list '= err '(ONE R)) err '(ZERO R))
                                          (laeg-ne-sym! '(ONE R) '(ZERO R))
                                          (laeg-contra! '(NOT (= (ZERO R) (ONE R)))))))))))))))))))))
  (lambda ()                                ; r > n: row r has no column >= r
    (ew 'bx)
    (dk-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal))
            (ass)
            (laeg-rows-succ! 'bx (laeg-old-row! 'bx)
              (lambda ()
                (mac 'COL-STEP-ROW)
                (dk-conj-close!
                  (lambda ()
                    (dk-peel!)
                    (if (dk-asm? (list 'IN laeg-r '(INTERVAL 1 n)))
                        (fact 'interval-hi 1 'n laeg-r)
                        (let ((j (cadddr (cadr (dk-goal)))))
                          (laeg-iv-facts! j 1 'n)
                          (dk-have! (list '<= laeg-r 'n) (lambda () (dk-nn! (list '< laeg-r j) (list '<= j 'n))))))
                    (laeg-contra! (list 'NOT (list '<= laeg-r 'n))))))))))))
(laeg-done! 'laeg-row-step)
(topic! 'laeg-row-step 'plumbing)

;;; =====================================================================
;;; (B5) The column-step proposition, by induction on the number of rows treated.
;;; =====================================================================
(sp (make-wff (list 'FORALL 't (list 'IMPLIES '(IN t NN)
  (forall-guarded '(R m n A) (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) '(<= t m) (list 'IN 'A laeg-mmn))
    (list 'FORSOME 'mnc_ (list 'AND (laeg-ce 'A 'mnc_) (laeg-rows 'mnc_ 't))))))))
(define laeg-cs-ind (use-induction))
(dk-focus! (cdr (assq 'base laeg-cs-ind)))
(dk-peel!)
(laeg-field!)
(fact 'col-equiv-refl 'R 'm 'n 'A)
(ew 'A)
(dk-conj-close!
  (lambda ()
    (if (dk-asm? (dk-goal))
        (ass)
        (begin
          (dk-peel!)
          (let ((i (list-ref (dk-goal) 4)))
            (laeg-iv-facts! i 1 0)
            (laeg-absurd! (list (list '<= 1 i) (list '<= i 0))))))))
(dk-focus! (cdr (assq 'step laeg-cs-ind)))
(let* ((ih (cdr (assq 'ih laeg-cs-ind)))
       (v (cdr (assq 'var laeg-cs-ind)))
       (sv (list 'succ v)))
  (dk-peel!)
  (laeg-field!)
  (fact 'nn-succ-closed v)
  (dk-have! (list '<= v 'm) (lambda () (dk-nn! (list '<= sv 'm))))
  (let ((c1 (dk-skolem! (laeg-app! ih 'R 'm 'n 'A))))
    (fact 'col-equiv-mat 'R 'm 'n 'A c1)
    (let ((c2 (dk-skolem! (dk-cite! 'laeg-row-step 'R 'm 'n v c1))))
      (fact 'col-equiv-mat 'R 'm 'n c1 c2)
      (fact 'col-equiv-trans 'R 'm 'n 'A c1 c2)
      (ew c2)
      (dk-conj-close! (lambda () (ass))))))
(laeg-done! 'laeg-colstep-ind)
(topic! 'laeg-colstep-ind 'plumbing)

;; every m-by-n matrix over a field is column equivalent to a REDUCED column step
;; matrix: each row is zero right of the diagonal, and a diagonal 1 is alone in its row
(sp (make-wff (forall-guarded '(R m n A) (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn))
  (list 'FORSOME 'csc_ (list 'AND (laeg-ce 'A 'csc_) (laeg-rows 'csc_ 'm))))))
(dk-peel!)
(dk-have! '(<= m m) (lambda () (dk-nn!)))
(laeg-app! (dk-cite! 'laeg-colstep-ind 'm) 'R 'm 'n 'A)
(ass)
(laeg-done! 'column-step-reduced)
(topic! 'column-step-reduced 'algebra)
(gloss! 'column-step-reduced
  "Over a field, every m-by-n matrix A is column equivalent to a matrix C each of whose rows is a
   row of a reduced column step matrix: zero to the right of the diagonal, the diagonal entry 0
   or 1, and a diagonal 1 the only nonzero entry of its row.")

(sp (make-wff (forall-guarded '(R m n C) (list '(IN m NN) '(IN n NN) (laeg-rows 'C 'm))
                '(IS-COLUMN-STEP R m n C))))
(dk-peel!)
(mac 'IS-COLUMN-STEP)
(dk-conj-close!
  (lambda ()
    (dk-peel!)
    (let ((g (dk-goal)))
      (if (eq? (car g) 'OR)
          (let* ((i (caddr (cadr (cadr g)))))
            (laeg-app! (laeg-rows 'C 'm) i)
            (let* ((parts (laeg-csr-open! 'C i))
                   (ps (dk-split! (laeg-app! (cadr parts)))))
              (ass)))
          (let* ((i (caddr (cadr g))) (j (cadddr (cadr g))))
            (laeg-app! (laeg-rows 'C 'm) i)
            (laeg-app! (car (laeg-csr-open! 'C i)) j)
            (ass))))))
(laeg-done! 'laeg-rows-colstep)
(topic! 'laeg-rows-colstep 'plumbing)

;; the notes' proposition before 3.12 (over a field, as the lemma it rests on says)
(sp (make-wff (forall-guarded '(R m n A) (list '(IS-FIELD-RING R) '(IN m NN) '(IN n NN) (list 'IN 'A laeg-mmn))
  '(FORSOME cse_ (AND (COL-EQUIV R n A cse_) (IS-COLUMN-STEP R m n cse_))))))
(dk-peel!)
(let ((c (dk-skolem! (dk-cite! 'column-step-reduced 'R 'm 'n 'A))))
  (fact 'laeg-rows-colstep 'R 'm 'n c)
  (ew c)
  (dk-conj-close! (lambda () (ass))))
(laeg-done! 'column-step-exists)
(topic! 'column-step-exists 'algebra)
(gloss! 'column-step-exists
  "Over a field, every m-by-n matrix is column equivalent to a column step matrix: zero above the
   diagonal, each diagonal entry 0 or 1 (the proposition before linear-algebra 3.12).")

;;; =====================================================================
;;; (C) 3.12 and 3.13.
;;; =====================================================================
;; A column equivalent to I is in ELEM-GEN: I = A P gives A = P^-1
(sp (make-wff (forall-guarded '(R n A)
                (list '(IS-RING R) '(IN n NN) (list 'IN 'A (laeg-mat 'n)) (laeg-ce 'A laeg-I))
                (list 'IN 'A laeg-gen))))
(dk-peel!)
(let* ((p (laeg-ce-open! 'A laeg-I))
       (ignore (laeg-gen-mat! p))
       (v (dk-skolem! (dk-cite! 'elem-gen-inverse 'R 'n p))))
  (laeg-gen-mat! v)
  (dk-have! (list '= (laeg-mm 'A p) laeg-I)
    (lambda () (subst (list '= (laeg-mm 'A p) laeg-I)) (rfl)))
  (fact 'mat-left-inverse-eq-right 'R 'n 'A p v)
  (subst (list '= 'A v))
  (ass))
(laeg-done! 'col-equiv-identity-in-elem-gen)
(topic! 'col-equiv-identity-in-elem-gen 'algebra)

;; an invertible n-square matrix all of whose rows are rows of a reduced column step
;; matrix is I: det = product of the diagonal /= 0, so the diagonal is 1, so the rest is 0
(define laeg-dfun '(VNB-LAMBDA dgk_ (INTERVAL 1 n) (ENTRY C dgk_ dgk_)))
(define laeg-diag1 '(FORALL dgq_ (IMPLIES (IN dgq_ (INTERVAL 1 n)) (= (ENTRY C dgq_ dgq_) (ONE R)))))
(sp (make-wff (forall-guarded '(R n C)
                (list '(IS-FIELD-RING R) '(IN n NN) (list 'IN 'C (laeg-mat 'n)) '(IS-INVERTIBLE-MAT R n C)
                      (laeg-rows 'C 'n))
                (list '= 'C laeg-I))))
(dk-peel!)
(laeg-field!)
(fact 'ladet-field-one-ne 'R)
(fact 'ring-zero-in 'R)
(fact 'ring-one-in 'R)
(laeg-typ! laeg-I (laeg-mat 'n))
(let ((iff (dk-cite! 'invertible-iff-det-nonzero 'R 'n 'C)))
  (dk-have! '(NOT (= (DET R n C) (ZERO R)))
    (lambda () (dk-only! iff '(IS-INVERTIBLE-MAT R n C)) (prop))))
(dk-have! '(IS-LOWER-TRIANGULAR R n C)
  (lambda ()
    (mac 'IS-LOWER-TRIANGULAR)
    (dk-peel!)
    (let* ((g (dk-goal)) (i (caddr (cadr g))) (j (cadddr (cadr g))))
      (laeg-app! (laeg-rows 'C 'n) i)
      (laeg-app! (car (laeg-csr-open! 'C i)) j)
      (ass))))
(let ((dprod (dk-cite! 'det-lower-triangular 'R 'n 'C))
      (prod (list 'PROD-RING 'R laeg-dfun '(INTERVAL 1 n))))
  (dk-have! laeg-diag1
    (lambda ()
      (dk-peel!)
      (let* ((k (caddr (cadr (dk-goal))))
             (ignore (laeg-app! (laeg-rows 'C 'n) k))
             (parts (laeg-csr-open! 'C k))
             (ps (dk-split! (laeg-app! (cadr parts))))
             (orf (find-first (dk-head? 'OR) ps)))
        (use-cases orf
          (lambda ()                        ; C_kk = 0: the product vanishes
            (dk-have! (laeg-ptw-typ laeg-dfun '(INTERVAL 1 n))
              (lambda ()
                (dk-peel!)
                (let ((z (cadr (cadr (dk-goal)))))
                  (dk-lam-b!)
                  (dk-typ-close!))))
            (dk-have! (list '= (list laeg-dfun k) '(ZERO R)) (lambda () (dk-lam-b!) (ass)))
            (laeg-app! (dk-cite! 'prod-ring-zero-factor 'R 'n) laeg-dfun k)
            (dk-rewrite-h! dprod prod '(ZERO R))
            (laeg-contra! '(NOT (= (DET R n C) (ZERO R)))))
          (lambda () (ass)))))))
(dk-have! '(FORALL exi_ (IMPLIES (IN exi_ (INTERVAL 1 n)) (FORALL exj_ (IMPLIES (IN exj_ (INTERVAL 1 n))
             (= (ENTRY C exi_ exj_) (ENTRY (IDENTMAT R n) exi_ exj_))))))
  (lambda ()
    (dk-peel!)
    (let* ((g (dk-goal)) (i (caddr (cadr g))) (j (cadddr (cadr g))))
      (laeg-app! laeg-diag1 i)
      (laeg-app! (laeg-rows 'C 'n) i)
      (let* ((parts (laeg-csr-open! 'C i))
             (ps (dk-split! (laeg-app! (cadr parts))))
             (h3 (laeg-app! (find-first (dk-head? 'IMPLIES) ps))))
        (use-em (list '= i j)
          (lambda ()
            (subst (list '= j i))
            (subst (list '= (list 'ENTRY 'C i i) '(ONE R)))
            (subst (dk-cite! 'identmat-entry-diag 'R 'n i))
            (rfl))
          (lambda ()
            (laeg-ne-sym! i j)
            (subst (laeg-app! h3 j))
            (subst (dk-cite! 'identmat-entry-off 'R 'n i j))
            (rfl)))))))
(fact 'matrix-entry-extensionality 'n 'n '(CARR R) 'C laeg-I)
(ass)
(laeg-done! 'laeg-reduced-invertible-identity)
(topic! 'laeg-reduced-invertible-identity 'plumbing)

;; ---- Corollary 3.12
(sp (make-wff (forall-guarded '(R n A) (list '(IS-FIELD-RING R) '(IN n NN) (list 'IN 'A (laeg-mat 'n)))
                (list 'IFF '(IS-INVERTIBLE-MAT R n A) (laeg-ce 'A laeg-I)))))
(dk-peel!)
(laeg-field!)
(dk-iff! (dk-head? 'COL-EQUIV)
  (lambda ()
    (let* ((c (dk-skolem! (dk-cite! 'column-step-reduced 'R 'n 'n 'A)))
           (p (laeg-ce-open! 'A c))
           (ap (laeg-mm 'A p)))
      (laeg-gen-mat! p)
      (fact 'elem-gen-invertible 'R 'n p)
      (fact 'product-of-invertibles-is-invertible 'R 'n 'A p)
      (dk-rewrite-h! (list 'IS-INVERTIBLE-MAT 'R 'n ap) ap c)
      (fact 'col-equiv-mat 'R 'n 'n 'A c)
      (fact 'laeg-reduced-invertible-identity 'R 'n c)
      (dk-rewrite-h! (laeg-ce 'A c) c laeg-I)
      (ass)))
  (lambda ()
    (fact 'col-equiv-identity-in-elem-gen 'R 'n 'A)
    (fact 'elem-gen-invertible 'R 'n 'A)
    (ass)))
(laeg-done! 'invertible-iff-col-equiv-identity)
(topic! 'invertible-iff-col-equiv-identity 'algebra)
(gloss! 'invertible-iff-col-equiv-identity
  "Over a field, an n-by-n matrix is invertible iff it is column equivalent to the identity
   matrix (linear-algebra 3.12).")

;; ---- Corollary 3.13
(sp (make-wff (forall-guarded '(R n A) (list '(IS-FIELD-RING R) '(IN n NN) (list 'IN 'A (laeg-mat 'n)))
                (list 'IFF '(IS-INVERTIBLE-MAT R n A) (list 'IN 'A laeg-gen)))))
(dk-peel!)
(laeg-field!)
(let ((iff (dk-cite! 'invertible-iff-col-equiv-identity 'R 'n 'A)))
  (dk-iff! (dk-head? 'IN)
    (lambda ()
      (dk-have! (laeg-ce 'A laeg-I) (lambda () (dk-only! iff '(IS-INVERTIBLE-MAT R n A)) (prop)))
      (fact 'col-equiv-identity-in-elem-gen 'R 'n 'A)
      (ass))
    (lambda ()
      (fact 'elem-gen-invertible 'R 'n 'A)
      (ass))))
(laeg-done! 'invertible-iff-elem-gen)
(topic! 'invertible-iff-elem-gen 'algebra)
(gloss! 'invertible-iff-elem-gen
  "Over a field, an n-by-n matrix is invertible iff it is a product of elementary column matrices,
   i.e. the elementary column matrices generate the invertible matrices (linear-algebra 3.13).")
