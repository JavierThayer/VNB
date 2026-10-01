;;; matof-in-mat.scm -- the tabulated matrix MATOF(m,n,g) is an m-by-n matrix
;;; over X when every value g(i,j) on the index box [1,m] x [1,n] lies in X.
;;;
;;;   forall m n X g.
;;;     m in NN  =>  n in NN  =>
;;;     (forall i in [1,m]. forall j in [1,n]. g(i,j) in X)
;;;       =>  MATOF(m,n,g) in MAT(m,n,X)
;;;
;;; GUARDED 2026-09-15 (soundness repair), final form 2026-09-16.  The two
;;; dimension guards are not decoration: without them the statement is FALSE,
;;; because `mat-rows-in-nn' reads `m in NN' out of any member of MAT(m,n,X) and
;;; `m' here was universally quantified with nothing said about it --
;;; instantiate at ORD and burali-forti contradicts the result.  They come in
;;; from `matof-exists', which carries them for the same reason and is PROVEN
;;; (theorem-library/tuple-tabulation.scm).  The wave-8 form also carried
;;; `1 <= m'; since the SIZE/MAT change of 2026-09-16 the matrix with no rows
;;; is a member of MAT(0, n, X), matof-exists covers m = 0, and the guard is gone.
;;;
;;; PROVEN from the definition of MATOF (matrix.scm): an IOTA over
;;; MAT(m, n, IMAGE(g, box)).  The description is pinned down by the two facts
;;; matrix.scm names for it -- `matof-exists' (existence) and
;;; `matrix-entry-extensionality' (uniqueness) -- and the typing is then a
;;; MONOTONICITY theorem: MAT(m,n,Y) is inside MAT(m,n,X) whenever Y is inside
;;; X.  That monotonicity is what the tree did not state (mat-basics.scm:52:
;;; "monotonicity of TUPLES ... the library states neither"), and it is proved
;;; here in three storeys:
;;;
;;;   tuples-mono    A inside B  =>  TUPLES(A)   inside TUPLES(B)   [tuples-induction]
;;;   matrix-mono    A inside B  =>  MATRIX(A)   inside MATRIX(B)   [matrix-membership, tuples-mono twice]
;;;   mat-mono       A inside B  =>  MAT(m,n,A)  inside MAT(m,n,B)  [mat-unfold, sep-me / sep-mi, matrix-mono]
;;;
;;; "A inside B" is written out as (FORALL w (IMPLIES (IN w A) (IN w B))) so
;;; that no SUBSET unfolding is owed at any call site.
;;;
;;; The inclusion IMAGE(g, box) inside X comes from the entry hypothesis, NOT
;;; from `image-subset-codomain': that axiom is guarded on g in FUN(box, X),
;;; and g here is an arbitrary functoid.  Instead: image-membership-iff gives
;;; w = g(x) for some x in the box, cartesian-decompose gives x = [a, b] with
;;; a in [1,m], b in [1,n], and apply-tupling-2 bridges g(a,b) to g([a,b]).
;;;
;;; THE BILL, stated up front.  Beyond the two facts the plan allows
;;; (matof-exists, matrix-entry-extensionality), the proof bills what the
;;; three storeys cost: `tuples-induction' is proven but bills
;;; `tuple-length-zero' and `tuple-cons-decompose' (list-recursion.scm, both
;;; well-known supports, both flagged there as candidates for the primitive
;;; shelf), and `cartesian-decompose' is a procedural macete carrying a
;;; well-known warrant (finsum-fiber.scm) because it is the membership schema
;;; of the product and has no provenance stamp.  Every one of these is a
;;; generation/membership principle for a base constructor, not a matrix fact.
;;;
;;; Load window: after theorem-library/tuples-induction (the latest citation;
;;; mat-basics, equality-basics, list-recursion, injection and axioms all load
;;; earlier) and before theorem-library/span-bricks2-proof, the earliest citer
;;; of matof-in-mat (`bc*').  Helper prefix: mim-.

;;; --------------------------------------------------------------------
;;; helpers

;; The conclusion under all leading FORALL/IMPLIES -- the handle used to tell
;; look-alike universals apart (CLAUDE.md: discriminate on the CONSEQUENT).
(define (mim-final f)
  (if (and (pair? f) (memq (car f) '(FORALL IMPLIES))) (mim-final (caddr f)) f))

;; Skolemize every FORSOME in the context, one binder per step, to exhaustion.
(define (mim-skolem-all!)
  (let lp ((k 0))
    (let ((ex (any-pred (dk-head? 'FORSOME) (dk-asms))))
      (if ex
          (if (> k 8)
              (error "mim-skolem-all!: runaway skolemization")
              (begin (dk-skolem! ex) (lp (+ k 1))))))))

;; The separation MAT(m,n,X) unfolds to (mat-unfold, mat-basics.scm).  The SEP
;; binder is P, as in matrix.scm; the quantified matrix below is Q for that
;; reason (mat-basics does the same).
(define (mim-sep-of m n x)
  (list 'SEP 'P (list 'MATRIX x)
        (list 'AND
              (list 'IN n 'NN)
              (list 'AND
                    (list 'IMPLIES '(= (LENGTH P) 0) (list '= m 0))
                    (list 'IMPLIES '(NOT (= (LENGTH P) 0)) (list '= '(SIZE P) (list 'LIST m n)))))))

;; The in-context universal whose consequent is (IN v SET-OF-SHAPE ...) with
;; the given member and a set NOT equal to `not-this'.
(define (mim-pick-membership v head not-this what)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'IN) (equal? (cadr f) v)
                  (pair? (caddr f)) (eq? (car (caddr f)) head)
                  (not (equal? (caddr f) not-this))))
           what))

;; The in-context inclusion (FORALL w (IMPLIES (IN w A) (IN w B))) for the given B.
(define (mim-pick-inclusion bb)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (equal? (mim-final f) (list 'IN (cadr f) bb))))
           "the inclusion A inside B"))

;;; --------------------------------------------------------------------
;;; tuples-mono:  A inside B  =>  every tuple over A is a tuple over B.
;;;
;;; By tuples-induction at the class C := TUPLES(B): [] is a tuple over B
;;; (empty-in-tuples), and if x in A and M is a tuple over B then CONS(x, M)
;;; is (x in B by the inclusion, then cons-in-tuples).

(sp (make-wff '(FORALL A (FORALL B
   (IMPLIES (FORALL w (IMPLIES (IN w A) (IN w B)))
     (FORALL L (IMPLIES (IN L (TUPLES A)) (IN L (TUPLES B)))))))))
(dk-peel!)
(let* ((g   (dk-goal))                                   ; (IN L (TUPLES B))
       (ll  (cadr g))
       (bb  (cadr (caddr g)))
       (hyp (mim-pick-membership ll 'TUPLES (caddr g) "L in TUPLES(A)"))
       (aa  (cadr (caddr hyp)))
       (sub (mim-pick-inclusion bb))
       (imp (dk-fact! 'tuples-induction aa (list 'TUPLES bb))))
  (if (not (and (pair? imp) (eq? (car imp) 'IMPLIES)))
      (error "tuples-mono: tuples-induction did not land its implication" imp))
  ;; the two induction premises, as one conjunction
  (have! (cadr imp)
    (lambda ()
      (dk-conj-close!
       (lambda ()
         (let ((g2 (dk-goal)))
           (if (eq? (car g2) 'IN)
               (begin (fact 'empty-in-tuples bb) (ass))          ; [] in TUPLES(B)
               (begin                                            ; the CONS step
                 (dk-peel!)
                 (dk-split-all!)
                 (let* ((g3 (dk-goal))                           ; (IN (CONS x M) (TUPLES B))
                        (x0 (cadr (cadr g3)))
                        (m0 (caddr (cadr g3))))
                   (inst*! sub x0)                               ; x in B
                   (have! (list 'AND (list 'IN x0 bb) (list 'IN m0 (list 'TUPLES bb))))
                   (fact 'cons-in-tuples bb x0 m0)
                   (ass)))))))))
  (let ((all (dk-apply! imp)))                            ; (FORALL L ...)
    (inst*! all ll)
    (ass)))
(qed 'tuples-mono)
(topic! 'tuples-mono 'plumbing)

;;; --------------------------------------------------------------------
;;; matrix-mono:  A inside B  =>  every matrix over A is a matrix over B.
;;;
;;; matrix-membership on both sides: the tuple-of-tuples conjunct is
;;; tuples-mono applied twice (at A, B and then at TUPLES(A), TUPLES(B)); the
;;; equilong-rows conjunct does not mention the set and is the same formula.

(sp (make-wff '(FORALL A (FORALL B
   (IMPLIES (FORALL w (IMPLIES (IN w A) (IN w B)))
     (FORALL M (IMPLIES (IN M (MATRIX A)) (IN M (MATRIX B)))))))))
(dk-peel!)
(let* ((g   (dk-goal))                                   ; (IN M (MATRIX B))
       (mm  (cadr g))
       (bb  (cadr (caddr g)))
       (hyp (mim-pick-membership mm 'MATRIX (caddr g) "M in MATRIX(A)"))
       (aa  (cadr (caddr hyp))))
  (mac 'matrix-membership)                                ; goal -> the AND
  (dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership hyp))))
  ;; TUPLES(A) inside TUPLES(B), then one storey up
  (have! (list 'FORALL 'w (list 'IMPLIES (list 'IN 'w (list 'TUPLES aa))
                                         (list 'IN 'w (list 'TUPLES bb))))
    (lambda () (fact 'tuples-mono aa bb) (ass)))
  (let ((fl (dk-fact! 'tuples-mono (list 'TUPLES aa) (list 'TUPLES bb))))
    (inst*! fl mm))                                       ; (IN M (TUPLES (TUPLES B)))
  (dk-conj-close!))
(qed 'matrix-mono)
(topic! 'matrix-mono 'plumbing)

;;; --------------------------------------------------------------------
;;; mat-mono:  A inside B  =>  MAT(m,n,A) inside MAT(m,n,B).
;;;
;;; mat-basics.scm's recipe on the hypothesis (mat-unfold, subst, sep-me), the
;;; functoid unfold on the goal (mac MAT, sep-mi); the MATRIX conjunct is
;;; matrix-mono, the shape conjunct is the same formula (it does not mention X).

(sp (make-wff '(FORALL m (FORALL n (FORALL A (FORALL B
   (IMPLIES (FORALL w (IMPLIES (IN w A) (IN w B)))
     (FORALL Q (IMPLIES (IN Q (MAT m n A)) (IN Q (MAT m n B)))))))))))
(dk-peel!)
(let* ((g     (dk-goal))                                 ; (IN Q (MAT m n B))
       (qq    (cadr g))
       (mat-b (caddr g))
       (mm    (cadr mat-b))
       (nn    (caddr mat-b))
       (bb    (cadddr mat-b))
       (hyp   (mim-pick-membership qq 'MAT mat-b "Q in MAT(m,n,A)"))
       (aa    (cadddr (caddr hyp)))
       (sep-a (mim-sep-of mm nn aa)))
  (fact 'mat-unfold mm nn aa)
  (have! (list 'IN qq sep-a)
    (lambda () (subst (list '== sep-a (list 'MAT mm nn aa))) (ass)))
  (sep-me (list 'IN qq sep-a))                            ; Q in MATRIX(A), SIZE(Q) = [m,n]
  (let ((fm (dk-fact! 'matrix-mono aa bb)))               ; (FORALL M ...)
    (inst*! fm qq))                                       ; Q in MATRIX(B)
  (mac 'MAT)                                              ; goal -> Q in the separation over B
  (for-each (lambda (l) (dk-focus! l) (ass))
            (dk-opened (lambda () (sep-mi)))))
(qed 'mat-mono)
(topic! 'mat-mono 'plumbing)

;;; --------------------------------------------------------------------
;;; matof-in-mat -- the statement, verbatim from matrix.scm.

;; The main branch of iota-d: the defining property of the description is in
;; the context; read MATOF(m,n,g) in MAT(m,n,IMAGE g box) off it and move it
;; to MAT(m,n,X) by mat-mono, whose inclusion premise was cut earlier.
(define (mim-main! mm nn xx img io)
  (let ((dp (dk-pick (lambda (f)
                       (and (pair? f) (eq? (car f) 'AND)
                            (equal? (cadr f) (list 'IN io (list 'MAT mm nn img)))))
                     "the defining property of the description")))
    (dk-split! dp)
    (let ((fq (dk-fact! 'mat-mono mm nn img xx)))         ; (FORALL Q ...), inclusion detached
      (inst*! fq io)
      (ass))))

;; The in-context entry law of a matrix t:  forall i j. ENTRY(t,i,j) = g(i,j).
(define (mim-entry-law t)
  (dk-pick (lambda (f)
             (and (pair? f) (eq? (car f) 'FORALL)
                  (let ((c (mim-final f)))
                    (and (pair? c) (eq? (car c) '=)
                         (pair? (cadr c)) (eq? (car (cadr c)) 'ENTRY)
                         (equal? (cadr (cadr c)) t)))))
           "the entry law"))

;; Uniqueness: any y with the defining property equals the witness p0, by
;; matrix-entry-extensionality over IMAGE(g, box) -- both are matrices there,
;; and their entries are both g(i,j).
(define (mim-unique! mm nn gg img p0)
  (dk-peel!)                                              ; y, then its property (an AND)
  (dk-split-all!)
  (let* ((g    (dk-goal))                                 ; (= p0 y)
         (y    (caddr g))
         (ent0 (mim-entry-law p0))
         (enty (mim-entry-law y))
         (eqs  (list 'FORALL 'i (list 'IMPLIES (list 'IN 'i (list 'INTERVAL 1 mm))
                 (list 'FORALL 'j (list 'IMPLIES (list 'IN 'j (list 'INTERVAL 1 nn))
                   (list '= (list 'ENTRY p0 'i 'j) (list 'ENTRY y 'i 'j))))))))
    (have! eqs
      (lambda ()
        (dk-peel!)
        (let* ((g2 (dk-goal))                              ; (= (ENTRY p0 i j) (ENTRY y i j))
               (i  (caddr  (cadr g2)))
               (j  (cadddr (cadr g2))))
          (inst*! ent0 i j)                                ; ENTRY(p0,i,j) = g(i,j)
          (inst*! enty i j)                                ; ENTRY(y,i,j)  = g(i,j)
          (fact 'eq-sym   (list 'ENTRY y i j) (list gg i j))
          (fact 'eq-trans (list 'ENTRY p0 i j) (list gg i j) (list 'ENTRY y i j))
          (ass))))
    (fact 'matrix-entry-extensionality mm nn img p0 y)     ; all three premises in context
    (ass)))

;; The existence-and-uniqueness obligation iota-d posts:
;;   FORSOME P. property(P) and forall y. property(y) => P = y.
;; matof-exists is GUARDED (2026-09-15): beside the two dimension guards, which
;; this proof's own premises supply, it wants DEFINEDNESS of g on the index box --
;; (IN (g i,j) SET) -- because `image-membership-iff' puts g(x) into IMAGE(g,box)
;; only when g(x) denotes.  Here that is one step weaker than the entry hypothesis
;; this proof already carries: `membership-implies-sethood' turns each
;; (IN (g i,j) X) into (IN (g i,j) SET).
(define (mim-ex-uniq! mm nn xx gg img)
  (have! (list 'FORALL 'i_
           (list 'IMPLIES (list 'IN 'i_ (list 'INTERVAL 1 mm))
             (list 'FORALL 'j_
               (list 'IMPLIES (list 'IN 'j_ (list 'INTERVAL 1 nn))
                 (list 'IN (list gg 'i_ 'j_) 'SET)))))
    (lambda ()
      (let ((ehyp (dk-pick (lambda (f)
                             (and (pair? f) (eq? (car f) 'FORALL)
                                  (let ((c (mim-final f)))
                                    (and (pair? c) (eq? (car c) 'IN)
                                         (pair? (cadr c)) (eq? (car (cadr c)) gg)
                                         (equal? (caddr c) xx)))))
                           "the entry hypothesis")))
        (dk-peel!)
        (let* ((g1 (dk-goal))                             ; (IN (g i j) SET)
               (en (cadr g1))
               (i0 (cadr en)) (j0 (caddr en)))
          (let ((inner (dk-apply! ehyp i0))) (dk-apply! inner j0))
          (fact 'membership-implies-sethood (list gg i0 j0) xx)
          (ass)))))
  (let* ((ex (dk-fact! 'matof-exists mm nn gg))
         (p0 (dk-skolem! ex)))                            ; lands the property of p0, split
    (ew p0)
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORALL)
           (mim-unique! mm nn gg img p0)
           (dk-conj-close!)))                             ; property(p0): both halves in context
     (dk-opened (lambda () (di))))))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL g
     (IMPLIES (IN m NN)
     (IMPLIES (IN n NN)
     (IMPLIES (FORALL i (IMPLIES (IN i (INTERVAL 1 m))
                (FORALL j (IMPLIES (IN j (INTERVAL 1 n))
                  (IN (g i j) X)))))
       (IN (MATOF m n g) (MAT m n X)))))))))))
(dk-peel!)
(let* ((g0  (dk-goal))                                   ; (IN (MATOF m n g) (MAT m n X))
       (mm  (cadr   (cadr g0)))
       (nn  (caddr  (cadr g0)))
       (gg  (cadddr (cadr g0)))
       (xx  (cadddr (caddr g0)))
       (box (list 'CARTESIAN (list 'INTERVAL 1 mm) (list 'INTERVAL 1 nn)))
       (img (list 'IMAGE gg box))
       (hyp (dk-pick (lambda (f)
                       (and (pair? f) (eq? (car f) 'FORALL)
                            (let ((c (mim-final f)))
                              (and (pair? c) (eq? (car c) 'IN)
                                   (pair? (cadr c)) (eq? (car (cadr c)) gg)))))
                     "the entry hypothesis"))
       (sub (list 'FORALL 'w (list 'IMPLIES (list 'IN 'w img) (list 'IN 'w xx)))))
  ;; ---- IMAGE(g, box) inside X ----------------------------------------
  (have! sub
    (lambda ()
      ;; both macetes BEFORE any di: they rewrite the antecedent in place
      ;; (under the binder: the goal is not the membership itself, so not dk-image-goal!;
      ;; the iff's sethood conjunct lands with the antecedent and mim-skolem-all! steps
      ;; over it)
      (mac 'image-membership-iff)
      (mac 'cartesian-decompose)
      (dk-peel!)
      (dk-split-all!)                    ; the iff's conjunction: (IN w SET) and the existential
      (mim-skolem-all!)
      (let* ((g1  (dk-goal))                               ; (IN w X)
             (w   (cadr g1))
             (eqg (dk-pick (lambda (f)
                             (and (pair? f) (eq? (car f) '=) (equal? (caddr f) w)
                                  (pair? (cadr f)) (eq? (car (cadr f)) gg)))
                           "g(x) = w"))
             (x   (cadr (cadr eqg)))
             (eqx (dk-pick (lambda (f)
                             (and (pair? f) (eq? (car f) '=) (equal? (cadr f) x)
                                  (pair? (caddr f)) (eq? (car (caddr f)) 'LIST)))
                           "x = [a, b]"))
             (a   (cadr  (caddr eqx)))
             (b   (caddr (caddr eqx))))
        (inst*! hyp a b)                                   ; g(a,b) in X
        (fact 'apply-tupling-2 gg a b)                     ; g(a,b) == g([a,b])
        (subst (list '= w (list gg x)))                    ; goal: g(x) in X
        (subst eqx)                                        ; goal: g([a,b]) in X
        (subst (list '== (list gg (list 'LIST a b)) (list gg a b)))
        (ass))))
  ;; ---- the description ---------------------------------------------------
  (mac 'MATOF)
  (let ((io (cadr (dk-goal))))
    (if (not (and (pair? io) (eq? (car io) 'IOTA)))
        (error "matof-in-mat: MATOF did not unfold to an IOTA" io))
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (car (dk-goal)) 'FORSOME)
           (mim-ex-uniq! mm nn xx gg img)
           (mim-main! mm nn xx img io)))
     (dk-opened (lambda () (iota-d io))))))
(qed 'matof-in-mat)
