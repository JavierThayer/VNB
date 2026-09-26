;;; mat-basics.scm -- MAT's read-offs, PROVEN from its definition.
;;;
;;; The companion to interval-basics.scm, one constructor over: MAT is a
;;; def-functoid (matrix.scm),
;;;
;;;     MAT(m, n, X) = { P in MATRIX(X) : n in NN and
;;;                                        (LENGTH P = 0 implies m = 0) and
;;;                                        (not LENGTH P = 0 implies SIZE(P) = [m, n]) }
;;;     SIZE(M)      = [ LENGTH(M), IF(LENGTH(M) = 0, 0, LENGTH(NTH(1, M))) ]
;;;
;;; and, like INTERVAL, it had no way to be read out of a HYPOTHESIS at all:
;;; `def-functoid' installs only a rewrite macete, so `mac' unfolds MAT in a
;;; goal but `mac-h' warns "unknown theorem/macete" and leaves the assumption
;;; untouched.  interval-basics.scm's recipe applies verbatim and is used here:
;;; prove the unfolding EQUATION once (the macete does apply to a goal that IS
;;; the equation), then every read-off `subst's its goal from the separation
;;; back to MAT, where the hypothesis matches.  No new axiom.
;;;
;;; The definitions changed on 2026-09-16 (matrix.scm's header gives the
;;; reason).  Files that need a MAT membership read it through the read-offs
;;; and introductions below -- mat-in-matrix, mat-cols-in-nn, mat-length,
;;; mat-rows-in-nn, mat-size, mat-cols, mat-size-rows, mat-size-cols,
;;; mat-intro, mat-intro-empty, nil-in-mat -- rather than
;;; through the separation, so that a later change to the definition is
;;; confined to this file.  One exception remains: `mat-mono'
;;; (theorem-library/matof-in-mat.scm) opens the separation on both sides,
;;; because its content is that the shape clauses do not mention X.
;;;
;;; WHY THIS FILE EXISTS.  It is step one of making CARD a definition rather
;;; than an axiom.  Before `CARD' can be defined, `interval-card-in-nn'
;;; (matrix.scm) has to be guarded -- stated unguarded it is FALSE under a
;;; defined CARD, since INTERVAL(1, +infinity) is all of NN and its cardinal is
;;; omega.  The guard it needs is `(IN b NN)' on the UPPER bound alone
;;; (INTERVAL is a separation over NN, so any natural upper bound makes it
;;; finite whatever the lower bound is).  The sites that cite it pass the
;;; literal 1 below and a matrix DIMENSION above, and the theorem statements
;;; there do not type their dimensions -- matmul-assoc quantifies `m n k l' with
;;; premises only `IN P (MAT m n (CARR A))'.  So the obligation has to come off
;;; the matrix itself, which every one of those sites has in context.  That is
;;; `mat-rows-in-nn'.
;;;
;;; STEP TWO IS DONE (2026-08-12): the guard is on, and the citing sites
;;; discharge it.  Of the 34 `fact' citations of interval-card-in-nn, 7 already
;;; had the typing in context from their own statement's premises
;;; (span-bricks2, rank-bound, and border-mult's `[1,q]' citation); 26 now land
;;; it with `mat-rows-in-nn' off a matrix in context, and border-mult's
;;; `[1, succ q]' citation lands it with `nn-succ-closed' off its premise
;;; `IN q NN'.  At every one of the 26 the dimension really is some matrix's ROW
;;; count, as surveyed above -- twice via the square elementary/unit matrix
;;; typed one line earlier (ELEM-F/G/H, MATUNIT are n-by-n), which is how the
;;; sites whose dimension is a COLUMN count of the data matrix are reached
;;; without a column read-off.  (The column read-off exists since 2026-09-16 as
;;; `mat-cols', GUARDED on `1 <= m': a matrix with no rows does not determine
;;; its column count, by the convention matrix.scm adopts.)
;;;
;;; The control that says this is not decoration: delete the two
;;; `mat-rows-in-nn' lines from matmul-assoc-proof.scm and the library load
;;; reports `qed: proof is not complete; cannot install matmul-assoc', with the
;;; cascade behind it.  An undischarged guard is NOT silent here, because the
;;; unfired `fact' leaves the typing the finsum bricks need missing.
;;;
;;; Needs: interactive + qed/proof-debt, driver-kit (have!, dk-landed-1,
;;; dk-split!), and `length-in-nn' in its GENERALISED form (library.scm) --
;;; `L in TUPLES(A)' for any A, not `TUPLES(SET)'.  The old guard could not be
;;; discharged here: matrix-membership gives `Q in TUPLES(TUPLES X)', and
;;; reaching TUPLES(SET) from it needs both "every member of a class is a set"
;;; and monotonicity of TUPLES, neither of which the library states.

;;; ---- the definitions, as citable equations ----------------------------
;;; `==' and separation-first, for interval-unfold's reasons: `rfl' owes a
;;; definedness witness that a bare SEP term does not syntactically have, while
;;; `==' is unconditional and `qrfl' closes it; and separation-first is the
;;; direction the read-offs `subst' in.

(define MB-BODY
  '(AND (IN n NN)
        (AND (IMPLIES (= (LENGTH P) 0) (= m 0))
             (IMPLIES (NOT (= (LENGTH P) 0)) (= (SIZE P) (LIST m n))))))
(define MB-SEP (list 'SEP 'P '(MATRIX X) MB-BODY))

(sp (make-wff (list 'FORALL 'm (list 'FORALL 'n (list 'FORALL 'X
   (list '== MB-SEP '(MAT m n X)))))))
(di)
(mac 'MAT)
(qrfl)
(qed 'mat-unfold)
(topic! 'mat-unfold 'plumbing)

(sp (make-wff '(FORALL M
   (== (LIST (LENGTH M) (IF (= (LENGTH M) 0) 0 (LENGTH (NTH 1 M)))) (SIZE M)))))
(di)
(mac 'SIZE)
(qrfl)
(qed 'size-unfold)
(topic! 'size-unfold 'plumbing)

;;; The unfolding on a matrix WITH rows: the IF is decided, and SIZE is the
;;; pair [rows, length of the first row].
(sp (make-wff '(FORALL M (IMPLIES (NOT (= (LENGTH M) 0))
   (== (LIST (LENGTH M) (LENGTH (NTH 1 M))) (SIZE M))))))
(dk-peel!)
(fact 'size-unfold 'M)
(let ((ift '(IF (= (LENGTH M) 0) 0 (LENGTH (NTH 1 M)))))
  (let* ((side '(NOT (= (LENGTH M) 0)))
         (ls   (dk-opened (lambda () (if-false ift)))))
    (for-each (lambda (l)
                (if (equal? (dk-goal-of l) side) (begin (dk-focus! l) (ass))))
              ls)
    (dk-focus! (find-first (lambda (l) (not (equal? (dk-goal-of l) side))) ls)))
  (subst (list '= '(LENGTH (NTH 1 M)) ift))
  (ass))
(qed 'size-nonempty)
(topic! 'size-nonempty 'plumbing)

;;; NTH on a literal pair.  `nth-r' reduces it in a GOAL; this makes the same
;;; reduction citable as an equation, which is what a `subst' chain needs.
(sp (make-wff '(FORALL a (FORALL b (== (NTH 1 (LIST a b)) a)))))
(di)
(nth-r)
(qrfl)
(qed 'nth1-pair)
(topic! 'nth1-pair 'plumbing)

;;; ---- opening a membership ------------------------------------------------
;;; Lands (IN Q (MATRIX X)) and the two conditional clauses of the separation;
;;; returns the clauses as (EMPTY-CLAUSE . ROWS-CLAUSE).
(define (mb-open! q m n x)
  (let* ((body (subst-free* (list (cons 'm m) (cons 'n n)) MB-BODY))
         (sep  (list 'SEP 'P (list 'MATRIX x) body)))
    (fact 'mat-unfold m n x)
    (have! (list 'IN q sep)
           (lambda () (subst (list '== sep (list 'MAT m n x))) (ass)))
    (let* ((landed (dk-landed (lambda () (sep-me (list 'IN q sep)))))
           (conj   (find-first (dk-head? 'AND) landed))
           (parts  (dk-split! conj))
           (imp-of (lambda (neg?)
                     (find-first (lambda (f)
                                   (and (pair? f) (eq? (car f) 'IMPLIES)
                                        (eq? neg? (and (pair? (cadr f))
                                                       (eq? (car (cadr f)) 'NOT)))))
                                 parts))))
      (cons (imp-of #f) (imp-of #t)))))

;;; ---- the read-offs ---------------------------------------------------------
;;;
;;;   IN Q (MAT m n X)  =>  IN Q (MATRIX X)
;;;   IN Q (MAT m n X)  =>  IN n NN
;;;   IN Q (MAT m n X)  =>  LENGTH(Q) = m                      (always)
;;;   IN Q (MAT m n X)  =>  1 <= m  =>  SIZE(Q) = [m, n]
;;;   IN Q (MAT m n X)  =>  1 <= m  =>  LENGTH(NTH(1, Q)) = n
;;;
;;; The row count is always available.  The column count is determined only
;;; when there are rows: a matrix with no rows is [] whatever the natural n is
;;; (see matrix.scm), so from `Q in MAT(0, n, X)' only `n in NN' follows.

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IN Q (MATRIX X)))))))))
(dk-peel!)
(mb-open! 'Q 'm 'n 'X)
(ass)
(qed 'mat-in-matrix)
(topic! 'mat-in-matrix 'plumbing)

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IN n NN))))))))
(dk-peel!)
(mb-open! 'Q 'm 'n 'X)
(ass)
(qed 'mat-cols-in-nn)
(topic! 'mat-cols-in-nn 'plumbing)

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (= (LENGTH Q) m))))))))
(dk-peel!)
(let ((cl (mb-open! 'Q 'm 'n 'X)))
  (use-em '(= (LENGTH Q) 0)
    (lambda ()                                   ; no rows: m = 0 = LENGTH(Q)
      (detach! (car cl))
      (subst '(= m 0))
      (ass))
    (lambda ()                                   ; rows: m is SIZE's first component
      (detach! (cdr cl))
      (fact 'size-nonempty 'Q)
      ;; 2026-09-18 (LUTINS instantiation): `fact nth1-pair' at the term
      ;; LENGTH(NTH 1 Q) owes its definedness, which the context does not
      ;; certify (nothing types NTH(1,Q) in a TUPLES class here).  The same
      ;; equation as a `have!' lane closed by nth-r/qrfl instantiates nothing
      ;; -- the mat-cols proof below already uses this shape.
      (have! '(== (NTH 1 (LIST (LENGTH Q) (LENGTH (NTH 1 Q)))) (LENGTH Q))
             (lambda () (nth-r) (qrfl)))
      (fact 'nth1-pair 'm 'n)
      (subst '(== (LENGTH Q) (NTH 1 (LIST (LENGTH Q) (LENGTH (NTH 1 Q))))))
      (subst '(== (LIST (LENGTH Q) (LENGTH (NTH 1 Q))) (SIZE Q)))
      (subst '(= (SIZE Q) (LIST m n)))
      (subst '(== (NTH 1 (LIST m n)) m))
      (rfl))))
(qed 'mat-length)
(topic! 'mat-length 'plumbing)

;;; ---- the read-off: a matrix knows how many rows it has ----------------
;;;
;;;   IN Q (MAT m n X)  =>  IN m NN
;;;
;;; m is LENGTH(Q) (mat-length), and the length of a tuple is a natural number.

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IN m NN))))))))
(dk-peel!)
(fact 'mat-length 'm 'n 'X 'Q)
(fact 'mat-in-matrix 'm 'n 'X 'Q)
(dk-split! (dk-landed-1 (lambda () (mac-h 'matrix-membership '(IN Q (MATRIX X))))))
(fact 'length-in-nn '(TUPLES X) 'Q)
(subst '(= m (LENGTH Q)))
(ass)
(qed 'mat-rows-in-nn)
(topic! 'mat-rows-in-nn 'plumbing)

;;; 1 <= m and LENGTH(Q) = m rule out LENGTH(Q) = 0.
(define (mb-rows-nonzero! q m)
  (have! (list 'NOT (list '= (list 'LENGTH q) 0))
    (lambda ()
      (di)                                       ; LENGTH(q) = 0 |- FALSITY
      (have! '(<= 1 0)
        (lambda ()
          (subst (list '= 0 (list 'LENGTH q)))
          (subst (list '= (list 'LENGTH q) m))
          (ass)))
      (dk-focus-having! '(<= 1 0))
      (have! '(NOT (<= 1 0)) (lambda () (arith)))
      (dk-focus-having! '(NOT (<= 1 0)))
      (ai '(NOT (<= 1 0))))))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IMPLIES (<= 1 m)
     (= (SIZE Q) (LIST m n))))))))))
(dk-peel!)
(fact 'mat-length 'm 'n 'X 'Q)
(let ((cl (mb-open! 'Q 'm 'n 'X)))
  (mb-rows-nonzero! 'Q 'm)
  (detach! (cdr cl))
  (ass))
(qed 'mat-size)
(topic! 'mat-size 'plumbing)

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IMPLIES (<= 1 m)
     (= (LENGTH (NTH 1 Q)) n)))))))))
(dk-peel!)
(fact 'mat-length 'm 'n 'X 'Q)
(fact 'mat-size 'm 'n 'X 'Q)
(mb-rows-nonzero! 'Q 'm)
(fact 'size-nonempty 'Q)
(have! '(== (NTH 2 (LIST (LENGTH Q) (LENGTH (NTH 1 Q)))) (LENGTH (NTH 1 Q)))
       (lambda () (nth-r) (qrfl)))
(have! '(== (NTH 2 (LIST m n)) n)
       (lambda () (nth-r) (qrfl)))
(subst '(== (LENGTH (NTH 1 Q)) (NTH 2 (LIST (LENGTH Q) (LENGTH (NTH 1 Q))))))
(subst '(== (LIST (LENGTH Q) (LENGTH (NTH 1 Q))) (SIZE Q)))
(subst '(= (SIZE Q) (LIST m n)))
(subst '(== (NTH 2 (LIST m n)) n))
(rfl)
(qed 'mat-cols)
(topic! 'mat-cols 'plumbing)

;;; The two components of SIZE as the operations (MATMUL, MATADD, ...) read
;;; them: the row count always, the column count when there are rows.
(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (= (NTH 1 (SIZE Q)) m))))))))
(dk-peel!)
(fact 'mat-length 'm 'n 'X 'Q)
(fact 'mat-rows-in-nn 'm 'n 'X 'Q)
(fact 'size-unfold 'Q)
(let ((ift '(IF (= (LENGTH Q) 0) 0 (LENGTH (NTH 1 Q)))))
  ;; 2026-09-18 (LUTINS instantiation): the IF term is not certified defined,
  ;; so `fact nth1-pair' at it owes `ift = ift'.  The have! lane below proves
  ;; the same equation with no instantiation.
  (have! (list '== (list 'NTH 1 (list 'LIST '(LENGTH Q) ift)) '(LENGTH Q))
         (lambda () (nth-r) (qrfl)))
  (subst (list '== '(SIZE Q) (list 'LIST '(LENGTH Q) ift)))
  (subst (list '== (list 'NTH 1 (list 'LIST '(LENGTH Q) ift)) '(LENGTH Q)))
  (subst '(= (LENGTH Q) m))
  (rfl))
(qed 'mat-size-rows)
(topic! 'mat-size-rows 'plumbing)

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IMPLIES (<= 1 m)
     (= (NTH 2 (SIZE Q)) n)))))))))
(dk-peel!)
(fact 'mat-size 'm 'n 'X 'Q)
(fact 'mat-cols-in-nn 'm 'n 'X 'Q)
(subst '(= (SIZE Q) (LIST m n)))
(nth-r)
(rfl)
(qed 'mat-size-cols)
(topic! 'mat-size-cols 'plumbing)

;;; ---- the introductions -----------------------------------------------------
;;;
;;;   Q in MATRIX(X), n in NN, 1 <= m, LENGTH(Q) = m, LENGTH(NTH(1,Q)) = n
;;;                                           =>  Q in MAT(m, n, X)
;;;   Q in MATRIX(X), n in NN, LENGTH(Q) = 0  =>  Q in MAT(0, n, X)
;;;   n in NN                                 =>  [] in MAT(0, n, X), every X

;; Goal (IN Q (MAT ..)) -> the separation's leaves; closes the membership leaf
;; and hands each remaining clause (an IMPLIES) to ON-CLAUSE, focused.
(define (mb-intro! on-clause)
  (mac 'MAT)
  (let loop ((ls (dk-opened (lambda () (sep-mi)))))
    (for-each
     (lambda (l)
       (if (memq l (proof-leaves))
           (begin
             (dk-focus! l)
             (let ((g (dk-goal)))
               (cond ((eq? (car g) 'AND) (loop (dk-opened (lambda () (di)))))
                     ((eq? (car g) 'IMPLIES) (on-clause g))
                     (#t (ass)))))))
     ls)))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MATRIX X))
   (IMPLIES (IN n NN)
   (IMPLIES (<= 1 m)
   (IMPLIES (= (LENGTH Q) m)
   (IMPLIES (= (LENGTH (NTH 1 Q)) n)
     (IN Q (MAT m n X)))))))))))))
(dk-peel!)
(mb-intro!
 (lambda (g)
   (di)
   (if (eq? (car (cadr g)) 'NOT)
       (begin                                    ; rows: SIZE(Q) = [m, n]
         (fact 'size-nonempty 'Q)
         (subst '(== (SIZE Q) (LIST (LENGTH Q) (LENGTH (NTH 1 Q)))))
         (subst '(= (LENGTH Q) m))
         (subst '(= (LENGTH (NTH 1 Q)) n))
         (rfl))
       (begin                                    ; no rows: m = 0
         (subst '(= m (LENGTH Q)))
         (ass)))))
(qed 'mat-intro)
(topic! 'mat-intro 'plumbing)

(sp (make-wff '(FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MATRIX X))
   (IMPLIES (IN n NN)
   (IMPLIES (= (LENGTH Q) 0)
     (IN Q (MAT 0 n X))))))))))
(dk-peel!)
(mb-intro!
 (lambda (g)
   (di)
   (if (eq? (car (cadr g)) 'NOT)
       (prop)                                    ; LENGTH(Q) = 0 and its negation
       (rfl))))                                  ; 0 = 0
(qed 'mat-intro-empty)
(topic! 'mat-intro-empty 'plumbing)

(sp (make-wff '(FORALL n (FORALL X (IMPLIES (IN n NN) (IN (LIST) (MAT 0 n X)))))))
(dk-peel!)
(fact 'length-of-empty)
(have! '(IN (LIST) (MATRIX X))
  (lambda ()
    (mac 'matrix-membership)
    (dk-conj-close!
     (lambda ()
       (let ((g1 (dk-goal)))
         (if (eq? (car g1) 'IN)
             (begin (fact 'empty-in-tuples '(TUPLES X)) (ass))
             (begin
               (dk-split-all! (dk-peel!))
               (let ((i0 (cadr (cadr (cadr (dk-goal))))))
                 ;; 1 <= i <= LENGTH([]) = 0 is absurd.  (contra loads much later;
                 ;; this is its argument by hand: 1 <= 0 over RR, refuted by arith.)
                 (have! (list '<= i0 0)
                   (lambda () (subst '(== 0 (LENGTH (LIST)))) (ass)))
                 (fact 'nn-in-rr i0)
                 (fact 'rr-one-in)
                 (fact 'rr-zero-in)
                 (have! (list 'AND (list '<= 1 i0) (list '<= i0 0))
                   (lambda () (dk-conj-close! (lambda () (ass)))))
                 (fact 'rr-le-trans 1 i0 0)              ; 1 <= 0
                 (dk-focus-having! '(<= 1 0))
                 (have! '(NOT (<= 1 0)) (lambda () (arith)))
                 (dk-focus-having! '(NOT (<= 1 0)))
                 (pbc)
                 (ai '(NOT (<= 1 0)))))))))))
(fact 'mat-intro-empty 'n 'X '(LIST))
(ass)
(qed 'nil-in-mat)
(topic! 'nil-in-mat 'plumbing)

;;; The column component of SIZE when nothing is known about the row count:
;;; it is a natural number, and if it is at least 1 the matrix has rows, so it
;;; is the column count.  And a matrix with no rows is a 0-by-k matrix for
;;; every natural k.

;; LENGTH(Q) = 0 in context: land NTH(2, SIZE(Q)) = 0.
(define (mb-size-cols-zero! q)
  (let* ((ift (list 'IF (list '= (list 'LENGTH q) 0) 0 (list 'LENGTH (list 'NTH 1 q))))
         (sz  (list 'LIST (list 'LENGTH q) ift))
         (side (list '= (list 'LENGTH q) 0)))
    (fact 'size-unfold q)
    (let ((ls (dk-opened (lambda () (if-true ift)))))
      (for-each (lambda (l)
                  (if (equal? (dk-goal-of l) side) (begin (dk-focus! l) (ass))))
                ls)
      (dk-focus! (find-first (lambda (l) (not (equal? (dk-goal-of l) side))) ls)))
    (have! (list '= (list 'NTH 2 (list 'SIZE q)) 0)
      (lambda ()
        (subst (list '== (list 'SIZE q) sz))
        (nth-r)
        (subst (list '= ift 0))
        (rfl)))
    (dk-focus-having! (list '= (list 'NTH 2 (list 'SIZE q)) 0))))

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IN (NTH 2 (SIZE Q)) NN))))))))
(dk-peel!)
(let ((cl (mb-open! 'Q 'm 'n 'X)))
  (use-em '(= (LENGTH Q) 0)
    (lambda ()
      (mb-size-cols-zero! 'Q)
      (subst '(= (NTH 2 (SIZE Q)) 0))
      (fact 'nn-zero-in)
      (ass))
    (lambda ()
      (detach! (cdr cl))                         ; SIZE(Q) = [m, n]
      (subst '(= (SIZE Q) (LIST m n)))
      (nth-r)
      (ass))))                                   ; n in NN, from the separation
(qed 'mat-size-cols-in-nn)
(topic! 'mat-size-cols-in-nn 'plumbing)

(sp (make-wff '(FORALL m (FORALL n (FORALL X (FORALL Q
   (IMPLIES (IN Q (MAT m n X)) (IMPLIES (<= 1 (NTH 2 (SIZE Q)))
     (= (NTH 2 (SIZE Q)) n)))))))))
(dk-peel!)
(let ((cl (mb-open! 'Q 'm 'n 'X)))
  (use-em '(= (LENGTH Q) 0)
    (lambda ()                                   ; no rows: 1 <= 0, absurd
      (mb-size-cols-zero! 'Q)
      (have! '(<= 1 0)
        (lambda () (subst '(= 0 (NTH 2 (SIZE Q)))) (ass)))
      (dk-focus-having! '(<= 1 0))
      (have! '(NOT (<= 1 0)) (lambda () (arith)))
      (dk-focus-having! '(NOT (<= 1 0)))
      (pbc)
      (ai '(NOT (<= 1 0))))
    (lambda ()
      (detach! (cdr cl))
      (subst '(= (SIZE Q) (LIST m n)))
      (nth-r)
      (rfl))))
(qed 'mat-size-cols-pos)
(topic! 'mat-size-cols-pos 'plumbing)

(sp (make-wff '(FORALL c (FORALL X (FORALL Q (FORALL k
   (IMPLIES (IN Q (MAT 0 c X)) (IMPLIES (IN k NN)
     (IN Q (MAT 0 k X))))))))))
(dk-peel!)
(fact 'mat-in-matrix 0 'c 'X 'Q)
(fact 'mat-length 0 'c 'X 'Q)
(fact 'mat-intro-empty 'k 'X 'Q)
(ass)
(qed 'mat-empty-any-cols)
(topic! 'mat-empty-any-cols 'plumbing)


;;; ---- the empty index interval ------------------------------------------
;;;
;;;   INTERVAL(1, 0) = EMPTY-SET
;;;
;;; An asserted support in matrix.scm until 2026-09-16, and the one debt left
;;; in the n = 0 base case of the spans-submodule-fg descent.  Both classes are
;;; empty, so class-extensionality equates them (seg0-empty's proof, card-
;;; finite.scm): i in [1,0] gives 1 <= i <= 0, and 1 <= 0 is refuted over RR.

(sp (make-wff '(= (INTERVAL 1 0) EMPTY-SET)))
(have! '(FORALL x (IFF (IN x (INTERVAL 1 0)) (IN x EMPTY-SET)))
  (lambda ()
    (di)                                         ; peels x, splits the IFF
    (for-each
     (lambda (l)
       (dk-focus! l)
       (if (equal? (dk-goal) '(IN x EMPTY-SET))
           (begin                                ; x in [1,0]: absurd
             (fact 'interval-elt-in-nn 1 0 'x)
             (fact 'interval-lo 1 0 'x)
             (fact 'interval-hi 1 0 'x)
             (fact 'nn-in-rr 'x)
             (fact 'rr-one-in)
             (fact 'rr-zero-in)
             (have! '(AND (<= 1 x) (<= x 0))
               (lambda () (dk-conj-close! (lambda () (ass)))))
             (fact 'rr-le-trans 1 'x 0)          ; 1 <= 0
             (dk-focus-having! '(<= 1 0))
             (have! '(NOT (<= 1 0)) (lambda () (arith)))
             (dk-focus-having! '(NOT (<= 1 0)))
             (pbc)
             (ai '(NOT (<= 1 0))))
           (begin                                ; x in EMPTY-SET: absurd
             (fact 'empty-set-has-no-members 'x)
             (ai '(NOT (IN x EMPTY-SET))))))
     (dk-opened (lambda () (di))))))
(dk-focus-having! '(FORALL x (IFF (IN x (INTERVAL 1 0)) (IN x EMPTY-SET))))
(fact 'class-extensionality '(INTERVAL 1 0) 'EMPTY-SET)
(ass)
(qed 'interval-1-0-empty)
