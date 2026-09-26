;;; min-degree-entry-proof.scm -- a matrix with a nonzero entry has a nonzero
;;; entry of MINIMAL Euclidean degree.  The "mu is achieved" fact that starts
;;; the Smith reduction (Prop 3.36).
;;;
;;; Was an ASSERTED support in structure-library/mat-equiv.scm, warranted
;;; 'well-known with the prose "apply nn-least-element to the degree set".  It
;;; is now a theorem, and the prose is a one-line tactic call: the whole
;;; content is
;;;
;;;     (minimize! '(i j) <i,j index a nonzero entry> <the degree of that entry>)
;;;
;;; leaving exactly the two obligations minimize! always leaves -- the measure
;;; is a natural number (gauge-is-degree + entry-in-carrier + fun-apply-type-c)
;;; and the guard is satisfiable (that is the hypothesis).  Everything the old
;;; warrant swallowed -- the degree set, the well-ordering, the recovery of the
;;; witnessing position -- is now machine-checked.
;;;
;;; Needs: minimize.scm, theorem-library/nn-least-element (for minimize!),
;;; matrix.scm (ENTRY/MAT/INTERVAL, entry-in-carrier), euclidean-ring.scm
;;; (GAUGE, gauge-is-degree), order-lemmas.scm (fun-apply-type-c).

;;; ---- driver helpers (mde- prefix; a bare `MDE' would case-fold onto a tactic)
(define (mde-goal) (wff-formula (sequent-node-assertion (proof-state-focus *ps*))))
(define (mde-foc! n) (dk-focus! n))
(define (mde-leaves)
  (filter (lambda (n) (and (not (sequent-node-grounded? n))
                           (null? (sequent-node-in-arrows n))))
          (dg-ungrounded-nodes (proof-state-dg *ps*))))
;; Focus the open leaf with this exact goal.  ERRORS on a miss: a helper that
;; returns #f and leaves focus put hides every later mistake (CLAUDE.md).
(define (mde-foc-goal! g)
  (let loop ((ls (mde-leaves)))
    (cond ((null? ls) (error "mde-foc-goal!: no open leaf with goal" g))
          ((equal? (wff-formula (sequent-node-assertion (car ls))) g)
           (mde-foc! (car ls)) (car ls))
          (else (loop (cdr ls))))))
(define (mde-di*)
  (let lp () (let* ((g (mde-goal)) (h (and (pair? g) (car g))))
               (when (memq h '(FORALL IMPLIES)) (di) (lp)))))

;;; ---- the shape
(define mde-rows '(INTERVAL 1 m))
(define mde-cols '(INTERVAL 1 n))
(define (mde-nz i j)  (list 'NOT (list '= (list 'ENTRY 'P i j) '(ZERO A))))
(define (mde-tail i j) (list 'AND (list 'IN j mde-cols) (mde-nz i j)))
(define (mde-guard i j) (list 'AND (list 'IN i mde-rows) (mde-tail i j)))
(define (mde-deg i j)  (list (list 'GAUGE 'A) (list 'ENTRY 'P i j)))
(define (mde-min a b i j) (list '<= (mde-deg a b) (mde-deg i j)))

;; The minimality clause of the conclusion, with the index guards CURRIED
;; (that is the shape place-min-pivot's `fact' consumes; keep it verbatim).
(define (mde-curried a b)
  (list 'FORALL 'i (list 'FORALL 'j
    (list 'IMPLIES (list 'IN 'i mde-rows)
      (list 'IMPLIES (list 'IN 'j mde-cols)
        (list 'IMPLIES (mde-nz 'i 'j) (mde-min a b 'i 'j)))))))

(sp (make-wff
  (list 'FORALL 'A (list 'IMPLIES '(IS-EUCLIDEAN-RING A)
    (list 'FORALL 'm (list 'FORALL 'n (list 'FORALL 'P
      (list 'IMPLIES '(IN P (MAT m n (CARR A)))
        (list 'IMPLIES (list 'FORSOME 'i0 (list 'FORSOME 'j0 (mde-guard 'i0 'j0)))
          (list 'FORSOME 'iS (list 'FORSOME 'jS
            (list 'AND (list 'IN 'iS mde-rows)
              (list 'AND (list 'IN 'jS mde-cols)
                (list 'AND (mde-nz 'iS 'jS) (mde-curried 'iS 'jS)))))))))))))))
(mde-di*)

;;; ===================================================================
;;; Choose (i,j) indexing a nonzero entry of least degree.
;;; ===================================================================
(define mde-r (minimize! '(i j) (mde-guard 'i 'j) (mde-deg 'i 'j)))
(define mde-ws   (car   mde-r))          ; the two eigenconstants
(define mde-a    (car   mde-ws))
(define mde-b    (cadr  mde-ws))
(define mde-type (or (cadr mde-r) (error "min-degree-entry: TYPE not opened")))
(define mde-ne   (caddr mde-r))          ; #f: NONEMPTY was already in context

;;; ---- obligation 1: the degree of a matrix entry is a natural number.
(mde-foc! mde-type)
(di)                                     ; peel i, j  (one di peels both)
(di)                                     ; assume the guard
(let* ((ent (cadr (cadr (mde-goal))))    ; goal (IN ((GAUGE A) (ENTRY P i j)) NN)
       (ii  (caddr ent))
       (jj  (cadddr ent)))
  (ai (mde-guard ii jj))                 ; (IN ii rows) | (AND (IN jj cols) (NOT ...))
  (ai (mde-tail ii jj))                  ; (IN jj cols) | (NOT ...)
  (fact 'entry-in-carrier 'm 'n '(CARR A) 'P ii jj)
  (fact 'gauge-is-degree 'A)
  (ai '(AND (IN (GAUGE A) (FUN (CARR A) NN)) (HAS-DIV-REMAINDER A (GAUGE A))))
  (fact 'fun-apply-type-c '(GAUGE A) '(CARR A) 'NN (list 'ENTRY 'P ii jj))
  (ass))

;;; ---- obligation 2: some position does index a nonzero entry.  That IS the
;;; hypothesis, up to the names of its bound variables -- so minimize! never
;;; cut it and hands back #f rather than a goal node.
(if mde-ne (begin (mde-foc! mde-ne) (ass)))

;;; ===================================================================
;;; The chosen position witnesses the conclusion.
;;; ===================================================================
(mde-foc-goal! (list 'FORSOME 'iS (list 'FORSOME 'jS
                 (list 'AND (list 'IN 'iS mde-rows)
                   (list 'AND (list 'IN 'jS mde-cols)
                     (list 'AND (mde-nz 'iS 'jS) (mde-curried 'iS 'jS)))))))
(ew mde-a) (ew mde-b)
(ai (mde-guard mde-a mde-b))             ; (IN a rows) | (AND (IN b cols) (NOT ...))
(ai (mde-tail mde-a mde-b))              ; (IN b cols) | (NOT ...)

;; The minimality assumption minimize! landed, in ITS shape (AND-guarded).
(define mde-minim
  (let loop ((as (map wff-formula (sequent-node-assumptions (proof-state-focus *ps*)))))
    (cond ((null? as) (error "min-degree-entry: minimality assumption not found"))
          ((and (pair? (car as)) (eq? (car (car as)) 'FORALL)) (car as))
          (else (loop (cdr as))))))

(di)                                     ; (IN a rows) | rest
(mde-foc-goal! (list 'IN mde-a mde-rows)) (ass)
(mde-foc-goal! (list 'AND (list 'IN mde-b mde-cols)
                     (list 'AND (mde-nz mde-a mde-b) (mde-curried mde-a mde-b))))
(di)
(mde-foc-goal! (list 'IN mde-b mde-cols)) (ass)
(mde-foc-goal! (list 'AND (mde-nz mde-a mde-b) (mde-curried mde-a mde-b)))
(di)
(mde-foc-goal! (mde-nz mde-a mde-b)) (ass)

;; ---- the minimality clause: re-curry minimize!'s AND-guarded universal.
(mde-foc-goal! (mde-curried mde-a mde-b))
(di)                                     ; peel i, j
(di) (di) (di)                           ; assume the three guards
(let* ((g  (mde-goal))                   ; (<= (deg a b) (deg ii jj))
       (e  (cadr (caddr g)))             ; (ENTRY P ii jj)
       (ii (caddr e))
       (jj (cadddr e))
       (gd (mde-guard ii jj)))
  (cut gd)
  ;; the guard, from its three curried pieces
  (di)
  (mde-foc-goal! (list 'IN ii mde-rows)) (ass)
  (mde-foc-goal! (mde-tail ii jj))
  (di)
  (mde-foc-goal! (list 'IN jj mde-cols)) (ass)
  (mde-foc-goal! (mde-nz ii jj)) (ass)
  ;; ... and now minimality applies at (ii,jj)
  (mde-foc-goal! (mde-min mde-a mde-b ii jj))
  (inst mde-minim ii)
  (let ((f2 (subst-free (cadr mde-minim) ii (caddr mde-minim))))
    (inst f2 jj)
    (detach! (list 'IMPLIES gd (mde-min mde-a mde-b ii jj)))
    (ass)))

(qed 'min-degree-entry)
(topic! 'min-degree-entry 'algebra)
