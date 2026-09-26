;;; nn-not-le-succ-le.scm -- NN is totally ordered and discrete, PROVEN.
;;;
;;;   forall m in NN. forall n in NN.  not (m <= n)  =>  succ n <= m
;;;
;;; Was a `well-known' support in structure-library/order-lemmas.scm (:335),
;;; whose warrant read "NN is totally ordered and discrete: not(m<=n) gives n<m,
;;; hence succ n <= m".  That sentence is the proof, run here on the ORDINAL
;;; route of theorem-library/nn-order-ord.scm -- the same three moves: cross to
;;; ORD (nn-subset-ord), argue with the ordinal order, cross back
;;; (ord-le-nn-compat).  The RR route is CIRCULAR: nn-lt-succ-le
;;; (theorem-library/finite-surgery.scm) is proved FROM this fact, so the
;;; discreteness has to come from where nn-order-ord gets it, the primitive
;;; ordinal axioms.
;;;
;;; THE ARGUMENT.  Split on m ORD-LE n.  If it holds, the bridge makes it
;;; m <= n, against the hypothesis.  If not, totality (ord-le-total) gives
;;; n ORD-LE m; and n /= m, since n = m would turn the refused m ORD-LE n into
;;; a reflexivity (ord-le-refl).  So n ORD-LT m (ord-lt-iff), and the immediate
;;; successor axiom (ord-succ-immediate) gives succ_ORD n ORD-LE m; ord-succ-nn
;;; rewrites succ_ORD n to succ n and the bridge brings the inequality down to
;;; NN.  It is the second branch of nn-le-succ-cases with the antisymmetry step
;;; removed -- there the conclusion was j = succ k, here it is the inequality
;;; itself.
;;;
;;; CITATIONS, and the load window.  Every fact cited is `primitive':
;;; nn-subset-ord, ord-le-refl, ord-le-total, ord-lt-iff, ord-succ-immediate,
;;; ord-succ-nn, ord-le-nn-compat (structure-library/ordinals.scm) and
;;; nn-succ-closed (number-systems.scm).  No theorem-library fact is used --
;;; not even nn-le-refl, which the triage named for the n = m case: ord-le-refl
;;; on the ORD side does that job and is primitive.  So the lower bound of the
;;; window is the 125 floor (where `sp'/`qed' first exist), and the natural
;;; home is directly after nn-order-ord (135), whose kit this copies.  The
;;; upper bound is the earliest citer, theorem-library/finite-surgery (162).
;;; Window: [125, 162).
;;;
;;; The kit below is the `nq-' kit of nn-order-ord.scm under this file's own
;;; prefix (`nls-'); each helper exists because `fact' will not split a
;;; conjunctive antecedent, and ord-le-total / ord-le-nn-compat /
;;; ord-succ-immediate all state their hypotheses as one AND.

;;; ---- file-local kit (nls- prefix; never named like a tactic) ------------

;; `have!' with NO thunk proves the side goal with driver-kit's
;; `from-context!', which di-splits an AND goal and recurses.
(define (nls-and2 a b) (have! (list 'AND a b)))

;; Consume the compatibility IFF (IFF (ORD-LE A B) (<= A B)) in the ORD -> NN
;; direction: `ai' on an IFF lands both implications, `detach!' takes the one
;; wanted (it takes the IMPLIES, not its antecedent).  ord-le-nn-compat is a
;; CONDITIONAL biconditional, so it is not usable as a rewrite macete.
(define (nls-ord->le! a b)
  (ai (list 'IFF (list 'ORD-LE a b) (list '<= a b)))
  (detach! (list 'IMPLIES (list 'ORD-LE a b) (list '<= a b))))

;; (ORD-LT A B) from its two halves.  ord-lt-iff is UNGUARDED, hence a live
;; macete: `mac' on the goal, then the two conjuncts are in context.
(define (nls-lt! a b)
  (have! (list 'ORD-LT a b) (lambda () (mac 'ord-lt-iff) (from-context!))))

;; `di' until the goal head stops being peelable.  NOT a `di' count: `di' is
;; greedy over a FORALL/IMPLIES prefix but stops at an implication whose
;; antecedent is not a typing.  Loop on the SHAPE.
(define (nls-peel!)
  (let loop ((prev #f) (n 0))
    (let ((g (dk-goal)))
      (if (and (< n 12) (not (equal? g prev))
               (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop g (+ n 1)))))))

;; Land the compatibility IFF at (A,B); both must already be typed in NN.
(define (nls-compat! a b)
  (nls-and2 (list 'IN a 'NN) (list 'IN b 'NN))
  (fact 'ord-le-nn-compat a b))

;; succ_ORD A ORD-LE B from A ORD-LT B, both typed in ORD.
(define (nls-immediate! a b)
  (have! (list 'AND (list 'IN a 'ORD) (list 'AND (list 'IN b 'ORD) (list 'ORD-LT a b))))
  (fact 'ord-succ-immediate a b))

;; Close the focus goal (<= A B) from (ORD-LE A B), both typed in NN.
(define (nls-close-le! a b)
  (nls-compat! a b)
  (nls-ord->le! a b)
  (ass))

;;; =====================================================================
;;; nn-not-le-succ-le:  not (m <= n)  =>  succ n <= m.
;;; The statement is the support's, unchanged (binders m, n as in
;;; order-lemmas.scm:335).
(sp (make-wff '(FORALL m (IMPLIES (IN m NN) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (NOT (<= m n)) (<= (succ n) m))))))))
(nls-peel!)                             ; goal (<= (succ n) m); NOT (<= m n) landed
(fact 'nn-subset-ord 'm)
(fact 'nn-subset-ord 'n)
(fact 'nn-succ-closed 'n)
(nls-compat! 'm 'n)                     ; (IFF (ORD-LE m n) (<= m n))
(use-em '(ORD-LE m n)
        ;; m ORD-LE n: bridge to m <= n and it contradicts the hypothesis.
        ;; `ai' on the NOT is not-elim: the positive is already in context.
        (lambda ()
          (nls-ord->le! 'm 'n)
          (ai '(NOT (<= m n))))
        ;; NOT (m ORD-LE n): totality gives n ORD-LE m, refl refutes n = m.
        (lambda ()
          (nls-and2 '(IN n ORD) '(IN m ORD))
          (fact 'ord-le-total 'n 'm)
          (use-cases (list '(ORD-LE n m) '(ORD-LE m n))
            (lambda ()
              (fact 'ord-le-refl 'm)
              ;; n /= m: were they equal, `subst' would turn the side goal
              ;; (ORD-LE m n) into (ORD-LE m m), a reflexivity, contradicting
              ;; the branch hypothesis.
              (have! '(NOT (= n m))
                     (lambda () (di)
                                (have! '(ORD-LE m n)
                                       (lambda () (subst '(= n m)) (ass)))
                                (ai '(NOT (ORD-LE m n)))))
              (nls-lt! 'n 'm)
              (nls-immediate! 'n 'm)
              (mac-h 'ord-succ-nn '(ORD-LE (succ_ORD n) m))
              (nls-close-le! '(succ n) 'm))
            (lambda () (ai '(NOT (ORD-LE m n)))))))
(qed 'nn-not-le-succ-le)
(topic! 'nn-not-le-succ-le 'inequalities)
