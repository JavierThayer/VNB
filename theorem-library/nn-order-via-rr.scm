;;; nn-order-via-rr.scm -- elementary NN order facts, PROVEN by taking the
;;; contradiction in RR.
;;;
;;;   nn-not-le-zero-pos   1 <= j      =>  not(j <= 0)
;;;   nn-succ-le-antisym   succ a <= b =>  not(b <= a)
;;;
;;; THE SHARED TECHNIQUE, and it is the point of collecting them: NN carries no
;;; order axioms of its own beyond the succ family, so an order fact about
;;; naturals that is not one of those is proved by pushing the hypotheses into
;;; RR (`nn-in-rr'), letting `ineq' find them jointly infeasible, and turning
;;; the resulting `1 <= 0' into FALSITY -- antisymmetry gives 1 = 0 and
;;; `rr-pos-ne-zero' at 1, fed by `rr-zero-lt-one', denies it.  Both proofs
;;; below are that shape with different premises.  `contra' would collapse the
;;; last four lines into one and loads 1600 entries too late to be used here.
;;;
;;; THE TOP OF THE GREEDY WHAT-IF.  `reference/DEBT-BUNDLE.md` ranks unproven
;;; leaves by bills CLEARED rather than by citations, and this one was #1 at
;;; TEN -- ahead of `card-subset-nn` (6) and `cont-agree-off-pt` (4).  It is not
;;; a leaf anybody would have picked by eye: it says something a reader would
;;; call obvious, and it was carried by the smith-diagonalization arc, the span
;;; bricks, card-inequalities, and -- as of this week -- the whole ratio-test
;;; arc, which inherits it through `nn-le-gap`.
;;;
;;; WHY IT GOES THROUGH RR, and why the obvious NN route is circular.  The
;;; natural argument is "j <= 0 makes j = 0 by `nn-le-zero-is-zero`, and then
;;; 1 <= 0".  That is exactly backwards: `nn-le-zero-is-zero`
;;; (theorem-library/nn-order-proof.scm:48) is proved BY CITING THIS FACT.  NN
;;; carries no order axioms of its own beyond the succ family; the order on NN
;;; is the order on RR restricted, so the contradiction has to be taken there.
;;;
;;; THE ARGUMENT.  `1 <= j` and `j <= 0` are jointly infeasible over RR, which
;;; `ineq` sees the moment j carries an `IN _ RR` certificate (`nn-in-rr`) --
;;; Fourier-Motzkin eliminates j and is left with 1 <= 0.  From `1 <= 0` and
;;; `0 <= 1` antisymmetry gives `1 = 0`, and `rr-pos-ne-zero` at 1 -- fed by
;;; `rr-zero-lt-one` -- gives `not(1 = 0)`.  `ai` on that is FALSITY.
;;;
;;; `contra' WOULD HAVE DONE THE WHOLE THING and cannot be used: contra.scm
;;; loads at load.scm ~2530, sixteen hundred entries below the earliest citer of
;;; this fact.  A tactic that exists is not a tactic that is available; check the
;;; load position before reaching for one in a structure-library-adjacent proof.
;;;
;;; WHERE IT SITS.  After rr-order-basics (rr-pos-ne-zero, rr-lt-implies-le),
;;; rr-recip-order (rr-zero-lt-one) and nn-order-basics (nn-in-rr); BEFORE
;;; nn-order-proof, the earliest citer.  Retires the `well-known` support of the
;;; same name from structure-library/order-lemmas.scm, statement byte-identical.

;;; 1 <= j  =>  not(j <= 0), for j in NN.
(define (nz-idx form)
  (let loop ((l (dk-asms)) (i 1))
    (cond ((null? l) (error "nz-idx: not in context" form))
          ((equal? (car l) form) i)
          (else (loop (cdr l) (+ i 1))))))
(define (nz-ineq . fs) (apply ineq (map nz-idx fs)))

;;; peel until the goal's head is HEAD; guard on progress, error on a miss.
(define (nz-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "nz-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff '(FORALL j (IMPLIES (IN j NN) (IMPLIES (<= 1 j) (NOT (<= j 0)))))))
(di)
(di)
(di)                                  ; assume j <= 0, goal FALSITY
(fact 'nn-in-rr 'j)
(fact 'rr-one-in)
(fact 'rr-zero-in)
;; the two hypotheses are jointly infeasible over RR; the oracle sees it once
;; j carries an IN _ RR certificate.
(have! '(<= 1 0) (lambda () (nz-ineq '(<= 1 j) '(<= j 0))))
(fact 'rr-zero-lt-one)
(fact 'rr-lt-implies-le 0 1)
(have! '(AND (IN 1 RR) (IN 0 RR)))
(have! '(AND (<= 1 0) (<= 0 1)))
(fact 'rr-leq-antisymmetric 1 0)      ; 1 = 0
(fact 'rr-pos-ne-zero 1)              ; 0 < 1, so not(1 = 0)
(ai '(NOT (= 1 0)))
(qed 'nn-not-le-zero-pos)

(topic! 'nn-not-le-zero-pos 'inequalities)
(alias! 'nn-not-le-zero-pos "a natural at least 1 is not at most 0")

;;; =====================================================================
;;; succ a <= b makes b <= a impossible.  Retires the `well-known' support from
;;; structure-library/mat-equiv.scm; statement byte-identical.  Sixth in the
;;; greedy ranking at SIX bills.  `nn-succ-plus-one' turns succ a into a + 1,
;;; after which succ a <= b <= a is a + 1 <= a and the oracle sees it.
;;; =====================================================================
(sp (make-wff '(FORALL a (IMPLIES (IN a NN)
     (FORALL b (IMPLIES (IN b NN)
       (IMPLIES (<= (succ a) b) (NOT (<= b a))))))))) 
(nz-peel-to! 'NOT)
(di)                                   ; assume b <= a, goal FALSITY
(fact 'nn-in-rr 'a) (fact 'nn-in-rr 'b)
(fact 'nn-succ-closed 'a)
(fact 'nn-in-rr '(succ a))
(fact 'nn-succ-plus-one 'a)            ; succ a = a + 1
(fact 'rr-one-in) (fact 'rr-zero-in)
;; succ a <= b <= a with succ a = a+1 is a+1 <= a: infeasible over RR
(have! '(<= 1 0)
  (lambda () (nz-ineq '(<= (succ a) b) '(<= b a) '(= (succ a) (+ a 1)))))
(fact 'rr-zero-lt-one)
(fact 'rr-lt-implies-le 0 1)
(have! '(AND (IN 1 RR) (IN 0 RR)))
(have! '(AND (<= 1 0) (<= 0 1)))
(fact 'rr-leq-antisymmetric 1 0)
(fact 'rr-pos-ne-zero 1)
(ai '(NOT (= 1 0)))
(qed 'nn-succ-le-antisym)

(topic! 'nn-succ-le-antisym 'inequalities)
(alias! 'nn-succ-le-antisym "a successor at most b puts b above a")
