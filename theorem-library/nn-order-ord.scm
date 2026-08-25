;;; nn-order-ord.scm -- the elementary NN order block, PROVEN.  Seven facts that
;;; were `well-known' supports in structure-library/order-lemmas.scm are
;;; theorems here, every one billing `modulo 0'.
;;;
;;; WHY THEY ARE NOT PEANO, AND WHY THAT IS NOT A DEFECT.
;;;
;;; The NN base in number-systems.scm is three axioms -- nn-zero-in (:116),
;;; nn-succ-closed (:118) and the class-form induction schema nn-induction
;;; (:164) -- together with the arithmetic closure/assoc/comm/distrib/unit laws.
;;; NOTHING there says 0 is not a successor, and nothing says succ is injective.
;;; So `succ n /= 0' is NOT derivable from that base, and no amount of induction
;;; will produce it: NN = {0} with succ 0 = 0 satisfies nn-zero-in,
;;; nn-succ-closed and nn-induction, and refutes it.  Inducting on `0 <= n'
;;; instead fares no better -- the successor step wants n <= succ n, which is
;;; the same missing fact one storey down.
;;;
;;; The facts come from the ORDINALS, which have been `primitive' since
;;; 2026-07-27 (the user's decision that they are foundational rather than owed
;;; an argument), and which say exactly what NN's own axioms decline to:
;;;
;;;   nn-subset-ord       n in NN  =>  n in ORD
;;;   ord-zero-least      0 ORD-LE alpha
;;;   ord-succ-above      alpha ORD-LT succ_ORD alpha
;;;   ord-succ-immediate  alpha ORD-LT beta  =>  succ_ORD alpha ORD-LE beta
;;;   ord-le-refl / -antisymm / -trans / -total,  ord-lt-iff
;;;   ord-succ-nn         succ_ORD n = succ n            on NN
;;;   ord-le-nn-compat    ORD-LE  IS  numeric <=         on NN
;;;
;;; The last two are the bridges, and they are what makes every proof below the
;;; same three moves: cross to ORD (nn-subset-ord), argue with the ordinal
;;; order, cross back (ord-le-nn-compat).  So the discreteness of NN is not an
;;; extra assumption ABOUT the naturals; it is the ordinal order restricted to
;;; them.  That is also why the file is named for the route and not for NN.
;;;
;;; CONSEQUENCE THE INTEGRATION ARC WANTED.  `nn-succ-nonzero'
;;; (theorem-library/nn-parity-proof.scm:158) was already PROVEN, from
;;; nn-zero-le and nn-le-imp-neq-succ -- both of which were asserted, so it
;;; billed `modulo {nn-zero-le, nn-le-imp-neq-succ}' [trust: well-known].  Both
;;; are theorems here, so it now bills `modulo 0' with its driver untouched.
;;; Note there is no separate "as a real" form to state: NN <= ZZ <= QQ <= RR
;;; are genuine inclusions of SETS, so `NOT (= (succ k) 0)' is one formula about
;;; one object, and it is already the antecedent `rr-recip-inverse'
;;; (number-systems.scm:395) asks for.
;;;
;;; LOADS after interactive / proof-debt / driver-kit, and BEFORE
;;; theorem-library/nn-order-basics (which cites nn-le-succ) -- the earliest
;;; citation of anything in this block.

;;; ---- file-local kit (nq- prefix; never named like a tactic) --------------
;;; Three of these exist only because `fact' will not split a conjunctive
;;; antecedent, and ord-le-trans / ord-le-antisymm / ord-le-total /
;;; ord-le-nn-compat / ord-succ-immediate all state their hypotheses as one AND.

;; `have!' with NO thunk proves the side goal with driver-kit's `from-context!',
;; which di-splits an AND goal and recurses.  That is what this needs, and the
;; hand-rolled (di)(ass)(focus b)(ass) it replaced was WRONG in one case: when
;; BOTH conjuncts are already in context, `di' hands back a single leaf, the
;; first `ass' closes the whole side goal, and the focus helper then errors
;; looking for a leaf that no longer exists.
(define (nq-and2 a b) (have! (list 'AND a b)))

;; Consume an IFF in the context: `ai' on an IFF is iff-elim (it lands BOTH
;; implications), and `detach!' then takes the one wanted -- note it takes the
;; IMPLIES, not its antecedent.  This is the idiom nn-least-element.scm exposed
;; and it is what the bridge needs, ord-le-nn-compat being a CONDITIONAL
;; biconditional and so not usable as a rewrite macete.
;;
;; `prop' would decide every one of these, and it was the first draft.  It does
;; not survive here: the ORD contexts run to 29 distinct atoms and the cap is 12
;; (*prop-atom-cap*, the search being 2^n).  Naming the implication costs one
;; line and does not grow with the context.
;; ord-le-nn-compat's IFF is always (IFF (ORD-LE A B) (<= A B)); these consume
;; it in the two directions.
(define (nq-le->ord! a b)
  (ai (list 'IFF (list 'ORD-LE a b) (list '<= a b)))
  (detach! (list 'IMPLIES (list '<= a b) (list 'ORD-LE a b))))
(define (nq-ord->le! a b)
  (ai (list 'IFF (list 'ORD-LE a b) (list '<= a b)))
  (detach! (list 'IMPLIES (list 'ORD-LE a b) (list '<= a b))))

;; (ORD-LT A B) from its two halves, and the two halves from it.  ord-lt-iff is
;; UNGUARDED, hence a live macete in both directions -- `mac' on the goal,
;; `mac-h' on an assumption.
(define (nq-lt! a b)
  (have! (list 'ORD-LT a b) (lambda () (mac 'ord-lt-iff) (from-context!))))
(define (nq-lt-split! a b)
  (mac-h 'ord-lt-iff (list 'ORD-LT a b))
  (dk-split! (list 'AND (list 'ORD-LE a b) (list 'NOT (list '= a b)))))

;; `di' until the goal head stops being peelable.  NOT a `di' count: `di' is
;; greedy over a leading FORALL/IMPLIES prefix but STOPS at an implication whose
;; antecedent is not a typing, so the statements below need two or three calls
;; and the number differs from statement to statement.  Loop on the SHAPE.
(define (nq-peel!)
  (let loop ((prev #f) (n 0))
    (let ((g (dk-goal)))
      (if (and (< n 12) (not (equal? g prev))
               (pair? g) (memq (car g) '(FORALL IMPLIES NOT)))
          (begin (di) (loop g (+ n 1)))))))

;; The ordinal successor facts for a term T already typed (IN T NN):
;;   (IN T ORD), (IN (succ T) NN), (ORD-LE T (succ T)), (NOT (= T (succ T))).
;; `ord-succ-above' is stated on succ_ORD, so the landed strict inequality is
;; rewritten by `mac-h' with ord-succ-nn -- the NN bridge -- before anything
;; else touches it.  A guarded macete on an ASSUMPTION applies and posts its
;; side condition; on a GOAL it would simply not fire.
(define (nq-succ! t)
  (fact 'nn-subset-ord t)
  (fact 'nn-succ-closed t)
  (fact 'ord-succ-above t)
  (mac-h 'ord-succ-nn (list 'ORD-LT t (list 'succ_ORD t)))
  (nq-lt-split! t (list 'succ t)))

;; Land the compatibility IFF at (A,B); both must already be typed in NN.
(define (nq-compat! a b)
  (nq-and2 (list 'IN a 'NN) (list 'IN b 'NN))
  (fact 'ord-le-nn-compat a b))

(define (nq-trans! a b c)
  (nq-and2 (list 'ORD-LE a b) (list 'ORD-LE b c))
  (fact 'ord-le-trans a b c))

(define (nq-antisym! a b)
  (nq-and2 (list 'ORD-LE a b) (list 'ORD-LE b a))
  (fact 'ord-le-antisymm a b))

(define (nq-immediate! a b)
  (have! (list 'AND (list 'IN a 'ORD) (list 'AND (list 'IN b 'ORD) (list 'ORD-LT a b))))
  (fact 'ord-succ-immediate a b))

;; Close the focus goal (<= A B) from (ORD-LE A B), both typed in NN.
(define (nq-close-le! a b)
  (nq-compat! a b)
  (nq-ord->le! a b)
  (ass))

;;; =====================================================================
;;; nn-one-in:  1 in NN.
;;; Was a `well-known' support whose warrant WAS the derivation ("1 = succ 0 in
;;; NN") -- two axioms and a ground arithmetic step, run here.
(sp (make-wff '(IN 1 NN)))
(fact 'nn-zero-in)
(fact 'nn-succ-closed 0)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(ass)
(qed 'nn-one-in)
(topic! 'nn-one-in 'plumbing)

;;; =====================================================================
;;; nn-zero-le:  0 <= n.
;;; 0 is the least ORDINAL (ord-zero-least), n is one (nn-subset-ord), and
;;; ORD-LE on NN is <= (ord-le-nn-compat).  No induction: see the header.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (<= 0 n_)))))
(nq-peel!)
(fact 'nn-zero-in)
(fact 'nn-subset-ord 'n_)
(fact 'ord-zero-least 'n_)
(nq-close-le! 0 'n_)
(qed 'nn-zero-le)
(topic! 'nn-zero-le 'inequalities)

;;; =====================================================================
;;; nn-le-succ:  k <= succ k.
;;; ord-succ-above gives k ORD-LT succ k outright; ord-lt-iff drops the strict
;;; part and the bridge brings it down to NN.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN) (<= k_ (succ k_))))))
(nq-peel!)
(nq-succ! 'k_)
(nq-close-le! 'k_ '(succ k_))
(qed 'nn-le-succ)
(topic! 'nn-le-succ 'plumbing)

;;; =====================================================================
;;; nn-le-imp-neq-succ:  j <= k  =>  j /= succ k.
;;; By contradiction, and the ONE step that is not bookkeeping: with j = succ k
;;; in context, `subst' rewrites the side goal (ORD-LE (succ k) k) back to the
;;; hypothesis (ORD-LE j k).  Antisymmetry against k ORD-LE succ k then gives
;;; k = succ k, which ord-succ-above has already denied.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN) (FORALL j_ (IMPLIES (IN j_ NN)
     (IMPLIES (<= j_ k_) (NOT (= j_ (succ k_))))))))))
(nq-peel!)                              ; ... and the NOT too: goal is FALSITY
(fact 'nn-subset-ord 'j_)
(nq-succ! 'k_)
(nq-compat! 'j_ 'k_)
(nq-le->ord! 'j_ 'k_)
(have! '(ORD-LE (succ k_) k_) (lambda () (subst '(= (succ k_) j_)) (ass)))
(nq-antisym! 'k_ '(succ k_))
(ai '(NOT (= k_ (succ k_))))
(qed 'nn-le-imp-neq-succ)
(topic! 'nn-le-imp-neq-succ 'inequalities)

;;; =====================================================================
;;; nn-succ-mono:  a <= b  =>  succ a <= succ b.
;;; ord-succ-immediate is the workhorse: it wants a ORD-LT succ b, i.e. the
;;; inequality (transitivity through b ORD-LE succ b) AND the disequality --
;;; and the disequality is nn-le-imp-neq-succ, just proved.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN) (FORALL b_ (IMPLIES (IN b_ NN)
     (IMPLIES (<= a_ b_) (<= (succ a_) (succ b_)))))))))
(nq-peel!)
(fact 'nn-subset-ord 'a_)
(fact 'nn-succ-closed 'a_)
(nq-succ! 'b_)
(fact 'nn-subset-ord '(succ b_))
(nq-compat! 'a_ 'b_)
(nq-le->ord! 'a_ 'b_)
(nq-trans! 'a_ 'b_ '(succ b_))
(fact 'nn-le-imp-neq-succ 'b_ 'a_)
(nq-lt! 'a_ '(succ b_))
(nq-immediate! 'a_ '(succ b_))
(mac-h 'ord-succ-nn '(ORD-LE (succ_ORD a_) (succ b_)))
(nq-close-le! '(succ a_) '(succ b_))
(qed 'nn-succ-mono)
(topic! 'nn-succ-mono 'inequalities)

;;; =====================================================================
;;; nn-one-le-succ:  1 <= succ n.  Monotonicity at 0 <= n, then 1 = succ 0.
;;; This is the fact prove-scripts/drives/poly-antiderivative-drive.scm named as
;;; the one asserted rung under Example 4.7; it is a theorem now, but the drive
;;; does not need it -- nn-succ-nonzero is the direct statement and it is
;;; `modulo 0' as of this file.
(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (<= 1 (succ n_))))))
(nq-peel!)
(fact 'nn-zero-in)
(fact 'nn-zero-le 'n_)
(fact 'nn-succ-mono 0 'n_)
(have! '(= 1 (succ 0)) (lambda () (arith)))
(subst '(= 1 (succ 0)))
(ass)
(qed 'nn-one-le-succ)
(topic! 'nn-one-le-succ 'inequalities)

;;; =====================================================================
;;; nn-le-succ-cases:  j <= succ k  =>  j <= k  or  j = succ k.
;;; THE discreteness statement, and the only proof here that splits.  On the
;;; NOT(j ORD-LE k) side, totality gives k ORD-LE j and reflexivity refutes
;;; k = j, so k ORD-LT j; ord-succ-immediate lifts that to succ k ORD-LE j, and
;;; antisymmetry against the hypothesis delivers the second disjunct.
(sp (make-wff '(FORALL k_ (IMPLIES (IN k_ NN) (FORALL j_ (IMPLIES (IN j_ NN)
     (IMPLIES (<= j_ (succ k_)) (OR (<= j_ k_) (= j_ (succ k_))))))))))
(nq-peel!)
(fact 'nn-subset-ord 'j_)
(nq-succ! 'k_)
(fact 'nn-subset-ord '(succ k_))
(nq-compat! 'j_ '(succ k_))
(nq-le->ord! 'j_ '(succ k_))
(use-em '(ORD-LE j_ k_)
        (lambda () (oi-l) (nq-close-le! 'j_ 'k_))
        (lambda ()
          (oi-r)
          (have! '(AND (IN k_ ORD) (IN j_ ORD)))
          (fact 'ord-le-total 'k_ 'j_)
          ;; totality's OR against the branch hypothesis.  `ai' on the NOT
          ;; closes the impossible case whatever the goal is (not-elim), which
          ;; is why the second body needs no more than one line.
          (use-cases (list '(ORD-LE k_ j_) '(ORD-LE j_ k_))
            (lambda ()
              (fact 'ord-le-refl 'k_)
              (fact 'ord-le-refl 'j_)
              ;; k /= j: were they equal, `subst' would turn the side goal
              ;; (ORD-LE j k) into a reflexivity, contradicting the branch.
              (have! '(NOT (= k_ j_))
                     (lambda () (di)
                                (have! '(ORD-LE j_ k_)
                                       (lambda () (subst '(= k_ j_)) (ass)))
                                (ai '(NOT (ORD-LE j_ k_)))))
              (nq-lt! 'k_ 'j_)
              (nq-immediate! 'k_ 'j_)
              (mac-h 'ord-succ-nn '(ORD-LE (succ_ORD k_) j_))
              (nq-antisym! 'j_ '(succ k_))
              (ass))
            (lambda () (ai '(NOT (ORD-LE j_ k_)))))))
(qed 'nn-le-succ-cases)
(topic! 'nn-le-succ-cases 'inequalities)
