;;; rr-recip-order.scm -- the L1 rung of the "attach the loose ends" program:
;;; the reciprocal's SIGN, and the two field facts it stands on.
;;;
;;; WHY THESE FOUR.  The elementary order facts of the reals were asserted
;;; supports (order-predicates.scm), and each of the analytic ones bottoms out
;;; on the RECIPROCAL: `nn-recip-succ-pos' ("1/(n+1) is a positive real") says
;;; in its own warrant that it "needs recip-order lemmas the tree does not have
;;; yet", and `rr-pos-halvable' wants the witness eps * recip(1+1) to be
;;; positive.  Nothing in the tree said a reciprocal of a positive is positive.
;;; That is what `rr-recip-pos' is.
;;;
;;; WHAT THEY REST ON.  The two multiplicative facts below (`rr-mul-zero',
;;; `rr-zero-lt-one') are closed by the `ineq' oracle alone -- both are linear
;;; over RR once the products are linearised (a * 0 has coefficient 0), so they
;;; cost no asserted lemma at all.  `rr-mul-pos' and `rr-recip-pos' additionally
;;; cite the `rr-lt-*' family of order-lemmas.scm, which is still ASSERTED
;;; (well-known).  So this file discharges one layer and names the next: the
;;; rr-lt-* lemmas -- scale-pos, trichotomy, trans, implies-le, add,
;;; diff-pos/neg -- are the remaining elementary loose ends on the strict order,
;;; and each of them is derivable from the ordered-field axioms in
;;; number-systems.scm.  See the `attach the loose ends' ladder.

;;; --------------------------------------------------------------------
;;; File-local driver helpers (the `rro-' prefix; two of them, so they stay
;;; here rather than in driver-kit.scm).

;;; Peel the whole FORALL/IMPLIES prefix.  `di' is greedy WITHIN one binder
;;; level but stops at the next, so a guarded FORALL followed by two
;;; implications takes three calls, not one.  Guarded on progress by the head.
(define (rro-peel!)
  (let loop ((g (dk-goal)) (n 0))
    (when (and (pair? g) (memq (car g) '(FORALL IMPLIES)) (< n 12))
      (di)
      (loop (dk-goal) (+ n 1)))))

;;; The 1-based index of the assumption that IS this formula -- what `ineq'
;;; wants.  Errors rather than returning #f: a mis-cited premise index is a
;;; silently different proof.
(define (rro-at form)
  (let loop ((as (dk-asms)) (i 1))
    (cond ((null? as) (error "rro-at: no assumption is" form))
          ((equal? (car as) form) i)
          (else (loop (cdr as) (+ i 1))))))

;;; --------------------------------------------------------------------
;;; a * 0 = 0.
;;;
;;; Not an axiom of number-systems.scm (RR's axioms give a + 0 = a and 1 * a = a
;;; and nothing about a * 0), and the ring-level `ring-mul-zero-left' is about a
;;; RING STRUCTURE's (MUL r), not the bare `*' the reals are written with.  The
;;; Farkas oracle has it directly: multiplication by the literal 0 is linear.
(sp (make-wff (forall-guarded 'a '(IN a RR) '(= (* a 0) 0))))
(di)
(ineq)
(qed 'rr-mul-zero)
(category! 'rr-mul-zero 'inequalities)

;;; 0 < 1.  Named because it is cited by hand constantly and because, until this
;;; file, NOTHING in the tree stated it -- the ordered-field axioms give
;;; reflexivity, antisymmetry, transitivity, totality and compatibility, none of
;;; which distinguishes 0 from 1.  Ground, so the oracle decides it.
(sp (make-wff '(< 0 1)))
(ineq)
(qed 'rr-zero-lt-one)
(category! 'rr-zero-lt-one 'inequalities)

;;; --------------------------------------------------------------------
;;; The product of two positive reals is positive.
;;;
;;; rr-leq-mul-nonneg (number-systems.scm) gives only the NONSTRICT form
;;; 0 <= a, 0 <= b => 0 <= a*b, which is exactly the fact that cannot conclude a
;;; strict inequality.  Scaling the strict 0 < b by the positive a and rewriting
;;; a * 0 to 0 does it.
(sp (make-wff (forall-guarded 'a '(IN a RR)
               (forall-guarded 'b '(IN b RR)
                 '(IMPLIES (< 0 a) (IMPLIES (< 0 b) (< 0 (* a b))))))))
(rro-peel!)
(fact 'rr-zero-in)
(have! '(AND (< 0 a) (< 0 b)))
(fact 'rr-lt-scale-pos 'a 0 'b)          ; a * 0 < a * b
(have! '(AND (IN a RR) (IN b RR)))
(fact 'rr-mul-closed 'a 'b)
(fact 'rr-mul-zero 'a)
(ineq (rro-at '(< (* a 0) (* a b))) (rro-at '(= (* a 0) 0)))
(qed 'rr-mul-pos)
(category! 'rr-mul-pos 'inequalities)

;;; --------------------------------------------------------------------
;;; 0 < a  =>  0 < recip a.
;;;
;;; By trichotomy on 0 and recip a.  Both bad cases die on the SAME fact,
;;; a * recip a = 1, read through the oracle: with `a * recip a' as an atom,
;;; "= 1" plus either "= a * 0" (the zero case, after the substitution) or
;;; "< a * 0" (the negative case, after scaling by a > 0) is infeasible, since
;;; a * 0 linearises to 0.  An infeasible premise set closes any order goal.
;;;
;;; The unfolding of `0 < a' by mac-h REPLACES it, so the third case has to
;;; rebuild it (mac + from-context!) before citing rr-lt-scale-pos, which wants
;;; the strict form.  That is the mac-h trap in miniature.
(sp (make-wff (forall-guarded 'a '(IN a RR) '(IMPLIES (< 0 a) (< 0 (recip a))))))
(rro-peel!)
(fact 'rr-zero-in)
(mac-h '< '(< 0 a))                      ; 0 <= a and not(0 = a)
(dk-split! '(AND (<= 0 a) (NOT (= 0 a))))
(fact 'neq-sym 0 'a)                     ; not(a = 0), which recip's guards want
(have! '(AND (IN a RR) (NOT (= a 0))))
(fact 'rr-recip-closed 'a)
(fact 'rr-recip-inverse 'a)              ; a * recip a = 1
(have! '(AND (IN a RR) (IN (recip a) RR)))
(fact 'rr-mul-closed 'a '(recip a))      ; the oracle must certify the atom
(have! '(AND (IN 0 RR) (IN (recip a) RR)))
(fact 'rr-lt-trichotomy 0 '(recip a))
(use-cases '((< 0 (recip a)) (= 0 (recip a)) (< (recip a) 0))
  ;; 0 < recip a -- the goal itself
  (lambda () (ass))
  ;; 0 = recip a -- then a * 0 = 1, and a * 0 is 0
  (lambda ()
    (have! '(= (* a 0) 1) (lambda () (subst '(= 0 (recip a))) (ass)))
    (ineq (rro-at '(= (* a 0) 1))))
  ;; recip a < 0 -- scaling by a > 0 gives 1 = a * recip a < a * 0 = 0
  (lambda ()
    (have! '(< 0 a) (lambda () (mac '<) (from-context!)))
    (have! '(AND (< 0 a) (< (recip a) 0)))
    (fact 'rr-lt-scale-pos 'a '(recip a) 0)
    (ineq (rro-at '(< (* a (recip a)) (* a 0)))
          (rro-at '(= (* a (recip a)) 1)))))
(qed 'rr-recip-pos)
(category! 'rr-recip-pos 'inequalities)
