;;; zz-order.scm -- the ORDER THEORY OF ZZ, proven.
;;;
;;; The integers had almost no order theory of their own in this tree.  Their
;;; order is RR's, restricted, and the only STRUCTURAL fact about ZZ anywhere is
;;; `zz-generated-by-nn' (number-systems.scm:236, primitive): every integer is a
;;; natural or the negative of one.  Everything below is that axiom plus RR's
;;; order, and nothing else.
;;;
;;;   zz-abs-in-nn      a in ZZ            =>  abs(a) in NN
;;;   zz-abs-cases      a in ZZ            =>  a = abs(a) or a = -abs(a)
;;;   zz-trichotomy     a in ZZ            =>  a < 0 or a = 0 or 0 < a
;;;   zz-discrete       a in ZZ, 0 < a     =>  1 <= a
;;;   zz-lt-succ-le     a, b in ZZ, a < b  =>  a + 1 <= b
;;;   zz-nonneg-in-nn   a in ZZ, 0 <= a    =>  a in NN
;;;
;;; WHY IT MATTERS.  `zz-is-euclidean-ring' -- the library's last `trust: none'
;;; bill, via zz-bezout -- needs the DIVISION ALGORITHM on ZZ, and the division
;;; algorithm needs exactly this block: the sign case split (zz-abs-cases,
;;; zz-trichotomy), the size measure landing in NN (zz-abs-in-nn), and the
;;; discreteness that makes "remainder strictly smaller" a descent
;;; (zz-discrete / zz-lt-succ-le).  gcd and Euclid's lemma sit on the same
;;; block.  The step plan for `zz-division' is at the END of this file.
;;;
;;; THE TECHNIQUE, and it is nn-order-via-rr.scm's one storey up: NN and ZZ
;;; carry no order axioms of their own, so an order fact about integers is
;;; proved by pushing the hypotheses into RR (`zz-in-rr' / `nn-in-rr'), letting
;;; the `ineq' oracle do the linear arithmetic, and letting `zz-generated-by-nn'
;;; supply the one thing RR cannot: that there is nothing strictly between 0 and
;;; 1 in ZZ.  Only `zz-discrete' has content; the other five are that axiom, a
;;; case split, and Fourier-Motzkin.
;;;
;;; NOTE ON DISCRETENESS.  The positive case of `zz-discrete' is where the
;;; naturals do the work: a = n with n /= 0, so n = succ(q) (nn-nonzero-is-succ,
;;; an INDUCTION in nn-parity-proof.scm) and 1 <= succ(q) (nn-one-le-succ).  The
;;; negative case never reaches the naturals at all -- 0 < a = -n and 0 <= n are
;;; jointly infeasible over RR, so `ineq' closes the branch from absurdity.
;;;
;;; LOAD WINDOW.  lo = 210: the deepest citation is `nn-nonzero-is-succ'
;;; (theorem-library/nn-parity-proof, load position 209).  Also cited:
;;; nn-order-ord (165: nn-zero-le, nn-one-le-succ), nn-order-basics (167:
;;; nn-in-rr, zz-in-rr), rr-order-basics (174: rr-lt-trichotomy,
;;; rr-pos-ne-zero), rr-abs-basics (177: rr-abs-of-nonneg, rr-abs-of-nonpos,
;;; rr-abs-cases, rr-abs-closed), binary-minus-laws (161: zz-sub-in-zz), and the
;;; primitives of number-systems (34).  hi = 297, theorem-library/zz-bezout-proof,
;;; the first consumer this block is being built for.  Nothing here is cited yet,
;;; so any slot in [210, 297) will do; beside nn-order-via-rr (216) is the
;;; natural home, since that file is the same technique for NN.

;;; =====================================================================
;;; HELPERS.  Prefix `zo-'.

;;; The arithmetic premises of the current context, by 1-BASED index (the
;;; oracle's convention, ineq-oracle.scm:206).  Anything whose head is not a
;;; relation is left out rather than named: a non-arithmetic premise is skipped
;;; by the oracle anyway, but an `=' between terms that cannot be certified in
;;; RR poisons the whole call (CLAUDE.md, the `contra' entry).
(define (zo-ineq-idx)
  (let loop ((l (dk-asms)) (i 1) (acc '()))
    (cond ((null? l) (reverse acc))
          ((and (pair? (car l)) (memq (caar l) '(< <= =)))
           (loop (cdr l) (+ i 1) (cons i acc)))
          (#t (loop (cdr l) (+ i 1) acc)))))

(define (zo-ineq!) (apply ineq (zo-ineq-idx)))

;;; (zo-gen-cases! A POS NEG) -- with (IN A ZZ) and (IN A RR) in context, cite
;;; `zz-generated-by-nn' at A, skolemize its witness n, land n's typings
;;; (n in RR, 0 <= n, -n in RR) on BOTH branches, and run POS on the branch
;;; assuming A = n and NEG on the branch assuming A = -n.  Each body is called
;;; with the eigenvariable n -- read off by dk-skolem!'s free-variable diff,
;;; never guessed from the binder.
(define (zo-gen-cases! a pos neg)
  (let* ((ex (dk-fact! 'zz-generated-by-nn a))
         (n  (dk-skolem! ex)))
    (fact 'nn-in-rr n)
    (fact 'nn-zero-le n)
    (fact 'rr-neg-closed n)
    (use-cases (list (list '= a n) (list '= a (list '- n)))
      (lambda () (pos n))
      (lambda () (neg n)))
    n))

;;; =====================================================================
;;; zz-abs-in-nn:  the absolute value of an integer is a NATURAL number.
;;;
;;; This is the size measure the division algorithm descends on, and it is the
;;; reason the whole file exists: `abs' is RR's, so nothing in the tree said
;;; that abs of an integer was even an integer, let alone a natural.
;;;
;;; a = n:   0 <= a, so |a| = a (rr-abs-of-nonneg) and a = n in NN.
;;; a = -n:  a <= 0, so |a| = -a (rr-abs-of-nonpos) and -a = n in NN.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ) (IN (abs a_) NN)))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'rr-zero-in)
(zo-gen-cases! 'a_
  (lambda (n)
    (have! '(<= 0 a_) (lambda () (zo-ineq!)))
    (fact 'rr-abs-of-nonneg 'a_)
    (subst '(= (abs a_) a_))
    (subst (list '= 'a_ n))
    (ass))
  (lambda (n)
    (have! '(<= a_ 0) (lambda () (zo-ineq!)))
    (fact 'rr-abs-of-nonpos 'a_)
    (subst '(= (abs a_) (- a_)))
    (have! (list '= '(- a_) n) (lambda () (zo-ineq!)))
    (subst (list '= '(- a_) n))
    (ass)))
(qed 'zz-abs-in-nn)
(topic! 'zz-abs-in-nn 'inequalities)

;;; =====================================================================
;;; zz-abs-cases:  an integer is its own absolute value, or minus it.
;;;
;;; Not an integer fact at all -- it is `rr-abs-cases' with the sign conditions
;;; discarded, which is the form a case split on the sign of an integer wants.
;;; Both branches are one `ineq' over the equation the RR case supplies.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ)
                 (OR (= a_ (abs a_)) (= a_ (- (abs a_))))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'rr-abs-closed 'a_)
(fact 'rr-abs-cases 'a_)
(use-cases (list '(AND (<= 0 a_) (= (abs a_) a_))
                 '(AND (NOT (<= 0 a_)) (= (abs a_) (- a_))))
  (lambda () (dk-split-all!) (oi-l) (zo-ineq!))
  (lambda () (dk-split-all!) (oi-r) (zo-ineq!)))
(qed 'zz-abs-cases)
(topic! 'zz-abs-cases 'inequalities)

;;; =====================================================================
;;; zz-trichotomy:  every integer is negative, zero, or positive.
;;;
;;; `rr-lt-trichotomy' at (a, 0), verbatim -- the nesting of the disjunction is
;;; the one that theorem produces, so `ass' closes it.  Stated here because a
;;; ZZ proof should not have to remember that ZZ's order is RR's.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ)
                 (OR (< a_ 0) (OR (= a_ 0) (< 0 a_)))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'rr-zero-in)
(fact 'rr-lt-trichotomy 'a_ 0)
(ass)
(qed 'zz-trichotomy)
(topic! 'zz-trichotomy 'inequalities)

;;; =====================================================================
;;; zz-discrete:  a positive integer is at least 1.
;;;
;;; THE ONE WITH CONTENT.  It is false in QQ, which satisfies every ring and
;;; order axiom ZZ has (zz-arith.scm's header is the statement of that gap), so
;;; it cannot be proved without `zz-generated-by-nn'.
;;;
;;; a = n:   0 < n, so n /= 0 (rr-pos-ne-zero), so n = succ(q)
;;;          (nn-nonzero-is-succ), and 1 <= succ(q) (nn-one-le-succ).
;;; a = -n:  0 < a = -n with 0 <= n is infeasible over RR; `ineq' closes the
;;;          branch outright, the goal never being reached on its own terms.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ) (IMPLIES (< 0 a_) (<= 1 a_))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'rr-zero-in)
(fact 'rr-one-in)
(zo-gen-cases! 'a_
  (lambda (n)
    (have! (list '< 0 n) (lambda () (zo-ineq!)))
    (fact 'rr-pos-ne-zero n)
    (let* ((ex (dk-fact! 'nn-nonzero-is-succ n))
           (q  (dk-skolem! ex)))
      (fact 'nn-succ-closed q)
      (fact 'nn-in-rr (list 'succ q))
      (fact 'nn-one-le-succ q)
      (zo-ineq!)))
  (lambda (n) (zo-ineq!)))
(qed 'zz-discrete)
(topic! 'zz-discrete 'inequalities)

;;; =====================================================================
;;; zz-lt-succ-le:  a < b  =>  a + 1 <= b, for integers.
;;;
;;; `zz-discrete' applied to the difference, which is an integer by
;;; `zz-sub-in-zz' (binary-minus-laws.scm).  This is the form every descent
;;; argument wants: it turns a strict inequality between integers into a gap of
;;; at least one, which is what makes a decreasing sequence of naturals finite.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ)
                 (FORALL b_ (IMPLIES (IN b_ ZZ)
                   (IMPLIES (< a_ b_) (<= (+ a_ 1) b_))))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'zz-in-rr 'b_)
(fact 'zz-sub-in-zz 'b_ 'a_)
(fact 'zz-in-rr '(- b_ a_))
(have! '(< 0 (- b_ a_)) (lambda () (zo-ineq!)))
(fact 'zz-discrete '(- b_ a_))
(zo-ineq!)
(qed 'zz-lt-succ-le)
(topic! 'zz-lt-succ-le 'inequalities)

;;; =====================================================================
;;; zz-nonneg-in-nn:  a non-negative integer IS a natural number.
;;;
;;; The converse of `nn-subset-zz' on the non-negative part, and the fact that
;;; lets a ZZ argument hand a quantity to an NN induction.  The division
;;; algorithm uses it to know that its remainder, once it is known non-negative,
;;; is a natural and so can be measured.
;;;
;;; a = n:   immediate.
;;; a = -n:  0 <= a = -n and 0 <= n force a = 0, and 0 in NN.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ ZZ) (IMPLIES (<= 0 a_) (IN a_ NN))))))
(dk-peel!)
(fact 'zz-in-rr 'a_)
(fact 'rr-zero-in)
(zo-gen-cases! 'a_
  (lambda (n) (subst (list '= 'a_ n)) (ass))
  (lambda (n)
    (have! '(= a_ 0) (lambda () (zo-ineq!)))
    (subst '(= a_ 0))
    (fact 'nn-zero-in)
    (ass)))
(qed 'zz-nonneg-in-nn)
(topic! 'zz-nonneg-in-nn 'inequalities)

;;; =====================================================================
;;; `zz-division' is PROVEN (2026-09-17) in theorem-library/zz-division.scm,
;;; together with `nn-division' and `zz-is-euclidean-ring', by the step plan
;;; that stood here from 2026-09-16 (archive/retired-2026-09-17/
;;; zz-order-division-plan.scm): nn-division by induction on a with b fixed,
;;; zz-division reduced to it at (|a|, |b|) with four sign cases and a signed
;;; remainder, and the Euclidean law from that with `abs' as the degree function.
