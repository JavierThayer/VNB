;;; RETIRED 2026-09-17 (proven): power-zero-base (was an add-to-pss here) -- theorem-library/rake-combinatorics.scm
;;; theorem-library/taylor-proof.scm -- Taylor's theorem, Lagrange remainder.
;;;   f^(n) C^0 on [a,x], f^(n+1) exists on (a,x), a<x  =>  there is theta in
;;;   (a,x) with  (n+1)! * R_n(x) = f^(n+1)(theta) * (x-a)^(n+1),
;;;   where R_n(x) = f(x) - TAYLOR-POLY(f,a,n,x).
;;; Strategy (Cauchy-MVT route): apply generalized-mvt to
;;;     G(t) = f(x) - TAYLOR-POLY(f,t,n,x)        (remainder as a fn of the base)
;;;     H(t) = (x-t)^(n+1)
;;; on [a,x].  G(x)=0, G(a)=R_n; H(x)=0, H(a)=(x-a)^(n+1); the telescoping
;;;     G'(t) = -(f^(n+1)(t)/n!)(x-t)^n,   H'(t) = -(n+1)(x-t)^n
;;; are warranted calc-101 supports (the f^(n+1)/n! (x-t)^n collapse of the
;;; differentiated Taylor sum; same warrant style as mvt-aux-diff/gmvt-aux-diff).
;;; gMVT gives G'(theta)(H(x)-H(a)) = H'(theta)(G(x)-G(a)); substituting and
;;; cancelling (x-theta)^n (>0) clears to the stated identity.
;;; Reuses deriv-constant-proof's global dc-* helpers; loads after
;;; generalized-mvt-proof.  Uses `fact', no bc*.
;;; ====================================================================
;;; RETIRED 2026-09-14 (proven): taylor-G-in-fun -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-H-in-fun -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-G-at-x -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-G-at-a -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-H-at-x -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-H-at-a -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-poly-in-rr -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-deriv-real -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-H-diff -- proven in the GUARDED block spliced below (was theorem-library/taylor-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-G-diff -- theorem-library/taylor-g-diff.scm (statement now GUARDED on n in NN, x in RR)
;;; RETIRED 2026-09-14 (proven): taylor-G-cont -- proven in the second spliced block (was theorem-library/taylor-gmvt-guarded.scm), GUARDED
;;; RETIRED 2026-09-14 (proven): taylor-H-cont -- proven in the second spliced block (was theorem-library/taylor-gmvt-guarded.scm), GUARDED
;;; RETIRED 2026-09-14 (proven): taylor-gmvt-cont -- proven in the second spliced block (was theorem-library/taylor-gmvt-guarded.scm), GUARDED
;;; RETIRED 2026-09-14 (proven): taylor-gmvt-diff -- proven in the second spliced block (was theorem-library/taylor-gmvt-guarded.scm), GUARDED
;;; RETIRED 2026-09-14 (proven): rr-power-pos -- proven in the third spliced block (was theorem-library/taylor-clear-guarded.scm)
;;; RETIRED 2026-09-14 (proven): rr-cancel-mul-left -- proven in the third spliced block (was theorem-library/taylor-clear-guarded.scm)
;;; RETIRED 2026-09-14 (proven): rr-recip-factorial -- proven in the third spliced block (was theorem-library/taylor-clear-guarded.scm)
;;; RETIRED 2026-09-14 (proven): taylor-clear -- proven in the third spliced block (was theorem-library/taylor-clear-guarded.scm)

;;; TAYLOR-POLY(f,a,n,x) = Sum_{k=0}^{n} f^(k)(a) (x-a)^k / k!
(def-functoid 'TAYLOR-POLY '(f a n x)
  '(SERIES-PARTIAL-SUM
     (VNB-LAMBDA k NN (* (* ((NTH-DERIV f k) a) (power (- x a) k)) (recip (FACTORIAL k))))
     (succ n)))

;;; TAYLOR-DIFFERENTIABLE(f,a,x,n): f^(k) (k<=n) continuous on [a,x] and
;;; differentiable on (a,x) with derivative f^(k+1).  The clean hypothesis.
(def-predicate 'TAYLOR-DIFFERENTIABLE '(f a x n)
  '(AND
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (IN t (CCINT a x))
           (IS-CONTINUOUS-AT RR-MS RR-MS (NTH-DERIV f k) t)))))
     (FORALL k (IMPLIES (AND (IN k NN) (<= k n))
        (FORALL t (IMPLIES (AND (< a t) (< t x))
           (IS-DIFF-AT (NTH-DERIV f k) t ((NTH-DERIV f (succ k)) t))))))))

;;; file-local auxiliary functions (free f,x,n; bind z -- NOT the point var, to
;;; avoid capture-rename when instantiating a support at point t)
(define GT '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define HT '(VNB-LAMBDA z RR (power (- x z) (succ n))))
;;; their warranted derivative values at t
(define (GVAL t) (list '- 0 (list '* (list '* '(recip (FACTORIAL n)) (list (list 'NTH-DERIV 'f '(succ n)) t)) (list 'power (list '- 'x t) 'n))))
(define (HVAL t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
;;; the gMVT-shaped continuity / differentiability hypotheses for (GT, HT)
(define GHCONT (list 'FORALL 't (list 'IMPLIES '(IN t (CCINT a x))
                 (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS GT 't)
                            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS HT 't)))))
(define GHDIFF (list 'FORALL 't (list 'IMPLIES '(AND (IN t RR) (AND (< a t) (< t x)))
                 (list 'AND (list 'FORSOME 'L (list 'IS-DIFF-AT GT 't 'L))
                            (list 'FORSOME 'M (list 'IS-DIFF-AT HT 't 'M))))))

;;; --- the calc-101 facts for G, H: were supports here; now THEOREMS in the two spliced blocks below ---




;;; gMVT-shaped hypotheses, warranted directly (G,H continuous on [a,x] and
;;; differentiable on (a,x)) -- assembled from the per-function facts above.


;;; function-typing of the auxiliaries.
;;;
;;; BOTH BIND n, and did not until 2026-08-03.  GT and HT mention the degree n,
;;; and these two statements left it FREE -- alone among the taylor-* supports,
;;; whose siblings above all quantify it.  A free variable in an installed
;;; formula is not a schema: it means whatever `n' denotes where the fact is
;;; cited, so these worked only because taylor-lagrange's own eigenvariable
;;; happens to be spelled `n' too.  Rename that binder and the citation quietly
;;; becomes a statement about a different, unrelated n.  It is the case-fold
;;; disease one level down -- a name collision that happened to be benign.


;;; endpoint computations
;; Guarded 2026-07-23.  TAYLOR-POLY(f,x,n,x) mentions the higher derivatives
;; f^(k)(x) (k<=n), so it is DEFINED only when those exist as reals; without a
;; guard the unrestricted forall f,x over-asserts (for a non-differentiable f the
;; polynomial is undefined while f(x) may not be, so neither `=' nor `==' holds).
;; Under the guard both sides are defined and this is a genuine partial equality.
;;;
;;; PROVEN 2026-08-29.  Until then this was an `add-to-pss' + `warrant!
;;; 'reference', and the warrant text WAS the proof -- written out in prose and
;;; never run (the species of comment CLAUDE.md warns about).  It is now
;;; mechanized, `modulo 0', by exactly the route that text named:
;;;
;;;   TAYLOR-POLY(f,x,n,x) unfolds (the def-functoid at the head of this file)
;;;   to  SERIES-PARTIAL-SUM(k |-> f^(k)(x) . (x-x)^k . recip(k!),  succ n),
;;;   and the sum falls to INDUCTION ON THE DEGREE:
;;;     base   SPS(term, succ 0) = SPS(term,0) + term(0) = 0 + f(x).1.recip(0!)
;;;     step   SPS(term, succ(succ n)) = SPS(term, succ n) + term(succ n),
;;;            and term(succ n) carries (x-x)^(succ n) = 0^(succ n) = 0.
;;;
;;; THE INDUCTION IS A SEPARATE THEOREM (`taylor-center-partial-sum') because
;;; `ni' tests the goal's SHAPE literally and the statement below binds n
;;; INNERMOST; the headline instantiates it.  Restating the headline with n
;;; outermost was not an option -- every citer sees the formula it always saw.
;;;
;;; THE STEP'S ONE PIECE OF BOOKKEEPING is the guard.  The induction hypothesis
;;; asks for f^(k)(x) in RR for k <= n while the goal supplies it for
;;; k <= succ n, so the WEAKER guard is rebuilt from the stronger one
;;; (nn-le-succ, then nn-le-trans-guarded) before the hypothesis can be used.
;;;
;;; WHAT COST THE MOST was not the analysis but a TYPING.  `series-partial-sum-
;;; succ' is guarded on BOTH its arguments being real, so each step of the
;;; recurrence owes the realness of the summand -- and the summand runs through
;;; recip(k!), which needs k! /= 0.  Nothing in the tree said so: `factorial-in-
;;; nn' is an unwarranted axiom, and citing it bills the whole result
;;; `trust: none'.  So `factorial-real-pos' proves  n! in RR and 0 < n!  in one
;;; induction (rr-mul-pos on the recurrence), and `recip-factorial-in-rr' reads
;;; the reciprocal's typing off it.
;;;
;;; AND THE PARTIAL SUM'S OWN REALNESS CANNOT COME FROM `series-partial-sum-
;;; in-rr'.  The summand is real only for k <= n -- above the degree f^(k)(x)
;;; need not exist -- so the sequence is NOT an element of FUN(NN,RR) and that
;;; theorem does not apply.  It comes from the INDUCTION HYPOTHESIS instead,
;;; which says the sum IS f(x): the equation is the typing.
;;;
;;; The nine lemmas below are proved here rather than borrowed because the tree
;;; had none of them; all are `modulo 0'.  (`power-zero-succ' duplicates the
;;; PSS support `power-zero-base' immediately after this block, which is now
;;; retirable.)

;;; ---- file-local shapes (the `tpc-' prefix; never named like a tactic) ----
;;; the Taylor summand at the centre, k |-> f^(k)(x) (x-x)^k recip(k!)
(define (tpc-term f x)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) x) (list 'power (list '- x x) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))
;;; the derivative-existence guard of the statement, at degree n
(define (tpc-guard f x n)
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k n))
                         (list 'IN (list (list 'NTH-DERIV f 'k) x) 'RR))))

;;; ---- the RR micro-identities.  `crs' decides each over VARIABLES; it is
;;; applied to the terms by citation, since crs sees neither `recip' nor a
;;; symbolic `power' (dyadic-weights.scm makes the same move).
(sp (make-wff '(= (recip 1) 1)))
(fact 'rr-one-in)
(have! '(NOT (= 1 0)) (lambda () (arith)))
(have! '(AND (IN 1 RR) (NOT (= 1 0))))
(fact 'rr-recip-inverse 1)                    ; 1 * recip 1 = 1
(fact 'rr-recip-closed 1)
(fact 'rr-one-mul '(recip 1))                 ; 1 * recip 1 = recip 1
(fact 'eq-sym '(* 1 (recip 1)) '(recip 1))
(fact 'eq-trans '(recip 1) '(* 1 (recip 1)) 1)
(ass)
(qed 'rr-recip-one)
(topic! 'rr-recip-one 'analysis)

(sp (make-wff '(FORALL v (IMPLIES (IN v RR) (= (* 0 v) 0)))))
(di) (crs)
(qed 'rr-zero-mul)
(topic! 'rr-zero-mul 'analysis)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (= (+ 0 u) u)))))
(di) (crs)
(qed 'rr-zero-add)
(topic! 'rr-zero-add 'analysis)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
   (= (* (* u 0) v) 0)))))))
(di) (di) (crs)
(qed 'rr-mul-zero-mid)
(topic! 'rr-mul-zero-mid 'analysis)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (= (* (* u 1) 1) u)))))
(di) (crs)
(qed 'rr-mul-one-mid)
(topic! 'rr-mul-one-mid 'analysis)

;;; ---- 0^(succ m) = 0.  One step of power-succ and then 0 * anything real.
(sp (make-wff '(FORALL m (IMPLIES (IN m NN) (= (power 0 (succ m)) 0)))))
(di)
(fact 'rr-zero-in)
(fact 'rr-subset-cc 0)
(have! '(AND (IN 0 CC) (IN m NN)))
(fact 'power-succ 0 'm)
(subst '(= (power 0 (succ m)) (* 0 (power 0 m))))
(fact 'power-real-closed 0 'm)
(fact 'rr-zero-mul '(power 0 m))
(ass)
(qed 'power-zero-succ)
(topic! 'power-zero-succ 'analysis)

;;; ---- n! is a POSITIVE REAL.  Realness and positivity are proved TOGETHER,
;;; in one induction: the step's rr-mul-pos needs both factors real, so
;;; splitting them would need the realness half twice.  Deliberately NOT via
;;; `factorial-in-nn' + nn-in-rr: that axiom carries no warrant, and leaning on
;;; it bills every result below it `trust: none'.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n)))))))
(define tpc-fact-br (use-induction))

(dk-focus! (cdr (assq 'base tpc-fact-br)))
(mac 'factorial-zero)                         ; 0! = succ 0
(have! '(= (succ 0) 1) (lambda () (arith)))
(subst '(= (succ 0) 1))
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(prop)

(dk-focus! (cdr (assq 'step tpc-fact-br)))
(define tpc-fact-n (cdr (assq 'var tpc-fact-br)))
(dk-split! (cdr (assq 'ih tpc-fact-br)))
(mac 'factorial-succ)                         ; (succ n)! = (succ n) * n!
(fact 'nn-succ-closed tpc-fact-n)
(fact 'nn-in-rr (list 'succ tpc-fact-n))
(fact 'nn-zero-le (list 'succ tpc-fact-n))
(fact 'nn-succ-nonzero tpc-fact-n)
(fact 'neq-sym (list 'succ tpc-fact-n) 0)
(have! (list 'AND (list '<= 0 (list 'succ tpc-fact-n))
                  (list 'NOT (list '= 0 (list 'succ tpc-fact-n)))))
(fact 'rr-le-ne-lt 0 (list 'succ tpc-fact-n))            ; 0 < succ n
(have! (list 'AND (list 'IN (list 'succ tpc-fact-n) 'RR)
                  (list 'IN (list 'FACTORIAL tpc-fact-n) 'RR)))
(fact 'rr-mul-closed (list 'succ tpc-fact-n) (list 'FACTORIAL tpc-fact-n))
(fact 'rr-mul-pos    (list 'succ tpc-fact-n) (list 'FACTORIAL tpc-fact-n))
(prop)
(qed 'factorial-real-pos)
(topic! 'factorial-real-pos 'analysis)
(alias! 'factorial-real-pos "n! is a positive real")

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN (recip (FACTORIAL n)) RR)))))
(di)
(fact 'factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'rr-pos-ne-zero '(factorial n))
(have! '(AND (IN (FACTORIAL n) RR) (NOT (= (FACTORIAL n) 0))))
(fact 'rr-recip-closed '(factorial n))
(ass)
(qed 'recip-factorial-in-rr)
(topic! 'recip-factorial-in-rr 'analysis)

;;; ---- the two values of the summand AT THE CENTRE.
;;; term(0) = f^(0)(x) (x-x)^0 recip(0!) = f(x) . 1 . 1 = f(x).
;;; `lam-b' needs its argument TYPED and PEELED first, hence the nn-zero-in.
(sp (make-wff (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
   (list 'IMPLIES '(IN (f x) RR)
     (list '= (list (tpc-term 'f 'x) 0) '(f x))))))))
(dk-peel-to! '=)
(fact 'nn-zero-in)
(lam-b)
(mac 'nth-deriv-zero)                         ; f^(0) = f
(fact 'rr-sub-in-rr 'x 'x)
(fact 'rr-subset-cc '(- x x))
(mac 'power-zero)                             ; (x-x)^0 = 1  (guarded on CC)
(mac 'factorial-zero)
(have! '(= (succ 0) 1) (lambda () (arith)))
(subst '(= (succ 0) 1))
(mac 'rr-recip-one)
(fact 'rr-mul-one-mid '(f x))
(ass)
(qed 'taylor-center-term-at-zero)
(topic! 'taylor-center-term-at-zero 'analysis)

;;; term(succ m) = 0: (x-x)^(succ m) = 0^(succ m) = 0 kills it.  The recip
;;; factor still has to be REAL for the product to be defined -- which is what
;;; recip-factorial-in-rr is for.
(sp (make-wff (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
   (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
     (list 'IMPLIES (list 'IN (list (list 'NTH-DERIV 'f '(succ m)) 'x) 'RR)
       (list '= (list (tpc-term 'f 'x) '(succ m)) 0)))))))))
(dk-peel-to! '=)
(fact 'nn-succ-closed 'm)
(lam-b)
(have! '(= (- x x) 0) (lambda () (crs)))
(subst '(= (- x x) 0))
(mac 'power-zero-succ)
(fact 'recip-factorial-in-rr '(succ m))
(fact 'rr-mul-zero-mid '((nth-deriv f (succ m)) x) '(recip (factorial (succ m))))
(ass)
(qed 'taylor-center-term-at-succ)
(topic! 'taylor-center-term-at-succ 'analysis)

;;; ---- THE INDUCTION.  Degree OUTERMOST, so that `ni' fires.
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'IMPLIES (tpc-guard 'f 'x 'n)
        (list '= (list 'SERIES-PARTIAL-SUM (tpc-term 'f 'x) '(succ n)) '(f x))))))))))
(define tpc-br (use-induction))
(define tpc-n  (cdr (assq 'var tpc-br)))
(define tpc-ih (cdr (assq 'ih  tpc-br)))

;;; --- base: SPS(term, succ 0) = 0 + term(0) = f(x) ---
(dk-focus! (cdr (assq 'base tpc-br)))
(dk-peel-to! '=)
;; read the eigenvariables off the GOAL's right-hand side, never off the context
(define tpc-b-fx (caddr (dk-goal)))                     ; (f x)
(define tpc-b-f  (car  tpc-b-fx))
(define tpc-b-x  (cadr tpc-b-fx))
(define tpc-b-tm (tpc-term tpc-b-f tpc-b-x))
(fact 'nn-zero-in)
(fact 'nn-le-refl 0)
(have! '(AND (IN 0 NN) (<= 0 0)))
(inst+ (tpc-guard tpc-b-f tpc-b-x 0) 0)                 ; f^(0)(x) in RR
(mac-h 'nth-deriv-zero (list 'IN (list (list 'NTH-DERIV tpc-b-f 0) tpc-b-x) 'RR))
(fact 'taylor-center-term-at-zero tpc-b-f tpc-b-x)      ; term(0) = f(x)
;; the recurrence's two typings, BEFORE the rewrite (series-partial-sum-succ is
;; guarded on both arguments); each is one substitution away from a known fact
(have! (list 'IN (list tpc-b-tm 0) 'RR)
       (lambda () (subst (list '= (list tpc-b-tm 0) tpc-b-fx)) (ass)))
(have! (list 'IN (list 'SERIES-PARTIAL-SUM tpc-b-tm 0) 'RR)
       (lambda () (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)))
(dk-sps-succ! tpc-b-tm 0)
(mac 'series-partial-sum-zero)
(subst (list '= (list tpc-b-tm 0) tpc-b-fx))
(fact 'rr-zero-add tpc-b-fx)
(ass)

;;; --- step: SPS(term, succ(succ n)) = f(x) + 0 = f(x) ---
(dk-focus! (cdr (assq 'step tpc-br)))
(dk-peel-to! '=)
(define tpc-s-fx (caddr (dk-goal)))                     ; (f x)
(define tpc-s-f  (car  tpc-s-fx))
(define tpc-s-x  (cadr tpc-s-fx))
(define tpc-s-tm (tpc-term tpc-s-f tpc-s-x))
(define tpc-sn   (list 'succ tpc-n))
(fact 'nn-succ-closed tpc-n)
(fact 'nn-le-succ tpc-n)                                ; n <= succ n
;; the goal's guard is at succ n; the induction hypothesis wants it at n
(have! (tpc-guard tpc-s-f tpc-s-x tpc-n)
  (lambda ()
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))      ; (AND (IN k NN) (<= k n))
           (kv     (cadr (cadr landed))))
      (dk-split! landed)
      (fact 'nn-le-trans-guarded kv tpc-n tpc-sn)
      (have! (list 'AND (list 'IN kv 'NN) (list '<= kv tpc-sn)))
      (inst+ (tpc-guard tpc-s-f tpc-s-x tpc-sn) kv)
      (ass))))
;; ... and now the hypothesis applies, at this f and this x
(define tpc-ih1 (dk-landed-1 (lambda () (inst+ tpc-ih tpc-s-f))))
(define tpc-eq  (dk-deepest  (lambda () (inst+ tpc-ih1 tpc-s-x))))  ; SPS(term,succ n) = f(x)
;; f(x) in RR, off the guard at k = 0
(fact 'nn-zero-in)
(fact 'nn-zero-le tpc-sn)
(have! (list 'AND '(IN 0 NN) (list '<= 0 tpc-sn)))
(inst+ (tpc-guard tpc-s-f tpc-s-x tpc-sn) 0)
(mac-h 'nth-deriv-zero (list 'IN (list (list 'NTH-DERIV tpc-s-f 0) tpc-s-x) 'RR))
;; the partial sum at succ n is real BECAUSE the hypothesis says it is f(x)
(have! (list 'IN (list 'SERIES-PARTIAL-SUM tpc-s-tm tpc-sn) 'RR)
       (lambda () (subst tpc-eq) (ass)))
;; the term at succ n vanishes (and is therefore real)
(fact 'nn-le-refl tpc-sn)
(have! (list 'AND (list 'IN tpc-sn 'NN) (list '<= tpc-sn tpc-sn)))
(inst+ (tpc-guard tpc-s-f tpc-s-x tpc-sn) tpc-sn)
(fact 'taylor-center-term-at-succ tpc-s-f tpc-s-x tpc-n)
(have! (list 'IN (list tpc-s-tm tpc-sn) 'RR)
       (lambda () (subst (list '= (list tpc-s-tm tpc-sn) 0)) (fact 'rr-zero-in) (ass)))
(dk-sps-succ! tpc-s-tm tpc-sn)
(subst tpc-eq)
(subst (list '= (list tpc-s-tm tpc-sn) 0))
(fact 'rr-add-zero tpc-s-fx)
(ass)
(qed 'taylor-center-partial-sum)
(topic! 'taylor-center-partial-sum 'analysis)
(alias! 'taylor-center-partial-sum
        "the Taylor partial sum at its own centre collapses to f(x)")

;;; ---- THE HEADLINE, statement unchanged from the support it replaces.
(sp (make-wff
  (forall-guarded '(f x n)
    (list
      '(IN x RR)
      '(IN n NN)
      '(FORALL k (IMPLIES (AND (IN k NN) (<= k n)) (IN ((NTH-DERIV f k) x) RR))))
    '(= (TAYLOR-POLY f x n x) (f x)))))
(dk-peel-to! '=)
(mac 'TAYLOR-POLY)
(fact 'taylor-center-partial-sum 'n 'f 'x)
(ass)
(qed 'taylor-poly-at-center)
(topic! 'taylor-poly-at-center 'analysis)

;;; endpoint VALUES of the auxiliaries (beta + the two facts above)




;;; --- elementary RR algebra micro-lemmas for the clearing step ---




;;; power-in-rr -- PROVEN 2026-08-23, not asserted.  It was an `add-to-pss' +
;;; `warrant! 'well-known' saying exactly what `power-closed-at' PROVES
;;; (theorem-library/dyadic-weights.scm:156, `modulo 0'), with the two binders
;;; in the other order -- the same statement twice, once checked and once not.
;;; dyadic-weights loads well before this file, so the recovery is three lines.
;;; MEASURED: it retires a leaf of exactly two bills (taylor-lagrange and
;;; vector-taylor-remainder-bound), and moves NEITHER of their tiers -- both
;;; carry two dozen other `reference'/`well-known' leaves, so this is the
;;; shadowing case: worth doing because the duplicate was misleading, not
;;; because any bill improves.
(sp (make-wff '(FORALL b (IMPLIES (IN b RR)
   (FORALL n (IMPLIES (IN n NN) (IN (power b n) RR)))))))
(dk-peel-to! 'IN)
(fact 'power-closed-at (caddr (cadr (dk-goal))) (cadr (cadr (dk-goal))))
(ass)
(qed 'power-in-rr)
(topic! 'power-in-rr 'analysis)



;;; the elementary clearing identity (pure RR algebra: cancel pw/=0, clear n!):
;;;   (-(fn1/n!)pw)(hx-ha) = (-(n+1)pw)(gx-ga),  gx=hx=0, ha=d, ga=r
;;;   =>  (n+1)! r = fn1 d.

;;; =====================================================================
;;; BEGIN spliced block (2026-09-14): the guarded endpoint / typing /
;;; derivative facts, PROVEN.  Lives here because its window is INSIDE this
;;; file: it cites the lemma block above and is cited by taylor-lagrange
;;; below, and a theorem-library file's helpers are invisible to another file.
;;; =====================================================================
;;; theorem-library/taylor-guarded.scm -- the endpoint / typing / derivative
;;; facts of Taylor's theorem, GUARDED and PROVEN.
;;;
;;; Eight supports of taylor-proof.scm were found FALSE AS WRITTEN (triage
;;; 2026-09-14): a binder was unguarded, so a beta redex at a non-real point,
;;; a power with a non-natural exponent, or a derivative of a function nobody
;;; said was differentiable, was undefined -- and `=' is partial.  The user's
;;; decision (2026-09-14): add the guards, prove the guarded statements.
;;;
;;; The ONE guard the G-side facts need is that the derivatives up to order n
;;; are total real functions:
;;;
;;;     DFUN(f,n)  :=  forall k. k in NN and k <= n  =>  NTH-DERIV(f,k) in FUN(RR,RR)
;;;
;;; That is what makes TAYLOR-POLY(f,z,n,x) a real number at EVERY real z, hence
;;; G a function RR -> RR, hence G(a) and G(x) defined.  TAYLOR-DIFFERENTIABLE
;;; (the citer's hypothesis) implies it -- `taylor-derivs-in-fun' below, through
;;; the FUN(PTS,PTS) conjunct of IS-CONTINUOUS-AT at the point a of [a,x] -- so
;;; the citer lands DFUN in ONE `fact' and every guarded G-fact then
;;; auto-detaches.  DFUN rather than TAYLOR-DIFFERENTIABLE itself as the guard
;;; because (i) the binder lists stay byte-identical (TD would add `a' to
;;; taylor-G-at-x and taylor-G-in-fun, whose statements never mention the
;;; interval), (ii) G(x) = 0 and G in FUN(RR,RR) have nothing to do with [a,x],
;;; and (iii) one hypothesis serves all four.
;;;
;;; Statements (the guard additions are the only change; binders and bodies
;;; are byte-identical to the support sites in taylor-proof.scm):
;;;   taylor-poly-in-rr   + DFUN
;;;   taylor-G-in-fun     + DFUN
;;;   taylor-G-at-a       + f in FUN(RR,RR), a in RR, x in RR, n in NN, DFUN
;;;   taylor-G-at-x       + f in FUN(RR,RR), x in RR, DFUN
;;;   taylor-H-at-a       + a in RR, x in RR, n in NN
;;;   taylor-H-at-x       + x in RR
;;;   taylor-H-diff       + n in NN
;;;   taylor-deriv-real   + n in NN
;;;   taylor-H-in-fun     unchanged (it was the one properly guarded)
;;;
;;; LOAD WINDOW.  This file cites `taylor-poly-at-center', `power-zero-succ',
;;; `recip-factorial-in-rr', `rr-zero-mul' -- all PROVEN in taylor-proof.scm
;;; ABOVE its support block (lines 138-431) -- and is cited by `taylor-lagrange'
;;; at the END of the same file (line 541).  So it must load between
;;; taylor-proof.scm:431 and taylor-proof.scm:541: the integrator either splices
;;; this file's body in at the support block, or splits taylor-proof.scm into
;;; its lemma half and its headline half and wires this file between them.
;;; Everything else cited loads well before taylor-proof: deriv-power /
;;; pow-lam-in-fun (deriv-power.scm), deriv-chain (chain-rule.scm),
;;; diff-transfer-ptwise-eq (diff-transfer.scm), deriv-sum (deriv-sum-product),
;;; deriv-const / deriv-identity (differentiation.scm), deriv-neg /
;;; diff-value-real (mvt-cluster-readoffs.scm), compose-apply, fun-apply-type-c,
;;; ccint-membership, power-closed-at (dyadic-weights), rr-sub-in-rr,
;;; rr-lt-implies-le, nn-le-refl / nn-le-trans-guarded, nn-le-succ,
;;; series-partial-sum-zero / -succ.
;;;
;;; Helper prefix: tg-.

;;; ---- file-local shapes ----
(define tg-gt '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tg-ht '(VNB-LAMBDA z RR (power (- x z) (succ n))))
(define (tg-hval t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
;;; DFUN(f,n)
(define (tg-dfun f n)
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k n))
                         (list 'IN (list 'NTH-DERIV f 'k) '(FUN RR RR)))))
;;; the pointwise guard at the point a (taylor-poly-at-center's shape)
(define (tg-guard f a n)
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k n))
                         (list 'IN (list (list 'NTH-DERIV f 'k) a) 'RR))))
;;; the Taylor summand k |-> f^(k)(a) (x-a)^k recip(k!)  (TAYLOR-POLY's body)
(define (tg-term f a x)
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) a) (list 'power (list '- x a) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))

(define (tg-mentions? sym form)
  (cond ((eq? form sym) #t)
        ((pair? form) (or (tg-mentions? sym (car form)) (tg-mentions? sym (cdr form))))
        (#t #f)))
(define (tg-pick pred what)
  (or (find-first pred (dk-asms)) (error "taylor-guarded: no assumption" what)))

;;; LUTINS instantiation (2026-09-18).  A `fact' AT an IOTA-valued term --
;;; NTH-DERIV(f,k), or an application of one -- owes (= t t) unless the context
;;; certifies the term.  Read the typing out of an IS-DIFF-AT hypothesis
;;; WITHOUT destroying it: `mac-h' REPLACES the assumption it unfolds, so the
;;; unfold runs on the side branch of a `have!' and the main branch keeps the
;;; hypothesis the citation still needs.  (tgd-proj! is the same thing, defined
;;; four hundred lines below for the second spliced block.)
(define (tg-split-ands!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME))))
                         (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))
(define (tg-diff-typ! hyp t X)
  (if (not (any-pred (lambda (a) (equal? a (list 'IN t X))) (dk-asms)))
      (have! (list 'IN t X)
             (lambda () (mac-h 'IS-DIFF-AT hyp) (tg-split-ands!) (ass)))))

;;; (IN (* a b) RR) from the two factor typings already in context
(define (tg-mul-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
(define (tg-add-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-add-closed a b))

;;; lam-b the goal to a fixpoint (nested redexes appear one reduction at a time)
(define (tg-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))

;;; =====================================================================
;;; (1) TAYLOR-DIFFERENTIABLE(f,a,x,n), a < x  =>  DFUN(f,n).
;;; The continuity conjunct at the point a of [a,x] carries the typing
;;; NTH-DERIV(f,k) in FUN(PTS RR-MS, PTS RR-MS).
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
    (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(< a x)
      (tg-dfun 'f 'n)))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN (NTH-DERIV f k) (FUN RR RR))
       (nd  (cadr g))
       (f   (cadr nd))
       (k   (caddr nd))
       (td  (tg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE) "TAYLOR-DIFFERENTIABLE"))
       (a   (caddr td))
       (x   (cadddr td))
       (mem (list 'AND (list 'IN a 'RR) (list 'AND (list '<= a a) (list '<= a x)))))
  ;; a in CCINT(a,x)
  (fact 'rr-leq-reflexive a)
  (fact 'rr-lt-implies-le a x)
  (have! mem)
  (fact 'ccint-membership a x a)
  (ai (list 'IFF (list 'IN a (list 'CCINT a x)) mem))
  (detach! (list 'IMPLIES mem (list 'IN a (list 'CCINT a x))))
  ;; unfold the hypothesis; the continuity conjunct at k, at the point a
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable td)))))
         (cont  (or (find-first (lambda (p) (tg-mentions? 'IS-CONTINUOUS-AT p)) parts)
                    (error "taylor-guarded: no continuity conjunct")))
         (u1    (dk-deepest (lambda () (inst+ cont k))))
         (u2    (dk-deepest (lambda () (inst+ u1 a)))))
    (dk-split! (dk-landed-1 (lambda () (mac-h 'is-continuous-at u2))))
    (slot-h 'PTS (list 'IN nd '(FUN (PTS RR-MS) (PTS RR-MS))))
    (ass)))
(qed 'taylor-derivs-in-fun)
(topic! 'taylor-derivs-in-fun 'analysis)
(alias! 'taylor-derivs-in-fun
        "a Taylor-differentiable f has total real derivatives up to order n")

;;; =====================================================================
;;; (2) DFUN(f,n), t in RR  =>  f^(k)(t) in RR for k <= n.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'n
    (list 'IMPLIES (tg-dfun 'f 'n)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR) (tg-guard 'f 't 'n))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN ((NTH-DERIV f k) t) RR)
       (app (cadr g))
       (nd  (car app))
       (t   (cadr app))
       (k   (caddr nd))
       (dfun (tg-pick (lambda (u) (and (pair? u) (eq? (car u) 'FORALL) (tg-mentions? 'FUN u)))
                      "DFUN")))
  (dk-deepest (lambda () (inst+ dfun k)))
  (fact 'fun-apply-type-c nd 'RR 'RR t)
  (ass))
(qed 'taylor-derivs-values-real)
(topic! 'taylor-derivs-values-real 'analysis)

;;; =====================================================================
;;; (3) The partial sum is real when the derivatives at the centre are:
;;; induction on the degree, taylor-center-partial-sum's shape.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'f (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
        (list 'IMPLIES (tg-guard 'f 'a 'n)
          (list 'IN (list 'SERIES-PARTIAL-SUM (tg-term 'f 'a 'x) '(succ n)) 'RR)))))))))))
(define tg-br (use-induction))
(define tg-n  (cdr (assq 'var tg-br)))
(define tg-ih (cdr (assq 'ih  tg-br)))

;; read f, a, x off the summand in the GOAL
(define (tg-goal-term) (cadr (cadr (dk-goal))))
(define (tg-term-f tm) (cadr (car (cadr (cadr (cadddr tm))))))
(define (tg-term-a tm) (cadr (cadr (cadr (cadddr tm)))))
(define (tg-term-x tm) (cadr (cadr (caddr (cadr (cadddr tm))))))

;; the summand at index idx is real: beta, then the three factor typings
(define (tg-term-real! tm idx)
  (let* ((f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm))
         (dv (list (list 'NTH-DERIV f idx) a))
         (pw (list 'power (list '- x a) idx))
         (rc (list 'recip (list 'FACTORIAL idx))))
    (have! (list 'IN (list tm idx) 'RR)
      (lambda ()
        (lam-b)
        (fact 'rr-sub-in-rr x a)
        (fact 'power-closed-at idx (list '- x a))
        (fact 'recip-factorial-in-rr idx)
        (tg-mul-real! dv pw)
        (tg-mul-real! (list '* dv pw) rc)
        (ass)))))

;;; --- base: SPS(term, succ 0) = SPS(term, 0) + term(0) ---
(dk-focus! (cdr (assq 'base tg-br)))
(dk-peel-to! 'IN)
(let* ((tm (tg-goal-term)) (f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm)))
  (fact 'nn-zero-in)
  (fact 'nn-le-refl 0)
  (have! '(AND (IN 0 NN) (<= 0 0)))
  (inst+ (tg-guard f a 0) 0)                             ; f^(0)(a) in RR
  (tg-term-real! tm 0)
  (have! (list 'IN (list 'SERIES-PARTIAL-SUM tm 0) 'RR)
         (lambda () (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)))
  (dk-sps-succ! tm 0)
  (tg-add-real! (list 'SERIES-PARTIAL-SUM tm 0) (list tm 0))
  (ass))

;;; --- step: SPS(term, succ(succ n)) = SPS(term, succ n) + term(succ n) ---
(dk-focus! (cdr (assq 'step tg-br)))
(dk-peel-to! 'IN)
(let* ((tm (tg-goal-term)) (f (tg-term-f tm)) (a (tg-term-a tm)) (x (tg-term-x tm))
       (sn (list 'succ tg-n)))
  (fact 'nn-succ-closed tg-n)
  (fact 'nn-le-succ tg-n)                                ; n <= succ n
  ;; the goal's guard is at succ n; the hypothesis wants it at n
  (have! (tg-guard f a tg-n)
    (lambda ()
      (di)
      (let* ((landed (dk-landed-1 (lambda () (di))))    ; (AND (IN k NN) (<= k n))
             (kv     (cadr (cadr landed))))
        (dk-split! landed)
        (fact 'nn-le-trans-guarded kv tg-n sn)
        (have! (list 'AND (list 'IN kv 'NN) (list '<= kv sn)))
        (inst+ (tg-guard f a sn) kv)
        (ass))))
  (let* ((ih1 (dk-deepest (lambda () (inst+ tg-ih f))))
         (ih2 (dk-deepest (lambda () (inst+ ih1 a)))))
    (dk-deepest (lambda () (inst+ ih2 x))))             ; SPS(term, succ n) in RR
  ;; the term at succ n
  (fact 'nn-le-refl sn)
  (have! (list 'AND (list 'IN sn 'NN) (list '<= sn sn)))
  (inst+ (tg-guard f a sn) sn)                           ; f^(succ n)(a) in RR
  (tg-term-real! tm sn)
  (dk-sps-succ! tm sn)
  (tg-add-real! (list 'SERIES-PARTIAL-SUM tm sn) (list tm sn))
  (ass))
(qed 'taylor-poly-in-rr-at)
(topic! 'taylor-poly-in-rr-at 'analysis)
(alias! 'taylor-poly-in-rr-at
        "the Taylor partial sum is real when the derivatives at the centre are")

;;; =====================================================================
;;; (4) taylor-poly-in-rr, guarded by DFUN.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN RR RR)) (list 'FORALL 'a (list 'IMPLIES '(IN a RR)
    (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
      (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
        (list 'IMPLIES (tg-dfun 'f 'n)
          '(IN (TAYLOR-POLY f a n x) RR))))))))))))
(dk-peel-to! 'IN)
(mac 'TAYLOR-POLY)
(fact 'taylor-derivs-values-real 'f 'n 'a)
(fact 'taylor-poly-in-rr-at 'n 'f 'a 'x)
(ass)
(qed 'taylor-poly-in-rr)
(topic! 'taylor-poly-in-rr 'analysis)

;;; =====================================================================
;;; (5) taylor-G-in-fun, guarded by DFUN.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'f (list 'IMPLIES '(IN f (FUN RR RR)) (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'IMPLIES (tg-dfun 'f 'n)
        (list 'IN tg-gt '(FUN RR RR)))))))))))
(dk-peel-to! 'IN)
(dk-lam-t!)
(let ((z (dk-di-var!)))
  (fact 'fun-apply-type-c 'f 'RR 'RR 'x)
  (fact 'taylor-poly-in-rr 'f z 'n 'x)
  (fact 'rr-sub-in-rr '(f x) (list 'TAYLOR-POLY 'f z 'n 'x))
  (ass))
(qed 'taylor-g-in-fun)
(topic! 'taylor-g-in-fun 'analysis)

;;; =====================================================================
;;; (6) taylor-H-in-fun -- statement unchanged.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'FORALL 'x (list 'IMPLIES '(IN x RR) (list 'IN tg-ht '(FUN RR RR))))))))
(dk-peel-to! 'IN)
(dk-lam-t!)
(let ((z (dk-di-var!)))
  (fact 'nn-succ-closed 'n)
  (fact 'rr-sub-in-rr 'x z)
  (fact 'power-closed-at '(succ n) (list '- 'x z))
  (ass))
(qed 'taylor-h-in-fun)
(topic! 'taylor-h-in-fun 'analysis)

;;; =====================================================================
;;; (7) taylor-H-at-a: beta, then reflexivity against the power's typing.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN n NN)
      (list '= (list tg-ht 'a) '(power (- x a) (succ n)))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'nn-succ-closed 'n)
(fact 'rr-sub-in-rr 'x 'a)
(fact 'power-closed-at '(succ n) '(- x a))
(rfl)
(qed 'taylor-h-at-a)
(topic! 'taylor-h-at-a 'analysis)

;;; =====================================================================
;;; (8) taylor-H-at-x: beta, x - x = 0, 0^(succ n) = 0.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN) (list 'IMPLIES '(IN x RR)
    (list '= (list tg-ht 'x) 0)))))))
(dk-peel-to! '=)
(lam-b)
(have! '(= (- x x) 0) (lambda () (crs)))
(subst '(= (- x x) 0))
(fact 'power-zero-succ 'n)
(ass)
(qed 'taylor-h-at-x)
(topic! 'taylor-h-at-x 'analysis)

;;; =====================================================================
;;; (9) taylor-G-at-a: beta, then reflexivity against the remainder's typing.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
    (list 'IMPLIES '(IN f (FUN RR RR)) (list 'IMPLIES '(IN a RR) (list 'IMPLIES '(IN x RR)
    (list 'IMPLIES '(IN n NN) (list 'IMPLIES (tg-dfun 'f 'n)
      (list '= (list tg-gt 'a) '(- (f x) (TAYLOR-POLY f a n x))))))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)
(fact 'taylor-poly-in-rr 'f 'a 'n 'x)
(fact 'rr-sub-in-rr '(f x) '(TAYLOR-POLY f a n x))
(rfl)
(qed 'taylor-g-at-a)
(topic! 'taylor-g-at-a 'analysis)

;;; =====================================================================
;;; (10) taylor-G-at-x: beta, taylor-poly-at-center, f(x) - f(x) = 0.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'x (list 'FORALL 'n (list 'IMPLIES '(IN n NN)
    (list 'IMPLIES '(IN f (FUN RR RR)) (list 'IMPLIES '(IN x RR)
    (list 'IMPLIES (tg-dfun 'f 'n)
      (list '= (list tg-gt 'x) 0))))))))))
(dk-peel-to! '=)
(lam-b)
(fact 'taylor-derivs-values-real 'f 'n 'x)
(fact 'taylor-poly-at-center 'f 'x 'n)
(subst '(= (TAYLOR-POLY f x n x) (f x)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)
(crs)
(qed 'taylor-g-at-x)
(topic! 'taylor-g-at-x 'analysis)

;;; =====================================================================
;;; (11) taylor-deriv-real: f^(n+1)(t) is the derivative value IS-DIFF-AT
;;; carries for f^(n) at t, hence real (diff-value-real).
;;; =====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (< a t) (IMPLIES (< t x) (IMPLIES (IN n NN)
       (IN ((NTH-DERIV f (succ n)) t) RR))))))))))))
(dk-peel-to! 'IN)
(let* ((g   (dk-goal))                                  ; (IN ((NTH-DERIV f (succ n)) t) RR)
       (app (cadr g))
       (t   (cadr app))
       (f   (cadr (car app)))
       (n   (cadr (caddr (car app))))
       (td  (tg-pick (dk-head? 'TAYLOR-DIFFERENTIABLE) "TAYLOR-DIFFERENTIABLE"))
       (a   (caddr td))
       (x   (cadddr td)))
  (fact 'nn-le-refl n)
  (have! (list 'AND (list 'IN n 'NN) (list '<= n n)))
  (have! (list 'AND (list '< a t) (list '< t x)))
  (let* ((parts (dk-split! (dk-landed-1 (lambda () (mac-h 'taylor-differentiable td)))))
         (dcon  (or (find-first (lambda (p) (tg-mentions? 'IS-DIFF-AT p)) parts)
                    (error "taylor-guarded: no differentiability conjunct")))
         (u1    (dk-deepest (lambda () (inst+ dcon n))))
         (u2    (dk-deepest (lambda () (inst+ u1 t)))))  ; IS-DIFF-AT f^(n) t f^(n+1)(t)
    ;; LUTINS instantiation (2026-09-18): `diff-value-real' was cited AT
    ;; NTH-DERIV(f,n) and at f^(n+1)(t), neither of which the certificate
    ;; accepts (an IOTA, and an application of one).  The third conjunct of u2
    ;; IS the goal, so project it directly instead -- an unfold is a REWRITE
    ;; and owes nothing.
    (mac-h 'IS-DIFF-AT u2) (tg-split-ands!)
    (ass)))
(qed 'taylor-deriv-real)
(topic! 'taylor-deriv-real 'analysis)

;;; =====================================================================
;;; (12) taylor-H-diff:  d/dt (x-t)^(n+1) = -(n+1)(x-t)^n.
;;; Chain rule: outer u |-> u^(succ n) (deriv-power), inner z |-> x - z, itself
;;; assembled from deriv-const + deriv-neg(deriv-identity) by deriv-sum and
;;; carried to the literal lambda by diff-transfer-ptwise-eq; the composite is
;;; carried to HT the same way, through compose-apply.
;;; =====================================================================
;; the value identity, over VARIABLES (crs sees no symbolic power)
(sp (make-wff '(FORALL s (IMPLIES (IN s RR) (FORALL p (IMPLIES (IN p RR)
   (= (- 0 (* s p)) (* (* s p) (+ 0 (- 1))))))))))
(dk-peel-to! '=)
(crs)
(qed 'tg-neg-scale)
(topic! 'tg-neg-scale 'plumbing)

(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'FORALL 't
    (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN t RR) (list 'IMPLIES '(IN n NN)
      (list 'IS-DIFF-AT tg-ht 't (tg-hval 't))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tg-fin '(VNB-LAMBDA z RR (- x z)))              ; the inner map
(define tg-lin '(+ 0 (- 1)))                            ; its derivative value
;; --- inner map: differentiable at t with value 0 + (-1) ---
(have! '(AND (IN x RR) (IN t RR)))
(define tg-fc (cadr (dk-fact! 'deriv-const 'x 't)))    ; lambda _. x   (bound var renamed)
(fact 'deriv-identity 't)
(define tg-fn (cadr (dk-fact! 'deriv-neg '(VNB-LAMBDA x RR x) 't 1)))   ; lambda z. -(id z)
(have! (list 'AND (list 'IS-DIFF-AT tg-fc 't 0) (list 'IS-DIFF-AT tg-fn 't '(- 1))))
(define tg-fsum (cadr (dk-fact! 'deriv-sum tg-fc tg-fn 't 0 '(- 1))))
(have! (list 'IN tg-fin '(FUN RR RR))
  (lambda () (dk-lam-t!) (let ((z (dk-di-var!))) (fact 'rr-sub-in-rr 'x z) (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '== (list tg-fin 'x_) (list tg-fsum 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (tg-beta!)                                        ; (- x v) == (+ x (- v))
      (have! (list '= (list '- 'x v) (list '+ 'x (list '- v))) (lambda () (crs)))
      (subst (list '= (list '- 'x v) (list '+ 'x (list '- v))))
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tg-fin tg-fsum 't tg-lin)   ; IS-DIFF-AT fin t (0 + -1)
;; --- outer map at the inner value ---
(fact 'fun-apply-type-c tg-fin 'RR 'RR 't)              ; (fin t) in RR
(define tg-gout (cadr (dk-fact! 'deriv-power 'n (list tg-fin 't))))
(define tg-mv  (list '* '(succ n) (list 'power (list tg-fin 't) 'n)))
;; LUTINS instantiation (2026-09-18): `deriv-chain' is cited AT tg-mv, a
;; product carrying a power, so its typing has to be in the context first --
;; the owed-leaf hook runs `in-rr', which cannot type a power.  (The two
;; nn-succ-closed / nn-in-rr citations moved up from the value block below.)
(fact 'nn-succ-closed 'n)
(fact 'nn-in-rr '(succ n))
(fact 'power-closed-at 'n (list tg-fin 't))
(tg-mul-real! '(succ n) (list 'power (list tg-fin 't) 'n))
;; --- chain ---
(define tg-comp (cadr (dk-fact! 'deriv-chain tg-fin tg-gout 't tg-lin tg-mv)))
(lam-b-h (list 'IS-DIFF-AT tg-comp 't (list '* tg-mv tg-lin)))   ; (fin t) -> (- x t)
(define tg-pw (list 'power '(- x t) 'n))
(define tg-val (list '* (list '* '(succ n) tg-pw) tg-lin))
;; --- the value, and the transfer to HT ---
(fact 'rr-sub-in-rr 'x 't)
(fact 'power-closed-at 'n '(- x t))
(fact 'tg-neg-scale '(succ n) tg-pw)
(subst (list '= (tg-hval 't) tg-val))                   ; goal: IS-DIFF-AT HT t VAL
(fact 'taylor-h-in-fun 'n 'x)
(fact 'pow-lam-in-fun '(succ n))
(have! (list 'AND (list 'IN tg-fin '(FUN RR RR)) (list 'IN tg-gout '(FUN RR RR))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR) (list '== (list tg-ht 'x_) (list tg-comp 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (fact 'compose-apply 'RR 'RR 'RR tg-gout tg-fin v)
      (subst (list '= (list tg-comp v) (list tg-gout (list tg-fin v))))
      (fact 'fun-apply-type-c tg-fin 'RR 'RR v)         ; licence for the outer redex
      (fact 'rr-sub-in-rr 'x v)
      (tg-beta!)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tg-ht tg-comp 't tg-val)
(ass)
(qed 'taylor-h-diff)
(topic! 'taylor-h-diff 'analysis)

;;; ===== END spliced block =====

;;; =====================================================================
;;; BEGIN spliced block 1b (2026-09-14): taylor-g-diff, the derivative of the
;;; Taylor polynomial in its centre, GUARDED and PROVEN (was
;;; theorem-library/taylor-g-diff.scm).  Here because it unfolds
;;; TAYLOR-DIFFERENTIABLE, defined at the top of THIS file, and is cited by the
;;; gMVT block below.
;;; =====================================================================
;;; theorem-library/taylor-g-diff.scm -- the derivative of the Taylor remainder
;;; in the CENTRE:  G(z) = f(x) - TAYLOR-POLY(f, z, n, x)  has, at any t with
;;; a < t < x,
;;;
;;;     G'(t) = 0 - (recip(n!) * f^(n+1)(t)) * (x - t)^n .
;;;
;;; This is `taylor-G-diff' of taylor-proof.scm, which was an `add-to-pss' +
;;; `warrant! 'reference' whose text WAS the telescoping argument, written out
;;; and never run.  It is proven here, `modulo 0', with ONE deliberate change of
;;; statement (the user's decision, 2026-09-14): the triage found the support
;;; FALSE AS WRITTEN because `n' was unguarded (off NN the sum, the power and
;;; the factorial mean nothing).  The statement below is the support's with two
;;; leading antecedents added and nothing else touched:
;;;
;;;     (IN n NN)   -- the guard the triage asked for;
;;;     (IN x RR)   -- the Taylor point is real.  Nothing in
;;;                    TAYLOR-DIFFERENTIABLE types x (it mentions x only inside
;;;                    CCINT and `<'), and (x - z)^k is real only for real x.
;;;
;;; Nothing else had to be added, and two things one might expect to need are
;;; DERIVED from TAYLOR-DIFFERENTIABLE rather than assumed:  (IN t RR), and the
;;; typing  (NTH-DERIV f k) in FUN(RR,RR)  for every k <= n.  Both sit inside
;;; IS-DIFF-AT (its first two conjuncts), and TD's second conjunct at k and t
;;; is exactly such an IS-DIFF-AT.  So the citing proof (taylor-lagrange, which
;;; has f, a, x in RR, n in NN and t = theta in context) detaches the new
;;; antecedents automatically.
;;;
;;; PLAN.  Unfold TAYLOR-POLY:  G(z) = f(x) - SPS(term_z, succ n)  where
;;;   term_z = k |-> f^(k)(z) (x-z)^k recip(k!)      (z FREE in the summand).
;;; The content is the derivative of  z |-> SPS(term_z, succ m),  by INDUCTION
;;; ON m (degree OUTERMOST so `ni' fires; CLAUDE.md on greedy `di'):
;;;
;;;   S_m'(t) = V_m := recip(m!) f^(m+1)(t) (x-t)^m
;;;
;;;   base  SPS(term_z, succ 0) == f(z) pointwise, so S_0' = f' by transfer
;;;         (diff-transfer-ptwise-eq), and V_0 = f^(1)(t) after 0! = 1,
;;;         (x-t)^0 = 1.
;;;   step  SPS(term_z, succ succ m) == S_m(z) + T_{m+1}(z) pointwise
;;;         (series-partial-sum-succ), where T_{m+1} is the summand at succ m
;;;         as a function of z.  deriv-sum, then transfer.  The TELESCOPING is
;;;         entirely in the value of T_{m+1}':  it is  V_{m+1} - V_m  (lemma
;;;         tgd-term-diff below), so  S_{m+1}' = V_m + (V_{m+1} - V_m) = V_{m+1}
;;;         and the induction step owes NO arithmetic beyond that one identity.
;;;
;;; tgd-term-diff is the product rule twice (f^(m+1) . (x-z)^(succ m), then
;;; . recip((succ m)!) as a constant), with d/dz (x-z)^(succ m) by the chain
;;; rule (deriv-chain on deriv-power and d/dz (x-z) = -1, transferred through
;;; compose-apply), and its value collapses to V_{m+1} - V_m by ONE ring
;;; identity over six variables (tgd-step-identity, `crs') once
;;;   recip(m!) = (succ m) recip((succ m)!)          (tgd-recip-factorial-succ)
;;; has been substituted -- that equation is the whole of the telescoping.
;;;
;;; The pointwise hypotheses the induction carries are
;;;   DH(f,t,m) = forall k <= m. IS-DIFF-AT (NTH-DERIV f k) t ((NTH-DERIV f (succ k)) t)
;;; which TD supplies at any t in (a,x); the step weakens DH(succ m) to DH(m)
;;; exactly as taylor-center-partial-sum weakens its guard (nn-le-trans-guarded).
;;;
;;; DUPLICATES, deliberate.  `rr-recip-one', `factorial-real-pos' and
;;; `recip-factorial-in-rr' are proven in taylor-proof.scm -- ABOVE this file's
;;; window, since taylor-proof is the citer.  They are re-proven here under the
;;; tgd- prefix (three short proofs); the integrator may instead hoist those
;;; three out of taylor-proof.scm into a file below this one and drop the copies.
;;;
;;; LOAD WINDOW [lo, hi):  hi = taylor-proof (the citer).  lo = the latest of:
;;; deriv-power (the power rule), comparison-test-proof (series-partial-sum-
;;; zero/-succ), chain-rule (deriv-chain), compose-apply-proof, deriv-sum-
;;; product, diff-transfer, mvt-cluster-readoffs (deriv-neg, diff-value-real),
;;; higher-derivatives (nth-deriv-zero), inverse-function (rr-recip-solve),
;;; nn-parity-proof (nn-succ-nonzero), dyadic-weights (power-closed-at), power-
;;; series (SERIES-PARTIAL-SUM).  All precede deriv-power in load.scm, so the
;;; file goes anywhere after deriv-power and before taylor-proof.
;;;
;;; Helper prefix: tgd-.  Every top-level define is prefixed (case folding:
;;; `tgd-PW' and `tgd-pw' are ONE name, which cost this file a probe).
;;; ====================================================================

;;; ---- file-local helpers ----
(define (tgd-di-var!) (cadr (car (dk-landed (lambda () (di))))))
(define (tgd-split-ands!)
  (let loop ((n 0))
    (let ((tgt (any-pred (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME)))) (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))
;; read a conjunct of an IS-DIFF-AT hypothesis WITHOUT destroying it (mac-h
;; replaces the assumption; the unfold happens on the have! side branch)
(define (tgd-proj! hyp claim)
  (have! claim (lambda () (mac-h 'IS-DIFF-AT hyp) (tgd-split-ands!) (ass))))
(define (tgd-mentions? sym f)
  (cond ((eq? f sym) #t)
        ((pair? f) (or (tgd-mentions? sym (car f)) (tgd-mentions? sym (cdr f))))
        (#t #f)))
(define (tgd-find pred what)
  (or (any-pred pred (dk-asms)) (error "taylor-g-diff: no assumption" what)))

;;; the shapes
(define (tgd-term f x)          ; the Taylor summand  k |-> f^(k)(z) (x-z)^k recip(k!),  z FREE
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) 'z) (list 'power (list '- x 'z) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))
(define (tgd-term-lam f x k)    ; z |-> f^(k)(z) (x-z)^k recip(k!)
  (list 'VNB-LAMBDA 'z 'RR
        (list '* (list '* (list (list 'NTH-DERIV f k) 'z) (list 'power (list '- x 'z) k))
                 (list 'recip (list 'FACTORIAL k)))))
(define (tgd-sum-lam f x m)     ; z |-> SPS(term_z, succ m)
  (list 'VNB-LAMBDA 'z 'RR (list 'SERIES-PARTIAL-SUM (tgd-term f x) (list 'succ m))))
(define (tgd-val f x t m)       ; V_m = (recip(m!) f^(m+1)(t)) (x-t)^m
  (list '* (list '* (list 'recip (list 'FACTORIAL m)) (list (list 'NTH-DERIV f (list 'succ m)) t))
           (list 'power (list '- x t) m)))
(define (tgd-dh f t m)          ; DH(f,t,m): f^(k) differentiable at t with value f^(k+1)(t), k <= m
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k m))
    (list 'IS-DIFF-AT (list 'NTH-DERIV f 'k) t (list (list 'NTH-DERIV f '(succ k)) t)))))

;;; ====================================================================
;;; (1) recip 1 = 1   (rr-recip-one, taylor-proof.scm, above the window)
;;; ====================================================================
(sp (make-wff '(= (recip 1) 1)))
(fact 'rr-one-in)
(have! '(NOT (= 1 0)) (lambda () (arith)))
(have! '(AND (IN 1 RR) (NOT (= 1 0))))
(fact 'rr-recip-inverse 1)
(fact 'rr-recip-closed 1)
(fact 'rr-one-mul '(recip 1))
(fact 'eq-sym '(* 1 (recip 1)) '(recip 1))
(fact 'eq-trans '(recip 1) '(* 1 (recip 1)) 1)
(ass)
(qed 'tgd-recip-one)
(topic! 'tgd-recip-one 'analysis)

;;; ====================================================================
;;; (2) n! is a POSITIVE REAL, and recip(n!) is real
;;;     (factorial-real-pos / recip-factorial-in-rr, taylor-proof.scm)
;;; ====================================================================
(sp (make-wff '(FORALL n (IMPLIES (IN n NN)
   (AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n)))))))
(define tgd-fbr (use-induction))
(dk-focus! (cdr (assq 'base tgd-fbr)))
(mac 'factorial-zero)
(have! '(= (succ 0) 1) (lambda () (arith)))
(subst '(= (succ 0) 1))
(fact 'rr-one-in)
(fact 'rr-zero-lt-one)
(prop)
(dk-focus! (cdr (assq 'step tgd-fbr)))
(define tgd-fn (cdr (assq 'var tgd-fbr)))
(dk-split! (cdr (assq 'ih tgd-fbr)))
(mac 'factorial-succ)
(fact 'nn-succ-closed tgd-fn)
(fact 'nn-in-rr (list 'succ tgd-fn))
(fact 'nn-zero-le (list 'succ tgd-fn))
(fact 'nn-succ-nonzero tgd-fn)
(fact 'neq-sym (list 'succ tgd-fn) 0)
(have! (list 'AND (list '<= 0 (list 'succ tgd-fn)) (list 'NOT (list '= 0 (list 'succ tgd-fn)))))
(fact 'rr-le-ne-lt 0 (list 'succ tgd-fn))
(have! (list 'AND (list 'IN (list 'succ tgd-fn) 'RR) (list 'IN (list 'FACTORIAL tgd-fn) 'RR)))
(fact 'rr-mul-closed (list 'succ tgd-fn) (list 'FACTORIAL tgd-fn))
(fact 'rr-mul-pos    (list 'succ tgd-fn) (list 'FACTORIAL tgd-fn))
(prop)
(qed 'tgd-factorial-real-pos)
(topic! 'tgd-factorial-real-pos 'analysis)

(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (IN (recip (FACTORIAL n)) RR)))))
(di)
(fact 'tgd-factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'rr-pos-ne-zero '(factorial n))
(have! '(AND (IN (FACTORIAL n) RR) (NOT (= (FACTORIAL n) 0))))
(fact 'rr-recip-closed '(factorial n))
(ass)
(qed 'tgd-recip-factorial-in-rr)
(topic! 'tgd-recip-factorial-in-rr 'analysis)

;;; ====================================================================
;;; (3) THE TELESCOPING EQUATION:  recip(m!) = (succ m) * recip((succ m)!).
;;; (succ m)! = (succ m) m!;  (succ m)m! . R = 1 (rr-recip-inverse) is
;;; rearranged to  1 = m! . ((succ m) R)  (crs over the typed generators) and
;;; rr-recip-solve reads  (succ m) R = recip(m!) . 1  off it.
;;; ====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IN m NN)
   (= (recip (FACTORIAL m)) (* (succ m) (recip (FACTORIAL (succ m)))))))))
(di)
(mac 'factorial-succ)
(fact 'tgd-factorial-real-pos 'm)
(dk-split! '(AND (IN (FACTORIAL m) RR) (< 0 (FACTORIAL m))))
(fact 'rr-pos-ne-zero '(factorial m))
(fact 'nn-succ-closed 'm)
(fact 'tgd-factorial-real-pos '(succ m))
(dk-split! '(AND (IN (FACTORIAL (succ m)) RR) (< 0 (FACTORIAL (succ m)))))
(mac-h 'factorial-succ '(IN (FACTORIAL (succ m)) RR))
(mac-h 'factorial-succ '(< 0 (FACTORIAL (succ m))))
(fact 'rr-pos-ne-zero '(* (succ m) (factorial m)))
(have! '(AND (IN (* (succ m) (FACTORIAL m)) RR) (NOT (= (* (succ m) (FACTORIAL m)) 0))))
(fact 'rr-recip-inverse '(* (succ m) (factorial m)))
(fact 'rr-recip-closed '(* (succ m) (factorial m)))
(fact 'nn-in-rr '(succ m))
(have! '(= (* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m))))
           (* (FACTORIAL m) (* (succ m) (recip (* (succ m) (FACTORIAL m))))))
       (lambda () (crs)))
(fact 'eq-sym '(* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m)))) 1)
(fact 'eq-trans 1 '(* (* (succ m) (FACTORIAL m)) (recip (* (succ m) (FACTORIAL m))))
                 '(* (FACTORIAL m) (* (succ m) (recip (* (succ m) (FACTORIAL m))))))
(have! '(AND (IN (FACTORIAL m) RR) (NOT (= (FACTORIAL m) 0))))
(have! '(AND (IN (succ m) RR) (IN (recip (* (succ m) (FACTORIAL m))) RR)))
(fact 'rr-mul-closed '(succ m) '(recip (* (succ m) (factorial m))))
(fact 'rr-one-in)
(fact 'rr-recip-solve '(factorial m) 1 '(* (succ m) (recip (* (succ m) (factorial m)))))
(subst '(= (* (succ m) (recip (* (succ m) (FACTORIAL m)))) (* (recip (FACTORIAL m)) 1)))
(fact 'rr-recip-closed '(factorial m))
(crs)
(qed 'tgd-recip-factorial-succ)
(topic! 'tgd-recip-factorial-succ 'analysis)
(alias! 'tgd-recip-factorial-succ "recip(m!) = (m+1) recip((m+1)!)")

;;; ====================================================================
;;; (4) d/dz (x - z) = -1.   deriv-const + deriv-identity + deriv-neg + deriv-sum
;;; build  z |-> x + (-z);  binary-minus-def carries it to the literal difference.
;;; ====================================================================
(sp (make-wff '(FORALL x (IMPLIES (IN x RR) (FORALL t (IMPLIES (IN t RR)
   (IS-DIFF-AT (VNB-LAMBDA z RR (- x z)) t (- 1))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-sub-lam '(VNB-LAMBDA z RR (- x z)))
(have! '(AND (IN x RR) (IN t RR)))
(define tgd-kx (dk-fact! 'deriv-const 'x 't))
(define tgd-klam (cadr tgd-kx))
(define tgd-idn (dk-fact! 'deriv-identity 't))
(define tgd-negi (dk-fact! 'deriv-neg (cadr tgd-idn) 't 1))
(define tgd-negi2 (dk-landed-1 (lambda () (lam-b-h tgd-negi))))      ; z |-> -z
(have! (list 'AND tgd-kx tgd-negi2))
(define tgd-sum (dk-fact! 'deriv-sum tgd-klam (cadr tgd-negi2) 't 0 '(- 1)))
(define tgd-sum2 (dk-landed-1 (lambda () (lam-b-h tgd-sum))))        ; z |-> x + (-z)
(define tgd-sumlam (cadr tgd-sum2))
(have! (list 'IN tgd-sub-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-sub-lam 'x_) (list tgd-sumlam 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (lam-b)
      (fact 'binary-minus-def 'x v)
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-sub-lam tgd-sumlam 't '(+ 0 (- 1)))
(have! '(= (- 1) (+ 0 (- 1))) (lambda () (crs)))
(subst '(= (- 1) (+ 0 (- 1))))
(ass)
(qed 'tgd-sub-diff)
(topic! 'tgd-sub-diff 'analysis)

;;; ====================================================================
;;; (5) d/dz (x - z)^(succ m) = ((succ m) (x-t)^m) . (-1).   The chain rule on
;;; deriv-power at the point x - t and (4); the COMPOSE is carried to the
;;; literal lambda by compose-apply + beta (diff-transfer-ptwise-eq).
;;; ====================================================================
(sp (make-wff '(FORALL m (IMPLIES (IN m NN) (FORALL x (IMPLIES (IN x RR) (FORALL t (IMPLIES (IN t RR)
   (IS-DIFF-AT (VNB-LAMBDA z RR (power (- x z) (succ m))) t
               (* (* (succ m) (power (- x t) m)) (- 1)))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-pw-lam '(VNB-LAMBDA z RR (power (- x z) (succ m))))
(define tgd-subd (dk-fact! 'tgd-sub-diff 'x 't))
(fact 'rr-sub-in-rr 'x 't)
(define tgd-pwr (dk-fact! 'deriv-power 'm '(- x t)))                ; u |-> u^(succ m) at x-t
(define tgd-glam (cadr tgd-pwr))
(define tgd-mv (cadddr tgd-pwr))
(have! (list 'IS-DIFF-AT tgd-glam (list tgd-sub-lam 't) tgd-mv)      ; ... at (SUB t), for the chain rule
  (lambda () (lam-b) (ass)))
;; LUTINS instantiation (2026-09-18): `deriv-chain' is cited AT tgd-mv and
;; `diff-transfer-ptwise-eq' at tgd-mv * (-1); both carry a power, which the
;; owed-leaf hook's `in-rr' cannot type.  (nn-succ-closed moved up from below.)
(fact 'nn-succ-closed 'm)
(fact 'nn-in-rr '(succ m))
(fact 'power-closed-at 'm '(- x t))
(fact 'rr-one-in)
(tg-mul-real! '(succ m) '(power (- x t) m))
(have! (list 'IN '(- 1) 'RR) (lambda () (in-rr)))
(tg-mul-real! tgd-mv '(- 1))
(define tgd-ch (dk-fact! 'deriv-chain tgd-sub-lam tgd-glam 't '(- 1) tgd-mv))
(define tgd-comp (cadr tgd-ch))                                      ; (COMPOSE G SUB)
(tgd-proj! tgd-subd (list 'IN tgd-sub-lam '(FUN RR RR)))
(tgd-proj! tgd-pwr (list 'IN tgd-glam '(FUN RR RR)))
(have! (list 'AND (list 'IN tgd-sub-lam '(FUN RR RR)) (list 'IN tgd-glam '(FUN RR RR))))
(define tgd-capp (dk-fact! 'compose-apply 'RR 'RR 'RR tgd-glam tgd-sub-lam))
(have! (list 'IN tgd-pw-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (fact 'power-closed-at '(succ m) (list '- 'x v))
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-pw-lam 'x_) (list tgd-comp 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (fact 'rr-sub-in-rr 'x v)
      (subst (dk-deepest (lambda () (inst+ tgd-capp v))))
      (lam-b)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tgd-pw-lam tgd-comp 't (list '* tgd-mv '(- 1)))
(ass)
(qed 'tgd-power-sub-diff)
(topic! 'tgd-power-sub-diff 'analysis)

;;; ====================================================================
;;; (6) the value identity of the telescoping step, over variables.
;;; `crs' decides it; it is applied to the terms by citation (crs sees no
;;; symbolic power), exactly as taylor-proof.scm applies its micro-identities.
;;;   s = succ m, r = recip((succ m)!), d1 = f^(m+1)(t), d2 = f^(m+2)(t),
;;;   p = (x-t)^m, q = (x-t)^(succ m).
;;; ====================================================================
(sp (make-wff '(FORALL s (IMPLIES (IN s RR) (FORALL r (IMPLIES (IN r RR)
   (FORALL d1 (IMPLIES (IN d1 RR) (FORALL d2 (IMPLIES (IN d2 RR)
   (FORALL p (IMPLIES (IN p RR) (FORALL q (IMPLIES (IN q RR)
     (= (+ (* (+ (* d2 q) (* d1 (* (* s p) (- 1)))) r) (* (* d1 q) 0))
        (- (* (* r d2) q) (* (* (* s r) d1) p)))))))))))))))))
(dk-peel-to! '=)
(crs)
(qed 'tgd-step-identity)
(topic! 'tgd-step-identity 'analysis)

(sp (make-wff '(FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
   (= v (+ u (- v u)))))))))
(dk-peel-to! '=)
(crs)
(qed 'tgd-telescope-identity)
(topic! 'tgd-telescope-identity 'analysis)

;;; ====================================================================
;;; (7) THE SUMMAND'S DERIVATIVE.  T_{m+1}(z) = f^(m+1)(z) (x-z)^(succ m) recip((succ m)!)
;;; has derivative  V_{m+1} - V_m  at t, given f^(m+1) differentiable at t with
;;; value f^(m+2)(t).  Product rule twice, `lam-b-h' reducing each landed
;;; lambda in place (deriv-polynomial.scm's move), then (3) + (6) on the value.
;;; ====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN) (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
    (list 'FORALL 't (list 'IMPLIES '(IN t RR)
      (list 'IMPLIES '(IS-DIFF-AT (NTH-DERIV f (succ m)) t ((NTH-DERIV f (succ (succ m))) t))
        (list 'IS-DIFF-AT (tgd-term-lam 'f 'x '(succ m)) 't
              (list '- (tgd-val 'f 'x 't '(succ m)) (tgd-val 'f 'x 't 'm)))))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-hyp '(IS-DIFF-AT (NTH-DERIV f (succ m)) t ((NTH-DERIV f (succ (succ m))) t)))
(define tgd-f1 '(NTH-DERIV f (succ m)))
(define tgd-d2 '((NTH-DERIV f (succ (succ m))) t))
(define tgd-d1 '((NTH-DERIV f (succ m)) t))
(tgd-proj! tgd-hyp (list 'IN tgd-f1 '(FUN RR RR)))
(tgd-proj! tgd-hyp (list 'IN tgd-d2 'RR))
(fact 'fun-apply-type-c tgd-f1 'RR 'RR 't)                            ; d1 in RR
(define tgd-pwd (dk-fact! 'tgd-power-sub-diff 'm 'x 't))
(define tgd-pwlam (cadr tgd-pwd))
(define tgd-mp (cadddr tgd-pwd))
;; LUTINS instantiation (2026-09-18): the two `deriv-product' citations below
;; are AT tgd-mp and at tgd-va, products carrying powers; the owed-leaf hook
;; runs `in-rr', which cannot type a power.  The four typing citations that
;; used to sit in the VALUE block below are moved up and the products
;; assembled here.
(fact 'nn-succ-closed 'm)
(fact 'nn-in-rr '(succ m))
(fact 'rr-one-in)
(fact 'rr-sub-in-rr 'x 't)
(fact 'power-closed-at 'm '(- x t))
(fact 'power-closed-at '(succ m) '(- x t))
(tg-mul-real! '(succ m) '(power (- x t) m))
(have! (list 'IN '(- 1) 'RR) (lambda () (in-rr)))
(tg-mul-real! '(* (succ m) (power (- x t) m)) '(- 1))                 ; tgd-mp in RR
(have! (list 'AND tgd-hyp tgd-pwd))
(define tgd-p1 (dk-fact! 'deriv-product tgd-f1 tgd-pwlam 't tgd-d2 tgd-mp))
(define tgd-p1b (dk-landed-1 (lambda () (lam-b-h tgd-p1))))          ; z |-> f^(m+1)(z) (x-z)^(succ m)
(define tgd-alam (cadr tgd-p1b))
(define tgd-va (cadddr tgd-p1b))
(tg-mul-real! tgd-d2 '(power (- x t) (succ m)))
(tg-mul-real! tgd-d1 tgd-mp)
(tg-add-real! (list '* tgd-d2 '(power (- x t) (succ m))) (list '* tgd-d1 tgd-mp))
(fact 'tgd-recip-factorial-in-rr '(succ m))
(have! '(AND (IN (recip (FACTORIAL (succ m))) RR) (IN t RR)))
(define tgd-kc (dk-fact! 'deriv-const '(recip (FACTORIAL (succ m))) 't))
(have! (list 'AND tgd-p1b tgd-kc))
(define tgd-p2 (dk-fact! 'deriv-product tgd-alam (cadr tgd-kc) 't tgd-va 0))
(lam-b-h tgd-p2)                                                     ; now literally T_{m+1}
;; the value: recip(m!) -> (succ m) recip((succ m)!), then the identity
(fact 'tgd-recip-factorial-succ 'm)
(subst '(= (recip (FACTORIAL m)) (* (succ m) (recip (FACTORIAL (succ m))))))
(define tgd-id (dk-fact! 'tgd-step-identity '(succ m) '(recip (FACTORIAL (succ m))) tgd-d1 tgd-d2
                         '(power (- x t) m) '(power (- x t) (succ m))))
(fact 'eq-sym (cadr tgd-id) (caddr tgd-id))
(subst (list '= (caddr tgd-id) (cadr tgd-id)))
(ass)
(qed 'tgd-term-diff)
(topic! 'tgd-term-diff 'analysis)
(alias! 'tgd-term-diff "the Taylor summand's derivative in the centre telescopes")

;;; ====================================================================
;;; (8) the base sum:  SPS(term_z, succ 0) == f(z).
;;; term_z(0) = f^(0)(z) (x-z)^0 recip(0!) = f(z) . 1 . 1, and the recurrence.
;;; ====================================================================
(sp (make-wff '(FORALL f (IMPLIES (IN f (FUN RR RR)) (FORALL x (IMPLIES (IN x RR) (FORALL z (IMPLIES (IN z RR)
   (== (SERIES-PARTIAL-SUM (VNB-LAMBDA k NN (* (* ((NTH-DERIV f k) z) (power (- x z) k)) (recip (FACTORIAL k)))) (succ 0))
       (f z))))))))))
(dk-peel-to! '==)
(define tgd-tm0 (tgd-term 'f 'x))
(fact 'nn-zero-in)
(fact 'fun-apply-type-c 'f 'RR 'RR 'z)
(fact 'rr-sub-in-rr 'x 'z)
(fact 'rr-subset-cc '(- x z))
(have! '(= (recip (succ 0)) 1)
  (lambda () (have! '(= (succ 0) 1) (lambda () (arith))) (subst '(= (succ 0) 1)) (fact 'tgd-recip-one) (ass)))
(have! (list '= (list tgd-tm0 0) '(f z))
  (lambda ()
    (lam-b)
    (mac 'nth-deriv-zero)
    (mac 'power-zero)
    (mac 'factorial-zero)
    (subst '(= (recip (succ 0)) 1))
    (crs)))
(have! (list 'IN (list tgd-tm0 0) 'RR) (lambda () (subst (list '= (list tgd-tm0 0) '(f z))) (ass)))
(have! (list 'IN (list 'SERIES-PARTIAL-SUM tgd-tm0 0) 'RR)
       (lambda () (mac 'series-partial-sum-zero) (fact 'rr-zero-in) (ass)))
(fact 'series-partial-sum-succ tgd-tm0 0)
(subst (list '== (list 'SERIES-PARTIAL-SUM tgd-tm0 '(succ 0))
                 (list '+ (list 'SERIES-PARTIAL-SUM tgd-tm0 0) (list tgd-tm0 0))))
(mac 'series-partial-sum-zero)
(subst (list '= (list tgd-tm0 0) '(f z)))
(have! '(= (+ 0 (f z)) (f z)) (lambda () (crs)))
(subst '(= (+ 0 (f z)) (f z)))
(qrfl)
(qed 'tgd-base-sum-value)
(topic! 'tgd-base-sum-value 'analysis)

;;; ====================================================================
;;; (9) THE INDUCTION:  S_m'(t) = V_m,  degree OUTERMOST.
;;; ====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
    (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR)
        (list 'IMPLIES (tgd-dh 'f 't 'm)
          (list 'IS-DIFF-AT (tgd-sum-lam 'f 'x 'm) 't (tgd-val 'f 'x 't 'm))))))))))))
(define tgd-br (use-induction))
(define tgd-m  (cdr (assq 'var tgd-br)))
(define tgd-ih (cdr (assq 'ih  tgd-br)))

;; read f, x, t off the GOAL  (IS-DIFF-AT (VNB-LAMBDA z RR (SPS TERM (succ m))) t V)
(define (tgd-goal-f) (cadr (car (cadr (cadr (cadddr (cadr (cadddr (cadr (dk-goal))))))))))
(define (tgd-goal-x) (cadr (cadr (caddr (cadr (cadddr (cadr (cadddr (cadr (dk-goal))))))))))
(define (tgd-goal-t) (caddr (dk-goal)))

;;; --- base:  S_0 == f pointwise, so S_0' = f'(t);  V_0 = f^(1)(t). ---
(dk-focus! (cdr (assq 'base tgd-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-bf (tgd-goal-f))
(define tgd-bx (tgd-goal-x))
(define tgd-bt (tgd-goal-t))
(define tgd-bs (tgd-sum-lam tgd-bf tgd-bx 0))
(define tgd-bd0 (list (list 'NTH-DERIV tgd-bf '(succ 0)) tgd-bt))
(fact 'nn-zero-in)
(fact 'nn-le-refl 0)
(have! '(AND (IN 0 NN) (<= 0 0)))
(define tgd-bh0 (dk-deepest (lambda () (inst+ (tgd-dh tgd-bf tgd-bt 0) 0))))   ; IS-DIFF-AT f^(0) t f^(1)(t)
(tgd-proj! tgd-bh0 (list 'IN (list 'NTH-DERIV tgd-bf 0) '(FUN RR RR)))
(mac-h 'nth-deriv-zero (list 'IN (list 'NTH-DERIV tgd-bf 0) '(FUN RR RR)))    ; f in FUN RR RR
(define tgd-bh0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgd-bh0))))  ; IS-DIFF-AT f t f^(1)(t)
(tgd-proj! tgd-bh0f (list 'IN tgd-bd0 'RR))
(have! (list 'IN tgd-bs '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (fact 'tgd-base-sum-value tgd-bf tgd-bx v)
      (subst (list '== (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term tgd-bf tgd-bx)) '(succ 0)) (list tgd-bf v)))
      (fact 'fun-apply-type-c tgd-bf 'RR 'RR v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-bs 'x_) (list tgd-bf 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      (lam-b)
      (fact 'tgd-base-sum-value tgd-bf tgd-bx v)
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-bs tgd-bf tgd-bt tgd-bd0)
;; the value:  (recip(0!) . f^(1)(t)) . (x-t)^0  =  f^(1)(t)
(mac 'factorial-zero)
(have! '(= (recip (succ 0)) 1)
  (lambda () (have! '(= (succ 0) 1) (lambda () (arith))) (subst '(= (succ 0) 1)) (fact 'tgd-recip-one) (ass)))
(subst '(= (recip (succ 0)) 1))
(fact 'rr-sub-in-rr tgd-bx tgd-bt)
(fact 'rr-subset-cc (list '- tgd-bx tgd-bt))
(mac 'power-zero)
(have! (list '= (list '* (list '* 1 tgd-bd0) 1) tgd-bd0) (lambda () (crs)))
(subst (list '= (list '* (list '* 1 tgd-bd0) 1) tgd-bd0))
(ass)

;;; --- step:  S_{m+1} == S_m + T_{m+1} pointwise;  V_m + (V_{m+1} - V_m) = V_{m+1}. ---
(dk-focus! (cdr (assq 'step tgd-br)))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-sf (tgd-goal-f))
(define tgd-sx (tgd-goal-x))
(define tgd-st (tgd-goal-t))
(define tgd-sm (list 'succ tgd-m))
(define tgd-ssm (list 'succ tgd-sm))
(define tgd-s-lo (tgd-sum-lam tgd-sf tgd-sx tgd-m))                   ; S_m
(define tgd-s-hi (tgd-sum-lam tgd-sf tgd-sx tgd-sm))                  ; S_{m+1}
(define tgd-s-tm (tgd-term tgd-sf tgd-sx))                            ; term_z
(define tgd-s-f1 (list 'NTH-DERIV tgd-sf tgd-sm))                     ; f^(m+1)
(define tgd-v-lo (tgd-val tgd-sf tgd-sx tgd-st tgd-m))                ; V_m
(define tgd-v-hi (tgd-val tgd-sf tgd-sx tgd-st tgd-sm))               ; V_{m+1}
(fact 'nn-succ-closed tgd-m)
(fact 'nn-le-succ tgd-m)                                              ; m <= succ m
;; the goal's DH is at succ m; the induction hypothesis wants it at m
(have! (tgd-dh tgd-sf tgd-st tgd-m)
  (lambda ()
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k m))
           (kv     (cadr (cadr landed))))
      (dk-split! landed)
      (fact 'nn-le-trans-guarded kv tgd-m tgd-sm)
      (have! (list 'AND (list 'IN kv 'NN) (list '<= kv tgd-sm)))
      (inst+ (tgd-dh tgd-sf tgd-st tgd-sm) kv)
      (ass))))
;; ... and the hypothesis applies:  IS-DIFF-AT S_m t V_m
(define tgd-ih1 (dk-landed-1 (lambda () (inst+ tgd-ih tgd-sf))))
(define tgd-ih2 (dk-deepest  (lambda () (inst+ tgd-ih1 tgd-sx))))
(define tgd-hs  (dk-deepest  (lambda () (inst+ tgd-ih2 tgd-st))))
(if (not (and (pair? tgd-hs) (eq? (car tgd-hs) 'IS-DIFF-AT)))
    (error "taylor-g-diff: the induction hypothesis did not detach" tgd-hs))
(tgd-proj! tgd-hs (list 'IN tgd-s-lo '(FUN RR RR)))
;; LUTINS instantiation (2026-09-18): `diff-value-real' would be cited AT
;; V_m, which is exactly the term it types -- and the certificate refuses it,
;; V_m carrying a recip(FACTORIAL) and a power.  The same conjunct comes out of
;; the induction hypothesis by an UNFOLD, which owes nothing.
(tgd-proj! tgd-hs (list 'IN tgd-v-lo 'RR))                             ; V_m in RR
;; f^(m+1) is differentiable at t (DH at k = succ m), so the summand is (7)
(fact 'nn-le-refl tgd-sm)
(have! (list 'AND (list 'IN tgd-sm 'NN) (list '<= tgd-sm tgd-sm)))
(define tgd-h1 (dk-deepest (lambda () (inst+ (tgd-dh tgd-sf tgd-st tgd-sm) tgd-sm))))
(tgd-proj! tgd-h1 (list 'IN tgd-s-f1 '(FUN RR RR)))
(tgd-proj! tgd-h1 (list 'IN (cadddr tgd-h1) 'RR))                     ; f^(m+2)(t) in RR
(define tgd-ht (dk-fact! 'tgd-term-diff tgd-m tgd-sf tgd-sx tgd-st))   ; IS-DIFF-AT T_{m+1} t (V_{m+1} - V_m)
(define tgd-t-lam (cadr tgd-ht))
;; V_{m+1} in RR, from its three factors
(fact 'tgd-recip-factorial-in-rr tgd-sm)
(fact 'rr-sub-in-rr tgd-sx tgd-st)
(fact 'power-closed-at tgd-sm (list '- tgd-sx tgd-st))
(have! (list 'AND (list 'IN (list 'recip (list 'FACTORIAL tgd-sm)) 'RR) (list 'IN (cadddr tgd-h1) 'RR)))
(fact 'rr-mul-closed (list 'recip (list 'FACTORIAL tgd-sm)) (cadddr tgd-h1))
(have! (list 'AND (list 'IN (cadr tgd-v-hi) 'RR) (list 'IN (caddr tgd-v-hi) 'RR)))
(fact 'rr-mul-closed (cadr tgd-v-hi) (caddr tgd-v-hi))                ; V_{m+1} in RR
;; the sum rule on S_m and T_{m+1}
(have! (list 'AND tgd-hs tgd-ht))
(define tgd-ssum (dk-fact! 'deriv-sum tgd-s-lo tgd-t-lam tgd-st tgd-v-lo (cadddr tgd-ht)))
(define tgd-ssum2 (dk-landed-1 (lambda () (lam-b-h tgd-ssum))))       ; z |-> SPS(term_z, succ m) + T_{m+1}(z)
(define tgd-ssum-lam (cadr tgd-ssum2))
;; the recurrence at a real point v:  SPS(term_v, succ succ m) == SPS(term_v, succ m) + term_v(succ m),
;; with its two typings landed first (series-partial-sum-succ is guarded on both)
(define (tgd-sps-step! v)
  (let ((tm (tgd-term tgd-sf tgd-sx)))
    (let ((tmv (subst-free 'z v tm)))
      ;; the lower sum is real BECAUSE S_m is a function (the IH's own typing)
      (fact 'fun-apply-type-c tgd-s-lo 'RR 'RR v)
      (lam-b-h (list 'IN (list tgd-s-lo v) 'RR))
      ;; the summand is real: its three factors are
      (have! (list 'IN (list tmv tgd-sm) 'RR)
        (lambda ()
          (lam-b)
          (fact 'fun-apply-type-c tgd-s-f1 'RR 'RR v)
          (fact 'rr-sub-in-rr tgd-sx v)
          (fact 'power-closed-at tgd-sm (list '- tgd-sx v))
          (have! (list 'AND (list 'IN (list tgd-s-f1 v) 'RR)
                            (list 'IN (list 'power (list '- tgd-sx v) tgd-sm) 'RR)))
          (fact 'rr-mul-closed (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm))
          (have! (list 'AND (list 'IN (list '* (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm)) 'RR)
                            (list 'IN (list 'recip (list 'FACTORIAL tgd-sm)) 'RR)))
          (fact 'rr-mul-closed (list '* (list tgd-s-f1 v) (list 'power (list '- tgd-sx v) tgd-sm))
                               (list 'recip (list 'FACTORIAL tgd-sm)))
          (ass)))
      (fact 'series-partial-sum-succ tmv tgd-sm)
      (list '== (list 'SERIES-PARTIAL-SUM tmv tgd-ssm)
                (list '+ (list 'SERIES-PARTIAL-SUM tmv tgd-sm) (list tmv tgd-sm))))))
;; S_{m+1} is a function RR -> RR
(have! (list 'IN tgd-s-hi '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((v (tgd-di-var!))
           (rec (tgd-sps-step! v)))
      (subst rec)
      (have! (list 'AND (list 'IN (cadr (caddr rec)) 'RR) (list 'IN (caddr (caddr rec)) 'RR)))
      (fact 'rr-add-closed (cadr (caddr rec)) (caddr (caddr rec)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-s-hi 'x_) (list tgd-ssum-lam 'x_))))
  (lambda ()
    (let* ((v (tgd-di-var!))
           (rec (tgd-sps-step! v)))
      (lam-b)
      (subst rec)
      (lam-b)
      (qrfl))))
(fact 'diff-transfer-ptwise-eq tgd-s-hi tgd-ssum-lam tgd-st (cadddr tgd-ssum2))
;; the value:  V_{m+1} = V_m + (V_{m+1} - V_m)
(fact 'tgd-telescope-identity tgd-v-lo tgd-v-hi)
(subst (list '= tgd-v-hi (list '+ tgd-v-lo (list '- tgd-v-hi tgd-v-lo))))
(ass)
(qed 'tgd-sum-diff)
(topic! 'tgd-sum-diff 'analysis)
(alias! 'tgd-sum-diff "the derivative of the Taylor partial sum in its centre")

;;; ====================================================================
;;; (10) THE HEADLINE -- taylor-G-diff, guarded (see the header).
;;; G = f(x) - S_n:  deriv-const, deriv-neg, deriv-sum, then the transfer to
;;; the literal G through TAYLOR-POLY's unfold and binary-minus-def.
;;; ====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (IN n NN)
     (IMPLIES (IN x RR)
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (AND (< a t) (< t x))
       (IS-DIFF-AT (VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))) t
                   (- 0 (* (* (recip (FACTORIAL n)) ((NTH-DERIV f (succ n)) t)) (power (- x t) n)))))))))))))))
(dk-peel-to! 'IS-DIFF-AT)
(define tgd-g-lam '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tgd-g-s (tgd-sum-lam 'f 'x 'n))
(define tgd-g-v (tgd-val 'f 'x 't 'n))
;; DH(f,t,n) out of TAYLOR-DIFFERENTIABLE's second conjunct, on a side branch.
;; (AND (< a t) (< t x)) stays WHOLE in context: `inst+' detaches it as one
;; antecedent, and `dk-split!' would have consumed it.)
(have! (tgd-dh 'f 't 'n)
  (lambda ()
    ;; split ONLY the unfolded TD (a blanket AND-split would also consume the
    ;; (AND (< a t) (< t x)) that the inst+ below detaches)
    (dk-split! (dk-landed-1 (lambda () (mac-h 'TAYLOR-DIFFERENTIABLE '(TAYLOR-DIFFERENTIABLE f a x n)))))
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k n)), kept whole
           (kv     (cadr (cadr landed)))
           (c2     (tgd-find (lambda (u) (and (pair? u) (eq? (car u) 'FORALL)
                                              (tgd-mentions? 'IS-DIFF-AT u)))
                             'the-differentiability-conjunct)))
      (let ((at-k (dk-deepest (lambda () (inst+ c2 kv)))))
        (inst+ at-k 't)                                               ; (AND (< a t) (< t x)) is in context
        (ass)))))
;; t in RR and f in FUN RR RR, both off DH at k = 0
(fact 'nn-zero-in)
(fact 'nn-zero-le 'n)
(have! '(AND (IN 0 NN) (<= 0 n)))
(define tgd-g-h0 (dk-deepest (lambda () (inst+ (tgd-dh 'f 't 'n) 0))))
(tgd-proj! tgd-g-h0 '(IN t RR))
(tgd-proj! tgd-g-h0 '(IN (NTH-DERIV f 0) (FUN RR RR)))
(mac-h 'nth-deriv-zero '(IN (NTH-DERIV f 0) (FUN RR RR)))
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)                                ; f(x) in RR
;; S_n' = V_n
(define tgd-g-hs (dk-fact! 'tgd-sum-diff 'n 'f 'x 't))
(if (not (and (pair? tgd-g-hs) (eq? (car tgd-g-hs) 'IS-DIFF-AT)))
    (error "taylor-g-diff: tgd-sum-diff did not detach" tgd-g-hs))
(tgd-proj! tgd-g-hs (list 'IN tgd-g-s '(FUN RR RR)))
;; LUTINS instantiation (2026-09-18): `deriv-neg' is cited AT V_n and
;; `deriv-sum' at -V_n; V_n carries a recip(FACTORIAL) and a power, so the
;; owed-leaf hook's `in-rr' cannot type it.  It is the value conjunct of the
;; IS-DIFF-AT just landed, one unfold away.
(tgd-proj! tgd-g-hs (list 'IN tgd-g-v 'RR))
(have! (list 'IN (list '- tgd-g-v) 'RR) (lambda () (in-rr)))
;; -S_n, the constant f(x), their sum
(define tgd-g-neg (dk-fact! 'deriv-neg tgd-g-s 't tgd-g-v))
(define tgd-g-neg2 (dk-landed-1 (lambda () (lam-b-h tgd-g-neg))))     ; z |-> -SPS(term_z, succ n)
(have! '(AND (IN (f x) RR) (IN t RR)))
(define tgd-g-kc (dk-fact! 'deriv-const '(f x) 't))
(have! (list 'AND tgd-g-kc tgd-g-neg2))
(define tgd-g-sum (dk-fact! 'deriv-sum (cadr tgd-g-kc) (cadr tgd-g-neg2) 't 0 (list '- tgd-g-v)))
(define tgd-g-sum2 (dk-landed-1 (lambda () (lam-b-h tgd-g-sum))))     ; z |-> f(x) + (-SPS(...))
(define tgd-g-sum-lam (cadr tgd-g-sum2))
;; G is a function RR -> RR ...
(have! (list 'IN tgd-g-lam '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (tgd-di-var!)))
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgd-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgd-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term 'f 'x)) '(succ n)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '== (list tgd-g-lam 'x_) (list tgd-g-sum-lam 'x_))))
  (lambda ()
    (let ((v (tgd-di-var!)))
      ;; LUTINS instantiation (2026-09-18): `binary-minus-def' is cited AT the
      ;; partial sum, and a SERIES-PARTIAL-SUM is never certified
      ;; syntactically.  Its typing is the beta of S_n's own function typing --
      ;; the same two lines the FUN lane just above uses.
      (fact 'fun-apply-type-c tgd-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgd-g-s v) 'RR))
      (lam-b)
      (mac 'TAYLOR-POLY)
      (fact 'binary-minus-def '(f x) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgd-term 'f 'x)) '(succ n)))
      (ass))))
(fact 'diff-transfer-ptwise-eq tgd-g-lam tgd-g-sum-lam 't (list '+ 0 (list '- tgd-g-v)))
;; the value:  0 - V_n == 0 + (-V_n)
(fact 'binary-minus-def 0 tgd-g-v)
(subst (list '== (list '- 0 tgd-g-v) (list '+ 0 (list '- tgd-g-v))))
(ass)
(qed 'taylor-G-diff)
(topic! 'taylor-G-diff 'analysis)
(alias! 'taylor-G-diff "the derivative of the Taylor remainder in its centre")

;;; ===== END spliced block 1b =====

;;; =====================================================================
;;; BEGIN second spliced block (2026-09-14): the gMVT wrappers, GUARDED and
;;; PROVEN (was theorem-library/taylor-gmvt-guarded.scm; same window reason).
;;; =====================================================================
;;; theorem-library/taylor-gmvt-guarded.scm -- the four gMVT hypotheses of
;;; Taylor's theorem, GUARDED and PROVEN:
;;;
;;;   taylor-H-cont     H(t) = (x-t)^(n+1) is continuous at every real t
;;;   taylor-G-cont     G(t) = f(x) - TAYLOR-POLY(f,t,n,x) is continuous at
;;;                     every t in [a,x], given TAYLOR-DIFFERENTIABLE(f,a,x,n)
;;;   taylor-gmvt-cont  both, at every t in [a,x]  (the shape generalized-mvt reads)
;;;   taylor-gmvt-diff  both have SOME derivative at every real t in (a,x)
;;;
;;; All four stood in taylor-proof.scm as `add-to-pss' + `warrant! 'reference'
;;; (lines 61-96).  The triage of 2026-09-14 found them FALSE AS WRITTEN: `n'
;;; was unguarded, and off NN the power (x-z)^(succ n), the factorial and the
;;; partial sum mean nothing.  The user's decision (2026-09-14): add the guards,
;;; prove the guarded statements.  The statements below are the supports' with
;;; antecedents ADDED and nothing else touched -- binders and bodies are
;;; byte-identical to taylor-proof.scm's (GT, HT, GHCONT, GHDIFF are copied
;;; verbatim as tgc-gt / tgc-ht / tgc-ghcont / tgc-ghdiff):
;;;
;;;   taylor-H-cont     + (IN n NN)
;;;   taylor-G-cont     + (IN n NN), (IN x RR)     -- the same two taylor-G-diff took
;;;   taylor-gmvt-cont  + (IN n NN)                -- (IN x RR) was already there
;;;   taylor-gmvt-diff  + (IN n NN), (IN x RR)
;;;
;;; No guard on `a': G-cont reads (IN t RR) off TAYLOR-DIFFERENTIABLE's own
;;; continuity conjunct (the point conjunct of IS-CONTINUOUS-AT), and gmvt-cont
;;; reads it off `ccint-membership', which is unguarded.
;;;
;;; PLAN.
;;;   H-cont:  taylor-h-diff (the spliced block of taylor-proof.scm) gives
;;;            IS-DIFF-AT HT t (HVAL t) at EVERY real t, and
;;;            diff-implies-continuous does the rest.  No endpoint case: H is
;;;            differentiable everywhere, endpoints included.
;;;   G-cont:  NOT through differentiability -- TD gives G a derivative only
;;;            on the OPEN interval, and continuity at the endpoints a, x is
;;;            exactly what that route cannot reach.  Instead the continuity
;;;            of z |-> TAYLOR-POLY(f,z,n,x) at t is proved by INDUCTION ON
;;;            THE DEGREE (taylor-g-diff.scm's `tgd-sum-diff', with
;;;            continuity in place of differentiability), from the hypothesis
;;;              CH(f,t,m) = forall k <= m. f^(k) continuous at t,
;;;            which TD's FIRST conjunct supplies at every t in [a,x],
;;;            endpoints included.  So one argument covers the whole closed
;;;            interval and no endpoint lemma is needed.
;;;              base  S_0 == f pointwise (tgd-base-sum-value), transfer.
;;;              step  S_{m+1} == S_m + T_{m+1} pointwise
;;;                    (series-partial-sum-succ), sum-continuous-at, transfer;
;;;                    T_{m+1} = f^(m+1) . (x-z)^(m+1) . recip((m+1)!) is
;;;                    continuous by product-continuous-at twice, on
;;;                    f^(m+1) (CH), taylor-H-cont at degree m, and the
;;;                    constant (const-continuous-at)  -- `tgc-term-cont'.
;;;            Then G = const(f(x)) - S_n by sub-continuous-at and one more
;;;            transfer through TAYLOR-POLY's unfold.
;;;   gmvt-cont:  the two above at t in [a,x]; `ccint-membership' for t in RR.
;;;   gmvt-diff:  taylor-g-diff / taylor-h-diff give the explicit derivatives;
;;;            `ew' each and close.
;;;
;;; LOAD WINDOW.  This file cites `taylor-h-diff' (the spliced block of
;;; taylor-proof.scm), `recip-factorial-in-rr' (taylor-proof.scm's lemma
;;; block), `tgd-base-sum-value' (theorem-library/taylor-g-diff.scm, which
;;; loads before taylor-proof), `taylor-G-diff' (same), and is cited by
;;; `taylor-lagrange' at the END of taylor-proof.scm.  So it must sit INSIDE
;;; taylor-proof.scm, after the existing spliced block (`END spliced block')
;;; and before the taylor-lagrange section: THE INTEGRATOR SPLICES THIS FILE'S
;;; BODY IN THERE and retires the four supports at taylor-proof.scm:61-96
;;; (with their warrant! / topic! lines).  Everything else cited loads well
;;; before taylor-proof: diff-implies-continuous (differentiation),
;;; sum-continuous-at / product-continuous-at / const-continuous-at /
;;; sub-continuous-at / cont-transfer-ptwise-eq (the continuity-* files),
;;; ccint-membership (ccint-basics), series-partial-sum-succ
;;; (comparison-test-proof), fun-apply-type-c, power-closed-at (dyadic-weights),
;;; rr-sub-in-rr, nn-le-refl / nn-le-succ / nn-le-trans-guarded / nn-zero-le,
;;; nth-deriv-zero (higher-derivatives).
;;;
;;; Helper prefix: tgc-.  Every top-level define is prefixed.
;;; ====================================================================

;;; ---- file-local shapes (VERBATIM copies of taylor-proof.scm's GT/HT/GHCONT/GHDIFF) ----
(define tgc-gt '(VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))))
(define tgc-ht '(VNB-LAMBDA z RR (power (- x z) (succ n))))
(define (tgc-gval t) (list '- 0 (list '* (list '* '(recip (FACTORIAL n)) (list (list 'NTH-DERIV 'f '(succ n)) t)) (list 'power (list '- 'x t) 'n))))
(define (tgc-hval t) (list '- 0 (list '* '(succ n) (list 'power (list '- 'x t) 'n))))
(define tgc-ghcont (list 'FORALL 't (list 'IMPLIES '(IN t (CCINT a x))
                 (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-gt 't)
                            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-ht 't)))))
(define tgc-ghdiff (list 'FORALL 't (list 'IMPLIES '(AND (IN t RR) (AND (< a t) (< t x)))
                 (list 'AND (list 'FORSOME 'L (list 'IS-DIFF-AT tgc-gt 't 'L))
                            (list 'FORSOME 'M (list 'IS-DIFF-AT tgc-ht 't 'M))))))

(define (tgc-cont fn t) (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS fn t))
(define (tgc-term f x)          ; the Taylor summand  k |-> f^(k)(z) (x-z)^k recip(k!),  z FREE
  (list 'VNB-LAMBDA 'k 'NN
        (list '* (list '* (list (list 'NTH-DERIV f 'k) 'z) (list 'power (list '- x 'z) 'k))
                 (list 'recip (list 'FACTORIAL 'k)))))
(define (tgc-term-lam f x k)    ; z |-> f^(k)(z) (x-z)^k recip(k!)
  (list 'VNB-LAMBDA 'z 'RR
        (list '* (list '* (list (list 'NTH-DERIV f k) 'z) (list 'power (list '- x 'z) k))
                 (list 'recip (list 'FACTORIAL k)))))
(define (tgc-sum-lam f x m)     ; z |-> SPS(term_z, succ m)
  (list 'VNB-LAMBDA 'z 'RR (list 'SERIES-PARTIAL-SUM (tgc-term f x) (list 'succ m))))
(define (tgc-pow-lam x m)       ; z |-> (x-z)^(succ m)   (HT with n := m)
  (list 'VNB-LAMBDA 'z 'RR (list 'power (list '- x 'z) (list 'succ m))))
(define (tgc-ch f t m)          ; CH(f,t,m): f^(k) continuous at t for k <= m
  (list 'FORALL 'k (list 'IMPLIES (list 'AND '(IN k NN) (list '<= 'k m))
    (tgc-cont (list 'NTH-DERIV f 'k) t))))

;;; ---- file-local helpers ----
(define (tgc-mentions? sym f)
  (cond ((eq? f sym) #t)
        ((pair? f) (or (tgc-mentions? sym (car f)) (tgc-mentions? sym (cdr f))))
        (#t #f)))
(define (tgc-find pred what)
  (or (find-first pred (dk-asms)) (error "taylor-gmvt-guarded: no assumption" what)))
(define (tgc-split-ands!)
  (let loop ((n 0))
    (let ((tgt (find-first (lambda (a) (and (pair? a) (memq (car a) '(AND FORSOME)))) (dk-asms))))
      (if (and tgt (< n 20)) (begin (ai tgt) (loop (+ n 1)))))))
;; read the FUN typing / the point off an IS-CONTINUOUS-AT hypothesis WITHOUT
;; destroying it: mac-h replaces the assumption, so the unfold runs on the
;; have! side branch only (continuity-sub.scm's cu-typing! / cu-point!).
(define (tgc-fun! hyp)
  (let ((fn (cadddr hyp)))
    (have! (list 'IN fn '(FUN RR RR))
      (lambda ()
        (mac-h 'IS-CONTINUOUS-AT hyp)
        (tgc-split-ands!)
        (slot-h 'PTS (list 'IN fn '(FUN (PTS RR-MS) (PTS RR-MS))))
        (ass)))))
(define (tgc-point! hyp)
  (let ((pt (car (cddddr hyp))))
    (have! (list 'IN pt 'RR)
      (lambda ()
        (mac-h 'IS-CONTINUOUS-AT hyp)
        (tgc-split-ands!)
        (slot-h 'PTS (list 'IN pt '(PTS RR-MS)))
        (ass)))))
;; (IN (* a b) RR) from the two factor typings already in context
(define (tgc-mul-real! a b)
  (have! (list 'AND (list 'IN a 'RR) (list 'IN b 'RR)))
  (fact 'rr-mul-closed a b))
;; lam-b the goal to a fixpoint (nested redexes appear one reduction at a time)
(define (tgc-beta!)
  (let loop ((k 0) (prev #f))
    (let ((g (dk-goal)))
      (if (and (< k 8) (not (equal? g prev)))
          (begin (quietly (lambda () (vnb-guard (lambda () (lam-b))))) (loop (+ k 1) g))))))
(define (tgc-check-head! f head what)
  (if (not (and (pair? f) (eq? (car f) head)))
      (error "taylor-gmvt-guarded: expected" head what f)))

;;; =====================================================================
;;; (1) taylor-H-cont, guarded by n in NN.  H is differentiable at every
;;; real t (taylor-h-diff), hence continuous there.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'x (list 'FORALL 'n (list 'FORALL 't (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN t RR)
    (list 'IMPLIES '(IN n NN)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS tgc-ht 't)))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(fact 'taylor-h-diff 'x 'n 't)
;; LUTINS instantiation (2026-09-18): `diff-implies-continuous' is cited AT
;; H'(t) = 0 - (n+1)(x-t)^n, which carries a power the owed-leaf hook's
;; `in-rr' cannot type.
(fact 'rr-zero-in)
(fact 'nn-succ-closed 'n)
(fact 'nn-in-rr '(succ n))
(fact 'rr-sub-in-rr 'x 't)
(fact 'power-closed-at 'n '(- x t))
(tgc-mul-real! '(succ n) '(power (- x t) n))
(have! (list 'IN (tgc-hval 't) 'RR) (lambda () (in-rr)))
(fact 'diff-implies-continuous tgc-ht 't (tgc-hval 't))
(ass)
(qed 'taylor-H-cont)
(topic! 'taylor-H-cont 'analysis)

;;; =====================================================================
;;; (2) THE SUMMAND IS CONTINUOUS.  T_{m+1}(z) = f^(m+1)(z) (x-z)^(succ m) recip((succ m)!)
;;; at t, given f^(m+1) continuous at t: product-continuous-at on f^(m+1) and
;;; z |-> (x-z)^(succ m) (taylor-H-cont at degree m), then on that and the
;;; constant recip((succ m)!); `lam-b-h' reduces each landed lambda in place.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN) (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
    (list 'FORALL 't (list 'IMPLIES '(IN t RR)
      (list 'IMPLIES (tgc-cont '(NTH-DERIV f (succ m)) 't)
        (tgc-cont (tgc-term-lam 'f 'x '(succ m)) 't)))))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-tc-f1 '(NTH-DERIV f (succ m)))
(define tgc-tc-pw (tgc-pow-lam 'x 'm))
(fact 'taylor-H-cont 'x 'm 't)                                        ; z |-> (x-z)^(succ m) continuous at t
;; LUTINS instantiation (2026-09-18): `product-continuous-at' is cited AT
;; NTH-DERIV(f, succ m), an IOTA.  Its FUN typing is one unfold of the
;; continuity hypothesis away -- on a have! side branch, mac-h being
;; destructive and the hypothesis still needed below.
(tgc-fun! (tgc-cont tgc-tc-f1 't))
(define tgc-tc-p1 (dk-fact! 'product-continuous-at tgc-tc-f1 tgc-tc-pw 't))
(tgc-check-head! tgc-tc-p1 'IS-CONTINUOUS-AT "product-continuous-at (1)")
(define tgc-tc-p1b (dk-landed-1 (lambda () (lam-b-h tgc-tc-p1))))    ; z |-> f^(m+1)(z) (x-z)^(succ m)
(fact 'nn-succ-closed 'm)
(fact 'recip-factorial-in-rr '(succ m))
(define tgc-tc-kc (dk-fact! 'const-continuous-at '(recip (FACTORIAL (succ m))) 't))
(tgc-check-head! tgc-tc-kc 'IS-CONTINUOUS-AT "const-continuous-at")
(define tgc-tc-p2 (dk-fact! 'product-continuous-at (cadddr tgc-tc-p1b) (cadddr tgc-tc-kc) 't))
(tgc-check-head! tgc-tc-p2 'IS-CONTINUOUS-AT "product-continuous-at (2)")
(lam-b-h tgc-tc-p2)                                                   ; now literally T_{m+1}
(ass)
(qed 'tgc-term-cont)
(topic! 'tgc-term-cont 'analysis)
(alias! 'tgc-term-cont "the Taylor summand is continuous in the centre")

;;; =====================================================================
;;; (3) THE INDUCTION:  S_m = z |-> SPS(term_z, succ m) is continuous at t
;;; given CH(f,t,m).  Degree OUTERMOST so `ni' fires.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'm (list 'IMPLIES '(IN m NN)
    (list 'FORALL 'f (list 'FORALL 'x (list 'IMPLIES '(IN x RR)
      (list 'FORALL 't (list 'IMPLIES '(IN t RR)
        (list 'IMPLIES (tgc-ch 'f 't 'm)
          (tgc-cont (tgc-sum-lam 'f 'x 'm) 't)))))))))))
(define tgc-br (use-induction))
(define tgc-m  (cdr (assq 'var tgc-br)))
(define tgc-ih (cdr (assq 'ih  tgc-br)))

;; read f, x, t off the GOAL  (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA z RR (SPS TERM (succ m))) t)
(define (tgc-goal-lam) (cadddr (dk-goal)))
(define (tgc-goal-t)   (car (cddddr (dk-goal))))
(define (tgc-goal-f)   (cadr (car (cadr (cadr (cadddr (cadr (cadddr (tgc-goal-lam)))))))))
(define (tgc-goal-x)   (cadr (cadr (caddr (cadr (cadddr (cadr (cadddr (tgc-goal-lam)))))))))

;;; --- base:  S_0 == f pointwise (tgd-base-sum-value), and f is continuous (CH at 0). ---
(dk-focus! (cdr (assq 'base tgc-br)))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-bf (tgc-goal-f))
(define tgc-bx (tgc-goal-x))
(define tgc-bt (tgc-goal-t))
(define tgc-bs (tgc-sum-lam tgc-bf tgc-bx 0))
(define (tgc-b-eq v)          ; SPS(term_v, succ 0) == f(v)
  (list '== (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgc-term tgc-bf tgc-bx)) '(succ 0))
            (list tgc-bf v)))
(fact 'nn-zero-in)
(fact 'nn-le-refl 0)
(have! '(AND (IN 0 NN) (<= 0 0)))
(define tgc-bh0 (dk-deepest (lambda () (inst+ (tgc-ch tgc-bf tgc-bt 0) 0))))     ; f^(0) continuous at t
(tgc-check-head! tgc-bh0 'IS-CONTINUOUS-AT "CH at 0")
(define tgc-bh0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgc-bh0))))       ; f continuous at t
(tgc-fun! tgc-bh0f)                                                                ; f in FUN RR RR
(have! (list 'IN tgc-bs '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (fact 'tgd-base-sum-value tgc-bf tgc-bx v)
      (subst (tgc-b-eq v))
      (fact 'fun-apply-type-c tgc-bf 'RR 'RR v)
      (ass))))
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-bs 'x_) (list tgc-bf 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (lam-b)
      (fact 'tgd-base-sum-value tgc-bf tgc-bx v)
      (subst (tgc-b-eq v))
      (fact 'fun-apply-type-c tgc-bf 'RR 'RR v)
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-bs tgc-bf tgc-bt)
(ass)

;;; --- step:  S_{m+1} == S_m + T_{m+1} pointwise;  sum-continuous-at. ---
(dk-focus! (cdr (assq 'step tgc-br)))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-sf (tgc-goal-f))
(define tgc-sx (tgc-goal-x))
(define tgc-st (tgc-goal-t))
(define tgc-sm (list 'succ tgc-m))
(define tgc-ssm (list 'succ tgc-sm))
(define tgc-s-lo (tgc-sum-lam tgc-sf tgc-sx tgc-m))                   ; S_m
(define tgc-s-hi (tgc-sum-lam tgc-sf tgc-sx tgc-sm))                  ; S_{m+1}
(define tgc-s-f1 (list 'NTH-DERIV tgc-sf tgc-sm))                     ; f^(m+1)
(fact 'nn-succ-closed tgc-m)
(fact 'nn-le-succ tgc-m)                                              ; m <= succ m
;; the goal's CH is at succ m; the induction hypothesis wants it at m
(have! (tgc-ch tgc-sf tgc-st tgc-m)
  (lambda ()
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k m))
           (kv     (cadr (cadr landed))))
      (dk-split! landed)
      (fact 'nn-le-trans-guarded kv tgc-m tgc-sm)
      (have! (list 'AND (list 'IN kv 'NN) (list '<= kv tgc-sm)))
      (inst+ (tgc-ch tgc-sf tgc-st tgc-sm) kv)
      (ass))))
;; ... and the hypothesis applies:  S_m continuous at t
(define tgc-ih1 (dk-landed-1 (lambda () (inst+ tgc-ih tgc-sf))))
(define tgc-ih2 (dk-deepest  (lambda () (inst+ tgc-ih1 tgc-sx))))
(define tgc-hs  (dk-deepest  (lambda () (inst+ tgc-ih2 tgc-st))))
(tgc-check-head! tgc-hs 'IS-CONTINUOUS-AT "the induction hypothesis did not detach")
(tgc-fun! tgc-hs)                                                     ; S_m in FUN RR RR
;; f^(m+1) is continuous at t (CH at k = succ m), so the summand is (2)
(fact 'nn-le-refl tgc-sm)
(have! (list 'AND (list 'IN tgc-sm 'NN) (list '<= tgc-sm tgc-sm)))
(define tgc-h1 (dk-deepest (lambda () (inst+ (tgc-ch tgc-sf tgc-st tgc-sm) tgc-sm))))
(tgc-check-head! tgc-h1 'IS-CONTINUOUS-AT "CH at succ m")
(tgc-fun! tgc-h1)                                                     ; f^(m+1) in FUN RR RR
(define tgc-ht-c (dk-fact! 'tgc-term-cont tgc-m tgc-sf tgc-sx tgc-st))   ; T_{m+1} continuous at t
(tgc-check-head! tgc-ht-c 'IS-CONTINUOUS-AT "tgc-term-cont did not detach")
(define tgc-t-lam (cadddr tgc-ht-c))
;; the sum rule on S_m and T_{m+1}
(define tgc-ssum (dk-fact! 'sum-continuous-at tgc-s-lo tgc-t-lam tgc-st))
(tgc-check-head! tgc-ssum 'IS-CONTINUOUS-AT "sum-continuous-at did not detach")
(define tgc-ssum2 (dk-landed-1 (lambda () (lam-b-h tgc-ssum))))       ; z |-> SPS(term_z, succ m) + T_{m+1}(z)
(define tgc-ssum-lam (cadddr tgc-ssum2))
(fact 'recip-factorial-in-rr tgc-sm)
;; at a real point v: the reduced summand B_v is real, and the recurrence
;;   SPS(term_v, succ succ m) == SPS(term_v, succ m) + term_v(succ m),
;; with its two typings landed first (series-partial-sum-succ is guarded on both).
;; Returns (rec . B_v).
(define (tgc-sps-step! v)
  (let* ((tmv (subst-free 'z v (tgc-term tgc-sf tgc-sx)))
         (dv  (list tgc-s-f1 v))
         (pw  (list 'power (list '- tgc-sx v) tgc-sm))
         (rc  (list 'recip (list 'FACTORIAL tgc-sm)))
         (bv  (list '* (list '* dv pw) rc)))
    ;; the lower sum is real BECAUSE S_m is a function (the IH's own typing)
    (fact 'fun-apply-type-c tgc-s-lo 'RR 'RR v)
    (lam-b-h (list 'IN (list tgc-s-lo v) 'RR))
    ;; the summand is real: its three factors are
    (fact 'fun-apply-type-c tgc-s-f1 'RR 'RR v)
    (fact 'rr-sub-in-rr tgc-sx v)
    (fact 'power-closed-at tgc-sm (list '- tgc-sx v))
    (tgc-mul-real! dv pw)
    (tgc-mul-real! (list '* dv pw) rc)                                ; (IN B_v RR)
    (have! (list 'IN (list tmv tgc-sm) 'RR) (lambda () (lam-b) (ass)))
    (fact 'series-partial-sum-succ tmv tgc-sm)
    (cons (list '== (list 'SERIES-PARTIAL-SUM tmv tgc-ssm)
                    (list '+ (list 'SERIES-PARTIAL-SUM tmv tgc-sm) (list tmv tgc-sm)))
          bv)))
;; S_{m+1} is a function RR -> RR
(have! (list 'IN tgc-s-hi '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let* ((v (dk-di-var!))
           (rec (car (tgc-sps-step! v))))
      (subst rec)
      (have! (list 'AND (list 'IN (cadr (caddr rec)) 'RR) (list 'IN (caddr (caddr rec)) 'RR)))
      (fact 'rr-add-closed (cadr (caddr rec)) (caddr (caddr rec)))
      (ass))))
;; ... and agrees pointwise with the sum-rule lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-s-hi 'x_) (list tgc-ssum-lam 'x_))))
  (lambda ()
    (let* ((v   (dk-di-var!))
           (rb  (tgc-sps-step! v))
           (rec (car rb))
           (bv  (cdr rb))
           (tmv-app (caddr (caddr rec)))                              ; term_v(succ m)
           (lo      (cadr  (caddr rec))))                             ; SPS(term_v, succ m)
      (tgc-beta!)
      (subst rec)
      (tgc-beta!)
      ;; both sides should now read  SPS(term_v, succ m) + B_v;  if the
      ;; summand redex survived on the left, reduce it by citation
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (begin
            (have! (list '= tmv-app bv) (lambda () (lam-b) (rfl)))
            (subst (list '= tmv-app bv))))
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (error "taylor-gmvt-guarded: the two sides did not meet" (dk-goal)))
      (have! (list 'AND (list 'IN lo 'RR) (list 'IN bv 'RR)))
      (fact 'rr-add-closed lo bv)
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-s-hi tgc-ssum-lam tgc-st)
(ass)
(qed 'tgc-sum-cont)
(topic! 'tgc-sum-cont 'analysis)
(alias! 'tgc-sum-cont "the Taylor partial sum is continuous in its centre")

;;; =====================================================================
;;; (4) taylor-G-cont, guarded by n in NN, x in RR.  G = f(x) - S_n:
;;; const-continuous-at, sub-continuous-at, then the transfer to the literal
;;; G through TAYLOR-POLY's unfold.  CH(f,t,n) is TD's FIRST conjunct at the
;;; point t of [a,x] -- endpoints included, which is why no case split.
;;; =====================================================================
(sp (make-wff
  '(FORALL f (FORALL a (FORALL x (FORALL n (FORALL t
     (IMPLIES (IN n NN)
     (IMPLIES (IN x RR)
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
     (IMPLIES (IN t (CCINT a x))
       (IS-CONTINUOUS-AT RR-MS RR-MS (VNB-LAMBDA z RR (- (f x) (TAYLOR-POLY f z n x))) t))))))))))))
(dk-peel-to! 'IS-CONTINUOUS-AT)
(define tgc-g-s (tgc-sum-lam 'f 'x 'n))
(define (tgc-g-sps v) (list 'SERIES-PARTIAL-SUM (subst-free 'z v (tgc-term 'f 'x)) '(succ n)))
;; CH(f,t,n) out of TAYLOR-DIFFERENTIABLE's first conjunct, on a side branch.
(have! (tgc-ch 'f 't 'n)
  (lambda ()
    (dk-split! (dk-landed-1 (lambda () (mac-h 'TAYLOR-DIFFERENTIABLE '(TAYLOR-DIFFERENTIABLE f a x n)))))
    (di)
    (let* ((landed (dk-landed-1 (lambda () (di))))                    ; (AND (IN k NN) (<= k n)), kept whole
           (kv     (cadr (cadr landed)))
           (c1     (tgc-find (lambda (u) (and (pair? u) (eq? (car u) 'FORALL)
                                              (tgc-mentions? 'IS-CONTINUOUS-AT u)))
                             'the-continuity-conjunct)))
      (let ((at-k (dk-deepest (lambda () (inst+ c1 kv)))))
        (inst+ at-k 't)                                               ; (IN t (CCINT a x)) is in context
        (ass)))))
;; t in RR and f in FUN RR RR, both off CH at k = 0
(fact 'nn-zero-in)
(fact 'nn-zero-le 'n)
(have! '(AND (IN 0 NN) (<= 0 n)))
(define tgc-g-h0 (dk-deepest (lambda () (inst+ (tgc-ch 'f 't 'n) 0))))
(tgc-check-head! tgc-g-h0 'IS-CONTINUOUS-AT "CH at 0")
(tgc-point! tgc-g-h0)                                                 ; (IN t RR)
(define tgc-g-h0f (dk-landed-1 (lambda () (mac-h 'nth-deriv-zero tgc-g-h0))))
(tgc-fun! tgc-g-h0f)                                                  ; f in FUN RR RR
(fact 'fun-apply-type-c 'f 'RR 'RR 'x)                                ; f(x) in RR
;; S_n continuous at t
(define tgc-g-hs (dk-fact! 'tgc-sum-cont 'n 'f 'x 't))
(tgc-check-head! tgc-g-hs 'IS-CONTINUOUS-AT "tgc-sum-cont did not detach")
(tgc-fun! tgc-g-hs)                                                   ; S_n in FUN RR RR
;; the constant f(x), and the difference
(define tgc-g-kc (dk-fact! 'const-continuous-at '(f x) 't))
(tgc-check-head! tgc-g-kc 'IS-CONTINUOUS-AT "const-continuous-at")
(define tgc-g-sub (dk-fact! 'sub-continuous-at (cadddr tgc-g-kc) tgc-g-s 't))
(tgc-check-head! tgc-g-sub 'IS-CONTINUOUS-AT "sub-continuous-at did not detach")
(define tgc-g-sub2 (dk-landed-1 (lambda () (lam-b-h tgc-g-sub))))     ; z |-> f(x) - SPS(term_z, succ n)
(define tgc-g-sub-lam (cadddr tgc-g-sub2))
;; G is a function RR -> RR ...
(have! (list 'IN tgc-gt '(FUN RR RR))
  (lambda ()
    (dk-lam-t!)
    (let ((v (dk-di-var!)))
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgc-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgc-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (tgc-g-sps v))
      (ass))))
;; ... and agrees pointwise with the difference lambda
(have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ RR)
              (list '= (list tgc-gt 'x_) (list tgc-g-sub-lam 'x_))))
  (lambda ()
    (let ((v (dk-di-var!)))
      (tgc-beta!)
      (mac 'TAYLOR-POLY)
      (fact 'fun-apply-type-c tgc-g-s 'RR 'RR v)
      (lam-b-h (list 'IN (list tgc-g-s v) 'RR))
      (fact 'rr-sub-in-rr '(f x) (tgc-g-sps v))
      (if (not (alpha-equiv? (cadr (dk-goal)) (caddr (dk-goal))))
          (error "taylor-gmvt-guarded: G and the difference lambda did not meet" (dk-goal)))
      (rfl))))
(fact 'cont-transfer-ptwise-eq tgc-gt tgc-g-sub-lam 't)
(ass)
(qed 'taylor-G-cont)
(topic! 'taylor-G-cont 'analysis)

;;; =====================================================================
;;; (5) taylor-gmvt-cont, guarded by n in NN: (1) and (4) at t in [a,x].
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
     (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
     (list 'IMPLIES '(IN x RR) (list 'IMPLIES '(IN n NN) tgc-ghcont)))))))))
(dk-peel-to! 'AND)
(define tgc-c-mem '(AND (IN t RR) (AND (<= a t) (<= t x))))
(fact 'ccint-membership 'a 'x 't)
(ai (list 'IFF '(IN t (CCINT a x)) tgc-c-mem))
(detach! (list 'IMPLIES '(IN t (CCINT a x)) tgc-c-mem))
(dk-split! tgc-c-mem)                                                 ; (IN t RR) ...
(fact 'taylor-G-cont 'f 'a 'x 'n 't)
(fact 'taylor-H-cont 'x 'n 't)
(dk-conj-close!)
(qed 'taylor-gmvt-cont)
(topic! 'taylor-gmvt-cont 'analysis)

;;; =====================================================================
;;; (6) taylor-gmvt-diff, guarded by n in NN, x in RR: the explicit
;;; derivatives taylor-G-diff / taylor-h-diff give, existentially closed.
;;; =====================================================================
(sp (make-wff
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'x (list 'FORALL 'n
     (list 'IMPLIES '(TAYLOR-DIFFERENTIABLE f a x n)
     (list 'IMPLIES '(IN n NN) (list 'IMPLIES '(IN x RR) tgc-ghdiff)))))))))
(dk-peel-to! 'AND)
(define tgc-d-t (caddr (caddr (cadr (dk-goal)))))                     ; the point, off the goal
(if (not (eq? tgc-d-t 't)) (error "taylor-gmvt-guarded: the point is not t" tgc-d-t))
(dk-split! '(AND (IN t RR) (AND (< a t) (< t x))))
(have! '(AND (< a t) (< t x)))                                        ; taylor-G-diff's antecedent, whole
(fact 'taylor-G-diff 'f 'a 'x 'n 't)                                  ; IS-DIFF-AT GT t (GVAL t)
(fact 'taylor-h-diff 'x 'n 't)                                        ; IS-DIFF-AT HT t (HVAL t)
(have! (list 'FORSOME 'L (list 'IS-DIFF-AT tgc-gt 't 'L))
       (lambda () (ew (tgc-gval 't)) (ass)))
(have! (list 'FORSOME 'M (list 'IS-DIFF-AT tgc-ht 't 'M))
       (lambda () (ew (tgc-hval 't)) (ass)))
(dk-conj-close!)
(qed 'taylor-gmvt-diff)
(topic! 'taylor-gmvt-diff 'analysis)

;;; ===== END second spliced block =====

;;; =====================================================================
;;; BEGIN third spliced block (2026-09-15): rr-power-pos, rr-cancel-mul-left,
;;; rr-recip-factorial, taylor-clear -- the last leaves of taylor-lagrange, PROVEN
;;; (was theorem-library/taylor-clear-guarded.scm; same window reason).
;;; =====================================================================
;;; theorem-library/taylor-clear-guarded.scm -- the two RR-algebra leaves of
;;; Taylor's theorem, and the two micro-lemmas beside them, PROVEN:
;;;
;;;   rr-power-pos         0 < d  =>  0 < d^n            (d in RR, n in NN)
;;;   rr-cancel-mul-left   c*u = c*v, c /= 0  =>  u = v  (c, u, v in RR)
;;;   rr-recip-factorial   n! * recip(n!) = 1            (n in NN)
;;;   taylor-clear         the clearing identity of taylor-lagrange's endgame:
;;;                        from  (0 - (recip(n!)*fn1)*pw)*(hx-ha)
;;;                                = (0 - succ(n)*pw)*(gx-ga)
;;;                        with gx = hx = 0, ha = d, ga = r, 0 < pw,
;;;                        conclude  succ(n)! * r = fn1 * d.
;;;
;;; All four stood in taylor-proof.scm as `add-to-pss' + `warrant! 'well-known'
;;; (rr-power-pos at ~399, the other three at ~407-463).  Tonight (2026-09-15)
;;; `taylor-lagrange' bills EXACTLY these two leaves, rr-power-pos and
;;; taylor-clear; the neighbours are what taylor-clear's own warrant chains
;;; through ("cancel pw /= 0", "multiply by n!"), so they are proven here too
;;; and taylor-clear cites them.  STATEMENTS ARE BYTE-IDENTICAL to the supports'
;;; (copied from the definition sites; nothing is unguarded -- gx, ga, hx, ha
;;; are untyped in taylor-clear but each is EQUATED to a real or to 0 by an
;;; antecedent, which is all the proof needs).
;;;
;;; SPLICE POINT.  This block goes into theorem-library/taylor-proof.scm right
;;; after the marker  `;;; ===== END second spliced block ====='  (line ~2089),
;;; i.e. immediately BEFORE the `taylor-lagrange (cleared form)' section that
;;; cites rr-power-pos and taylor-clear.  It cannot be a separate load.scm
;;; entry: the window is INSIDE taylor-proof.scm (the lemma block above --
;;; factorial-real-pos, recip-factorial-in-rr -- is cited, and taylor-lagrange
;;; below is the citer), and load.scm gives each theorem-library file its own
;;; environment.  Window, as a file: [taylor-proof's own position, itself).
;;;
;;; CITATIONS (all loaded before taylor-proof, load.scm line in parentheses,
;;; or in taylor-proof.scm's own lemma block above the splice point):
;;;   primitive (number-systems.scm / injection.scm def-constant):
;;;     rr-subset-cc, power-zero, power-succ, rr-mul-closed, rr-recip-closed,
;;;     rr-recip-inverse, nn-succ-closed, factorial-succ, rr-zero-in
;;;   equality-basics (589):   eq-sym, eq-trans
;;;   nn-order-basics (675):   nn-in-rr
;;;   rr-order-basics (688):   rr-pos-ne-zero
;;;   rr-recip-order (735):    rr-zero-lt-one, rr-mul-pos
;;;   inverse-function (1510): rr-recip-solve
;;;   dyadic-weights (1962):   power-real-closed
;;;   taylor-proof.scm above:  factorial-real-pos, recip-factorial-in-rr
;;;
;;; MECHANICS.
;;;   rr-power-pos binds d OUTERMOST, so `ni' cannot fire on the statement (it
;;;   wants the NN binder on top).  `dk-peel!' takes the whole prefix, then the
;;;   n-outermost form is `cut' and proved by `use-induction' (the induction
;;;   lane's recipe, CLAUDE.md), and the main branch closes by instantiating
;;;   the cut at n.  The cut binds `n_', not `n': `n' is already an
;;;   eigenvariable of the context.  Base: power-zero (guarded on CC, hence
;;;   rr-subset-cc first) + rr-zero-lt-one.  Step: power-succ, then the
;;;   product of positives (rr-mul-pos) with power-real-closed for the typing.
;;;   This is dyadic-weights' `power-two-pos' with d for 2.
;;;
;;;   taylor-clear is goal-directed and never rewrites a hypothesis.  The four
;;;   equations are pushed into the gMVT equation by REVERSE substitution
;;;   inside `have!' lanes (the lane's goal carries d, r, 0; the context's
;;;   equation carries ha, ga, hx, gx; the lane substitutes hx:=0 etc. INTO ITS
;;;   OWN GOAL and closes by `crs' or `ass').  Then both sides are normalised
;;;   by `crs' (generators: recip(n!), fn1, pw, d, r, succ(n) -- each typed in
;;;   RR beforehand, since crs certifies its generators), chained by eq-trans,
;;;   pw is cancelled by rr-cancel-mul-left, and n! is cleared by
;;;   factorial-succ + rr-recip-factorial.
;;;
;;; Helper prefix: `tcl-' (never a tactic name; case folding).

;;; ---- rr-power-pos: a positive real to a natural power is positive ----------
(sp (make-wff '(FORALL d (IMPLIES (IN d RR) (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 d) (< 0 (power d n)))))))))
(dk-peel!)                                   ; d in RR, n in NN, 0 < d
(fact 'rr-subset-cc 'd)                      ; d in CC (power-zero/succ are on CC)
(define tcl-pp-cut '(FORALL n_ (IMPLIES (IN n_ NN) (< 0 (power d n_)))))
(define tcl-pp-leaves (dk-opened (lambda () (cut tcl-pp-cut))))
(define tcl-pp-side
  (let ((l (filter (lambda (s) (alpha-equiv? (dk-goal-of s) tcl-pp-cut)) tcl-pp-leaves)))
    (if (= (length l) 1) (car l) (error "tcl: cut side goal not found" (length l)))))
(define tcl-pp-main
  (let ((l (filter (lambda (s) (not (eq? s tcl-pp-side))) tcl-pp-leaves)))
    (if (= (length l) 1) (car l) (error "tcl: cut main branch not found" (length l)))))
(dk-focus! tcl-pp-side)
(define tcl-pp-br (use-induction))
(dk-focus! (cdr (assq 'base tcl-pp-br)))
(mac 'power-zero)                            ; 0 < 1
(fact 'rr-zero-lt-one)
(ass)
(dk-focus! (cdr (assq 'step tcl-pp-br)))
(define tcl-pp-k (cdr (assq 'var tcl-pp-br)))
(have! (list 'AND '(IN d CC) (list 'IN tcl-pp-k 'NN)))
(fact 'power-succ 'd tcl-pp-k)               ; d^(succ k) = d * d^k
(subst (list '= (list 'power 'd (list 'succ tcl-pp-k))
                (list '* 'd (list 'power 'd tcl-pp-k))))
(fact 'power-real-closed 'd tcl-pp-k)        ; d^k in RR
(fact 'rr-mul-pos 'd (list 'power 'd tcl-pp-k))   ; 0 < d * d^k
(ass)
(dk-focus! tcl-pp-main)
(inst+ tcl-pp-cut 'n)                        ; 0 < d^n
(ass)
(qed 'rr-power-pos)
(topic! 'rr-power-pos 'analysis)

;;; ---- rr-cancel-mul-left: c*u = c*v, c /= 0  =>  u = v ----------------------
;;; Through rr-recip-solve (u' = c*v' => v' = recip(c)*u') at u' := c*u,
;;; v' := v, then recip(c)*(c*u) = (c*recip(c))*u = 1*u = u.  The right-factor
;;; twin (rr-cancel-mul-right, rr-order-basics.scm) goes through
;;; rr-no-zero-divisors instead; either works, this one is four rewrites.
(sp (make-wff '(FORALL c (IMPLIES (IN c RR) (FORALL u (IMPLIES (IN u RR) (FORALL v (IMPLIES (IN v RR)
     (IMPLIES (NOT (= c 0)) (IMPLIES (= (* c u) (* c v)) (= u v)))))))))))
(dk-peel!)                                   ; c,u,v in RR; c /= 0; c*u = c*v
(have! '(AND (IN c RR) (IN u RR)))
(fact 'rr-mul-closed 'c 'u)                  ; c*u in RR
(have! '(AND (IN c RR) (NOT (= c 0))))
(fact 'rr-recip-closed 'c)                   ; recip c in RR
(fact 'rr-recip-inverse 'c)                  ; c * recip c = 1
(fact 'rr-recip-solve 'c '(* c u) 'v)        ; v = recip(c) * (c*u)
(subst '(= v (* (recip c) (* c u))))         ; goal: u = recip(c) * (c*u)
(have! '(= (* (recip c) (* c u)) (* (* c (recip c)) u)) (lambda () (crs)))
(subst '(= (* (recip c) (* c u)) (* (* c (recip c)) u)))
(subst '(= (* c (recip c)) 1))               ; goal: u = 1 * u
(crs)
(qed 'rr-cancel-mul-left)
(topic! 'rr-cancel-mul-left 'analysis)

;;; ---- rr-recip-factorial: n! * recip(n!) = 1 --------------------------------
;;; recip-factorial-in-rr's proof with rr-recip-inverse in place of
;;; rr-recip-closed at the last line.
(sp (make-wff '(FORALL n (IMPLIES (IN n NN) (= (* (FACTORIAL n) (recip (FACTORIAL n))) 1)))))
(dk-peel!)
(fact 'factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'rr-pos-ne-zero '(FACTORIAL n))
(have! '(AND (IN (FACTORIAL n) RR) (NOT (= (FACTORIAL n) 0))))
(fact 'rr-recip-inverse '(FACTORIAL n))
(ass)
(qed 'rr-recip-factorial)
(topic! 'rr-recip-factorial 'analysis)

;;; ---- taylor-clear: the clearing identity ------------------------------------
(sp (make-wff
  '(FORALL fn1 (IMPLIES (IN fn1 RR)
   (FORALL pw (IMPLIES (IN pw RR)
   (FORALL d (IMPLIES (IN d RR)
   (FORALL r (IMPLIES (IN r RR)
   (FORALL gx (FORALL ga (FORALL hx (FORALL ha
   (FORALL n (IMPLIES (IN n NN)
     (IMPLIES (< 0 pw)
     (IMPLIES (= gx 0)
     (IMPLIES (= hx 0)
     (IMPLIES (= ha d)
     (IMPLIES (= ga r)
     (IMPLIES (= (* (- 0 (* (* (recip (FACTORIAL n)) fn1) pw)) (- hx ha))
                 (* (- 0 (* (succ n) pw)) (- gx ga)))
       (= (* (FACTORIAL (succ n)) r) (* fn1 d))))))))))))))))))))))))
(dk-peel!)   ; fn1 pw d r in RR; n in NN; 0<pw; gx=0; hx=0; ha=d; ga=r; the equation
;; typings of every generator crs will see, and the two clearing facts
(fact 'recip-factorial-in-rr 'n)             ; recip(n!) in RR
(fact 'factorial-real-pos 'n)
(dk-split! '(AND (IN (FACTORIAL n) RR) (< 0 (FACTORIAL n))))
(fact 'nn-succ-closed 'n)
(fact 'nn-in-rr '(succ n))                   ; succ n in RR
(fact 'rr-pos-ne-zero 'pw)                   ; pw /= 0
(fact 'rr-recip-factorial 'n)                ; n! * recip(n!) = 1
(fact 'factorial-succ 'n)                    ; succ(n)! = succ(n) * n!
(define tcl-rf '(recip (FACTORIAL n)))
(define tcl-A  (list '- 0 (list '* (list '* tcl-rf 'fn1) 'pw)))   ; the G' factor
(define tcl-B  '(- 0 (* (succ n) pw)))                            ; the H' factor
;; the gMVT equation with the four endpoint equations substituted in:
;;   A * (0 - d) = B * (0 - r)
(have! '(= (- 0 d) (- hx ha)) (lambda () (subst '(= hx 0)) (subst '(= ha d)) (crs)))
(have! '(= (- 0 r) (- gx ga)) (lambda () (subst '(= gx 0)) (subst '(= ga r)) (crs)))
(define tcl-E1 (list '= (list '* tcl-A '(- 0 d)) (list '* tcl-B '(- 0 r))))
(have! tcl-E1 (lambda () (subst '(= (- 0 d) (- hx ha)))
                         (subst '(= (- 0 r) (- gx ga)))
                         (ass)))
;; normalise both sides:  pw * ((rf*fn1)*d)  =  pw * (succ(n)*r)
(define tcl-U  (list '* (list '* tcl-rf 'fn1) 'd))
(define tcl-V  '(* (succ n) r))
(define tcl-LN (list '* 'pw tcl-U))
(define tcl-RN (list '* 'pw tcl-V))
(have! (list '= tcl-LN (cadr tcl-E1)) (lambda () (crs)))
(have! (list '= (caddr tcl-E1) tcl-RN) (lambda () (crs)))
(fact 'eq-trans tcl-LN (cadr tcl-E1) (caddr tcl-E1))   ; LN = B*(0-r)
(fact 'eq-trans tcl-LN (caddr tcl-E1) tcl-RN)          ; LN = RN
;; cancel pw:  (rf*fn1)*d = succ(n)*r
(have! (list 'AND (list 'IN tcl-rf 'RR) '(IN fn1 RR)))
(fact 'rr-mul-closed tcl-rf 'fn1)
(have! (list 'AND (list 'IN (list '* tcl-rf 'fn1) 'RR) '(IN d RR)))
(fact 'rr-mul-closed (list '* tcl-rf 'fn1) 'd)          ; U in RR
(have! '(AND (IN (succ n) RR) (IN r RR)))
(fact 'rr-mul-closed '(succ n) 'r)                      ; V in RR
(fact 'rr-cancel-mul-left 'pw tcl-U tcl-V)              ; U = V
(fact 'eq-sym tcl-U tcl-V)                              ; V = U
;; clear n!:  goal  succ(n)! * r = fn1 * d
(subst '(= (FACTORIAL (succ n)) (* (succ n) (FACTORIAL n))))   ; (succ n * n!) * r = fn1*d
(have! (list '= '(* (* (succ n) (FACTORIAL n)) r) (list '* '(FACTORIAL n) tcl-V))
       (lambda () (crs)))
(subst (list '= '(* (* (succ n) (FACTORIAL n)) r) (list '* '(FACTORIAL n) tcl-V)))
(subst (list '= tcl-V tcl-U))                           ; n! * ((rf*fn1)*d) = fn1*d
(have! (list '= (list '* '(FACTORIAL n) tcl-U)
                (list '* (list '* '(FACTORIAL n) tcl-rf) '(* fn1 d)))
       (lambda () (crs)))
(subst (list '= (list '* '(FACTORIAL n) tcl-U)
                (list '* (list '* '(FACTORIAL n) tcl-rf) '(* fn1 d))))
(subst (list '= (list '* '(FACTORIAL n) tcl-rf) 1))    ; 1 * (fn1*d) = fn1*d
(crs)
(qed 'taylor-clear)
(topic! 'taylor-clear 'analysis)

;;; ===== END third spliced block =====

;;; ====================================================================
;;; taylor-lagrange (cleared form)
;;; ====================================================================
(sp `(FORALL f (FORALL a (FORALL x (FORALL n
     (IMPLIES (AND (IN f (FUN RR RR)) (AND (IN a RR) (AND (IN x RR) (AND (IN n NN) (< a x)))))
     (IMPLIES (TAYLOR-DIFFERENTIABLE f a x n)
       (FORSOME theta (AND (IN theta RR) (AND (< a theta) (AND (< theta x)
         (= (* (FACTORIAL (succ n)) (- (f x) (TAYLOR-POLY f a n x)))
            (* ((NTH-DERIV f (succ n)) theta) (power (- x a) (succ n)))))))))))))))
(quietly (lambda () (di)(di)(di)(di)))     ; f,a,x,n
(dc-split)                                  ; typing AND
(quietly (lambda () (di)))                 ; TAYLOR-DIFFERENTIABLE hyp
(define GOAL (dc-gf))

;;; ---- DFUN(f,n): derivatives up to n are total real functions -- the ONE guard
;;; the guarded G-facts need; from TAYLOR-DIFFERENTIABLE via taylor-derivs-in-fun ----
(quietly (lambda () (fact 'taylor-derivs-in-fun 'f 'a 'x 'n)))
;;; ---- gMVT typing: GT, HT in FUN RR RR (forward facts, land in ctx) ----
(quietly (lambda () (fact 'taylor-G-in-fun 'n 'f 'x)))   ; n now BOUND in the support
(quietly (lambda () (fact 'taylor-H-in-fun 'n 'x)))

;;; ---- gMVT continuity + differentiability hyps (warranted, land in ctx) ----
(quietly (lambda () (fact 'taylor-gmvt-cont 'f 'a 'x 'n)))   ; -> GHCONT
(quietly (lambda () (fact 'taylor-gmvt-diff 'f 'a 'x 'n)))   ; -> GHDIFF

;;; ---- apply generalized-mvt to (GT, HT) on [a,x] ----
(define GMTYP (list 'AND (list 'IN GT '(FUN RR RR))
                (list 'AND (list 'IN HT '(FUN RR RR)) '(AND (IN a RR) (AND (IN x RR) (< a x))))))
(cut GMTYP) (dc-grind!) (dc-focus! GOAL)
(quietly (lambda () (fact 'generalized-mvt GT HT 'a 'x)))
(let loop ((k 0))                            ; detach GMTYP, GHCONT, GHDIFF (alpha-equiv)
  (let ((ri (dc-find (lambda (z) (and ((dc-head? 'IMPLIES) z) (dc-ment? 'VNB-LAMBDA z))))))
    (when (and ri (< k 4)) (detach! ri) (loop (+ k 1)))))
;; existential elimination: theta, then L (for GT) and M (for HT)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'VNB-LAMBDA z) (dc-ment? 'is-diff-at z)))))
(dc-split)
(define THETA (caddr (dc-find (lambda (z) (and ((dc-head? '<) z) (eq? (cadr z) 'a) (symbol? (caddr z))
                 (dc-find (lambda (y) (and ((dc-head? '<) y) (equal? (cadr y) (caddr z)) (eq? (caddr y) 'x)))))))))
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'taylor-poly z)))))   ; FORSOME L (for GT)
(ai (dc-find (lambda (z) (and ((dc-head? 'FORSOME) z) (dc-ment? 'is-diff-at z)))))    ; FORSOME M (for HT)
(dc-split)
(define LW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (equal? (caddr z) THETA) (dc-ment? 'taylor-poly z))))))
(define MW (cadddr (dc-find (lambda (z) (and ((dc-head? 'IS-DIFF-AT) z) (equal? (caddr z) THETA) (dc-ment? 'power z) (not (dc-ment? 'taylor-poly z)))))))

;;; ---- endgame: pin L,M; endpoint values; elementary clearing ----
;; (IN theta RR) came out of the generalized-mvt existential with the rest of its body.
(dc-have! (list 'IN (list '- 'x THETA) 'RR) GOAL)                 ; IN (x-theta) RR
(dc-have! '(IN (- x a) RR) GOAL)                                  ; IN (x-a) RR
(cut (list 'AND (list '< 'a THETA) (list '< THETA 'x))) (dc-grind!) (dc-focus! GOAL)
;;; LUTINS instantiation (2026-09-18): the two `derivative-unique' citations
;;; below are AT GVAL(theta) and HVAL(theta) -- a recip(FACTORIAL), an applied
;;; NTH-DERIV and a power, none of them certified syntactically.  Type them
;;; here; the taylor-deriv-real / power-in-rr / nn-succ-closed citations that
;;; used to sit in the "typings for taylor-clear" block below are moved up to
;;; do it, and are not repeated there.
(quietly (lambda () (fact 'rr-zero-in)))
(quietly (lambda () (fact 'nn-succ-closed 'n)))
(quietly (lambda () (fact 'nn-in-rr '(succ n))))
(quietly (lambda () (fact 'recip-factorial-in-rr 'n)))
(quietly (lambda () (fact 'taylor-deriv-real 'f 'a 'x 'n THETA)))  ; IN fn1 RR
(quietly (lambda () (fact 'power-in-rr (list '- 'x THETA) 'n)))    ; IN pw RR
(dc-have! (list 'IN (GVAL THETA) 'RR) GOAL)
(dc-have! (list 'IN (HVAL THETA) 'RR) GOAL)
(quietly (lambda () (fact 'taylor-G-diff 'f 'a 'x 'n THETA)))   ; IS-DIFF-AT GT theta (GVAL theta)
(quietly (lambda () (fact 'taylor-H-diff 'x 'n THETA)))         ; IS-DIFF-AT HT theta (HVAL theta)
(let ((dd (list 'AND (list 'IS-DIFF-AT GT THETA (GVAL THETA)) (list 'IS-DIFF-AT GT THETA LW))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique GT THETA (GVAL THETA) LW))))   ; (= (GVAL theta) LW)
(let ((dd (list 'AND (list 'IS-DIFF-AT HT THETA (HVAL THETA)) (list 'IS-DIFF-AT HT THETA MW))))
  (cut dd) (di) (quietly (lambda () (ass-all))) (dc-focus! GOAL)
  (quietly (lambda () (fact 'derivative-unique HT THETA (HVAL THETA) MW))))   ; (= (HVAL theta) MW)

;;; TCIN: the gMVT equation with L,M pinned to their explicit values
(define TCIN (list '= (list '* (GVAL THETA) (list '- (list HT 'x) (list HT 'a)))
                      (list '* (HVAL THETA) (list '- (list GT 'x) (list GT 'a)))))
(cut TCIN)
(subst (list '= (GVAL THETA) LW))
(subst (list '= (HVAL THETA) MW))
(quietly (lambda () (ass-all)))            ; closes from the gMVT equation
(dc-focus! GOAL)

;;; endpoint values (warranted)
(define RREM '(- (f x) (TAYLOR-POLY f a n x)))
(define DPOW '(power (- x a) (succ n)))
(define FN1 (list (list 'NTH-DERIV 'f '(succ n)) THETA))
(define PW (list 'power (list '- 'x THETA) 'n))
(quietly (lambda () (fact 'taylor-G-at-x 'f 'x 'n)))   ; (= (GT x) 0)
(quietly (lambda () (fact 'taylor-G-at-a 'f 'a 'x 'n))) ; (= (GT a) RREM)
(quietly (lambda () (fact 'taylor-H-at-x 'x 'n)))       ; (= (HT x) 0)
(quietly (lambda () (fact 'taylor-H-at-a 'a 'x 'n)))    ; (= (HT a) DPOW)

;;; pw /= 0 and typings for taylor-clear
(quietly (lambda () (fact 'rr-lt-diff-pos THETA 'x)))           ; 0 < x-theta
(quietly (lambda () (fact 'rr-power-pos (list '- 'x THETA) 'n)))  ; 0 < (x-theta)^n
(quietly (lambda () (fact 'rr-pos-ne-zero PW)))                 ; (x-theta)^n /= 0
(quietly (lambda () (fact 'power-in-rr '(- x a) '(succ n))))    ; IN DPOW RR
(quietly (lambda () (fact 'taylor-poly-in-rr 'f 'a 'n 'x)))     ; IN taylor-poly RR
(dc-have! (list 'IN RREM 'RR) GOAL)                            ; IN R RR

;;; clear: taylor-clear -> (n+1)! R = fn1 D
(quietly (lambda () (fact 'taylor-clear FN1 PW DPOW RREM (list GT 'x) (list GT 'a) (list HT 'x) (list HT 'a) 'n)))

;;; finish: ew theta, close the three conjuncts
(ew THETA)
(quietly (lambda () (dc-grind!) (ass-all)))
(qed 'taylor-lagrange)

;;; Classic textbook name, for (find-theorem "...") lookup.
(alias! 'taylor-lagrange "Taylor's theorem" "Taylor's theorem with Lagrange remainder")
(topic! 'taylor-lagrange 'analysis)

;;; -----------------------------------------------------------------------
;;; Notation -- the ENGLISH of these predicates, declared beside their
;;; definitions and read by wff->english / the proof reader (operators.scm).
;;; A def-predicate's reading cannot be derived the way a structure's noun can
;;; (noun vs adjective: IS-COMPLETE wants "s is complete", not "s is a complete"),
;;; so it is written here, once, next to what it means.
(notation! 'TAYLOR-DIFFERENTIABLE 'kind 'predicate 'arity 4
           'english "$1 is $4 times differentiable from $2 to $3")
