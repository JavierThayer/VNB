;;; nn-order-proof.scm -- three elementary facts about <= and + on NN, PROVEN.
;;;
;;; The library's NN order toolkit (structure-library/order-lemmas.scm) is rich
;;; in facts relating <= to succ -- nn-le-succ, nn-le-succ-cases, nn-succ-mono,
;;; nn-succ-le-cancel, nn-not-le-succ-le -- and has NOTHING relating <= to +.
;;; The gap only became visible when the Cantor pairing needed to compare
;;; TRINUM(s) + j with TRINUM(s') + j'.  All three below are one induction each.
;;;
;;; They live in their OWN file, not in the pairing file that first wanted them,
;;; for the reason recorded at order-lemmas.scm:445: nn-le-succ spent months
;;; buried in noetherian-maximal-proof.scm, invisible to everything that loads
;;; earlier, and had to be moved.  A general fact in a special-purpose file is
;;; a fact nobody else can find.
;;;
;;; Loads after nn-parity-proof (nn-zero-or-succ) and before nn-pairing.
;;; ====================================================================

;;; ---- a <= 0 => a = 0 ---------------------------------------------------
;;; 0 is not merely least (nn-zero-le); nothing else is <= it.  By
;;; nn-zero-or-succ: a is 0, or a = succ q, and then 1 <= a, so not(a <= 0).
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN) (IMPLIES (<= a_ 0) (= a_ 0))))))
(dk-peel-to! '=)
(fact 'nn-zero-or-succ 'a_)
(for-each
  (lambda (br)
    (dk-focus! br)
    (if (any-pred (lambda (a) (equal? a '(= a_ 0)))
                  (map wff-formula (sequent-node-assumptions br)))
        (ass)
        (begin
          (dk-ai-head! 'FORSOME)
          (dk-ai-head! 'AND)
          (let* ((eqq (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) '=)
                                                     (eq? (cadr a) 'a_)
                                                     (pair? (caddr a))
                                                     (eq? (car (caddr a)) 'succ)))
                                    (dk-asms))
                          (error "nn-le-zero-is-zero: no a_ = succ q")))
                 (q (cadr (caddr eqq))))
            ;; `have!' with a THUNK is how an equation gets used INSIDE a claim:
            ;; subst rewrites the GOAL only, so to turn "1 <= succ q" into
            ;; "1 <= a_" we claim the latter and rewrite it on its own side goal.
            (have! '(<= 1 a_)
                   (lambda ()
                     (subst `(= a_ (succ ,q)))
                     (fact 'nn-one-le-succ q)
                     (ass)))
            (fact 'nn-not-le-zero-pos 'a_)
            (dk-ai-not!)))))
  (dk-opened (lambda () (dk-ai-head! 'OR))))
(qed 'nn-le-zero-is-zero)

;;; ---- a <= a + b --------------------------------------------------------
;;; Induction on b, which is therefore the OUTER binder: ni wants the goal in
;;; the form (FORALL n (IMPLIES (IN n NN) P)).  NB the binder order this fixes
;;; -- (fact 'nn-le-add X Y) instantiates the ADDEND first, landing Y <= Y + X.
(sp (make-wff '(FORALL b_ (IMPLIES (IN b_ NN)
                 (FORALL a_ (IMPLIES (IN a_ NN) (<= a_ (+ a_ b_))))))))
(ni)
(dk-focus-goal! "+ 0")
(dk-peel-to! '<=)
(fact 'nn-add-zero 'a_)
(subst '(= (+ a_ 0) a_))
(fact 'nn-le-refl 'a_)
(ass)
(dk-focus-goal! "succ(b_)")
(di) (di)
(let ((ih (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL))) (dk-asms))
              (error "nn-le-add: no IH"))))
  (dk-peel-to! '<=)
  (fact 'nn-add-succ 'a_ 'b_)
  (subst '(= (+ a_ (succ b_)) (succ (+ a_ b_))))
  (inst+ ih 'a_)
  (have! '(AND (IN a_ NN) (IN b_ NN)))
  (fact 'nn-add-closed 'a_ 'b_)
  (fact 'nn-le-succ '(+ a_ b_))
  ;; nn-le-trans is GUARDED on NN (2026-08-02).  succ(a_+b_) is the term this
  ;; chain passes through and it was never typed; nn-add-closed above types
  ;; a_+b_, so one nn-succ-closed finishes the job.
  (fact 'nn-succ-closed '(+ a_ b_))
  (fact 'nn-le-trans 'a_ '(+ a_ b_) '(succ (+ a_ b_)))
  (ass))
(qed 'nn-le-add)

;;; ---- b <= c => a + b <= a + c ------------------------------------------
;;; Induction on c.  Base: b <= 0 forces b = 0 (above).  Step: b <= succ c
;;; splits (nn-le-succ-cases) into b <= c, where the IH plus a+c <= succ(a+c)
;;; = a + succ c does it, and b = succ c, where the two sides coincide.
(sp (make-wff '(FORALL c_ (IMPLIES (IN c_ NN)
                 (FORALL a_ (IMPLIES (IN a_ NN)
                   (FORALL b_ (IMPLIES (IN b_ NN)
                     (IMPLIES (<= b_ c_) (<= (+ a_ b_) (+ a_ c_)))))))))))
(ni)
(dk-focus-goal! "+ 0")
(dk-peel-to! '<=)
(fact 'nn-le-zero-is-zero 'b_)
(subst '(= b_ 0))
(have! '(AND (IN a_ NN) (IN 0 NN)))
(fact 'nn-add-closed 'a_ 0)
(fact 'nn-le-refl '(+ a_ 0))
(ass)
(dk-focus-goal! "succ(c_)")
(di) (di)
(let ((ih (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL))) (dk-asms))
              (error "nn-add-le-mono: no IH"))))
  (dk-peel-to! '<=)
  (fact 'nn-le-succ-cases 'c_ 'b_)
  (for-each
    (lambda (br)
      (dk-focus! br)
      (if (any-pred (lambda (a) (equal? a '(<= b_ c_)))
                    (map wff-formula (sequent-node-assumptions br)))
          (begin
            (inst+ ih 'a_)
            (inst+ (or (any-pred (lambda (a) (and (pair? a) (eq? (car a) 'FORALL)))
                                 (dk-asms))
                       (error "nn-add-le-mono: no instantiated IH"))
                   'b_)
            (fact 'nn-add-succ 'a_ 'c_)
            (subst '(= (+ a_ (succ c_)) (succ (+ a_ c_))))
            (have! '(AND (IN a_ NN) (IN c_ NN)))
            (fact 'nn-add-closed 'a_ 'c_)
            (fact 'nn-le-succ '(+ a_ c_))
            (fact 'nn-le-trans '(+ a_ b_) '(+ a_ c_) '(succ (+ a_ c_)))
            (ass))
          (begin
            (subst '(= b_ (succ c_)))
            (fact 'nn-succ-closed 'c_)
            (have! '(AND (IN a_ NN) (IN (succ c_) NN)))
            (fact 'nn-add-closed 'a_ '(succ c_))
            (fact 'nn-le-refl '(+ a_ (succ c_)))
            (ass))))
    (dk-opened (lambda () (dk-ai-head! 'OR)))))
(qed 'nn-add-le-mono)

;;; ---- nn-le-add-left : b <= a + b ---------------------------------------
;;; The mirror of nn-le-add, which only ever puts the bounded term FIRST
;;; (a <= a + b).  nnpair-inj needs j <= i + j, where the sum is written with
;;; the addend on the left, so commute once and cite nn-le-add.
(sp (make-wff (forall-guarded '(a_ b_) (list '(IN a_ NN) '(IN b_ NN))
                '(<= b_ (+ a_ b_)))))
;; `di' takes the FORALL block plus ONE guard when the statement is built flat,
;; so peel to the head rather than counting.
(dk-peel-to! '<=)
(have! '(AND (IN a_ NN) (IN b_ NN)))
(fact 'nn-add-comm 'a_ 'b_)
(subst '(= (+ a_ b_) (+ b_ a_)))
(fact 'nn-le-add 'a_ 'b_)
(ass)
(qed 'nn-le-add-left)

;;; ---- nn-le-antisym : a <= b and b <= a  =>  a = b ----------------------
;;; order-lemmas.scm had reflexivity and transitivity of <= on NN but not
;;; antisymmetry, which is what nnpair-inj (nn-pairing.scm) needs to turn "no
;;; strict inequality either way" into an equality of antidiagonals.  It is
;;; PROVED rather than asserted, and the proof is three citations: <= on NN is
;;; the RR order restricted (that is exactly how nn-le-refl is justified), so
;;; nn-in-rr lifts both arguments and rr-leq-antisymmetric (number-systems.scm,
;;; an axiom) closes it.
;;;
;;; Both of that axiom's antecedents are CONJUNCTIONS, which `fact' will not
;;; cross, so each wants a `have!' immediately before -- the same shape as
;;; np2-comm! / np2-sum-type! in nn-pairing.scm.  Three `di's, not one: the
;;; first takes the whole guarded-FORALL prefix, then one implication each.
(sp (make-wff '(FORALL a_ (IMPLIES (IN a_ NN)
                 (FORALL b_ (IMPLIES (IN b_ NN)
                   (IMPLIES (<= a_ b_) (IMPLIES (<= b_ a_) (= a_ b_)))))))))
(di) (di) (di)
(fact 'nn-in-rr 'a_)
(fact 'nn-in-rr 'b_)
(have! '(AND (IN a_ RR) (IN b_ RR)))
(have! '(AND (<= a_ b_) (<= b_ a_)))
(fact 'rr-leq-antisymmetric 'a_ 'b_)
(ass)
(qed 'nn-le-antisym)

(category! 'nn-le-zero-is-zero 'inequalities)
(category! 'nn-le-add          'inequalities)
(category! 'nn-add-le-mono     'inequalities)
(category! 'nn-le-antisym      'inequalities)
(category! 'nn-le-add-left     'inequalities)
