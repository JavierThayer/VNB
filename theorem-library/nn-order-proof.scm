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
;;; the form (FORALL n (IMPLIES (IN n NN) P)).
;;;
;;; a_ <= a_ + b_ was proven here as `nn-le-add'; REMOVED 2026-09-20 (batch 11,
;;; proven-duplicate-audit): it was alpha-equal to `nn-le-add-right'
;;; (theorem-library/nn-order-basics.scm:175), which loads well before this
;;; file -- and before this file is reachable, since nn-order-basics uses its
;;; own copy internally.  Same binder order: (fact 'nn-le-add-right X Y)
;;; instantiates the ADDEND first, landing Y <= Y + X.  The five citations
;;; (here, card-inequalities, cauchy-criterion-left/-right, nn-pairing) name
;;; that one.

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
            ;; nn-le-trans-guarded needs EVERY term of the chain typed, and this
            ;; site chained through two it never named: a_+b_ at the left end and
            ;; succ(a_+c_) at the right.  That is precisely what the unguarded
            ;; nn-le-trans let it get away with.
            (have! '(AND (IN a_ NN) (IN b_ NN)))
            (fact 'nn-add-closed 'a_ 'b_)
            (fact 'nn-succ-closed '(+ a_ c_))
            (fact 'nn-le-trans-guarded '(+ a_ b_) '(+ a_ c_) '(succ (+ a_ c_)))
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
;;; The mirror of nn-le-add-right, which only ever puts the bounded term FIRST
;;; (a <= a + b).  nnpair-inj needs j <= i + j, where the sum is written with
;;; the addend on the left, so commute once and cite nn-le-add-right.
(sp (make-wff (forall-guarded '(a_ b_) (list '(IN a_ NN) '(IN b_ NN))
                '(<= b_ (+ a_ b_)))))
;; `di' takes the FORALL block plus ONE guard when the statement is built flat,
;; so peel to the head rather than counting.
(dk-peel-to! '<=)
(have! '(AND (IN a_ NN) (IN b_ NN)))
(fact 'nn-add-comm 'a_ 'b_)
(subst '(= (+ a_ b_) (+ b_ a_)))
(fact 'nn-le-add-right 'a_ 'b_)
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

(topic! 'nn-le-zero-is-zero 'inequalities)
(topic! 'nn-add-le-mono     'inequalities)
(topic! 'nn-le-antisym      'inequalities)
(topic! 'nn-le-add-left     'inequalities)

;;; =====================================================================
;;; nn-succ-not-le -- succ n is never <= n
;;; =====================================================================
;;;
;;; The discreteness brick every "n is not minimal, take one less" argument
;;; below ends on, and the tree did not have it: order-lemmas has nn-le-succ
;;; (n <= succ n) and nn-le-imp-neq-succ (j <= k => j /= succ k) but nothing
;;; that puts them together.  Four citations, and it turns each of the three
;;; sites that need it from five lines into one.  Stated in poly-degree-laws.scm
;;; until 2026-10-06, MOVED here by the library gate (cited from the strand book).

(sp (make-wff '(FORALL n_ (IMPLIES (IN n_ NN) (NOT (<= (succ n_) n_))))))
(dk-peel!)
(di)                                    ; assume succ n_ <= n_; goal FALSITY
(fact 'nn-succ-closed 'n_)
(fact 'nn-le-succ 'n_)
(fact 'nn-le-antisym 'n_ '(succ n_))    ; n_ = succ n_
(fact 'nn-le-refl 'n_)
(fact 'nn-le-imp-neq-succ 'n_ 'n_)      ; n_ /= succ n_
(ai '(NOT (= n_ (succ n_))))
(qed 'nn-succ-not-le)
(gloss! 'nn-succ-not-le
  "succ n is never <= n, for n in NN.  Antisymmetry against nn-le-succ gives
   n = succ n, which nn-le-imp-neq-succ forbids.")
(topic! 'nn-succ-not-le 'inequalities)

;;; -----------------------------------------------------------------------
;;; nn-le-gap -- m <= k  =>  k = m + d for some d in NN.  The standard induction
;;; on k with nn-le-succ-cases at the step.  Stated in series-block-abs.scm until
;;; 2026-10-07 (where the block estimate of a series needed it), MOVED here by the
;;; library gate: an NN order lemma, cited from the core book.
;;; -----------------------------------------------------------------------

(define (ng-peel-to! head)
  (let loop ((n 0))
    (let ((g (dk-goal)))
      (cond ((and (pair? g) (eq? (car g) head)) g)
            ((> n 8) (error "ng-peel-to!: never reached" head))
            (else (di) (loop (+ n 1)))))))

(sp (make-wff '(FORALL k (IMPLIES (IN k NN)
   (FORALL m (IMPLIES (IN m NN) (IMPLIES (<= m k)
     (FORSOME d (AND (IN d NN) (= k (+ m d)))))))))))
(define ng-br (use-induction))

;;; BASE k = 0:  m <= 0 forces m = 0, and 0 = 0 + 0.
(dk-focus! (cdr (assq 'base ng-br)))
(ng-peel-to! 'FORSOME)
(fact 'nn-le-zero-is-zero 'm)
(fact 'nn-zero-in)
(ew 0)
(mac 'nn-add-zero)            ; m + 0 = m, so the claim is 0 = m
(for-each (lambda (l)
            (dk-focus! l)
            (if (eq? (car (dk-goal)) 'IN)
                (ass)
                (begin (fact 'eq-sym 'm 0) (ass))))
          (dk-opened (lambda () (di))))

;;; STEP
(dk-focus! (cdr (assq 'step ng-br)))
(define ng-k  (cdr (assq 'var ng-br)))
(define ng-ih (cdr (assq 'ih  ng-br)))
(ng-peel-to! 'FORSOME)
(fact 'nn-le-succ-cases ng-k 'm)          ; m <= k  or  m = succ k
(use-cases
 (list (list '<= 'm ng-k) (list '= 'm (list 'succ ng-k)))
 ;; CASE 1: the induction hypothesis supplies the gap, and one more succ does it.
 (lambda ()
   (let* ((ex (dk-deepest (lambda () (inst+ ng-ih 'm))))
          (dd (let* ((fv0 (apply append (map free-vars (dk-asms))))
                     (landed (dk-landed (lambda () (ai ex)))))
                (for-each (lambda (f) (if (and (pair? f) (eq? (car f) 'AND)) (dk-split! f)))
                          landed)
                (let ((fresh (filter (lambda (v) (not (memq v fv0)))
                                     (apply append (map free-vars (dk-asms))))))
                  (if (null? fresh) (error "gap: no witness appeared") (car fresh))))))
     (fact 'nn-succ-closed dd)
     (ew (list 'succ dd))
     (for-each (lambda (l)
                 (dk-focus! l)
                 (if (eq? (car (dk-goal)) 'IN)
                     (ass)
                     (begin
                       (have! (list 'AND '(IN m NN) (list 'IN dd 'NN)))
                       (mac 'nn-add-succ)
                       ;; goal is succ(k) = succ(m + d); the IH witness says
                       ;; k = m + d, so rewrite and reflect.
                       ;; `rfl' carries a DEFINEDNESS guard (pi-reflexivity!,
                       ;; primitive-inferences.scm:647): t = t needs t defined,
                       ;; syntactically or by a context (IN t _).  succ(m+d) is
                       ;; neither until this typing lands -- and the warning it
                       ;; gives without it says "goal is not (= a a)", which
                       ;; names the wrong reason entirely.
                       (fact 'nn-add-closed 'm dd)
                       (fact 'nn-succ-closed (list '+ 'm dd))
                       (subst (list '= ng-k (list '+ 'm dd)))
                       ;; `qrfl', not `rfl': succ(m + d) is not MANIFESTLY
                       ;; defined, and rfl demands that.
                       (rfl))))
               (dk-opened (lambda () (di))))))
 ;; CASE 2: m IS succ k, so the gap is 0.
 (lambda ()
   (fact 'nn-zero-in)
   (ew 0)
   (mac 'nn-add-zero)
   (for-each (lambda (l)
               (dk-focus! l)
               (if (eq? (car (dk-goal)) 'IN)
                   (ass)
                   (begin (fact 'eq-sym 'm (list 'succ ng-k)) (ass))))
             (dk-opened (lambda () (di))))))
(qed 'nn-le-gap)
