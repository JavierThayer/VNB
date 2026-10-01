;;; regulated-primitive-laws.scm -- the laws of IS-COUNTABLE,
;;; IS-RIGHT-LIMIT-WITHIN / IS-LEFT-LIMIT-WITHIN, IS-REGULATED-ON and
;;; IS-PRIMITIVE (structure-library/regulated-primitive.scm).  Batch 20-D,
;;; 2026-09-23.  THE SPECIFICATION is docs/roads-regulated-primitives-2026-09-23.md.
;;;
;;; THE FILE IN ORDER.
;;;   (1) COUNTABLE SETS.  The introduction rule `countable-of-enum' and the
;;;       non-destructive read-off `countable-cases'; the empty set, a
;;;       singleton PAIR(x,x), a subset (the enumeration is redirected to a
;;;       default point of the subset by an IF), a union of two (NN-pairing:
;;;       `nn-flatten' at i |-> IF(i = 0, f, g), so no parity arithmetic), a
;;;       FINITE set (`finite-set-induction' over the class of countable sets,
;;;       the step being union with a singleton -- the CARD bijection is not
;;;       needed), and the image under a function on a superset of the set.
;;;   (2) Three splits of |x| <= c, |x| < c into linear halves: `ineq' does
;;;       not read `abs'.
;;;   (3) Continuity on D gives both one-sided limits within D with value
;;;       f(x); hence a function continuous on [a,b] is regulated on [a,b].
;;;   (4) Uniqueness of a one-sided limit within W where x is approached by
;;;       points of W from that side, and the approach discharged for [a,b]
;;;       (x < b from the right, x > a from the left).
;;;   (5) Restriction: a limit within W is one within V subset W for any
;;;       function on V agreeing with f; a function regulated on [a,b] is
;;;       regulated on every [c,d] inside it.
;;;   (6) The read-offs of IS-PRIMITIVE, and `pw-antiderivative-implies-
;;;       primitive' (the only citation of path-integral.scm; everything else
;;;       loads right after structure-library/interval-calculus).
;;;
;;; Helper prefix: rpl-.  Theorem binders: rq..._ (none used by a predicate
;;; body); the predicates' own binders are rp..._.
;;;
;;; Dependencies: structure-library/regulated-primitive.scm,
;;; interval-calculus.scm (IS-CONTINUOUS-ON, OOINT), path-integral.scm (the
;;; bridge only); theorem-library: rake-card-star-laws (finite-set-induction),
;;; nn-pairing (nn-flatten), subset/union/image basics, ccint-basics
;;; (ccint-membership), monotone-inverse (ccint-subset-rr), metric-subspace-laws
;;; (subspace-pts, subspace-dist), rr-ms-dist, rr-halving, pos-rr-bridges,
;;; rr-le-all-pos (rr-le-all-pos-nonpos), rr-abs (rr-abs-cases), heine-borel-baby
;;; (union-right-subset).

(define (rpl-head g) (and (pair? g) (car g)))

;;; =====================================================================
;;; (1) COUNTABLE SETS.
;;; =====================================================================

;;; the introduction rule: a set covered by an NN-indexed family of its own
;;; points is countable.
(sp (make-wff "forall([rqd_, rqe_], rqd_ in set implies rqe_ in fun(nn, rqd_) implies
   forall([rqy_], rqy_ in rqd_ implies forsome([rqn_], rqn_ in nn and rqy_ = rqe_(rqn_)))
   implies is-countable(rqd_))"))
(dk-peel!)
(mac 'IS-COUNTABLE)
(dk-conj-close!
 (lambda ()
   (if (eq? (rpl-head (dk-goal)) 'OR)
       (begin (oi-r) (ew 'rqe_) (dk-conj-close! (lambda () (ass))))
       (ass))))
(qed 'countable-of-enum)

(sp (make-wff '(IS-COUNTABLE EMPTY-SET)))
(mac 'IS-COUNTABLE)
(fact 'empty-set-is-set)
(dk-conj-close!
 (lambda ()
   (if (eq? (rpl-head (dk-goal)) 'OR)
       (begin (oi-l) (rfl))
       (ass))))
(qed 'countable-empty)

;;; |x| < c, split into its two linear halves -- what `ineq' can read.
(sp (make-wff "forall([rqx_ in rr, rqc_ in rr], abs(rqx_) < rqc_ implies
   -rqc_ < rqx_ and rqx_ < rqc_)"))
(dk-peel!)
(fact 'rr-abs-cases 'rqx_)
(let ((cs (dk-pick (dk-head? 'OR) "the two cases of abs")))
  (use-cases cs
    (lambda ()
      (dk-split-all!)
      (dk-conj-close! (lambda ()
        (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(< (ABS rqx_) rqc_)
                  '(= (ABS rqx_) rqx_) '(<= 0 rqx_)))))
    (lambda ()
      (dk-split-all!)
      (fact 'rr-abs-nonneg 'rqx_)
      (dk-conj-close! (lambda ()
        (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(< (ABS rqx_) rqc_)
                  '(= (ABS rqx_) (- rqx_)) '(<= 0 (ABS rqx_))))))))
(qed 'rr-abs-lt-parts)

;;; the singleton {x} = PAIR(x, x) is countable: the constant enumeration.
(sp (make-wff "forall([rqx_], rqx_ in set implies is-countable(pair(rqx_, rqx_)))"))
(dk-peel!)
(have! '(AND (IN rqx_ SET) (IN rqx_ SET)))
(fact 'pairing 'rqx_ 'rqx_)
(define rpl-pm (dk-fact! 'pairing-membership 'rqx_ 'rqx_))
(define rpl-one '(VNB-LAMBDA rqk_ NN rqx_))
(dk-have! (list 'IN rpl-one '(FUN NN (PAIR rqx_ rqx_)))
  (lambda ()
    (dk-lam-t!)
    (dk-peel!)
    (let ((i (dk-apply! rpl-pm 'rqx_)))
      (dk-have! '(= rqx_ rqx_) (lambda () (rfl)))
      (dk-only! i '(= rqx_ rqx_))
      (prop))))
(fact 'nn-zero-in)
(dk-have! (list 'FORALL 'rqy_
            (list 'IMPLIES '(IN rqy_ (PAIR rqx_ rqx_))
              (list 'FORSOME 'rqn_ (list 'AND '(IN rqn_ NN)
                                        (list '= 'rqy_ (list rpl-one 'rqn_))))))
  (lambda ()
    (let* ((y (dk-di-var!))
           (i (dk-apply! rpl-pm y)))
      (dk-have! (list '= y 'rqx_)
        (lambda () (dk-only! i (list 'IN y '(PAIR rqx_ rqx_))) (prop)))
      (ew 0)
      (dk-conj-close!
       (lambda ()
         (if (eq? (rpl-head (dk-goal)) '=)
             (begin (dk-lam-b!) (ass))
             (ass)))))))
(fact 'countable-of-enum '(PAIR rqx_ rqx_) rpl-one)
(ass)
(qed 'countable-singleton)

;;; An IF term on the side the context decides: the kit's
;;; (dk-if-branch! TRUE? IFT ass ass) -- condition and main leaf by `ass'.
;;; (rpl-if-close! retired 2026-09-25.)

;;; a subset of a countable set is countable.
(sp (make-wff "forall([rqa_, rqd_], is-countable(rqd_) implies rqa_ subset rqd_
   implies is-countable(rqa_))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-COUNTABLE '(IS-COUNTABLE rqd_)))))
(fact 'subclass-of-set-is-set 'rqa_ 'rqd_)
(use-em '(FORSOME rqz_ (IN rqz_ rqa_))
  ;; ---- A has a point z0: it is the default value --------------------
  (lambda ()
    (let ((z0 (dk-skolem! '(FORSOME rqz_ (IN rqz_ rqa_))))
          (cs (dk-pick (dk-head? 'OR) "the two cases of countability")))
      (fact 'subset-mem-fwd 'rqa_ 'rqd_ z0)
      (use-cases cs
        (lambda ()
          (dk-have! (list 'IN z0 'EMPTY-SET)
            (lambda () (subst '(= EMPTY-SET rqd_)) (ass)))
          (fact 'empty-set-has-no-members z0)
          (ai (list 'NOT (list 'IN z0 'EMPTY-SET))))
        (lambda ()
          (let* ((ex (dk-pick (dk-head? 'FORSOME) "the enumeration"))
                 (e  (dk-skolem! ex))
                 (cov (dk-pick (lambda (f) (and (eq? (rpl-head f) 'FORALL)
                                                (dk-contains? f e)))
                               "the covering clause"))
                 (lam (list 'VNB-LAMBDA 'rqk_ 'NN
                            (list 'IF (list 'IN (list e 'rqk_) 'rqa_) (list e 'rqk_) z0))))
            (dk-have! (list 'IN lam '(FUN NN rqa_))
              (lambda ()
                (dk-lam-t!)
                (let* ((k (dk-di-var!))
                       (ek (list e k))
                       (ift (list 'IF (list 'IN ek 'rqa_) ek z0)))
                  (fact 'fun-apply-type-c e 'NN 'rqd_ k)
                  (use-em (list 'IN ek 'rqa_)
                    (lambda () (dk-if-branch! #t ift ass ass))
                    (lambda () (dk-if-branch! #f ift ass ass))))))
            (dk-have! (list 'FORALL 'rqy_
                        (list 'IMPLIES '(IN rqy_ rqa_)
                          (list 'FORSOME 'rqn_ (list 'AND '(IN rqn_ NN)
                                                    (list '= 'rqy_ (list lam 'rqn_))))))
              (lambda ()
                (let* ((y (dk-di-var!)))
                  (fact 'subset-mem-fwd 'rqa_ 'rqd_ y)
                  (let* ((n (dk-skolem! (dk-apply! cov y)))
                         (enk (list e n))
                         (ift (list 'IF (list 'IN enk 'rqa_) enk z0)))
                    (dk-have! (list 'IN enk 'rqa_)
                      (lambda () (subst (list '= enk y)) (ass)))
                    (ew n)
                    (dk-conj-close!
                     (lambda ()
                       (if (eq? (rpl-head (dk-goal)) '=)
                           (begin (dk-lam-b!) (dk-if-branch! #t ift ass ass))
                           (ass))))))))
            (fact 'countable-of-enum 'rqa_ lam)
            (ass))))))
  ;; ---- A is empty ----------------------------------------------------
  (lambda ()
    (dk-have! '(FORALL rqw_ (IMPLIES (IN rqw_ rqa_) (IN rqw_ EMPTY-SET)))
      (lambda ()
        (let ((w (dk-di-var!)))
          (dk-have! '(FORSOME rqz_ (IN rqz_ rqa_)) (lambda () (ew w) (ass)))
          (ai '(NOT (FORSOME rqz_ (IN rqz_ rqa_)))))))
    (fact 'subset-of-empty-is-empty 'rqa_)
    (mac 'IS-COUNTABLE)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rpl-head (dk-goal)) 'OR)
           (begin (oi-l) (ass))
           (ass))))))
(qed 'countable-subset)

;;; the two cases of IS-COUNTABLE, as a citable read-off: `mac-h' of the
;;; predicate CONSUMES it, and the union proof needs the predicate again.
(sp (make-wff "forall([rqd_], is-countable(rqd_) implies rqd_ in set and
   (rqd_ = empty-set or forsome([rqe_], rqe_ in fun(nn, rqd_) and
      forall([rqy_], rqy_ in rqd_ implies forsome([rqn_], rqn_ in nn and rqy_ = rqe_(rqn_))))))"))
(dk-peel!)
(mac-h 'IS-COUNTABLE '(IS-COUNTABLE rqd_))
(ass)
(qed 'countable-cases)

;;; the reduction of an IF whose condition the context does not hold
;;; literally: CLOSE-COND closes the condition leaf.
(define (rpl-if-close-by! ift true? close-cond)
  (for-each
   (lambda (leaf)
     (dk-focus! leaf)
     (if (dk-contains? (dk-goal) ift)
         (begin (subst (list '= ift (if true? (caddr ift) (cadddr ift)))) (ass))
         (close-cond)))
   (dk-opened (lambda () (if true? (if-true ift) (if-false ift))))))

;;; a set covered by TWO NN-indexed families of its points is countable:
;;; NN-pairing (`nn-flatten') applied to i |-> IF(i = 0, f, g).
(sp (make-wff "forall([rqu_, rqf_, rqg_], rqu_ in set implies rqf_ in fun(nn, rqu_)
   implies rqg_ in fun(nn, rqu_) implies
   forall([rqy_], rqy_ in rqu_ implies
      (forsome([rqj_], rqj_ in nn and rqy_ = rqf_(rqj_)) or
       forsome([rqj_], rqj_ in nn and rqy_ = rqg_(rqj_))))
   implies is-countable(rqu_))"))
(dk-peel!)
(define rpl-h '(VNB-LAMBDA rqi_ NN (IF (= rqi_ 0) rqf_ rqg_)))
(fact 'nn-zero-in)
(fact 'nn-one-in)
(fact 'rr-one-in)
(dk-have! '(< 0 1) (lambda () (dk-ineq!)))
(fact 'rr-pos-ne-zero 1)
(dk-have! (list 'IN rpl-h '(FUN NN (FUN NN rqu_)))
  (lambda ()
    (dk-lam-t!)
    (let* ((i (dk-di-var!))
           (ift (list 'IF (list '= i 0) 'rqf_ 'rqg_)))
      (use-em (list '= i 0)
        (lambda () (dk-if-branch! #t ift ass ass))
        (lambda () (dk-if-branch! #f ift ass ass))))))
(define rpl-e (dk-skolem! (dk-fact! 'nn-flatten 'rqu_ rpl-h)))
(define rpl-flat (dk-pick (lambda (f) (and (eq? (rpl-head f) 'FORALL) (dk-contains? f rpl-e)))
                          "the flattening clause"))
(define rpl-cov2 (dk-pick (lambda (f) (and (eq? (rpl-head f) 'FORALL) (dk-contains? f 'OR)))
                          "the two-family cover"))
;;; y = fam(j) with fam the value at index IDX of rpl-h: land e(m) = h(idx)(j),
;;; and close the goal forsome n. y = e(n).
(define (rpl-hit! y j idx true?)
  (let* ((ex (dk-apply! rpl-flat idx j))
         (m  (dk-skolem! ex))
         (eq (dk-pick (lambda (f) (and (eq? (rpl-head f) '=) (equal? (cadr f) (list rpl-e m))))
                      "e(m) = h(idx)(j)"))
         (ift (list 'IF (list '= idx 0) 'rqf_ 'rqg_)))
    (ew m)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rpl-head (dk-goal)) '=)
           (begin
             (subst eq)
             (dk-lam-b!)
             (rpl-if-close-by! ift true?
               (lambda () (if true? (rfl) (ass)))))
           (ass))))))
(dk-have! (list 'FORALL 'rqy_
            (list 'IMPLIES '(IN rqy_ rqu_)
              (list 'FORSOME 'rqn_ (list 'AND '(IN rqn_ NN)
                                        (list '= 'rqy_ (list rpl-e 'rqn_))))))
  (lambda ()
    (let* ((y (dk-di-var!))
           (cs (dk-apply! rpl-cov2 y)))
      (use-cases cs
        (lambda ()
          (let ((j (dk-skolem! (cadr cs))))
            (rpl-hit! y j 0 #t)))
        (lambda ()
          (let ((j (dk-skolem! (caddr cs))))
            (rpl-hit! y j 1 #f)))))))
(fact 'countable-of-enum 'rqu_ rpl-e)
(ass)
(qed 'countable-of-two-enum)

;;; the union of two countable sets is countable.
(sp (make-wff "forall([rqa_, rqb_], is-countable(rqa_) implies is-countable(rqb_)
   implies is-countable(union(rqa_, rqb_)))"))
(dk-peel!)
(define rpl-ca (dk-fact! 'countable-cases 'rqa_))
(define rpl-cb (dk-fact! 'countable-cases 'rqb_))
(dk-split-all!)
(have! '(AND (IN rqa_ SET) (IN rqb_ SET)))
(fact 'union-set-closure 'rqa_ 'rqb_)
(define rpl-u '(UNION rqa_ rqb_))
;;; U subset of the NON-empty one, when the other is EMPTY-SET.
(define (rpl-union-into! empty other)
  (dk-have! (list 'SUBSET rpl-u other)
    (lambda ()
      (let* ((z (subset-by-element!))
             (cs (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN z rpl-u))))))
        (use-cases cs
          (lambda ()
            (if (eq? empty 'rqa_)
                (begin
                  (dk-have! (list 'IN z 'EMPTY-SET)
                    (lambda () (subst '(= EMPTY-SET rqa_)) (ass)))
                  (fact 'empty-set-has-no-members z)
                  (ai (list 'NOT (list 'IN z 'EMPTY-SET))))
                (ass)))
          (lambda ()
            (if (eq? empty 'rqb_)
                (begin
                  (dk-have! (list 'IN z 'EMPTY-SET)
                    (lambda () (subst '(= EMPTY-SET rqb_)) (ass)))
                  (fact 'empty-set-has-no-members z)
                  (ai (list 'NOT (list 'IN z 'EMPTY-SET))))
                (ass)))))))
  (fact 'countable-subset rpl-u other)
  (ass))
(define (rpl-or-of f) (dk-pick (lambda (g) (and (eq? (rpl-head g) 'OR) (dk-contains? g f)))
                               "a countability disjunction"))
(use-cases (rpl-or-of '(= rqa_ EMPTY-SET))
  (lambda () (rpl-union-into! 'rqa_ 'rqb_))
  (lambda ()
    (use-cases (rpl-or-of '(= rqb_ EMPTY-SET))
      (lambda () (rpl-union-into! 'rqb_ 'rqa_))
      (lambda ()
        (let* ((ea (dk-skolem! (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORSOME)
                                                        (dk-contains? g '(FUN NN rqa_))))
                                        "the enumeration of A")))
               (eb (dk-skolem! (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORSOME)
                                                        (dk-contains? g '(FUN NN rqb_))))
                                        "the enumeration of B")))
               (cova (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g ea)))
                              "the cover of A"))
               (covb (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g eb)))
                              "the cover of B")))
          (fact 'union-right-subset 'rqa_ 'rqb_)          ; B subset U
          (dk-have! (list 'SUBSET 'rqa_ rpl-u)
            (lambda ()
              (let ((z (subset-by-element!)))
                (mac 'union-membership)
                (oi-l) (ass))))
          (fact 'fun-codomain-superset ea 'NN 'rqa_ rpl-u)
          (fact 'fun-codomain-superset eb 'NN 'rqb_ rpl-u)
          (dk-have! (list 'FORALL 'rqy_
                      (list 'IMPLIES (list 'IN 'rqy_ rpl-u)
                        (list 'OR
                          (list 'FORSOME 'rqj_ (list 'AND '(IN rqj_ NN) (list '= 'rqy_ (list ea 'rqj_))))
                          (list 'FORSOME 'rqj_ (list 'AND '(IN rqj_ NN) (list '= 'rqy_ (list eb 'rqj_)))))))
            (lambda ()
              (let* ((y (dk-di-var!))
                     (cs (dk-landed-1 (lambda () (mac-h 'union-membership (list 'IN y rpl-u))))))
                (use-cases cs
                  (lambda () (oi-l) (dk-apply! cova y) (ass))
                  (lambda () (oi-r) (dk-apply! covb y) (ass))))))
          (fact 'countable-of-two-enum rpl-u ea eb)
          (ass))))))
(qed 'countable-union-2)

;;; a FINITE set is countable: finite-set-induction over the class of
;;; countable sets, the step being `countable-union-2' with a singleton.
(define rpl-cls '(COMP rqs_ (IS-COUNTABLE rqs_)))
(define rpl-base-claim (list 'IN 'EMPTY-SET rpl-cls))
(define rpl-step-claim
  (list 'FORALL 'rqs_
    (list 'IMPLIES
      (list 'AND '(IN rqs_ SET)
            (list 'AND '(IN (CARD rqs_) NN) (list 'IN 'rqs_ rpl-cls)))
      (list 'FORALL 'rqx_
        (list 'IMPLIES (list 'AND '(IN rqx_ SET) '(NOT (IN rqx_ rqs_)))
              (list 'IN '(UNION rqs_ (PAIR rqx_ rqx_)) rpl-cls))))))
(sp (make-wff "forall([rqd_], rqd_ in set implies card(rqd_) in nn implies is-countable(rqd_))"))
(dk-peel!)
(have! rpl-base-claim
  (lambda ()
    (for-each
     (lambda (leaf)
       (dk-focus! leaf)
       (if (eq? (rpl-head (dk-goal)) 'IN)
           (begin (fact 'empty-set-is-set) (ass))
           (begin (fact 'countable-empty) (ass))))
     (dk-opened (lambda () (comp-mi))))))
(have! rpl-step-claim
  (lambda ()
    (dk-peel!)
    (dk-split-all!)
    (let* ((g  (dk-goal))
           (un (cadr g))
           (sv (cadr un))
           (xv (cadr (caddr un))))
      (have! (list 'AND (list 'IN xv 'SET) (list 'IN xv 'SET)))
      (fact 'pairing xv xv)
      (have! (list 'AND (list 'IN sv 'SET) (list 'IN (list 'PAIR xv xv) 'SET)))
      (fact 'union-set-closure sv (list 'PAIR xv xv))
      (dk-landed-find (lambda () (comp-me (list 'IN sv rpl-cls))) (dk-head? 'IS-COUNTABLE))
      (fact 'countable-singleton xv)
      (fact 'countable-union-2 sv (list 'PAIR xv xv))
      (for-each (lambda (leaf) (dk-focus! leaf) (ass))
                (dk-opened (lambda () (comp-mi)))))))
(have! (list 'AND rpl-base-claim rpl-step-claim))
(let ((ind (dk-fact! 'finite-set-induction rpl-cls)))
  (have! '(AND (IN rqd_ SET) (IN (CARD rqd_) NN)))
  (let ((mem (dk-apply! ind 'rqd_)))
    (dk-landed-find (lambda () (comp-me mem)) (dk-head? 'IS-COUNTABLE))
    (ass)))
(qed 'finite-implies-countable)

;;; the image of a countable set under a function is countable.
(sp (make-wff "forall([rqd_, rqh_, rqa_, rqb_], is-countable(rqd_) implies
   rqh_ in fun(rqa_, rqb_) implies rqd_ subset rqa_ implies
   is-countable(image(rqh_, rqd_)))"))
(dk-peel!)
(define rpl-im '(IMAGE rqh_ rqd_))
(dk-fact! 'countable-cases 'rqd_)
(dk-split-all!)
(fact 'image-set 'rqh_ 'rqd_)
(use-cases (dk-pick (dk-head? 'OR) "the two cases of countability")
  (lambda ()
    (dk-have! (list 'SUBSET rpl-im 'EMPTY-SET)
      (lambda ()
        (let* ((z (subset-by-element!))
               (ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff (list 'IN z rpl-im)))))
               (x (dk-skolem! ex)))
          (dk-have! (list 'IN x 'EMPTY-SET)
            (lambda () (subst '(= EMPTY-SET rqd_)) (ass)))
          (fact 'empty-set-has-no-members x)
          (ai (list 'NOT (list 'IN x 'EMPTY-SET))))))
    (fact 'countable-empty)
    (fact 'countable-subset rpl-im 'EMPTY-SET)
    (ass))
  (lambda ()
    (let* ((e (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the enumeration")))
           (cov (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g e)))
                         "the cover"))
           (lam (list 'VNB-LAMBDA 'rqk_ 'NN (list 'rqh_ (list e 'rqk_)))))
      (dk-have! (list 'IN lam (list 'FUN 'NN rpl-im))
        (lambda ()
          (dk-lam-t!)
          (let* ((k (dk-di-var!)) (ek (list e k)))
            (fact 'fun-apply-type-c e 'NN 'rqd_ k)
            (fact 'subset-mem-fwd 'rqd_ 'rqa_ ek)
            (dk-image-goal!)
            (ew ek)
            (dk-conj-close!
             (lambda ()
               (if (eq? (rpl-head (dk-goal)) '=) (rfl) (ass)))))))
      (dk-have! (list 'FORALL 'rqy_
                  (list 'IMPLIES (list 'IN 'rqy_ rpl-im)
                    (list 'FORSOME 'rqn_ (list 'AND '(IN rqn_ NN)
                                              (list '= 'rqy_ (list lam 'rqn_))))))
        (lambda ()
          (let* ((y (dk-di-var!))
                 (ex (dk-landed-1 (lambda () (mac-h 'image-membership-iff (list 'IN y rpl-im)))))
                 (x (dk-skolem! ex))
                 (n (dk-skolem! (dk-apply! cov x))))
            (ew n)
            (dk-conj-close!
             (lambda ()
               (if (eq? (rpl-head (dk-goal)) '=)
                   (begin
                     (dk-lam-b!)
                     (subst (list '= (list e n) x))
                     (subst (list '= (list 'rqh_ x) y))
                     (rfl))
                   (ass)))))))
      (fact 'countable-of-enum rpl-im lam)
      (ass))))
(qed 'countable-image)

;;; =====================================================================
;;; (2) THREE ABSOLUTE-VALUE SPLITS, so that `ineq' (which does not read
;;; `abs') can use a bound and prove one.
;;; =====================================================================
(sp (make-wff "forall([rqx_ in rr, rqc_ in rr], abs(rqx_) <= rqc_ implies
   -rqc_ <= rqx_ and rqx_ <= rqc_)"))
(dk-peel!)
(fact 'rr-abs-cases 'rqx_)
(fact 'rr-abs-nonneg 'rqx_)
(use-cases (dk-pick (dk-head? 'OR) "the two cases of abs")
  (lambda ()
    (dk-split-all!)
    (dk-conj-close! (lambda ()
      (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(<= (ABS rqx_) rqc_)
                '(= (ABS rqx_) rqx_) '(<= 0 (ABS rqx_))))))
  (lambda ()
    (dk-split-all!)
    (dk-conj-close! (lambda ()
      (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(<= (ABS rqx_) rqc_)
                '(= (ABS rqx_) (- rqx_)) '(<= 0 (ABS rqx_)))))))
(qed 'rr-abs-le-parts)

(sp (make-wff "forall([rqx_ in rr, rqc_ in rr], -rqc_ <= rqx_ implies rqx_ <= rqc_
   implies abs(rqx_) <= rqc_)"))
(dk-peel!)
(fact 'rr-abs-cases 'rqx_)
(use-cases (dk-pick (dk-head? 'OR) "the two cases of abs")
  (lambda ()
    (dk-split-all!)
    (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(<= rqx_ rqc_) '(= (ABS rqx_) rqx_)))
  (lambda ()
    (dk-split-all!)
    (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(<= (- rqc_) rqx_) '(= (ABS rqx_) (- rqx_)))))
(qed 'rr-abs-le-of-parts)

(sp (make-wff "forall([rqx_ in rr, rqc_ in rr], -rqc_ < rqx_ implies rqx_ < rqc_
   implies abs(rqx_) < rqc_)"))
(dk-peel!)
(fact 'rr-abs-cases 'rqx_)
(use-cases (dk-pick (dk-head? 'OR) "the two cases of abs")
  (lambda ()
    (dk-split-all!)
    (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(< rqx_ rqc_) '(= (ABS rqx_) rqx_)))
  (lambda ()
    (dk-split-all!)
    (dk-ineq! '(IN rqx_ RR) '(IN rqc_ RR) '(< (- rqc_) rqx_) '(= (ABS rqx_) (- rqx_)))))
(qed 'rr-abs-lt-of-parts)

;;; =====================================================================
;;; (3) CONTINUITY GIVES BOTH ONE-SIDED LIMITS WITHIN, WITH VALUE f(x).
;;; =====================================================================

;;; goal abs(y) <= c (resp. < c): the two linear halves by `ineq' from
;;; PREMS, then the split lemma.  y and c must be typed in context.
(define (rpl-abs-bound! strict? y c prems)
  (let ((op (if strict? '< '<=)))
    (dk-have! (list op (list '- c) y) (lambda () (apply dk-ineq! prems)))
    (dk-have! (list op y c) (lambda () (apply dk-ineq! prems)))
    (fact (if strict? 'rr-abs-lt-of-parts 'rr-abs-le-of-parts) y c)
    (ass)))

;;; the eps-clause of a one-sided limit at x from continuity at x on the
;;; subspace W.  RIGHT? selects the window.  Goal on entry: the eps-universal.
(define (rpl-cont-eps! f w x right?)
  (let* ((sub (list 'SUBSPACE-MS 'RR-MS w))
         (cont (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g 'DIST)))
                        "the eps-delta clause of continuity"))
         (pe (dk-peel!))
         (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (d  (dk-halve! e))
         (dl (dk-skolem! (dk-apply! cont d)))
         (cl (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g dl)))
                      "the delta clause")))
    (fact 'rr-pos-rr-in-rr dl)
    (fact 'rr-lt-of-pos-rr dl)
    (fact 'rr-pos-rr-in-rr e)
    (ew dl)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rpl-head (dk-goal)) 'POS-RR)
           (ass)
           (let* ((ls (dk-peel!))
                  (t  (cadr (car (filter (lambda (g) (and (eq? (rpl-head g) 'IN)
                                                          (equal? (caddr g) w)))
                                         ls))))
                  (ft (list f t)) (fx (list f x))
                  (xt (list '- x t)) (dfx (list '- fx ft)) (dft (list '- ft fx)))
             (fact 'subset-mem-fwd w 'RR t)
             (fact 'fun-apply-type-c f w 'RR t)
             (fact 'subspace-pts 'RR-MS w)
             (dk-have! (list 'IN t (list 'PTS sub))
               (lambda () (subst (list '= (list 'PTS sub) w)) (ass)))
             (fact 'subspace-dist 'RR-MS w x t)
             (fact 'rr-ms-dist x t)
             (fact 'rr-sub-in-rr x t)
             (dk-have! (list '<= (list (list 'DIST sub) x t) dl)
               (lambda ()
                 (subst (list '= (list (list 'DIST sub) x t) (list '(DIST RR-MS) x t)))
                 (subst (list '= (list '(DIST RR-MS) x t) (list 'ABS xt)))
                 (rpl-abs-bound! #f xt dl
                   (append (list (list 'IN x 'RR) (list 'IN t 'RR) (list 'IN dl 'RR))
                           (if right?
                               (list (list '< x t) (list '< t (list '+ x dl)))
                               (list (list '< (list '- x dl) t) (list '< t x)))))))
             (dk-apply! cl t)
             (fact 'rr-ms-dist fx ft)
             (fact 'rr-sub-in-rr fx ft)
             (fact 'rr-sub-in-rr ft fx)
             (dk-have! (list '<= (list 'ABS dfx) d)
               (lambda ()
                 (subst (list '= (list 'ABS dfx) (list '(DIST RR-MS) fx ft)))
                 (ass)))
             (dk-split-all! (list (dk-fact! 'rr-abs-le-parts dfx d)))
             (rpl-abs-bound! #t dft e
               (list (list 'IN fx 'RR) (list 'IN ft 'RR) (list 'IN d 'RR)
                     (list '<= (list '- d) dfx) (list '<= dfx d)
                     (list '= (list '+ d d) e) (list '< 0 d)))))))))

;;; D subset RR, f continuous on D: at every x of D, f(x) is the right limit
;;; of f within D.
(sp (make-wff "forall([f, rqw_], rqw_ subset rr implies is-continuous-on(f, rqw_) implies
   forall([rqx_ in rqw_], is-right-limit-within(f, rqw_, rqx_, f(rqx_))))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-CONTINUOUS-ON '(IS-CONTINUOUS-ON f rqw_)))))
(fact 'subset-mem-fwd 'rqw_ 'RR 'rqx_)
(fact 'fun-apply-type-c 'f 'rqw_ 'RR 'rqx_)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-CONTINUOUS-AT
         (dk-apply! (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL)
                                              (dk-contains? g 'IS-CONTINUOUS-AT)))
                             "continuity on W")
                    'rqx_)))))
(mac 'IS-RIGHT-LIMIT-WITHIN)
(dk-conj-close!
 (lambda ()
   (if (eq? (rpl-head (dk-goal)) 'FORALL)
       (rpl-cont-eps! 'f 'rqw_ 'rqx_ #t)
       (ass))))
(qed 'continuous-on-right-limit-within)

(sp (make-wff "forall([f, rqw_], rqw_ subset rr implies is-continuous-on(f, rqw_) implies
   forall([rqx_ in rqw_], is-left-limit-within(f, rqw_, rqx_, f(rqx_))))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-CONTINUOUS-ON '(IS-CONTINUOUS-ON f rqw_)))))
(fact 'subset-mem-fwd 'rqw_ 'RR 'rqx_)
(fact 'fun-apply-type-c 'f 'rqw_ 'RR 'rqx_)
(dk-split-all! (dk-landed* (lambda ()
  (mac-h 'IS-CONTINUOUS-AT
         (dk-apply! (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL)
                                              (dk-contains? g 'IS-CONTINUOUS-AT)))
                             "continuity on W")
                    'rqx_)))))
(mac 'IS-LEFT-LIMIT-WITHIN)
(dk-conj-close!
 (lambda ()
   (if (eq? (rpl-head (dk-goal)) 'FORALL)
       (rpl-cont-eps! 'f 'rqw_ 'rqx_ #f)
       (ass))))
(qed 'continuous-on-left-limit-within)

;;; a function continuous on [a,b] is regulated on [a,b] (Dieudonne 8.7.2's
;;; parenthesis: "and in particular any continuous mapping").
(sp (make-wff "forall([f, a, b], a in rr implies b in rr implies a < b implies
   is-continuous-on(f, ccint(a, b)) implies is-regulated-on(f, a, b))"))
(dk-peel!)
(dk-have! '(IN f (FUN (CCINT a b) RR))
  (lambda ()
    (dk-split-all! (dk-landed* (lambda ()
      (mac-h 'IS-CONTINUOUS-ON '(IS-CONTINUOUS-ON f (CCINT a b))))))
    (ass)))
(fact 'ccint-subset-rr 'a 'b)
(mac 'IS-REGULATED-ON)
(dk-conj-close!
 (lambda ()
   (let ((g (dk-goal)))
     (if (eq? (rpl-head g) 'FORALL)
         (let* ((right? (dk-contains? g 'IS-RIGHT-LIMIT-WITHIN))
                (x (dk-di-var!)))
           (dk-peel!)
           (ew (list 'f x))
           (fact (if right? 'continuous-on-right-limit-within 'continuous-on-left-limit-within)
                 'f '(CCINT a b) x)
           (ass))
         (ass)))))
(qed 'continuous-on-implies-regulated-on)

;;; =====================================================================
;;; (4) UNIQUENESS OF A ONE-SIDED LIMIT WITHIN W, when x is approached by
;;; points of W from that side.  Stated first as `l - m <= 0'; the
;;; equation is that fact twice.
;;; =====================================================================
(define (rpl-lim-stmt right? concl)
  (string-append
   "forall([f, rqw_, rqx_, rql_, rqm_], "
   (if right? "is-right-limit-within" "is-left-limit-within")
   "(f, rqw_, rqx_, rql_) implies "
   (if right? "is-right-limit-within" "is-left-limit-within")
   "(f, rqw_, rqx_, rqm_) implies
   forall([rqr_], pos-rr(rqr_) implies forsome([rqt_], rqt_ in rqw_ and "
   (if right? "rqx_ < rqt_ and rqt_ < rqx_ + rqr_" "rqx_ - rqr_ < rqt_ and rqt_ < rqx_")
   ")) implies " concl ")"))

(define (rpl-lim-le! right?)
  (dk-peel!)
  (let ((pred (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN)))
    (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f 'rqw_ 'rqx_ 'rql_)))))
    (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f 'rqw_ 'rqx_ 'rqm_))))))
  (let* ((univ (lambda (l) (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL)
                                                     (dk-contains? g 'ABS)
                                                     (dk-contains? g l)))
                                    "a limit clause")))
         (liml (univ 'rql_))
         (limm (univ 'rqm_))
         (acc  (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g 'rqr_)))
                        "the approach clause")))
    (fact 'rr-sub-in-rr 'rql_ 'rqm_)
    (dk-have! '(FORALL eps (IMPLIES (POS-RR eps) (<= (- rql_ rqm_) eps)))
      (lambda ()
        (let* ((pe (dk-peel!))
               (d  (cadr (car (filter (dk-head? 'POS-RR) pe))))
               (e  (dk-halve! d))
               (d1 (dk-skolem! (dk-apply! liml e)))
               (c1 (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g d1)))
                            "the first delta clause"))
               (d2 (dk-skolem! (dk-apply! limm e)))
               (c2 (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g d2)))
                            "the second delta clause")))
          (for-each (lambda (v) (fact 'rr-pos-rr-in-rr v) (fact 'rr-lt-of-pos-rr v))
                    (list d1 d2))
          (let ((w (dk-skolem! (dk-fact! 'rr-min-pos d1 d2))))
            (dk-split-all!)
            (fact 'rr-pos-rr-of-lt w)
            (let* ((t (dk-skolem! (dk-apply! acc w)))
                   (ft (list 'f t)))
              (dk-split-all!)
              (fact 'subset-mem-fwd 'rqw_ 'RR t)
              (fact 'fun-apply-type-c 'f 'rqw_ 'RR t)
              (for-each
               (lambda (dv cl)
                 (if right?
                     (dk-have! (list '< t (list '+ 'rqx_ dv))
                       (lambda () (dk-ineq! '(IN rqx_ RR) (list 'IN t 'RR) (list 'IN w 'RR)
                                            (list 'IN dv 'RR) (list '< t (list '+ 'rqx_ w))
                                            (list '<= w dv))))
                     (dk-have! (list '< (list '- 'rqx_ dv) t)
                       (lambda () (dk-ineq! '(IN rqx_ RR) (list 'IN t 'RR) (list 'IN w 'RR)
                                            (list 'IN dv 'RR) (list '< (list '- 'rqx_ w) t)
                                            (list '<= w dv)))))
                 (dk-apply! cl t))
               (list d1 d2) (list c1 c2))
              (fact 'rr-sub-in-rr ft 'rql_)
              (fact 'rr-sub-in-rr ft 'rqm_)
              (dk-split-all! (list (dk-fact! 'rr-abs-lt-parts (list '- ft 'rql_) e)))
              (dk-split-all! (list (dk-fact! 'rr-abs-lt-parts (list '- ft 'rqm_) e)))
              (fact 'rr-pos-rr-in-rr d)
              (dk-ineq! (list 'IN ft 'RR) '(IN rql_ RR) '(IN rqm_ RR) (list 'IN e 'RR)
                        (list 'IN d 'RR)
                        (list '< (list '- e) (list '- ft 'rql_))
                        (list '< (list '- ft 'rqm_) e)
                        (list (quote =) (list (quote +) e e) d)))))))
    (fact 'rr-le-all-pos-nonpos '(- rql_ rqm_))
    (ass)))

(sp (make-wff (rpl-lim-stmt #t "rql_ - rqm_ <= 0")))
(rpl-lim-le! #t)
(qed 'right-limit-within-le)

(sp (make-wff (rpl-lim-stmt #f "rql_ - rqm_ <= 0")))
(rpl-lim-le! #f)
(qed 'left-limit-within-le)

(define (rpl-lim-unique! right?)
  (dk-peel!)
  (let ((le (if right? 'right-limit-within-le 'left-limit-within-le))
        (pred (if right? 'IS-RIGHT-LIMIT-WITHIN 'IS-LEFT-LIMIT-WITHIN)))
    (fact le 'f 'rqw_ 'rqx_ 'rql_ 'rqm_)
    (fact le 'f 'rqw_ 'rqx_ 'rqm_ 'rql_)
    (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f 'rqw_ 'rqx_ 'rql_)))))
    (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f 'rqw_ 'rqx_ 'rqm_)))))
    (have! '(AND (IN rql_ RR) (IN rqm_ RR)))
    (dk-have! '(<= rql_ rqm_)
      (lambda () (dk-ineq! '(IN rql_ RR) '(IN rqm_ RR) '(<= (- rql_ rqm_) 0))))
    (dk-have! '(<= rqm_ rql_)
      (lambda () (dk-ineq! '(IN rql_ RR) '(IN rqm_ RR) '(<= (- rqm_ rql_) 0))))
    (have! '(AND (<= rql_ rqm_) (<= rqm_ rql_)))
    (fact 'rr-leq-antisymmetric 'rql_ 'rqm_)
    (ass)))

(sp (make-wff (rpl-lim-stmt #t "rql_ = rqm_")))
(rpl-lim-unique! #t)
(qed 'right-limit-within-unique)

(sp (make-wff (rpl-lim-stmt #f "rql_ = rqm_")))
(rpl-lim-unique! #f)
(qed 'left-limit-within-unique)

;;; every point x of [a,b) is approached from the right by points of [a,b],
;;; every point of (a,b] from the left: the approach hypothesis of the two
;;; uniqueness theorems, discharged for an interval.
(define (rpl-close-by! prems)
  (dk-conj-close!
   (lambda ()
     (if (dk-ctx-form (dk-goal)) (ass) (apply dk-ineq! prems)))))

(define (rpl-approach! right?)
  (let* ((pe (dk-peel!))
         (r  (cadr (car (filter (dk-head? 'POS-RR) pe))))
         (gap (if right? '(- b rqx_) '(- rqx_ a))))
    (fact 'rr-pos-rr-in-rr r)
    (fact 'rr-lt-of-pos-rr r)
    (fact 'rr-sub-in-rr (cadr gap) (caddr gap))
    (dk-have! (list '< 0 gap)
      (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(IN rqx_ RR)
                           (if right? '(< rqx_ b) '(< a rqx_)))))
    (let ((w (dk-skolem! (dk-fact! 'rr-min-pos r gap))))
      (dk-split-all!)
      (fact 'rr-pos-rr-of-lt w)
      (let* ((h (dk-halve! w))
             (t (list (if right? '+ '-) 'rqx_ h)))
        (if right? (fact 'rr-add-in-rr 'rqx_ h) (fact 'rr-sub-in-rr 'rqx_ h))
        (let ((prems (list '(IN a RR) '(IN b RR) '(IN rqx_ RR) (list 'IN r 'RR)
                           (list 'IN w 'RR) (list 'IN h 'RR) (list 'IN t 'RR)
                           (if right? '(<= a rqx_) '(< a rqx_))
                           (if right? '(< rqx_ b) '(<= rqx_ b))
                           (list '<= w r) (list '<= w gap)
                           (list '= (list '+ h h) w) (list '< 0 h))))
          (ew t)
          (dk-conj-close!
           (lambda ()
             (if (eq? (rpl-head (dk-goal)) 'IN)
                 (begin (mac 'ccint-membership) (rpl-close-by! prems))
                 (rpl-close-by! prems)))))))))

(sp (make-wff "forall([a in rr, b in rr, rqx_ in rr], a <= rqx_ implies rqx_ < b implies
   forall([rqr_], pos-rr(rqr_) implies forsome([rqt_], rqt_ in ccint(a, b) and
      rqx_ < rqt_ and rqt_ < rqx_ + rqr_)))"))
(rpl-approach! #t)
(qed 'ccint-right-approach)

(sp (make-wff "forall([a in rr, b in rr, rqx_ in rr], a < rqx_ implies rqx_ <= b implies
   forall([rqr_], pos-rr(rqr_) implies forsome([rqt_], rqt_ in ccint(a, b) and
      rqx_ - rqr_ < rqt_ and rqt_ < rqx_)))"))
(rpl-approach! #f)
(qed 'ccint-left-approach)

;;; the one-sided limits of a function on [a,b] are unique where they are
;;; required by IS-REGULATED-ON: the right one at x < b, the left at x > a.
(sp (make-wff "forall([f, a in rr, b in rr, rqx_ in rr, rql_, rqm_], a <= rqx_ implies
   rqx_ < b implies is-right-limit-within(f, ccint(a, b), rqx_, rql_) implies
   is-right-limit-within(f, ccint(a, b), rqx_, rqm_) implies rql_ = rqm_)"))
(dk-peel!)
(fact 'ccint-right-approach 'a 'b 'rqx_)
(fact 'right-limit-within-unique 'f '(CCINT a b) 'rqx_ 'rql_ 'rqm_)
(ass)
(qed 'right-limit-within-ccint-unique)

(sp (make-wff "forall([f, a in rr, b in rr, rqx_ in rr, rql_, rqm_], a < rqx_ implies
   rqx_ <= b implies is-left-limit-within(f, ccint(a, b), rqx_, rql_) implies
   is-left-limit-within(f, ccint(a, b), rqx_, rqm_) implies rql_ = rqm_)"))
(dk-peel!)
(fact 'ccint-left-approach 'a 'b 'rqx_)
(fact 'left-limit-within-unique 'f '(CCINT a b) 'rqx_ 'rql_ 'rqm_)
(ass)
(qed 'left-limit-within-ccint-unique)

;;; =====================================================================
;;; (5) RESTRICTION.  A one-sided limit within W is one within any V subset
;;; W, for any function on V agreeing with f there; hence a regulated
;;; function is regulated on every subinterval.
;;; =====================================================================
(define (rpl-lim-subset! pred)
  (dk-peel!)
  (dk-split-all! (dk-landed* (lambda () (mac-h pred (list pred 'f 'rqw_ 'rqx_ 'rql_)))))
  (fact 'subset-trans 'rqv_ 'rqw_ 'RR)
  (let ((cl (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g 'ABS)))
                     "the limit clause"))
        (pw (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g 'g)))
                     "the pointwise agreement")))
    (mac pred)
    (dk-conj-close!
     (lambda ()
       (if (eq? (rpl-head (dk-goal)) 'FORALL)
           (let* ((pe (dk-peel!))
                  (e  (cadr (car (filter (dk-head? 'POS-RR) pe))))
                  (dl (dk-skolem! (dk-apply! cl e)))
                  (c2 (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g dl)))
                               "the delta clause")))
             (ew dl)
             (dk-conj-close!
              (lambda ()
                (if (eq? (rpl-head (dk-goal)) 'POS-RR)
                    (ass)
                    (let* ((ls (dk-peel!))
                           (t (cadr (car (filter (lambda (g) (and (eq? (rpl-head g) 'IN)
                                                                  (eq? (caddr g) 'rqv_)))
                                                 ls)))))
                      (fact 'subset-mem-fwd 'rqv_ 'rqw_ t)
                      (dk-apply! c2 t)
                      (dk-apply! pw t)
                      (subst (list '= (list 'g t) (list 'f t)))
                      (ass))))))
           (ass))))))

(sp (make-wff "forall([f, rqw_, rqx_, rql_, g, rqv_], is-right-limit-within(f, rqw_, rqx_, rql_)
   implies rqv_ subset rqw_ implies g in fun(rqv_, rr) implies
   forall([rqz_ in rqv_], g(rqz_) = f(rqz_)) implies is-right-limit-within(g, rqv_, rqx_, rql_))"))
(rpl-lim-subset! 'IS-RIGHT-LIMIT-WITHIN)
(qed 'right-limit-within-subset)

(sp (make-wff "forall([f, rqw_, rqx_, rql_, g, rqv_], is-left-limit-within(f, rqw_, rqx_, rql_)
   implies rqv_ subset rqw_ implies g in fun(rqv_, rr) implies
   forall([rqz_ in rqv_], g(rqz_) = f(rqz_)) implies is-left-limit-within(g, rqv_, rqx_, rql_))"))
(rpl-lim-subset! 'IS-LEFT-LIMIT-WITHIN)
(qed 'left-limit-within-subset)

;;; a function regulated on [a,b] is regulated on every [c,d] inside it --
;;; stated for any g on [c,d] agreeing with f there (RESTRICT(f, [c,d]) is
;;; one, by `restrict-apply' / `restrict-in-fun').
(sp (make-wff "forall([f, a, b, rqc_, rqd_, g], is-regulated-on(f, a, b) implies
   rqc_ in rr implies rqd_ in rr implies a <= rqc_ implies rqc_ < rqd_ implies rqd_ <= b implies
   g in fun(ccint(rqc_, rqd_), rr) implies
   forall([rqz_ in ccint(rqc_, rqd_)], g(rqz_) = f(rqz_)) implies is-regulated-on(g, rqc_, rqd_))"))
(dk-peel!)
(dk-split-all! (dk-landed* (lambda () (mac-h 'IS-REGULATED-ON '(IS-REGULATED-ON f a b)))))
(dk-have! '(SUBSET (CCINT rqc_ rqd_) (CCINT a b))
  (lambda ()
    (let ((z (subset-by-element!)))
      (dk-split-all! (dk-landed* (lambda ()
        (mac-h 'ccint-membership (list 'IN z '(CCINT rqc_ rqd_))))))
      (mac 'ccint-membership)
      (rpl-close-by! (list '(IN a RR) '(IN b RR) '(IN rqc_ RR) '(IN rqd_ RR) (list 'IN z 'RR)
                           '(<= a rqc_) '(<= rqd_ b) (list '<= 'rqc_ z) (list '<= z 'rqd_))))))
(fact 'ccint-subset-rr 'rqc_ 'rqd_)
(define (rpl-reg-univ pred)
  (dk-pick (lambda (g) (and (eq? (rpl-head g) 'FORALL) (dk-contains? g pred) (dk-contains? g 'f)))
           "a limit requirement of f"))
(define rpl-ru (rpl-reg-univ 'IS-RIGHT-LIMIT-WITHIN))
(define rpl-lu (rpl-reg-univ 'IS-LEFT-LIMIT-WITHIN))
(mac 'IS-REGULATED-ON)
(dk-conj-close!
 (lambda ()
   (let ((gl (dk-goal)))
     (if (eq? (rpl-head gl) 'FORALL)
         (let* ((right? (dk-contains? gl 'IS-RIGHT-LIMIT-WITHIN))
                (x (dk-di-var!)))
           (dk-peel!)
           (fact 'subset-mem-fwd '(CCINT rqc_ rqd_) '(CCINT a b) x)
           (fact 'subset-mem-fwd '(CCINT rqc_ rqd_) 'RR x)
           (if right?
               (dk-have! (list '< x 'b)
                 (lambda () (dk-ineq! '(IN rqd_ RR) '(IN b RR) (list 'IN x 'RR)
                                      (list '< x 'rqd_) '(<= rqd_ b))))
               (dk-have! (list '< 'a x)
                 (lambda () (dk-ineq! '(IN rqc_ RR) '(IN a RR) (list 'IN x 'RR)
                                      (list '< 'rqc_ x) '(<= a rqc_)))))
           (let ((l (dk-skolem! (dk-apply! (if right? rpl-ru rpl-lu) x))))
             (ew l)
             (fact (if right? 'right-limit-within-subset 'left-limit-within-subset)
                   'f '(CCINT a b) x l 'g '(CCINT rqc_ rqd_))
             (ass)))
         (ass)))))
(qed 'regulated-on-restrict)

;;; =====================================================================
;;; (6) PRIMITIVES: the read-offs, and the bridge from the finite
;;; exceptional set of path-integral.scm.
;;; =====================================================================
(define (rpl-prim-open!)
  (dk-split-all! (dk-landed* (lambda ()
    (mac-h 'IS-PRIMITIVE '(IS-PRIMITIVE pwf_ pphi_ a b))))))

(sp (make-wff "forall([pwf_, pphi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   a in rr and b in rr and a < b)"))
(dk-peel!) (rpl-prim-open!) (dk-conj-close! (lambda () (ass)))
(qed 'primitive-endpoints)

(sp (make-wff "forall([pwf_, pphi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   pwf_ in fun(ccint(a, b), rr))"))
(dk-peel!) (rpl-prim-open!) (ass)
(qed 'primitive-in-fun)

(sp (make-wff "forall([pwf_, pphi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   pphi_ in fun(ccint(a, b), rr))"))
(dk-peel!) (rpl-prim-open!) (ass)
(qed 'primitive-integrand-in-fun)

(sp (make-wff "forall([pwf_, pphi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   is-continuous-on(pwf_, ccint(a, b)))"))
(dk-peel!) (rpl-prim-open!) (ass)
(qed 'primitive-continuous)

(sp (make-wff "forall([pwf_, pphi_, a, b], is-primitive(pwf_, pphi_, a, b) implies
   forsome([rqs_], is-countable(rqs_) and rqs_ subset ccint(a, b) and
     forall([rqt_ in ooint(a, b)], not(rqt_ in rqs_) implies has-deriv-at(pwf_, rqt_, pphi_(rqt_)))))"))
(dk-peel!) (rpl-prim-open!) (ass)
(qed 'primitive-exceptional-set)

;;; The bridge `pw-antiderivative-implies-primitive' (a FINITE exceptional set is a
;;; countable one) was proven here on 2026-09-23 and retired the same day: the
;;; finite-set predicate IS-PW-ANTIDERIVATIVE was renamed onto IS-PRIMITIVE
;;; (wave 2 of batch 20), so the bridge became the identity.  Its proof is in
;;; archive/2026-09-23-batch20/regulated-primitive-laws.scm.

;;; ---- topics ------------------------------------------------------------
(for-each (lambda (n) (topic! n 'sets))
  '(countable-of-enum countable-empty countable-singleton countable-subset countable-cases
    countable-of-two-enum countable-union-2 finite-implies-countable countable-image))
(for-each (lambda (n) (topic! n 'inequalities))
  '(rr-abs-lt-parts rr-abs-le-parts rr-abs-le-of-parts rr-abs-lt-of-parts))
(for-each (lambda (n) (topic! n 'analysis))
  '(continuous-on-right-limit-within continuous-on-left-limit-within
    continuous-on-implies-regulated-on right-limit-within-le left-limit-within-le
    right-limit-within-unique left-limit-within-unique ccint-right-approach ccint-left-approach
    right-limit-within-ccint-unique left-limit-within-ccint-unique right-limit-within-subset
    left-limit-within-subset regulated-on-restrict primitive-endpoints primitive-in-fun
    primitive-integrand-in-fun primitive-continuous primitive-exceptional-set))
