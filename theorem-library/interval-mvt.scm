;;; interval-mvt.scm -- ROLLE, THE TWO MEAN VALUE THEOREMS AND THE THREE
;;; BOUNDS, STATED FOR A FUNCTION ON ITS INTERVAL.
;;;
;;; docs/real-calculus-statements.tex, section 3, and the user's notes
;;; (Supplements to Calculus) 2.11, 2.12, 2.13.  The notes say: h is a function
;;; on [a, b], continuous on [a, b], differentiable on (a, b).  The library's
;;; `rolle', `mvt', `generalized-mvt', `mvt-upper-bound', `mvt-lower-bound' and
;;; `mvt-abs-bound' say: h is a function on ALL of RR, continuous at each point
;;; of [a, b] AS A POINT OF THE LINE.  Those are different statements, because
;;; a member of FUN(A, B) is defined exactly on A.  The six theorems here are
;;; the notes' statements; each is the corresponding library theorem applied to
;;; the constant extension EXTEND-CONST(h, a, b) of
;;; structure-library/interval-calculus.scm, whose four laws are in
;;; theorem-library/interval-calculus-laws.scm.  The library's theorems are not
;;; re-proved and are not retired: they remain as the lemmas these rest on.
;;;
;;; THE HYPOTHESIS BLOCK, written H(h, a, b) in the specification, is
;;;
;;;     h in FUN(CCINT(a,b), RR),  IS-CONTINUOUS-ON(h, CCINT(a,b)),
;;;     forall x in OOINT(a,b). forsome l. HAS-DERIV-AT(h, x, l)
;;;
;;; and it is spelled out in each statement rather than abbreviated: the tree
;;; has no abbreviation mechanism for a conjunction of hypotheses, and naming
;;; it as a predicate would put a definition between the reader and the notes.
;;;
;;; THE DERIVATIVE IS A RELATION, so the notes' h'(theta) appears as an
;;; existentially quantified value l -- the only difference of form, and the
;;; one the specification records.
;;;
;;; Helper prefix: im-.
;;;
;;; Dependencies: structure-library/interval-calculus.scm,
;;; theorem-library/interval-calculus-laws.scm, ccint-basics.scm, and the six
;;; total-function theorems (rolle-proof, mvt-proof, mvt-bounds-proof,
;;; mvt-abs-bound, generalized-mvt-proof).

;;; ---- file-local driver helpers ---------------------------------------

(define (im-head g) (and (pair? g) (car g)))
(define (im-ext fn) (list 'EXTEND-CONST fn 'a 'b))

;;; a <= b, from a < b.
(define (im-le!)
  (dk-have! '(<= a b) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b)))))

;;; x in OOINT(a,b) from x in RR, a < x, x < b (all three in context).
(define (im-in-ooint! z)
  (dk-have! (list 'IN z '(OOINT a b))
    (lambda () (mac 'ooint-membership) (dk-conj-close! (lambda () (ass))))))

;;; the library's continuity hypothesis for the EXTENSION, in its own spelling:
;;;   forall x. x in CCINT(a,b) implies IS-CONTINUOUS-AT(RR-MS, RR-MS, F, x)
;;; The binder is `x' because `fact' detaches an antecedent only when the
;;; context holds it verbatim.
(define (im-cont-univ! fn)
  (dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
              (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (im-ext fn) 'x)))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'ccint-elt-in-rr 'a 'b z)
        (fact 'extend-const-continuous-at 'a 'b fn z)
        (ass)))))

;;; the hypothesis universal of the STATEMENT: forall x in OOINT(a,b) ...
(define (im-hyp-univ)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT)))
           "the interval differentiability hypothesis"))

;;; the library's differentiability hypothesis for the EXTENSION.
(define (im-diff-univ! fn)
  (let ((hyp (im-hyp-univ)))
    (dk-have! (list 'FORALL 'x (list 'IMPLIES '(AND (IN x RR) (AND (< a x) (< x b)))
                (list 'FORSOME 'l (list 'IS-DIFF-AT (im-ext fn) 'x 'l))))
      (lambda ()
        (dk-peel!)
        (dk-split-all!)
        (im-in-ooint! 'x)
        (let ((lv (dk-skolem! (dk-apply! hyp 'x))))
          (fact 'extend-const-deriv-fwd 'a 'b fn 'x lv)
          (ew lv)
          (ass))))))

;;; the library's first, CONJUNCTIVE antecedent.
(define (im-block! fn)
  (fact 'extend-const-in-fun 'a 'b fn)
  (dk-have! (list 'AND (list 'IN (im-ext fn) '(FUN RR RR))
                  '(AND (IN a RR) (AND (IN b RR) (< a b))))
    (lambda () (dk-conj-close! (lambda () (ass))))))

;;; F(a) = F(b), from h(a) = h(b).
(define (im-endpoints-eq! fn)
  (dk-have! '(<= a a) (lambda () (dk-ineq! '(IN a RR))))
  (dk-have! '(<= b b) (lambda () (dk-ineq! '(IN b RR))))
  (fact 'extend-const-fixes 'a 'b 'a fn)
  (fact 'extend-const-fixes 'a 'b 'b fn)
  (dk-have! (list '= (list (im-ext fn) 'a) (list (im-ext fn) 'b))
    (lambda ()
      (subst (list '== (list (im-ext fn) 'a) (list fn 'a)))
      (subst (list '== (list (im-ext fn) 'b) (list fn 'b)))
      (ass))))

;;; =====================================================================
;;; 2.12 -- ROLLE'S LEMMA ON [a, b].
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([h], h in fun(ccint(a,b), rr) implies
     is-continuous-on(h, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(h, x, l))) implies
     h(a) = h(b) implies
     forsome([theta in ooint(a,b)], has-deriv-at(h, theta, 0))))"))
(dk-peel!)
(im-le!)
(im-block! 'h)
(im-cont-univ! 'h)
(im-diff-univ! 'h)
(im-endpoints-eq! 'h)
(let ((th (dk-skolem! (dk-fact! 'rolle (im-ext 'h) 'a 'b))))
  (dk-split-all!)
  (im-in-ooint! th)
  (fact 'extend-const-deriv-bwd 'a 'b 'h th 0)
  (ew th)
  (dk-conj-close! (lambda () (ass))))
(qed 'rolle-on-interval)
(topic! 'rolle-on-interval 'analysis)
(alias! 'rolle-on-interval
        "Rolle's lemma for a function on a closed interval")

;;; the value equations at the endpoints, and the rewrite that takes f(a), f(b)
;;; in a GOAL to the extension's values, which is the spelling the library's
;;; conclusions use.
(define (im-values! fn)
  (dk-have! '(<= a a) (lambda () (dk-ineq! '(IN a RR))))
  (dk-have! '(<= b b) (lambda () (dk-ineq! '(IN b RR))))
  (fact 'extend-const-fixes 'a 'b 'a fn)
  (fact 'extend-const-fixes 'a 'b 'b fn))
(define (im-to-ext! fn)
  (subst (list '== (list fn 'a) (list (im-ext fn) 'a)))
  (subst (list '== (list fn 'b) (list (im-ext fn) 'b))))

;;; the hypothesis universal about FN.
(define (im-hyp-univ-of fn)
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'HAS-DERIV-AT) (dk-contains? fm fn)))
           "the interval differentiability hypothesis"))

;;; =====================================================================
;;; 2.11 -- THE GENERALIZED MEAN VALUE THEOREM ON [a, b].
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([f, g], f in fun(ccint(a,b), rr) implies g in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies is-continuous-on(g, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(f, x, l))) implies
     forall([x in ooint(a,b)], forsome([m], has-deriv-at(g, x, m))) implies
     forsome([theta in ooint(a,b)],
       forsome([l, m], has-deriv-at(f, theta, l) and has-deriv-at(g, theta, m)
                       and l * (g(b) - g(a)) = m * (f(b) - f(a))))))"))
(dk-peel!)
(im-le!)
(fact 'extend-const-in-fun 'a 'b 'f)
(fact 'extend-const-in-fun 'a 'b 'g)
(dk-have! (list 'AND (list 'IN (im-ext 'f) '(FUN RR RR))
            (list 'AND (list 'IN (im-ext 'g) '(FUN RR RR))
                  '(AND (IN a RR) (AND (IN b RR) (< a b)))))
  (lambda () (dk-conj-close! (lambda () (ass)))))
(dk-have! (list 'FORALL 'x (list 'IMPLIES '(IN x (CCINT a b))
            (list 'AND (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (im-ext 'f) 'x)
                       (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (im-ext 'g) 'x))))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (fact 'extend-const-continuous-at 'a 'b 'f z)
      (fact 'extend-const-continuous-at 'a 'b 'g z)
      (dk-conj-close! (lambda () (ass))))))
(let ((huf (im-hyp-univ-of 'f)) (hug (im-hyp-univ-of 'g)))
  (dk-have! (list 'FORALL 'x (list 'IMPLIES '(AND (IN x RR) (AND (< a x) (< x b)))
              (list 'AND (list 'FORSOME 'l (list 'IS-DIFF-AT (im-ext 'f) 'x 'l))
                         (list 'FORSOME 'm (list 'IS-DIFF-AT (im-ext 'g) 'x 'm)))))
    (lambda ()
      (dk-peel!)
      (dk-split-all!)
      (im-in-ooint! 'x)
      (let ((lv (dk-skolem! (dk-apply! huf 'x)))
            (mv (dk-skolem! (dk-apply! hug 'x))))
        (fact 'extend-const-deriv-fwd 'a 'b 'f 'x lv)
        (fact 'extend-const-deriv-fwd 'a 'b 'g 'x mv)
        (dk-conj-close!
         (lambda ()
           (if (dk-contains? (dk-goal) (im-ext 'f)) (ew lv) (ew mv))
           (ass)))))))
(im-values! 'f)
(im-values! 'g)
(let ((th (dk-skolem! (dk-fact! 'generalized-mvt (im-ext 'f) (im-ext 'g) 'a 'b))))
  (dk-split-all!)
  (im-in-ooint! th)
  (let* ((lv (dk-skolem! (dk-pick (lambda (fm)
                                    (and (pair? fm) (eq? (car fm) 'FORSOME)
                                         (dk-contains? fm 'IS-DIFF-AT)))
                                  "the l existential")))
         (mv (dk-skolem! (dk-pick (lambda (fm)
                                    (and (pair? fm) (eq? (car fm) 'FORSOME)
                                         (dk-contains? fm 'IS-DIFF-AT)))
                                  "the m existential"))))
    (dk-split-all!)
    (fact 'extend-const-deriv-bwd 'a 'b 'f th lv)
    (fact 'extend-const-deriv-bwd 'a 'b 'g th mv)
    (ew th)
    (dk-conj-close!
     (lambda ()
       (if (eq? (im-head (dk-goal)) 'IN)
           (ass)
           (begin (ew lv) (ew mv)
                  (dk-conj-close!
                   (lambda ()
                     (if (eq? (im-head (dk-goal)) '=)
                         (begin (im-to-ext! 'f) (im-to-ext! 'g) (ass))
                         (ass))))))))))
(qed 'generalized-mvt-on-interval)
(topic! 'generalized-mvt-on-interval 'analysis)
(alias! 'generalized-mvt-on-interval
        "the generalized mean value theorem for functions on a closed interval")

;;; =====================================================================
;;; 2.13 -- THE MEAN VALUE THEOREM ON [a, b], WITH THE QUOTIENT.
;;;
;;; The notes write f'(theta) = (f(b) - f(a)) / (b - a); the library's `mvt'
;;; concludes l * (b - a) = f(b) - f(a).  The two are one `rr-recip-solve'
;;; apart, and b - a is nonzero because a < b (`rr-pos-ne-zero').
;;; =====================================================================
(sp (make-wff "forall([a in rr, b in rr], a < b implies
   forall([f], f in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(f, x, l))) implies
     forsome([theta in ooint(a,b)],
       forsome([l], has-deriv-at(f, theta, l) and l = (f(b) - f(a)) / (b - a)))))"))
(dk-peel!)
(im-le!)
(im-block! 'f)
(im-cont-univ! 'f)
(im-diff-univ! 'f)
(im-values! 'f)
(dk-have! '(IN a (CCINT a b))
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(dk-have! '(IN b (CCINT a b))
  (lambda () (mac 'ccint-membership) (dk-conj-close! (lambda () (ass)))))
(fact 'fun-apply-type-c 'f '(CCINT a b) 'RR 'a)
(fact 'fun-apply-type-c 'f '(CCINT a b) 'RR 'b)
(fact 'rr-sub-in-rr '(f b) '(f a))
(fact 'rr-sub-in-rr 'b 'a)
(dk-have! '(< 0 (- b a)) (lambda () (dk-ineq! '(IN a RR) '(IN b RR) '(< a b))))
(fact 'rr-pos-ne-zero '(- b a))
(dk-have! '(AND (IN (- b a) RR) (NOT (= (- b a) 0)))
  (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'rr-recip-closed '(- b a))
(dk-have! '(AND (IN (- (f b) (f a)) RR) (IN (recip (- b a)) RR))
  (lambda () (dk-conj-close! (lambda () (ass)))))
(fact 'rr-mul-comm '(- (f b) (f a)) '(recip (- b a)))
(let ((th (dk-skolem! (dk-fact! 'mvt (im-ext 'f) 'a 'b))))
  (dk-split-all!)
  (im-in-ooint! th)
  (let ((lv (dk-skolem! (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORSOME)
                                                   (dk-contains? fm 'IS-DIFF-AT)))
                                 "the l existential"))))
    (dk-split-all!)
    (fact 'extend-const-deriv-bwd 'a 'b 'f th lv)
    (fact 'has-deriv-at-in-rr 'f th lv)
    (dk-have! (list '= '(- (f b) (f a)) (list '* '(- b a) lv))
      (lambda ()
        (im-to-ext! 'f)
        (subst (list '= (list '- (list (im-ext 'f) 'b) (list (im-ext 'f) 'a))
                     (list '* lv '(- b a))))
        (crs)))
    (fact 'rr-recip-solve '(- b a) '(- (f b) (f a)) lv)
    (ew th)
    (dk-conj-close!
     (lambda ()
       (if (eq? (im-head (dk-goal)) 'IN)
           (ass)
           (begin
             (ew lv)
             (dk-conj-close!
              (lambda ()
                (if (eq? (im-head (dk-goal)) '=)
                    (begin
                      ;; the parser desugars `/' at read time, so the stored
                      ;; statement already says (f(b) - f(a)) * recip(b - a)
                      ;; and there is no `binary-divide-def' rewrite to make.
                      (subst '(= (* (- (f b) (f a)) (recip (- b a)))
                                 (* (recip (- b a)) (- (f b) (f a)))))
                      (ass))
                    (ass)))))))))) 
(qed 'mvt-on-interval)
(topic! 'mvt-on-interval 'analysis)
(alias! 'mvt-on-interval
        "the mean value theorem for a function on a closed interval")

;;; =====================================================================
;;; THE THREE BOUNDS, ON [a, b].
;;; =====================================================================

;;; the library's first antecedent for the bounds, which carries m as well.
(define (im-block-m! fn)
  (fact 'extend-const-in-fun 'a 'b fn)
  (dk-have! (list 'AND (list 'IN (im-ext fn) '(FUN RR RR))
                  '(AND (IN a RR) (AND (IN b RR) (AND (IN m RR) (< a b)))))
    (lambda () (dk-conj-close! (lambda () (ass))))))

;;; the library's differentiability hypothesis for the extension, with the
;;; extra conjunct EXTRA(l) beside IS-DIFF-AT.  XV / LV are the binder names
;;; the library's own statement uses, and they must match verbatim.
(define (im-diff-univ-x! fn xv lv extra)
  (let ((hyp (im-hyp-univ-of fn)))
    (dk-have! (list 'FORALL xv
                (list 'IMPLIES (list 'AND (list 'IN xv 'RR)
                                     (list 'AND (list '< 'a xv) (list '< xv 'b)))
                      (list 'FORSOME lv (extra lv))))
      (lambda ()
        (dk-peel!)
        (dk-split-all!)
        (im-in-ooint! xv)
        (let ((w (dk-skolem! (dk-apply! hyp xv))))
          (dk-split-all!)
          (fact 'has-deriv-at-in-rr fn xv w)
          (fact 'extend-const-deriv-fwd 'a 'b fn xv w)
          (ew w)
          (dk-conj-close! (lambda () (ass))))))))

(sp (make-wff "forall([a in rr, b in rr, m in rr], a < b implies
   forall([f], f in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(f, x, l) and l <= m)) implies
     f(b) - f(a) <= m * (b - a)))"))
(dk-peel!)
(im-le!)
(im-block-m! 'f)
(im-cont-univ! 'f)
(im-diff-univ-x! 'f 'x 'l
  (lambda (lv) (list 'AND (list 'IS-DIFF-AT (im-ext 'f) 'x lv) (list '<= lv 'm))))
(im-values! 'f)
(fact 'mvt-upper-bound (im-ext 'f) 'a 'b 'm)
(im-to-ext! 'f)
(ass)
(qed 'mvt-upper-bound-on-interval)
(topic! 'mvt-upper-bound-on-interval 'analysis)
(alias! 'mvt-upper-bound-on-interval
        "the mean value upper bound for a function on a closed interval")

(sp (make-wff "forall([a in rr, b in rr, m in rr], a < b implies
   forall([f], f in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(f, x, l) and m <= l)) implies
     m * (b - a) <= f(b) - f(a)))"))
(dk-peel!)
(im-le!)
(im-block-m! 'f)
(im-cont-univ! 'f)
(im-diff-univ-x! 'f 'x 'l
  (lambda (lv) (list 'AND (list 'IS-DIFF-AT (im-ext 'f) 'x lv) (list '<= 'm lv))))
(im-values! 'f)
(fact 'mvt-lower-bound (im-ext 'f) 'a 'b 'm)
(im-to-ext! 'f)
(ass)
(qed 'mvt-lower-bound-on-interval)
(topic! 'mvt-lower-bound-on-interval 'analysis)
(alias! 'mvt-lower-bound-on-interval
        "the mean value lower bound for a function on a closed interval")

(sp (make-wff "forall([a in rr, b in rr, m in rr], a < b implies
   forall([f], f in fun(ccint(a,b), rr) implies
     is-continuous-on(f, ccint(a,b)) implies
     forall([x in ooint(a,b)], forsome([l], has-deriv-at(f, x, l) and abs(l) <= m))
       implies
     abs(f(b) - f(a)) <= m * (b - a)))"))
(dk-peel!)
(im-le!)
(fact 'extend-const-in-fun 'a 'b 'f)
(dk-have! (list 'FORALL 'x_ (list 'IMPLIES '(IN x_ (CCINT a b))
            (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS (im-ext 'f) 'x_)))
  (lambda ()
    (let ((z (dk-di-var!)))
      (fact 'ccint-elt-in-rr 'a 'b z)
      (fact 'extend-const-continuous-at 'a 'b 'f z)
      (ass))))
(im-diff-univ-x! 'f 'x_ 'l_
  (lambda (lv) (list 'AND (list 'IN lv 'RR)
                     (list 'AND (list 'IS-DIFF-AT (im-ext 'f) 'x_ lv)
                           (list '<= (list 'abs lv) 'm)))))
(im-values! 'f)
(fact 'mvt-abs-bound (im-ext 'f) 'a 'b 'm)
(im-to-ext! 'f)
(ass)
(qed 'mvt-abs-bound-on-interval)
(topic! 'mvt-abs-bound-on-interval 'analysis)
(alias! 'mvt-abs-bound-on-interval
        "the mean value absolute bound for a function on a closed interval")
