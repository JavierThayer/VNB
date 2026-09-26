;;; theorem-library/primitive-uniform-limit.scm -- Dieudonne (8.6.4) on a
;;; compact interval [a,b], with COUNTABLE exceptional sets: A UNIFORM LIMIT
;;; OF PRIMITIVES IS A PRIMITIVE.  Batch 22-B, 2026-09-23.
;;;
;;; THE SOURCE.  Dieudonne (8.6.4), specialised to I = [a,b] and F = R, with
;;; "primitive" in the sense of (8.7) (IS-PRIMITIVE: continuous on [a,b],
;;; derivative f(t) at every t of (a,b) off a denumerable set):  if g_n is a
;;; primitive of f_n, the f_n converge uniformly on [a,b] to f, and (g_n(x_0))
;;; converges, then the g_n converge (uniformly) to a primitive g of f.
;;; The statement here NORMALISES g_n(a) = 0: a family with g_n(a) convergent
;;; is reduced to it by subtracting the constant g_n(a) (pw-antiderivative-sum
;;; with a constant primitive of 0), and the limits then differ by lim g_n(a).
;;; The uniform convergence is spelled out (IS-UNIF-LIMIT-ON is stated for
;;; total functions); nothing new is defined in this file.
;;;
;;; THE FILE IN ORDER.
;;;   (1) countable-union-nn -- a set covered by an NN-indexed family of
;;;       countable sets is countable.  One enumeration per index is CHOSEN
;;;       (choice-axiom on the SEP of the enumerations of puu_ covering
;;;       puu_ n pud_(k), each redirected into puu_ by an IF as in
;;;       countable-subset), then `nn-flatten'.  The family is untyped:
;;;       instantiate it at a vnb-lambda over NN.
;;;   (2) primitive-pair-lipschitz -- the Cauchy estimate: |f1 - f2| <= m on
;;;       [a,b] gives |(g1 - g2)(y) - (g1 - g2)(x)| <= m (y - x) for x < y in
;;;       [a,b]: g1 - g2 is a primitive of f1 - f2 (pw-antiderivative-linear),
;;;       so is its restriction to [x,y] (pw-antiderivative-restrict), and
;;;       (8.5.2) with a countable exceptional set applies there
;;;       (mvi-abs-off-countable-on-interval).
;;;   (3) rr-mul-le-cancel-pos (a c <= m c, c > 0 => a <= m) and
;;;       primitive-pair-lipschitz-abs, the estimate in either order with
;;;       m |y - x|.
;;;   (4) primitive-family-limit -- normalised primitives of a uniformly
;;;       Cauchy family converge on [a,b] to the restriction of a limit fc
;;;       that is CONTINUOUS AT EVERY REAL: the clamped extensions
;;;       G(k) = EXTEND-CONST(g_k, a, b) are uniformly Cauchy on all of RR
;;;       (the estimate at CLAMP(a,b,x) and a), `uniform-cauchy-limit' gives
;;;       fc, `uniform-limit-continuous-at' its continuity.
;;;   (5) primitive-family-deriv-at -- at a t of (a,b) where every g_k has
;;;       derivative f_k(t), IS-DIFF-AT(fc, t, lim f_k(t)): Caratheodory
;;;       witnesses W(k) of G(k) at t (`diff-at-witness-family'); dividing the
;;;       estimate of (3) by |x - t| makes them uniformly Cauchy on [a,b]; and
;;;       `uniform-witness-diff-at' (antiderivable-uniform-limit.scm, the
;;;       everywhere-differentiable model of this file) concludes.
;;;   (6) primitive-uniform-limit -- g = RESTRICT(fc, [a,b]); continuous on
;;;       [a,b] by `cont-on-of-total'; the exceptional set is
;;;       E = {t in [a,b] : some g_k has no derivative f_k(t) at t in (a,b)},
;;;       countable by (1) since its k-th piece lies in g_k's own exceptional
;;;       set; off E, (5) and `has-deriv-at-local' on a ball inside [a,b].
;;;
;;; MECHANICS WORTH KEEPING.
;;; * The clamped family and the Caratheodory witnesses are handled as
;;;   FUNCTION SYMBOLS (a skolemised FORSOME with the value equation
;;;   G(k) == EXTEND-CONST(g_k, a, b)), never as a vnb-lambda: G(k_) inside
;;;   vnb-lambda(k_, nn, G(k_)(x)) is then not a redex, and nothing is beta-
;;;   reduced under the sequence binder.
;;; * CASE FOLDING bit twice in driver `let*'s: `seqg'/`seqG' and `gk'/`Gk'
;;;   are ONE variable each, the second silently shadowing the first (the
;;;   symptom was a lemma instantiated at the wrong term).
;;; * `dk-apply!' detaches to exhaustion and ERRORS at an antecedent that is
;;;   not in context; where an antecedent has to be proved, stop with
;;;   `inst*!' and use `detach-with!' (or the kit's `dk-chain!').
;;;
;;; Helper prefixes: pul- / pu5- / pu6-.  Theorem binders: pu..._ (none used
;;; by a predicate body).  Loads after zero-deriv-off-countable
;;; (mvi-abs-off-countable-on-interval), pw-int-laws-2
;;; (pw-antiderivative-restrict), pw-int-laws-3 (pw-antiderivative-linear),
;;; antiderivable-uniform-limit (uniform-cauchy-limit, uniform-witness-diff-at),
;;; witness-family-choice, regulated-primitive-laws, nn-pairing and
;;; interval-calculus-laws.  No top-level macro is used: compilable.
;;; =====================================================================

(define (pul-head g) (and (pair? g) (car g)))

;;; An IF term on the side the context decides: the kit's (dk-if-branch! TRUE? IFT ass ass).
;;; (pul-if-close! retired 2026-09-25.)

;;; the cover clause "every point of puu_ in pud_(K) is a value of E"
(define (pul-cover k e)
  (list 'FORALL 'puv_
    (list 'IMPLIES '(IN puv_ puu_)
      (list 'IMPLIES (list 'IN 'puv_ (list 'pud_ k))
        (list 'FORSOME 'pun_ (list 'AND '(IN pun_ NN) (list '= 'puv_ (list e 'pun_))))))))
;;; the class of enumerations of puu_ covering puu_ n pud_(K)
(define (pul-enums k) (list 'SEP 'pue_ '(FUN NN puu_) (pul-cover k 'pue_)))
(define (pul-chosen k) (list 'CHOICE (pul-enums k)))

(sp (make-wff "forall([pud_, puu_], puu_ in set implies
   (forall([puk_ in nn], is-countable(pud_(puk_)))) implies
   (forall([puy_ in puu_], forsome([puk_ in nn], puy_ in pud_(puk_)))) implies
   is-countable(puu_))"))
(dk-peel!)
(define pul-h1 (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'IS-COUNTABLE)))
                        "the countability of each piece"))
(define pul-h2 (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'FORSOME)))
                        "the cover by the pieces"))
(use-em '(FORSOME puz_ (IN puz_ puu_))
  ;; ---- puu_ has a point z0, the default value of every enumeration ----
  (lambda ()
    (let* ((z0 (dk-skolem! '(FORSOME puz_ (IN puz_ puu_))))
           (ch (list 'FORALL 'puk_ (list 'IMPLIES '(IN puk_ NN)
                  (list 'IN (pul-chosen 'puk_) (pul-enums 'puk_))))))
      ;; for each k an enumeration of puu_ covering puu_ n pud_(k) is CHOSEN
      (dk-have! ch
        (lambda ()
          (let* ((k (dk-di-var!))
                 (cnt (dk-apply! pul-h1 k))
                 (parts (dk-split! (dk-fact! 'countable-cases (list 'pud_ k))))
                 (cs (dk-pick (dk-head? 'OR) "the two cases of countability")))
            (use-cases cs
              ;; pud_(k) is empty: the constant enumeration, the cover is vacuous
              (lambda ()
                (let ((w (list 'VNB-LAMBDA 'pum_ 'NN z0)))
                  (choose-mem! (pul-enums k) w
                    (lambda ()
                      (in-sep!
                        (lambda () (dk-lam-t!) (dk-di-var!) (ass))
                        (lambda ()
                          (dk-peel!)
                          (let ((y (cadr (dk-pick (lambda (f) (and (eq? (pul-head f) 'IN)
                                                                   (equal? (caddr f) (list 'pud_ k))))
                                                  "y in pud_(k)"))))
                            (dk-have! (list 'IN y 'EMPTY-SET)
                              (lambda () (subst (list '= 'EMPTY-SET (list 'pud_ k))) (ass)))
                            (fact 'empty-set-has-no-members y)
                            (ai (list 'NOT (list 'IN y 'EMPTY-SET))))))))
                  (ass)))
              ;; pud_(k) has an enumeration e: redirect it into puu_ by an IF
              (lambda ()
                (let* ((e (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the enumeration")))
                       (cov (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f e)))
                                     "the covering clause"))
                       (w (list 'VNB-LAMBDA 'pum_ 'NN
                                (list 'IF (list 'IN (list e 'pum_) 'puu_) (list e 'pum_) z0))))
                  (choose-mem! (pul-enums k) w
                    (lambda ()
                      (in-sep!
                        (lambda ()
                          (dk-lam-t!)
                          (let* ((m (dk-di-var!))
                                 (em (list e m))
                                 (ift (list 'IF (list 'IN em 'puu_) em z0)))
                            (fact 'fun-apply-type-c e 'NN (list 'pud_ k) m)
                            (use-em (list 'IN em 'puu_)
                              (lambda () (dk-if-branch! #t ift ass ass))
                              (lambda () (dk-if-branch! #f ift ass ass)))))
                        (lambda ()
                          (dk-peel!)
                          (let* ((y (cadr (dk-pick (lambda (f) (and (eq? (pul-head f) 'IN)
                                                                    (equal? (caddr f) (list 'pud_ k))))
                                                   "y in pud_(k)")))
                                 (n (dk-skolem! (dk-apply! cov y)))
                                 (enn (list e n))
                                 (ift (list 'IF (list 'IN enn 'puu_) enn z0)))
                            (dk-have! (list 'IN enn 'puu_)
                              (lambda () (subst (list '= enn y)) (ass)))
                            (ew n)
                            (dk-conj-close!
                              (lambda ()
                                (if (eq? (pul-head (dk-goal)) '=)
                                    (begin (dk-lam-b!) (dk-if-branch! #t ift ass ass))
                                    (ass)))))))))
                  (ass)))))))
      (let ((h (list 'VNB-LAMBDA 'puk_ 'NN (pul-chosen 'puk_))))
        (dk-have! (list 'IN h '(FUN NN (FUN NN puu_)))
          (lambda ()
            (dk-lam-t!)
            (let* ((k (dk-di-var!))
                   (mem (dk-apply! ch k)))
              (sep-me mem)
              (ass))))
        (let* ((e (dk-skolem! (dk-fact! 'nn-flatten 'puu_ h)))
               (flat (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f e)))
                              "the flattening clause")))
          (dk-have! (list 'FORALL 'puw_
                      (list 'IMPLIES '(IN puw_ puu_)
                        (list 'FORSOME 'pun_ (list 'AND '(IN pun_ NN)
                                                  (list '= 'puw_ (list e 'pun_))))))
            (lambda ()
              (let* ((y (dk-di-var!))
                     (k (dk-skolem! (dk-apply! pul-h2 y)))
                     (mem (dk-apply! ch k))
                     (parts (dk-landed (lambda () (sep-me mem))))
                     (covk (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL)
                                                     (dk-contains? f (pul-chosen k))))
                                    "the cover by the chosen enumeration"))
                     (n (dk-skolem! (dk-apply! covk y)))
                     (m (dk-skolem! (dk-apply! flat k n)))
                     (eq (dk-pick (lambda (f) (and (eq? (pul-head f) '=) (equal? (cadr f) (list e m))))
                                  "e(m) = h(k)(n)")))
                (ew m)
                (dk-conj-close!
                  (lambda ()
                    (if (eq? (pul-head (dk-goal)) '=)
                        (begin (subst eq) (dk-lam-b!) (ass))
                        (ass)))))))
          (fact 'countable-of-enum 'puu_ e)
          (ass)))))
  ;; ---- puu_ is empty: a subset of the empty set ----
  (lambda ()
    (dk-have! '(SUBSET puu_ EMPTY-SET)
      (lambda ()
        (let ((z (subset-by-element!)))
          (dk-have! '(FORSOME puz_ (IN puz_ puu_)) (lambda () (ew z) (ass)))
          (ai '(NOT (FORSOME puz_ (IN puz_ puu_)))))))
    (fact 'countable-empty)
    (fact 'countable-subset 'puu_ 'EMPTY-SET)
    (ass)))
(qed 'countable-union-nn)
(topic! 'countable-union-nn 'combinatorial)
;;; =====================================================================
;;; (2) THE CAUCHY ESTIMATE.  Two primitives whose integrands differ by at
;;; most m on [a,b] have a difference that is m-Lipschitz on [a,b]
;;; (Dieudonne (8.5.2) applied to g1 - g2 on [x,y], through the restriction
;;; of the primitive g1 - g2 of f1 - f2).
;;; =====================================================================

(define (pul-typ! f dom x) (fact 'fun-apply-type-c f dom 'RR x))

(sp (make-wff "forall([a, b, pug1_, puf1_, pug2_, puf2_, pum_ in rr],
   is-primitive(pug1_, puf1_, a, b) implies is-primitive(pug2_, puf2_, a, b) implies
   (forall([pux_ in ccint(a, b)], abs(puf1_(pux_) - puf2_(pux_)) <= pum_)) implies
   forall([pux_ in ccint(a, b), puy_ in ccint(a, b)], pux_ < puy_ implies
     abs((pug1_(puy_) - pug2_(puy_)) - (pug1_(pux_) - pug2_(pux_))) <= pum_ * (puy_ - pux_)))"))
(dk-peel!)
(define pul-bd (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'ABS)))
                        "the integrand bound"))
(dk-split! (dk-fact! 'primitive-endpoints 'pug1_ 'puf1_ 'a 'b))
(fact 'primitive-in-fun 'pug1_ 'puf1_ 'a 'b)
(fact 'primitive-in-fun 'pug2_ 'puf2_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pug1_ 'puf1_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pug2_ 'puf2_ 'a 'b)
(dk-split! (dk-fact! 'ccint-parts 'a 'b 'pux_))
(dk-split! (dk-fact! 'ccint-parts 'a 'b 'puy_))
(define pul-cab '(CCINT a b))
(define pul-cxy '(CCINT pux_ puy_))
(define pul-hh (list 'VNB-LAMBDA 'puz_ pul-cab '(+ (* 1 (pug1_ puz_)) (* -1 (pug2_ puz_)))))
(define pul-ch (list 'VNB-LAMBDA 'puz_ pul-cab '(+ (* 1 (puf1_ puz_)) (* -1 (puf2_ puz_)))))
(fact 'fun-domain-in-set pul-cab 'RR 'pug1_)
(dk-have! '(IN -1 RR) (lambda () (arith)))
(fact 'rr-one-in)
(define (pul-type-lam! lam g1 g2)
  (dk-have! (list 'IN lam (list 'FUN pul-cab 'RR))
    (lambda ()
      (dk-lam-t!)
      (let ((z (dk-di-var!)))
        (pul-typ! g1 pul-cab z)
        (pul-typ! g2 pul-cab z)
        (in-rr)))))
(pul-type-lam! pul-hh 'pug1_ 'pug2_)
(pul-type-lam! pul-ch 'puf1_ 'puf2_)
(define (pul-value-eq! lam g1 g2)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ pul-cab)
              (list '== (list lam 'pay_)
                    (list '+ (list '* 1 (list g1 'pay_)) (list '* -1 (list g2 'pay_))))))
    (lambda () (dk-di-var!) (dk-lam-b!) (qrfl))))
(pul-value-eq! pul-hh 'pug1_ 'pug2_)
(pul-value-eq! pul-ch 'puf1_ 'puf2_)
;; g1 - g2 is a primitive of f1 - f2 on [a,b] ...
(dk-split!
 (dk-apply! (dk-apply! (dk-apply! (dk-fact! 'pw-antiderivative-linear 'a 'b) 1 -1)
                       'pug1_ 'pug2_ 'puf1_ 'puf2_)
            pul-hh pul-ch))
;; ... and so is its restriction to [x,y]
(define pul-rh (list 'RESTRICT pul-hh pul-cxy))
(define pul-rc (list 'RESTRICT pul-ch pul-cxy))
(dk-have! '(<= pux_ puy_) (lambda () (dk-ineq! '(< pux_ puy_) '(IN pux_ RR) '(IN puy_ RR))))
(define pul-rp (dk-fact! 'pw-antiderivative-restrict 'a 'b 'pux_ 'puy_ pul-hh pul-ch))
(fact 'primitive-in-fun pul-rh pul-rc 'pux_ 'puy_)
(fact 'primitive-continuous pul-rh pul-rc 'pux_ 'puy_)
(define pul-dd (dk-skolem! (dk-fact! 'primitive-exceptional-set pul-rh pul-rc 'pux_ 'puy_)))
(define pul-ex (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pul-dd)
                                         (dk-contains? f 'HAS-DERIV-AT)))
                        "the derivative off the exceptional set"))
(fact 'ccint-subset-ccint 'a 'b 'pux_ 'puy_)
(fact 'ooint-subset-ccint 'pux_ 'puy_)
(define pul-mv
  (inst*! (dk-apply! (dk-fact! 'mvi-abs-off-countable-on-interval 'pux_ 'puy_ 'pum_) pul-rh)
          pul-dd))
(if (not (eq? (pul-head pul-mv) 'IMPLIES))
    (error "pul: mvi instance did not stop at the derivative clause" pul-mv))
;; the derivative of the restriction is bounded by m off the exceptional set
(dk-have! (cadr pul-mv)
  (lambda ()
    (let* ((t (dk-di-var!)))
      (dk-peel!)
      (fact 'ooint-elt-in-rr 'pux_ 'puy_ t)
      (fact 'subset-mem-fwd '(OOINT pux_ puy_) pul-cxy t)
      (fact 'subset-mem-fwd pul-cxy pul-cab t)
      (dk-apply! pul-ex t)
      (ew (list pul-rc t))
      (dk-conj-close!
        (lambda ()
          (if (eq? (pul-head (dk-goal)) 'HAS-DERIV-AT)
              (ass)
              (begin
                (fact 'restrict-apply pul-ch pul-cxy t)
                (subst (list '== (list pul-rc t) (list pul-ch t)))
                (dk-lam-b!)
                (pul-typ! 'puf1_ pul-cab t)
                (pul-typ! 'puf2_ pul-cab t)
                (let ((eqn (list '= (list '+ (list '* 1 (list 'puf1_ t)) (list '* -1 (list 'puf2_ t)))
                                 (list '- (list 'puf1_ t) (list 'puf2_ t)))))
                  (dk-have! eqn (lambda () (crs)))
                  (subst eqn))
                (dk-apply! pul-bd t)
                (ass))))))))
(define pul-mv2 (dk-apply! pul-mv))
;; rewrite the two values of the restriction back to g1 - g2
(dk-have! '(IN puy_ (CCINT pux_ puy_))
  (lambda () (mac 'ccint-membership)
    (dk-conj-close! (lambda () (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                                   (dk-ineq! '(< pux_ puy_) '(IN pux_ RR) '(IN puy_ RR)))))))
(dk-have! '(IN pux_ (CCINT pux_ puy_))
  (lambda () (mac 'ccint-membership)
    (dk-conj-close! (lambda () (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                                   (dk-ineq! '(< pux_ puy_) '(IN pux_ RR) '(IN puy_ RR)))))))
(fact 'restrict-apply pul-hh pul-cxy 'puy_)
(fact 'restrict-apply pul-hh pul-cxy 'pux_)
(for-each (lambda (z) (pul-typ! 'pug1_ pul-cab z) (pul-typ! 'pug2_ pul-cab z)) '(pux_ puy_))
(define pul-deq
  (list '= '(- (- (pug1_ puy_) (pug2_ puy_)) (- (pug1_ pux_) (pug2_ pux_)))
        (list '- (list pul-rh 'puy_) (list pul-rh 'pux_))))
(dk-have! pul-deq
  (lambda ()
    (subst (list '== (list pul-rh 'puy_) (list pul-hh 'puy_)))
    (subst (list '== (list pul-rh 'pux_) (list pul-hh 'pux_)))
    (dk-lam-b!)
    (crs)))
(subst pul-deq)
(ass)
(qed 'primitive-pair-lipschitz)
(topic! 'primitive-pair-lipschitz 'analysis)
;;; =====================================================================
;;; (3) The cancellation of a positive factor in an inequality, and the
;;; Cauchy estimate in both orders.
;;; =====================================================================

(sp (make-wff "forall([pula_ in rr, pulc_ in rr, pulm_ in rr], 0 < pulc_ implies
   pula_ * pulc_ <= pulm_ * pulc_ implies pula_ <= pulm_)"))
(dk-peel!)
(for-each (lambda (pr) (dk-have! (list 'AND (list 'IN (car pr) 'RR) (list 'IN (cadr pr) 'RR)))
                       (fact 'rr-mul-closed (car pr) (cadr pr)))
          '((pula_ pulc_) (pulm_ pulc_)))
(fact 'rr-sub-in-rr 'pulm_ 'pula_)
(dk-have! '(AND (IN pulc_ RR) (IN (- pulm_ pula_) RR)))
(fact 'rr-mul-closed 'pulc_ '(- pulm_ pula_))
(dk-have! '(= (* pulc_ (- pulm_ pula_)) (- (* pulm_ pulc_) (* pula_ pulc_))) (lambda () (crs)))
(dk-have! '(<= 0 (* pulc_ (- pulm_ pula_)))
  (lambda ()
    (dk-ineq! '(<= (* pula_ pulc_) (* pulm_ pulc_))
              '(= (* pulc_ (- pulm_ pula_)) (- (* pulm_ pulc_) (* pula_ pulc_)))
              '(IN (* pula_ pulc_) RR) '(IN (* pulm_ pulc_) RR)
              '(IN (* pulc_ (- pulm_ pula_)) RR))))
(fact 'rr-nonneg-cancel-pos 'pulc_ '(- pulm_ pula_))
(dk-ineq! '(<= 0 (- pulm_ pula_)) '(IN pula_ RR) '(IN pulm_ RR))
(qed 'rr-mul-le-cancel-pos)
(topic! 'rr-mul-le-cancel-pos 'inequalities)

;;; the three cases x < y, x = y, y < x of two reals
(define (pul-trichotomy! x y lt eq gt)
  (use-cases (dk-fact! 'rr-lt-trichotomy x y) lt eq gt))

(sp (make-wff "forall([a, b, pug1_, puf1_, pug2_, puf2_, pum_ in rr],
   is-primitive(pug1_, puf1_, a, b) implies is-primitive(pug2_, puf2_, a, b) implies
   (forall([pux_ in ccint(a, b)], abs(puf1_(pux_) - puf2_(pux_)) <= pum_)) implies
   forall([pux_ in ccint(a, b), puy_ in ccint(a, b)],
     abs((pug1_(puy_) - pug2_(puy_)) - (pug1_(pux_) - pug2_(pux_))) <= pum_ * abs(puy_ - pux_)))"))
(dk-peel!)
(dk-split! (dk-fact! 'primitive-endpoints 'pug1_ 'puf1_ 'a 'b))
(fact 'primitive-in-fun 'pug1_ 'puf1_ 'a 'b)
(fact 'primitive-in-fun 'pug2_ 'puf2_ 'a 'b)
(dk-split! (dk-fact! 'ccint-parts 'a 'b 'pux_))
(dk-split! (dk-fact! 'ccint-parts 'a 'b 'puy_))
(for-each (lambda (z) (pul-typ! 'pug1_ '(CCINT a b) z) (pul-typ! 'pug2_ '(CCINT a b) z)) '(pux_ puy_))
(define pul-dx '(- (pug1_ pux_) (pug2_ pux_)))
(define pul-dy '(- (pug1_ puy_) (pug2_ puy_)))
(dk-real! pul-dx)
(dk-real! pul-dy)
(define pul-l (dk-fact! 'primitive-pair-lipschitz 'a 'b 'pug1_ 'puf1_ 'pug2_ 'puf2_ 'pum_))
(pul-trichotomy! 'pux_ 'puy_
  (lambda ()
    (dk-apply! pul-l 'pux_ 'puy_)
    (dk-real! '(- puy_ pux_))
    (dk-have! '(<= 0 (- puy_ pux_)) (lambda () (dk-ineq! '(< pux_ puy_) '(IN pux_ RR) '(IN puy_ RR))))
    (fact 'rr-abs-of-nonneg '(- puy_ pux_))
    (subst '(= (ABS (- puy_ pux_)) (- puy_ pux_)))
    (ass))
  (lambda ()
    (subst '(= puy_ pux_))
    (let ((e1 (list '= (list '- pul-dx pul-dx) 0)))
      (dk-have! e1 (lambda () (crs)))
      (subst e1))
    (dk-have! '(= (- pux_ pux_) 0) (lambda () (crs)))
    (subst '(= (- pux_ pux_) 0))
    (fact 'rr-abs-zero-value)
    (subst '(= (ABS 0) 0))
    (dk-have! '(= (* pum_ 0) 0) (lambda () (crs)))
    (subst '(= (* pum_ 0) 0))
    (dk-ineq!))
  (lambda ()
    (dk-apply! pul-l 'puy_ 'pux_)
    (fact 'rr-abs-sub-sym pul-dy pul-dx)
    (subst (list '= (list 'ABS (list '- pul-dy pul-dx)) (list 'ABS (list '- pul-dx pul-dy))))
    (fact 'rr-abs-sub-sym 'puy_ 'pux_)
    (subst '(= (ABS (- puy_ pux_)) (ABS (- pux_ puy_))))
    (dk-real! '(- pux_ puy_))
    (dk-have! '(<= 0 (- pux_ puy_)) (lambda () (dk-ineq! '(< puy_ pux_) '(IN pux_ RR) '(IN puy_ RR))))
    (fact 'rr-abs-of-nonneg '(- pux_ puy_))
    (subst '(= (ABS (- pux_ puy_)) (- pux_ puy_)))
    (ass)))
(qed 'primitive-pair-lipschitz-abs)
(topic! 'primitive-pair-lipschitz-abs 'analysis)
;;; =====================================================================
;;; (4) THE LIMIT FUNCTION.  Normalised primitives g_k(a) = 0 of a uniformly
;;; Cauchy family f_k are uniformly Cauchy on [a,b] (the Cauchy estimate at
;;; x and a); their clamped extensions EXTEND-CONST(g_k, a, b) are then
;;; uniformly Cauchy on ALL of RR, and `uniform-cauchy-limit' hands back a
;;; limit fc, continuous at every real by `uniform-limit-continuous-at'.
;;; =====================================================================

;;; (IN X (CCINT LO HI)) from the premises PS (x's typing among them)
(define (pul-in-ccint! x lo hi . ps)
  (dk-have! (list 'IN x (list 'CCINT lo hi))
    (lambda ()
      (mac 'ccint-membership)
      (dk-conj-close!
        (lambda ()
          (if (eq? (pul-head (dk-goal)) 'IN) (ass) (apply dk-ineq! ps)))))))

;;; f(x) in B, loudly
(define (pul-typ-strict! f dom cod x)
  (let ((r (dk-fact! 'fun-apply-type-c f dom cod x)))
    (if (not (equal? r (list 'IN (list f x) cod)))
        (error "pul-typ-strict!: typing did not detach" (expression->string r)
               (map expression->string (dk-asms))))
    r))

;;; the POS-RR hypothesis landed by a peel
(define (pul-pos-var landed)
  (let ((p (any-pred (dk-head? 'POS-RR) landed)))
    (if p (cadr p) (error "pul-pos-var: no POS-RR landed" (map expression->string landed)))))

;;; the clamped family EXTEND-CONST(gfam(k), a, b), k in NN, as a FUNCTION
;;; SYMBOL G with its value equation G(k) == EXTEND-CONST(gfam(k), a, b): an
;;; opaque symbol applied at an index is never a redex, so nothing has to be
;;; beta-reduced under the binder of a sequence (vnb-lambda(k_, nn, G(k_)(x))).
;;; Needs (<= a b) and gfam's typing in context.  Returns (G . value-equation).
(define (pul-clamped!)          ; the kit's `dk-abstract!' (2026-09-25)
  (dk-abstract! 'NN '(FUN RR RR)
    (lambda (k) (list 'EXTEND-CONST (list 'gfam k) 'a 'b))
    (lambda (k)
      (fact 'fun-apply-type-c 'gfam 'NN '(FUN (CCINT a b) RR) k)
      (fact 'extend-const-in-fun 'a 'b (list 'gfam k))
      (ass))))

;;; rewrite G(k) in the goal to EXTEND-CONST(gfam(k), a, b)
(define (pul-unG-with! geq k) (subst (dk-apply! geq k)))

(define pul-fc-stmt "forall([a in rr, b in rr], a < b implies
   forall([gfam in fun(nn, fun(ccint(a, b), rr)), ffam in fun(nn, fun(ccint(a, b), rr))],
   (forall([puk_ in nn], is-primitive(gfam(puk_), ffam(puk_), a, b))) implies
   (forall([eps], pos-rr(eps) implies forsome([pun_ in nn], forall([puk_ in nn, pul_ in nn],
      pun_ <= puk_ implies pun_ <= pul_ implies
      forall([pux_ in ccint(a, b)], abs((ffam(puk_))(pux_) - (ffam(pul_))(pux_)) <= eps))))) implies
   (forall([puk_ in nn], (gfam(puk_))(a) = 0)) implies
   forsome([pufc_ in fun(rr, rr)],
     (forall([pux_ in ccint(a, b)],
        converges-to(rr-ms, vnb-lambda(puk_, nn, (gfam(puk_))(pux_)), pufc_(pux_)))) and
     forall([put_ in rr], is-continuous-at(rr-ms, rr-ms, pufc_, put_)))))")

(sp (make-wff pul-fc-stmt))
(dk-peel!)
(define pul-cab '(CCINT a b))
(define pul-fcab (list 'FUN pul-cab 'RR))
(define pul-pr (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'IS-PRIMITIVE)))
                        "the primitives"))
(define pul-fcy (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'POS-RR)))
                         "the uniform Cauchy hypothesis"))
(define pul-z (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f '(= ((gfam puk_) a) 0))))
                       "the normalisation"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(< a b) '(IN a RR) '(IN b RR))))
(pul-in-ccint! 'a 'a 'b '(< a b) '(IN a RR) '(IN b RR))

;; ---- the clamped family G, as a function symbol with its value equation ----
(define pul-g-pair (pul-clamped!))
(define pul-g (car pul-g-pair))
(define pul-geq (cdr pul-g-pair))
(define (pul-unG! k) (pul-unG-with! pul-geq k))
(define (pul-gk k) (list 'gfam k))
(define (pul-fk k) (list 'ffam k))

;; ---- the clamped family is uniformly Cauchy on RR ----
(define pul-ucl (dk-fact! 'uniform-cauchy-limit pul-g 'RR))
(define pul-lim
  (detach-with! pul-ucl
    (lambda ()
      (let* ((e (pul-pos-var (dk-peel!)))
             (_ (dk-pos-parts! e))
             (_2 (fact 'rr-sub-in-rr 'b 'a))
             (_3 (dk-have! '(<= 0 (- b a)) (lambda () (dk-ineq! '(< a b) '(IN a RR) '(IN b RR)))))
             (d (dk-skolem! (dk-fact! 'rr-scale-eps '(- b a) e)))
             (sc (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f d)))
                          "the scaling clause"))
             (_4 (dk-pos-parts! d))
             (n (dk-skolem! (dk-apply! pul-fcy d)))
             (fn (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f n)
                                           (dk-contains? f 'ffam)))
                          "the Cauchy clause at d")))
        (ew n)
        (dk-conj-close!
          (lambda ()
            (if (eq? (pul-head (dk-goal)) 'IN)
                (ass)
                (begin
                  (dk-peel!)
                  ;; goal: |G(k)(x) - G(l)(x)| <= e ; the indices off the GOAL
                  (let* ((df (cadr (cadr (dk-goal))))
                         (k (cadr (car (cadr df))))
                         (l (cadr (car (caddr df))))
                         (x (cadr (cadr df)))
                         (c (list 'CLAMP 'a 'b x)))
                    (pul-unG! k)
                    (pul-unG! l)
                    (subst (dk-fact! 'extend-const-value (pul-gk k) 'a 'b x))
                    (subst (dk-fact! 'extend-const-value (pul-gk l) 'a 'b x))
                    (fact 'clamp-in-ccint 'a 'b x)
                    (fact 'clamp-in-rr 'a 'b x)
                    (dk-split! (dk-fact! 'ccint-parts 'a 'b c))
                    (dk-apply! pul-pr k)
                    (dk-apply! pul-pr l)
                    (dk-apply! fn k l)
                    (let* ((lip (dk-fact! 'primitive-pair-lipschitz-abs 'a 'b
                                          (pul-gk k) (pul-fk k) (pul-gk l) (pul-fk l) d))
                           (bd (dk-apply! lip 'a c))
                           (big (cadr (cadr bd)))
                           (gc (list '- (list (pul-gk k) c) (list (pul-gk l) c))))
                      (fact 'fun-apply-type-c 'gfam 'NN pul-fcab k)
                      (fact 'fun-apply-type-c 'gfam 'NN pul-fcab l)
                      (for-each (lambda (g) (for-each (lambda (z) (pul-typ! g pul-cab z)) (list 'a c)))
                                (list (pul-gk k) (pul-gk l)))
                      (dk-apply! pul-z k)
                      (dk-apply! pul-z l)
                      (let ((e1 (list '= gc big)))
                        (dk-have! e1
                          (lambda ()
                            (subst (list '= (list (pul-gk k) 'a) 0))
                            (subst (list '= (list (pul-gk l) 'a) 0))
                            (crs)))
                        (subst e1))
                      ;; |c - a| <= b - a, then the chain
                      (dk-real! (list '- c 'a))
                      (fact 'rr-abs-closed (list '- c 'a))
                      (dk-have! (list '<= 0 (list '- c 'a))
                        (lambda () (dk-ineq! (list '<= 'a c) '(IN a RR) (list 'IN c 'RR))))
                      (fact 'rr-abs-of-nonneg (list '- c 'a))
                      (dk-have! (list '<= (list 'ABS (list '- c 'a)) '(- b a))
                        (lambda () (dk-ineq! (list '= (list 'ABS (list '- c 'a)) (list '- c 'a))
                                             (list '<= c 'b) '(IN a RR) '(IN b RR) (list 'IN c 'RR)
                                             (list 'IN (list 'ABS (list '- c 'a)) 'RR))))
                      (dk-have! (list '<= 0 d) (lambda () (dk-ineq! (list '< 0 d) (list 'IN d 'RR))))
                      (fact 'rr-mul-le-right (list 'ABS (list '- c 'a)) '(- b a) d)
                      (dk-have! (list '= (list '* d (list 'ABS (list '- c 'a)))
                                      (list '* (list 'ABS (list '- c 'a)) d))
                        (lambda () (crs)))
                      (fact 'rr-leq-reflexive d)
                      (dk-apply! sc d)
                      (dk-real! big)
                      (fact 'rr-abs-closed big)
                      (dk-le-chain! (list 'ABS big)
                                    (list '* d (list 'ABS (list '- c 'a)))
                                    (list '* (list 'ABS (list '- c 'a)) d)
                                    (list '* '(- b a) d)
                                    e)))))))))))
(define pul-fc (dk-skolem! pul-lim))
(define pul-pt (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pul-fc)
                                         (dk-contains? f 'CONVERGES-TO)))
                        "pointwise convergence"))
(define pul-un (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pul-fc)
                                         (dk-contains? f 'POS-RR)))
                        "uniform convergence"))
(ew pul-fc)
(dk-conj-close!
  (lambda ()
    (let ((gl (dk-goal)))
      (cond
        ((eq? (pul-head gl) 'IN) (ass))
        ((dk-contains? gl 'CONVERGES-TO)
         ;; the limit of the unclamped values on [a,b]
         (let* ((x (dk-di-var!)))
           (dk-split! (dk-fact! 'ccint-parts 'a 'b x))
           (dk-apply! pul-pt x)
           (let* ((sqsmall (list 'VNB-LAMBDA 'puk_ 'NN (list (list 'gfam 'puk_) x)))
                  (sqbig (list 'VNB-LAMBDA 'puj_ 'NN (list (list pul-g 'puj_) x))))
             (dk-have! (list 'IN sqsmall '(FUN NN RR))
               (lambda () (dk-lam-t!)
                 (let ((j (dk-di-var!)))
                   (fact 'fun-apply-type-c 'gfam 'NN pul-fcab j)
                   (pul-typ! (pul-gk j) pul-cab x)
                   (ass))))
             (dk-have! (list 'IN sqbig '(FUN NN RR))
               (lambda () (dk-lam-t!)
                 (let ((j (dk-di-var!)))
                   (pul-typ-strict! pul-g 'NN '(FUN RR RR) j)
                   (pul-typ-strict! (list pul-g j) 'RR 'RR x)
(ass))))
             (fact 'fun-apply-type-c pul-fc 'RR 'RR x)
             (dk-have! (list 'CONVERGES-TO 'RR-MS sqbig (list pul-fc x)) (lambda () (ass)))
             (let ((pe (dk-fact! 'rr-limit-ptwise-eq sqbig sqsmall (list pul-fc x))))
               (dk-apply! (detach-with! pe
                 (lambda ()
                   (let ((j (dk-di-var!)))
                     (dk-lam-b!)
                     (pul-unG! j)
                     (subst (dk-fact! 'extend-const-ccint-fixes 'a 'b x (pul-gk j)))
                     (fact 'fun-apply-type-c 'gfam 'NN pul-fcab j)
                     (pul-typ! (pul-gk j) pul-cab x)
                     (rfl)))))
               (ass)))))
        (#t
         ;; continuity at every real
         (let* ((t (dk-di-var!)))
           (fact 'rr-one-in)
           (dk-have! '(< 0 1) (lambda () (dk-ineq!)))
           (let ((uc (dk-fact! 'uniform-limit-continuous-at pul-g pul-fc t 1)))
             (let ((uc2 (detach-with! uc
                          (lambda ()
                            (let ((k (dk-di-var!)))
                              (pul-unG! k)
                              (dk-apply! pul-pr k)
                              (fact 'fun-apply-type-c 'gfam 'NN pul-fcab k)
                              (fact 'primitive-continuous (pul-gk k) (pul-fk k) 'a 'b)
                              (dk-apply! (dk-fact! 'extend-const-continuous-at 'a 'b) (pul-gk k) t)
                              (ass))))))
               (detach-with! uc2
                 (lambda ()
                   (let* ((e (pul-pos-var (dk-peel!)))
                          (n (dk-skolem! (dk-apply! pul-un e)))
                          (un (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f n)
                                                        (dk-contains? f pul-fc)))
                                       "the uniform clause at e")))
                     (ew n)
                     (dk-conj-close!
                       (lambda ()
                         (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                             (begin
                               (dk-peel!)
                               (let* ((df (cadr (cadr (dk-goal))))
                                      (x (cadr (cadr df)))
                                      (k (cadr (car (caddr df)))))
                                 (dk-apply! un k x)
                                 (ass)))))))))
               (ass)))))))))
(qed 'primitive-family-limit)
(topic! 'primitive-family-limit 'analysis)
;;; =====================================================================
;;; (5) THE DERIVATIVE OF THE LIMIT at an interior point t where every g_k
;;; has derivative f_k(t).  Caratheodory witnesses W(k) of the clamped
;;; G(k) at t (`diff-at-witness-family'); the Cauchy estimate divided by
;;; |x - t| makes them uniformly Cauchy on [a,b]; `uniform-witness-diff-at'
;;; (antiderivable-uniform-limit.scm) concludes.
;;; =====================================================================

;;; An IMPLIES chain is run by the kit's (dk-chain! F PROVERS), PROVERS a list of
;;; (PRED . THUNK).  (pul-chain! retired 2026-09-25.)

(define (pul-has? . subs) (lambda (f) (every (lambda (s) (dk-contains? f s)) subs)))

(define pul-da-stmt "forall([a in rr, b in rr], a < b implies
   forall([gfam in fun(nn, fun(ccint(a, b), rr)), ffam in fun(nn, fun(ccint(a, b), rr)),
           pufc_ in fun(rr, rr), put_ in ooint(a, b), pulv_ in rr],
   (forall([puk_ in nn], is-primitive(gfam(puk_), ffam(puk_), a, b))) implies
   (forall([eps], pos-rr(eps) implies forsome([pun_ in nn], forall([puk_ in nn, pul_ in nn],
      pun_ <= puk_ implies pun_ <= pul_ implies
      forall([pux_ in ccint(a, b)], abs((ffam(puk_))(pux_) - (ffam(pul_))(pux_)) <= eps))))) implies
   (forall([pux_ in ccint(a, b)],
      converges-to(rr-ms, vnb-lambda(puk_, nn, (gfam(puk_))(pux_)), pufc_(pux_)))) implies
   (forall([puk_ in nn], has-deriv-at(gfam(puk_), put_, (ffam(puk_))(put_)))) implies
   converges-to(rr-ms, vnb-lambda(puk_, nn, (ffam(puk_))(put_)), pulv_) implies
   is-diff-at(pufc_, put_, pulv_)))")

(sp (make-wff pul-da-stmt))
(dk-peel!)
(define pu5-pr (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'IS-PRIMITIVE)))
                        "the primitives"))
(define pu5-fcy (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'POS-RR)))
                         "the uniform Cauchy hypothesis"))
(define pu5-cv (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'pufc_)))
                        "the convergence of the primitives"))
(define pu5-hd (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'HAS-DERIV-AT)))
                        "the derivatives at t"))
(define pu5-hf (dk-pick (lambda (f) (and (eq? (pul-head f) 'CONVERGES-TO) (dk-contains? f 'ffam)))
                        "the convergence of the integrands at t"))
(define pu5-cab '(CCINT a b))
(define pu5-fcab (list 'FUN pu5-cab 'RR))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(< a b) '(IN a RR) '(IN b RR))))
(fact 'ooint-elt-in-rr 'a 'b 'put_)
(fact 'ooint-subset-ccint 'a 'b)
(fact 'subset-mem-fwd '(OOINT a b) pu5-cab 'put_)
(define pu5-g-pair (pul-clamped!))
(define pu5-g (car pu5-g-pair))
(define pu5-geq (cdr pu5-g-pair))
(define (pu5-unG! k) (pul-unG-with! pu5-geq k))
;;; (= G(k)(z) gfam(k)(z)) for z in [a,b]
(define (pu5-gval-goal! k z)
  (pu5-unG! k)
  (subst (dk-fact! 'extend-const-ccint-fixes 'a 'b z (list 'gfam k)))
  (rfl))
(define (pu5-gval! k z)
  (fact 'fun-apply-type-c 'gfam 'NN pu5-fcab k)
  (pul-typ! (list 'gfam k) pu5-cab z)
  (dk-have! (list '= (list (list pu5-g k) z) (list (list 'gfam k) z))
    (lambda () (pu5-gval-goal! k z))))

;; ---- the Caratheodory witnesses of G(k) at t ----
(define pu5-lf '(VNB-LAMBDA puk_ NN ((ffam puk_) put_)))
(dk-have! (list 'IN pu5-lf '(FUN NN RR))
  (lambda ()
    (dk-lam-t!)
    (let ((j (dk-di-var!)))
      (fact 'fun-apply-type-c 'ffam 'NN pu5-fcab j)
      (pul-typ! (list 'ffam j) pu5-cab 'put_)
      (ass))))
(define pu5-wex
  (detach-with! (dk-fact! 'diff-at-witness-family pu5-g pu5-lf 'put_)
    (lambda ()
      (let ((k (dk-di-var!)))
        (dk-lam-b!)
        (pu5-unG! k)
        (fact 'fun-apply-type-c 'gfam 'NN pu5-fcab k)
        (dk-apply! pu5-hd k)
        (dk-apply! (dk-fact! 'extend-const-deriv-fwd 'a 'b) (list 'gfam k) 'put_ (list (list 'ffam k) 'put_))
        (ass)))))
(define pu5-w (dk-skolem! pu5-wex))
(define pu5-wc (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pu5-w)))
                        "the witness clause"))
(define (pu5-wparts! k) (dk-split-all! (list (dk-apply! pu5-wc k))))
(define (pu5-wid parts) (any-pred (dk-head? 'FORALL) parts))

;; ---- a radius: the ball of radius r about t lies in [a,b]; rho = r/2 ----
(define pu5-r (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b 'put_)))
(dk-pos-parts! pu5-r)
(define pu5-rho (dk-halve! pu5-r))
(define pu5-ball (list 'OOINT (list '- 'put_ pu5-r) (list '+ 'put_ pu5-r)))

;;; |W(k)(x) - W(l)(x)| <= e at x /= t (LT? says x < t): the Cauchy estimate
;;; |D(x) - D(t)| <= e |x - t| for D = g_k - g_l, the Caratheodory identities
;;; D(x) - D(t) = (W(k)(x) - W(l)(x)) (x - t), and the cancellation of |x - t|.
(define (pu5-wbound! k l x e bd pk pl aa dd lt?)
  (let* ((gk (list 'gfam k)) (gl (list 'gfam l))
         (gkx (list gk x)) (glx (list gl x)) (gkt (list gk 'put_)) (glt (list gl 'put_))
         (ck (list pu5-g k)) (cl (list pu5-g l))
         (ckx (list ck x)) (clx (list cl x)) (ckt (list ck 'put_)) (clt (list cl 'put_))
         (wkx (cadr aa)) (wlx (caddr aa))
         (big (list '- (list '- gkx glx) (list '- gkt glt))))
    (for-each (lambda (j) (for-each (lambda (z) (pu5-gval! j z)) (list x 'put_))) (list k l))
    (for-each (lambda (j) (pul-typ-strict! pu5-g 'NN '(FUN RR RR) j)) (list k l))
    (for-each (lambda (gg) (for-each (lambda (z) (pul-typ-strict! gg 'RR 'RR z)) (list x 'put_)))
              (list ck cl))
    (dk-apply! pu5-pr k)
    (dk-apply! pu5-pr l)
    (let* ((lip (dk-fact! 'primitive-pair-lipschitz-abs 'a 'b gk (list 'ffam k) gl (list 'ffam l) e))
           (l1 (dk-apply! lip 'put_ x))
           (idk (dk-apply! (pu5-wid pk) x))
           (idl (dk-apply! (pu5-wid pl) x))
           (e2 (list '= big (list '* aa dd))))
      (dk-real! dd)
      (dk-real! aa)
      (dk-have! e2
        (lambda ()
          (for-each (lambda (pr) (subst (list '= (car pr) (cadr pr))))
                    (list (list gkx ckx) (list glx clx) (list gkt ckt) (list glt clt)))
          (let ((e2a (list '= (list '- (list '- ckx clx) (list '- ckt clt))
                           (list '- (list '- ckx ckt) (list '- clx clt)))))
            (dk-have! e2a (lambda () (crs)))
            (subst e2a))
          (subst idk)
          (subst idl)
          (crs)))
      (dk-real! big)
      (fact 'rr-abs-closed big)
      (fact 'rr-abs-closed aa)
      (fact 'rr-abs-closed dd)
      (dk-real! (list '* aa dd))
      (fact 'rr-abs-closed (list '* aa dd))
      (dk-have! (list 'AND (list 'IN aa 'RR) (list 'IN dd 'RR)))
      (fact 'rr-abs-mult aa dd)
      (dk-have! (list '= (list 'ABS big) (list 'ABS (list '* aa dd)))
        (lambda () (subst e2) (rfl)))
      (dk-le-chain! (list '* (list 'ABS aa) (list 'ABS dd))
                    (list 'ABS (list '* aa dd))
                    (list 'ABS big)
                    (list '* e (list 'ABS dd)))
      (if lt?
          (begin
            (dk-have! (list '< dd 0) (lambda () (dk-ineq! (list '< x 'put_) (list 'IN x 'RR) '(IN put_ RR))))
            (fact 'rr-abs-of-neg dd)
            (dk-have! (list '< 0 (list 'ABS dd))
              (lambda () (dk-ineq! (list '= (list 'ABS dd) (list '- dd)) (list '< x 'put_)
                                   (list 'IN x 'RR) '(IN put_ RR) (list 'IN (list 'ABS dd) 'RR)))))
          (begin
            (dk-have! (list '<= 0 dd) (lambda () (dk-ineq! (list '< 'put_ x) (list 'IN x 'RR) '(IN put_ RR))))
            (fact 'rr-abs-of-nonneg dd)
            (dk-have! (list '< 0 (list 'ABS dd))
              (lambda () (dk-ineq! (list '= (list 'ABS dd) dd) (list '< 'put_ x)
                                   (list 'IN x 'RR) '(IN put_ RR) (list 'IN (list 'ABS dd) 'RR))))))
      (fact 'rr-mul-le-cancel-pos (list 'ABS aa) (list 'ABS dd) e)
      (ass))))

(define pu5-u0 (dk-fact! 'uniform-witness-diff-at pu5-g pu5-w 'pufc_ 'pulv_))
(define pu5-u1 (inst*! pu5-u0 'a 'b 'put_ pu5-rho))
(define pu5-done
  (dk-chain! pu5-u1 (list
     ;; |y - t| <= rho puts y in [a,b]
     (cons (pul-has? pu5-rho 'CCINT)
       (lambda ()
         (let ((y (dk-di-var!)))
           (dk-peel!)
           (dk-real! (list '- y 'put_))
           (dk-split! (dk-fact! 'rr-abs-le-parts (list '- y 'put_) pu5-rho))
           (dk-have! (list 'IN y pu5-ball)
             (lambda ()
               (mac 'ooint-membership)
               (dk-conj-close!
                 (lambda ()
                   (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                       (dk-ineq! (list '<= (list '- pu5-rho) (list '- y 'put_))
                                 (list '<= (list '- y 'put_) pu5-rho)
                                 (list '= (list '+ pu5-rho pu5-rho) pu5-r)
                                 (list '< 0 pu5-rho) (list 'IN y 'RR) '(IN put_ RR)
                                 (list 'IN pu5-rho 'RR) (list 'IN pu5-r 'RR)))))))
           (fact 'subset-mem-fwd pu5-ball pu5-cab y)
           (ass))))
     ;; each witness is continuous at t
     (cons (pul-has? 'IS-CONTINUOUS-AT)
       (lambda ()
         (let ((k (dk-di-var!)))
           (pu5-wparts! k)
           (ass))))
     ;; the Caratheodory identities on [a,b]
     (cons (pul-has? pu5-g '*)
       (lambda ()
         (let* ((k (dk-di-var!))
                (y (dk-di-var!)))
           (dk-peel!)
           (dk-apply! (pu5-wid (pu5-wparts! k)) y)
           (ass))))
     ;; G(k)(y) -> fc(y) on [a,b]
     (cons (pul-has? pu5-g 'CONVERGES-TO)
       (lambda ()
         (let* ((y (dk-di-var!)))
           (dk-peel!)
           (dk-split! (dk-fact! 'ccint-parts 'a 'b y))
           (let* ((big (caddr (dk-goal)))
                  (cvs (dk-apply! pu5-cv y))
                  (small (caddr cvs)))
             (dk-have! (list 'IN small '(FUN NN RR))
               (lambda () (dk-lam-t!)
                 (let ((j (dk-di-var!)))
                   (fact 'fun-apply-type-c 'gfam 'NN pu5-fcab j)
                   (pul-typ! (list 'gfam j) pu5-cab y)
                   (ass))))
             (dk-have! (list 'IN big '(FUN NN RR))
               (lambda () (dk-lam-t!)
                 (let ((j (dk-di-var!)))
                   (pul-typ-strict! pu5-g 'NN '(FUN RR RR) j)
                   (pul-typ-strict! (list pu5-g j) 'RR 'RR y)
                   (ass))))
             (fact 'fun-apply-type-c 'pufc_ 'RR 'RR y)
             (dk-apply!
              (detach-with! (dk-fact! 'rr-limit-ptwise-eq small big (list 'pufc_ y))
                (lambda ()
                  (let ((j (dk-di-var!)))
                    (dk-lam-b!)
                    (fact 'fun-apply-type-c 'gfam 'NN pu5-fcab j)
                    (pul-typ! (list 'gfam j) pu5-cab y)
                    (pu5-gval-goal! j y)))))
             (ass)))))
     ;; the witnesses are uniformly Cauchy on [a,b]
     (cons (pul-has? 'POS-RR pu5-w)
       (lambda ()
         (let* ((e (pul-pos-var (dk-peel!)))
                (_ (dk-pos-parts! e))
                (n (dk-skolem! (dk-apply! pu5-fcy e)))
                (fn (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f n)
                                              (dk-contains? f 'ffam)))
                             "the Cauchy clause at e")))
           (ew n)
           (dk-conj-close!
             (lambda ()
               (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                   (begin
                     (dk-peel!)
                     (let* ((df (cadr (cadr (dk-goal))))
                            (k (cadr (car (cadr df))))
                            (l (cadr (car (caddr df))))
                            (x (cadr (cadr df)))
                            (pk (pu5-wparts! k))
                            (pl (pu5-wparts! l))
                            (bd (dk-apply! fn k l))
                            (wkx (list (list pu5-w k) x)) (wlx (list (list pu5-w l) x))
                            (aa (list '- wkx wlx))
                            (dd (list '- x 'put_)))
                       (dk-split! (dk-fact! 'ccint-parts 'a 'b x))
                       (pul-typ-strict! pu5-w 'NN '(FUN RR RR) k)
                       (pul-typ-strict! pu5-w 'NN '(FUN RR RR) l)
                       (pul-typ-strict! (list pu5-w k) 'RR 'RR x)
                       (pul-typ-strict! (list pu5-w l) 'RR 'RR x)
                       (pul-trichotomy! x 'put_
                         (lambda () (pu5-wbound! k l x e bd pk pl aa dd #t))
                         (lambda ()
                           ;; x = t: the witnesses take the values f_k(t), f_l(t)
                           (subst (list '= x 'put_))
                           (for-each
                             (lambda (parts)
                               (let ((eqv (any-pred (lambda (f) (and (eq? (pul-head f) '=)
                                                                     (pair? (cadr f)) (equal? (cdr (cadr f)) '(put_))))
                                                    parts)))
                                 (dk-lam-b-h! eqv)))
                             (list pk pl))
                           (for-each
                             (lambda (j)
                               (subst (dk-pick (lambda (f) (and (eq? (pul-head f) '=)
                                                                (equal? (cadr f) (list (list pu5-w j) 'put_))))
                                               "the witness value at t")))
                             (list k l))
                           (dk-apply! bd 'put_)
                           (ass))
                         (lambda () (pu5-wbound! k l x e bd pk pl aa dd #f)))))))))))
     ;; W(k)(t) = f_k(t) -> lv
     (cons (pul-has? pu5-w 'CONVERGES-TO)
       (lambda ()
         (let* ((big (caddr (dk-goal)))
                (small (caddr pu5-hf)))
           (dk-have! (list 'IN big '(FUN NN RR))
             (lambda () (dk-lam-t!)
               (let ((j (dk-di-var!)))
                 (pul-typ-strict! pu5-w 'NN '(FUN RR RR) j)
                 (pul-typ-strict! (list pu5-w j) 'RR 'RR 'put_)
                 (ass))))
           (dk-apply!
            (detach-with! (dk-fact! 'rr-limit-ptwise-eq small big 'pulv_)
              (lambda ()
                (let* ((j (dk-di-var!))
                       (pj (pu5-wparts! j))
                       (eqv (any-pred (lambda (f) (and (eq? (pul-head f) '=)
                                                       (pair? (cadr f)) (equal? (cdr (cadr f)) '(put_))))
                                      pj)))
                  (dk-lam-b!)
                  (dk-lam-b-h! eqv)
                  (ass)))))
           (ass)))))))
(ass)
(qed 'primitive-family-deriv-at)
(topic! 'primitive-family-deriv-at 'analysis)
;;; =====================================================================
;;; (6) DIEUDONNE (8.6.4) ON [a,b] WITH COUNTABLE EXCEPTIONAL SETS.
;;; =====================================================================

(define pul-main-stmt "forall([a in rr, b in rr], a < b implies
   forall([gfam in fun(nn, fun(ccint(a, b), rr)), ffam in fun(nn, fun(ccint(a, b), rr)),
           f in fun(ccint(a, b), rr)],
   (forall([puk_ in nn], is-primitive(gfam(puk_), ffam(puk_), a, b))) implies
   (forall([eps], pos-rr(eps) implies forsome([pun_ in nn], forall([puk_ in nn], pun_ <= puk_ implies
      forall([pux_ in ccint(a, b)], abs((ffam(puk_))(pux_) - f(pux_)) <= eps))))) implies
   (forall([puk_ in nn], (gfam(puk_))(a) = 0)) implies
   forsome([pug_], is-primitive(pug_, f, a, b) and
     forall([pux_ in ccint(a, b)],
       converges-to(rr-ms, vnb-lambda(puk_, nn, (gfam(puk_))(pux_)), pug_(pux_))))))")

(sp (make-wff pul-main-stmt))
(dk-peel!)
(define pu6-cab '(CCINT a b))
(define pu6-fcab (list 'FUN pu6-cab 'RR))
(define pu6-pr (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'IS-PRIMITIVE)))
                        "the primitives"))
(define pu6-uc (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'POS-RR)))
                        "the uniform convergence"))
(dk-have! '(<= a b) (lambda () (dk-ineq! '(< a b) '(IN a RR) '(IN b RR))))
(fact 'ccint-subset-rr 'a 'b)

;; ---- the integrands are uniformly Cauchy; the limit fc of the primitives ----
(define pu6-lim
  (dk-apply!
   (detach-with! (dk-fact! 'primitive-family-limit 'a 'b 'gfam 'ffam)
     (lambda ()
       (let* ((e (pul-pos-var (dk-peel!)))
              (h (dk-halve! e))
              (n (dk-skolem! (dk-apply! pu6-uc h)))
              (un (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f n)
                                            (dk-contains? f 'ffam)))
                           "the uniform clause at e/2")))
         (dk-pos-parts! e)
         (ew n)
         (dk-conj-close!
           (lambda ()
             (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                 (begin
                   (dk-peel!)
                   (let* ((df (cadr (cadr (dk-goal))))
                          (k (cadr (car (cadr df))))
                          (l (cadr (car (caddr df))))
                          (x (cadr (cadr df)))
                          (fkx (list (list 'ffam k) x))
                          (flx (list (list 'ffam l) x))
                          (fx (list 'f x)))
                     (for-each (lambda (j) (fact 'fun-apply-type-c 'ffam 'NN pu6-fcab j)
                                           (pul-typ! (list 'ffam j) pu6-cab x))
                               (list k l))
                     (pul-typ! 'f pu6-cab x)
                     (dk-apply! un k x)
                     (dk-apply! un l x)
                     (dk-real! (list '- fkx fx))
                     (dk-real! (list '- flx fx))
                     (dk-real! (list '- fkx flx))
                     (dk-split! (dk-fact! 'rr-abs-le-parts (list '- fkx fx) h
                                          ))
                     (dk-split! (dk-fact! 'rr-abs-le-parts (list '- flx fx) h))
                     (let ((ps (list (list 'IN fkx 'RR) (list 'IN flx 'RR) (list 'IN fx 'RR)
                                     (list 'IN h 'RR) (list 'IN e 'RR) (list '= (list '+ h h) e)
                                     (list '<= (list '- h) (list '- fkx fx)) (list '<= (list '- fkx fx) h)
                                     (list '<= (list '- h) (list '- flx fx)) (list '<= (list '- flx fx) h))))
                       (dk-have! (list '<= (list '- e) (list '- fkx flx)) (lambda () (apply dk-ineq! ps)))
                       (dk-have! (list '<= (list '- fkx flx) e) (lambda () (apply dk-ineq! ps))))
                     (fact 'rr-abs-le-of-parts (list '- fkx flx) e)
                     (ass)))))))))))
(define pu6-fc (dk-skolem! pu6-lim))
(define pu6-cv (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pu6-fc)
                                         (dk-contains? f 'CONVERGES-TO)))
                        "the convergence of the primitives"))
(define pu6-ct (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f pu6-fc)
                                         (dk-contains? f 'IS-CONTINUOUS-AT)))
                        "the continuity of the limit"))
(define pu6-fcy (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f 'POS-RR)
                                          (dk-contains? f 'pul_)))
                         "the uniform Cauchy property"))
(define pu6-g (list 'RESTRICT pu6-fc pu6-cab))
(fact 'restrict-in-fun pu6-fc 'RR 'RR pu6-cab)
;;; g(z) == fc(z) on [a,b]
(define (pu6-gval! z) (dk-fact! 'restrict-apply pu6-fc pu6-cab z))

;; ---- the exceptional set: the points of (a,b) where SOME g_k fails ----
(define (pu6-bad k v) (list 'AND (list 'IN v '(OOINT a b))
                            (list 'NOT (list 'HAS-DERIV-AT (list 'gfam k) v (list (list 'ffam k) v)))))
(define pu6-e (list 'SEP 'pus_ pu6-cab
                    (list 'FORSOME 'puk_ (list 'AND '(IN puk_ NN) (pu6-bad 'puk_ 'pus_)))))
(define pu6-dl (list 'VNB-LAMBDA 'puk_ 'NN (list 'SEP 'pus_ pu6-cab (pu6-bad 'puk_ 'pus_))))
(fact 'fun-domain-in-set pu6-cab 'RR 'f)
(dk-have! (list 'IN pu6-e 'SET) (lambda () (sep-set) (ass)))
(dk-have! (list 'IS-COUNTABLE pu6-e)
  (lambda ()
    (let ((cu (dk-fact! 'countable-union-nn pu6-dl pu6-e)))
      (dk-chain! cu (list
         (cons (pul-has? 'IS-COUNTABLE)
           (lambda ()
             (let* ((k (dk-di-var!))
                    (_ (dk-lam-b!))
                    (sk (cadr (dk-goal)))
                    (_2 (dk-apply! pu6-pr k))
                    (d (dk-skolem! (dk-fact! 'primitive-exceptional-set (list 'gfam k) (list 'ffam k) 'a 'b)))
                    (exk (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f d)
                                                   (dk-contains? f 'HAS-DERIV-AT)))
                                  "the derivative off the exceptional set")))
               (dk-have! (list 'SUBSET sk d)
                 (lambda ()
                   (let* ((z (subset-by-element!)))
                     (dk-split-all! (dk-landed (lambda () (sep-me (list 'IN z sk)))))
                     (use-em (list 'IN z d)
                       (lambda () (ass))
                       (lambda ()
                         (let ((hd (dk-apply! exk z)))
                           (ai (list 'NOT hd))))))))
               (fact 'countable-subset sk d)
               (ass))))
         (cons (pul-has? 'FORSOME)
           (lambda ()
             (let* ((y (dk-di-var!))
                    (parts (dk-landed (lambda () (sep-me (list 'IN y pu6-e)))))
                    (k (dk-skolem! (dk-pick (dk-head? 'FORSOME) "the failing index"))))
               (ew k)
               (dk-conj-close!
                 (lambda ()
                   (if (equal? (dk-goal) (list 'IN k 'NN)) (ass)
                       (begin
                         (dk-lam-b!)
                         (in-sep! (lambda () (ass))
                                  (lambda () (dk-conj-close! (lambda () (ass))))))))))))))
      (ass))))

;; ---- the derivative of g at a point of (a,b) off the exceptional set ----
(define (pu6-deriv!)
  (let* ((t (dk-di-var!))
         (_ (dk-peel!))
         (ft (list 'f t)))
    (fact 'ooint-elt-in-rr 'a 'b t)
    (fact 'ooint-subset-ccint 'a 'b)
    (fact 'subset-mem-fwd '(OOINT a b) pu6-cab t)
    (pul-typ! 'f pu6-cab t)
    ;; every g_k has derivative f_k(t) at t: else t is exceptional
    (dk-have! (list 'FORALL 'puk_ (list 'IMPLIES '(IN puk_ NN)
                (list 'HAS-DERIV-AT '(gfam puk_) t (list '(ffam puk_) t))))
      (lambda ()
        (let* ((k (dk-di-var!))
               (hd (dk-goal)))
          (use-em hd
            (lambda () (ass))
            (lambda ()
              (dk-have! (list 'IN t pu6-e)
                (lambda ()
                  (in-sep! (lambda () (ass))
                           (lambda ()
                             (ew k)
                             (dk-conj-close! (lambda () (ass)))))))
              (ai (list 'NOT (list 'IN t pu6-e))))))))
    ;; f_k(t) -> f(t)
    (let ((sq (list 'VNB-LAMBDA 'puk_ 'NN (list '(ffam puk_) t))))
      (dk-have! (list 'IN sq '(FUN NN RR))
        (lambda () (dk-lam-t!)
          (let ((j (dk-di-var!)))
            (fact 'fun-apply-type-c 'ffam 'NN pu6-fcab j)
            (pul-typ! (list 'ffam j) pu6-cab t)
            (ass))))
      (dk-apply!
       (detach-with! (dk-fact! 'rr-converges-to-abs sq ft)
         (lambda ()
           (let* ((e (pul-pos-var (dk-peel!)))
                  (n (dk-skolem! (dk-apply! pu6-uc e)))
                  (un (dk-pick (lambda (f) (and (eq? (pul-head f) 'FORALL) (dk-contains? f n)
                                                (dk-contains? f 'ffam)))
                               "the uniform clause at e")))
             (ew n)
             (dk-conj-close!
               (lambda ()
                 (if (eq? (pul-head (dk-goal)) 'IN) (ass)
                     (let ((k (dk-di-var!)))
                       (dk-peel!)
                       (dk-lam-b!)
                       (dk-apply! un k t)
                       (ass))))))))))
    ;; the limit fc is differentiable at t with derivative f(t) ...
    (dk-apply! (dk-fact! 'primitive-family-deriv-at 'a 'b 'gfam 'ffam) pu6-fc t ft)
    (fact 'fun-apply-type-c pu6-fc 'RR 'RR t)
    (dk-have! (list 'HAS-DERIV-AT pu6-fc t ft)
      (lambda () (mac 'has-deriv-at-iff-diff-at) (ass)))
    ;; ... and g agrees with fc on a ball about t inside [a,b]
    (let* ((r (dk-skolem! (dk-fact! 'ooint-inner-radius 'a 'b t)))
           (ball (list 'OOINT (list '- t r) (list '+ t r))))
      (fact 'restrict-in-fun pu6-g pu6-cab 'RR ball)
      (dk-have! (list 'FORALL 'puh_ (list 'IMPLIES (list 'IN 'puh_ ball)
                  (list '== (list pu6-g 'puh_) (list pu6-fc 'puh_))))
        (lambda ()
          (let ((z (dk-di-var!)))
            (fact 'subset-mem-fwd ball pu6-cab z)
            (pu6-gval! z)
            (ass))))
      (dk-apply! (dk-fact! 'has-deriv-at-local r) pu6-g pu6-fc t ft)
      (ass))))

(ew pu6-g)
(dk-conj-close!
  (lambda ()
    (let ((gl (dk-goal)))
      (cond
        ((eq? (pul-head gl) 'FORALL)
         ;; the primitives converge to g on [a,b]
         (let ((x (dk-di-var!)))
           (subst (pu6-gval! x))
           (dk-apply! pu6-cv x)
           (ass)))
        (#t
         (mac 'IS-PRIMITIVE)
         (dk-conj-close!
           (lambda ()
             (let ((g2 (dk-goal)))
               (cond
                 ((eq? (pul-head g2) 'IS-CONTINUOUS-ON)
                  (let ((ct (dk-fact! 'cont-on-of-total pu6-cab pu6-fc)))
                    (dk-apply! (detach-with! (inst*! ct pu6-g)
                      (lambda ()
                        (let ((z (dk-di-var!)))
                          (fact 'subset-mem-fwd pu6-cab 'RR z)
                          (fact 'fun-apply-type-c pu6-fc 'RR 'RR z)
                          (subst (pu6-gval! z))
                          (rfl)))))
                    (ass)))
                 ((eq? (pul-head g2) 'FORSOME)
                  (ew pu6-e)
                  (dk-conj-close!
                    (lambda ()
                      (let ((g3 (dk-goal)))
                        (cond
                          ((eq? (pul-head g3) 'IS-COUNTABLE) (ass))
                          ((eq? (pul-head g3) 'SUBSET)
                           (let ((z (subset-by-element!)))
                             (sep-me (list 'IN z pu6-e))
                             (ass)))
                          (#t (pu6-deriv!)))))))
                 (#t (ass)))))))))))
(qed 'primitive-uniform-limit)
(topic! 'primitive-uniform-limit 'analysis)
