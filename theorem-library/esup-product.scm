;;; ====================================================================
;;; theorem-library/esup-product.scm -- THE ESUP PRODUCT LAW in [0, +inf], THE
;;; INTEGRAL OF c f FOR c = +inf, and THE PRODUCT MEASURE OF A RECTANGLE WITH
;;; ARBITRARY (possibly infinite) SIDES.
;;; Agent ESUP-PROD, 2026-10-18 (scratchpad/triage/ESUP-PROD.md).  Library: measure.
;;; Helper prefix esp-.  No vocabulary.  9 theorems, every one `modulo 0'; no
;;; support, warrant!, stamp or add-axiom!.
;;;
;;; SOURCE.  Thayer, Construction of Measures, Def. 3.8 (p. 23): rho(A x B) = mu(A) nu(B).
;;; product-measure-rectangle here has no finiteness hypothesis.  (product-measure.scm had
;;; proved it for FINITE mu(aa), nu(bb) under the same name; that form was retired at the
;;; wiring of 2026-10-20, and this statement, written as product-measure-rectangle-general,
;;; took the name.)
;;;
;;; THE THEOREMS:
;;;   rps-monotone-step-implies-le   u(n) <= u(n+1) for all n  ==>  u nondecreasing, in [0, +inf]
;;;   etimes-mono-star-left          s <= t  ==>  s w <= t w            (s, t, w in [0, +inf])
;;;   etimes-mono-star               p <= q, s <= t  ==>  p s <= q t     (in [0, +inf])
;;;   esup-etimes-ge-star            w sup m <= sup (w m), every w in [0, +inf]
;;;                                  (esup-etimes-ge: w real)
;;;   esup-etimes-eq                 THE ESUP PRODUCT LAW: u, v nondecreasing in [0, +inf]
;;;                                  ==>  sup_n u(n) v(n) = (sup u)(sup v)
;;;   esup-nn-identity               g(n) = n  ==>  sup_n g(n) = +inf
;;;   esup-etimes-nn-pos-inf         h(n) = n t  ==>  sup_n h(n) = +inf t
;;;   integral-homogeneous-star      integral(c f) = c integral(f), every c in [0, +inf]
;;;                                  (integral-homogeneous: c real)
;;;   product-measure-rectangle           rho(aa x bb) = mu(aa) nu(bb), no finiteness
;;;
;;; THE 0 * inf = 0 CONVENTION.  esup-etimes-eq needs NO guard beyond monotonicity:
;;; if sup u = 0 then every u(n) = 0 and both sides are 0 (a_n = 0, b_n -> inf:
;;; left sup 0 = 0, right 0 * inf = 0); if sup u > 0 then u(n) >= c > 0 eventually, and
;;; when sup v = +inf the products are unbounded.  Monotonicity of BOTH sequences is
;;; needed: u = 1, 0, 1, 0, ...; v = 0, 1, 0, 1, ...: left 0, right 1; and u(n) = 1/(n+1)
;;; (decreasing), v(n) = n + 1: left 1, right 1 * inf = inf.
;;;
;;; THE ROUTE TO THE RECTANGLE.  Not FUBINI-1's section-5 route (continuity from below
;;; on a sigma-finite exhaustion), but its alternative: integral(c f) = c integral(f) for
;;; c = +inf.  n f increases pointwise to +inf f (esup-etimes-nn-pos-inf at f(x)), so
;;; monotone convergence gives integral(+inf f) = sup_n n integral(f) = +inf integral(f).
;;; Then x |-> nu((aa x bb)_x) = nu(bb) 1_aa(x) integrates to nu(bb) mu(aa) whatever
;;; nu(bb) is.  Shorter, and the theorem needs neither finiteness nor sigma-finiteness
;;; (the continuity route needs product-measure-is-measure, hence sigma-finite mu, nu).
;;;
;;; LOAD WINDOW.  After "theorem-library/product-measure" (load.scm 3596): it cites
;;; product-measure-apply, x-section-measure-type, x-section-measure-apply,
;;; x-section-rectangle-in / -out, rectangle-in-product-sigma, integral-congruence-ptwise and
;;; ptwise-sup-apply from there; ptwise-scale-value (lp-inequalities, 3590);
;;; ptwise-scale-measurable (real-integral, 3565); monotone-convergence and
;;; esup-etimes-ge, esup-lt-witness (integral-convergence, 3554); integral-homogeneous,
;;; integral-in, integral-indicator, etimes-mono-real-left (integral-laws, 3440); earlier
;;; core files.  Nothing cites this file.  No top-level macro: it may be compiled.
;;; ====================================================================

;;; =====================================================================
;;; (0) file-local kit.  Prefix esp-.  Copied (renamed) from
;;;     theorem-library/integral-convergence.scm (icv-) and product-measure.scm (pms-).
;;; =====================================================================

(define (esp-keep-prop! . keepers)
  (let ((leaf (proof-state-focus *ps*)))
    (apply dk-only! keepers)
    (if (not (sequent-node-grounded? leaf)) (prop))))

(define (esp-and! p q)
  (dk-have! (list 'AND p q) (lambda () (dk-conj-close! dk-ass!))))
(define (esp-and3! p q r)
  (dk-have! (list 'AND p (list 'AND q r)) (lambda () (dk-conj-close! dk-ass!))))

;;; Split on tm in RR-POS-STAR: REAL-BODY with (IN tm RR), (<= 0 tm) in
;;; context, INF-BODY with (= tm POS-INF).  (icv-star-cases!)
(define (esp-real-case tm) (list 'AND (list 'IN tm 'RR) (list '<= 0 tm)))
(define (esp-inf-case  tm) (list '= tm 'POS-INF))
(define (esp-star-cases! tm real-body inf-body)
  (have! (list 'OR (esp-real-case tm) (esp-inf-case tm))
         (lambda ()
           (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
             (esp-keep-prop! inst (list 'IN tm 'RR-POS-STAR)))))
  (use-cases (list (esp-real-case tm) (esp-inf-case tm))
    (lambda () (dk-split! (esp-real-case tm)) (real-body))
    inf-body))

;;; (IN tm RR-POS-STAR) from (IN tm RR), (<= 0 tm) in context.  (icv-rps!)
(define (esp-rps! tm)
  (if (not (dk-asm? (list 'IN tm 'RR-POS-STAR)))
      (dk-have! (list 'IN tm 'RR-POS-STAR)
        (lambda ()
          (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
            (esp-keep-prop! inst (list 'IN tm 'RR) (list '<= 0 tm)))))))

;;; (IN 0 RR-POS-STAR)
(define (esp-zero-rps!)
  (if (not (dk-asm? '(IN 0 RR-POS-STAR)))
      (begin
        (fact 'nn-zero-in)
        (fact 'nn-in-rr 0)
        (fact 'nn-zero-le 0)
        (esp-rps! 0))))

;;; (NOT (= c 0)) from (< 0 c).  (icv-nz-of-pos!)
(define (esp-nz-of-pos! c)
  (if (not (dk-asm? (list 'NOT (list '= c 0))))
      (dk-have! (list 'NOT (list '= c 0))
        (lambda ()
          (di)
          (fact 'equality-symmetry c 0)
          (let ((iff (dk-fact! '< 0 c)))
            (esp-keep-prop! iff (list '< 0 c) (list '= 0 c)))))))

;;; (< 0 c) from (<= 0 c) and (NOT (= c 0)).  (icv-pos!)
(define (esp-pos! c)
  (if (not (dk-asm? (list '< 0 c)))
      (dk-have! (list '< 0 c)
        (lambda ()
          (mac '<)
          (dk-conj-close!
            (lambda ()
              (if (equal? (dk-goal) (list '<= 0 c))
                  (ass)
                  (begin
                    (di)
                    (fact 'equality-symmetry 0 c)
                    (esp-keep-prop! (list '= c 0) (list 'NOT (list '= c 0)))))))))))

;;; (IN (etimes a b) RR-POS-STAR), a, b typed in RR-POS-STAR in context
(define (esp-et-type! a b)
  (let ((g (list 'IN (list 'etimes a b) 'RR-POS-STAR)))
    (if (not (dk-asm? g))
        (begin
          (esp-and! (list 'IN a 'RR-POS-STAR) (list 'IN b 'RR-POS-STAR))
          (fact 'etimes-closed a b)))))

;;; (= (etimes a b) (etimes b a)), a, b typed in RR-POS-STAR in context
(define (esp-comm! a b)
  (let ((g (list '= (list 'etimes a b) (list 'etimes b a))))
    (if (not (dk-asm? g))
        (begin
          (esp-and! (list 'IN a 'RR-POS-STAR) (list 'IN b 'RR-POS-STAR))
          (fact 'etimes-comm a b)))
    g))

;;; x <= z from x <= y, y <= z, all typed in RR-POS-STAR in context
(define (esp-trans! x y z)
  (let ((g (list '<= x z)))
    (if (not (dk-asm? g))
        (begin
          (esp-and3! (list 'IN x 'RR-POS-STAR) (list 'IN y 'RR-POS-STAR) (list 'IN z 'RR-POS-STAR))
          (esp-and! (list '<= x y) (list '<= y z))
          (fact 'rr-pos-star-le-trans x y z)))
    g))

;;; (SUBSET (IMAGE u NN) RR-POS-STAR) and (IN (ESUP ..) RR-POS-STAR); u in FUN(NN, RR-POS-STAR)
;;; in context.  Returns the ESUP term.  (icv-seq-sup!)
(define (esp-seq-sup! u)
  (let ((img (list 'IMAGE u 'NN)))
    (if (not (dk-asm? (list 'SUBSET img 'RR-POS-STAR)))
        (dk-have! (list 'SUBSET img 'RR-POS-STAR)
          (lambda ()
            (mac 'subset-def)
            (let ((v (dk-di-var!)))
              (fact 'image-subset-codomain 'NN 'RR-POS-STAR u v)
              (ass)))))
    (if (not (dk-asm? (list 'IN (list 'ESUP img) 'RR-POS-STAR)))
        (fact 'esup-in img))
    (list 'ESUP img)))

;;; From (IN x (IMAGE phi d)) in context: land (IN n d) and phi(n) = x, beta-reduced
;;; when phi is a lambda; return n.  (icv-img-elt!)
(define (esp-img-elt! phi d x)
  (let ((iff (dk-fact! 'image-membership-iff phi d x)))
    (ai iff)
    (detach! (list 'IMPLIES (cadr iff) (caddr iff)))
    (let ((n (dk-skolem! (dk-ctx-form (caddr iff)))))
      (if (and (pair? phi) (eq? (car phi) 'VNB-LAMBDA))
          (dk-lam-b-h! (dk-ctx-form (list '= (list phi n) x))))
      n)))

;;; tm = phi(k) is in IMAGE(phi, NN): (IN tm RR-POS-STAR), (IN k NN) in context.
;;; (icv-in-image!, with the beta made conditional: phi may be a symbol)
(define (esp-in-image! phi kv tm)
  (let* ((iff (dk-fact! 'image-membership-iff phi 'NN tm))
         (lhs (cadr iff)) (rhs (caddr iff)))
    (dk-have! rhs
      (lambda ()
        (dk-conj-close!
          (lambda ()
            (let ((g (dk-goal)))
              (cond ((equal? g (list 'IN tm 'SET))
                     (fact 'membership-implies-sethood tm 'RR-POS-STAR) (ass))
                    ((eq? (car g) 'FORSOME)
                     (ew kv)
                     (dk-conj-close!
                       (lambda ()
                         (cond ((dk-ass!))
                               ((dk--redex? (dk-goal))
                                (if (not (dk-lam-b!)) (rfl)))
                               (#t (rfl))))))
                    (#t (ass))))))))
    (ai iff)
    (detach! (list 'IMPLIES rhs lhs))))

;;; land (<= tm (ESUP (IMAGE phi NN))) for tm = phi(k); phi typed, (IN tm RPS), (IN k NN)
(define (esp-le-sup! phi kv tm)
  (let ((img (list 'IMAGE phi 'NN)))
    (esp-seq-sup! phi)
    (if (not (dk-asm? (list 'IN tm img))) (esp-in-image! phi kv tm))
    (dk-fact! 'esup-upper img tm)
    (list '<= tm (list 'ESUP img))))

;;; land (<= (ESUP (IMAGE phi NN)) b): phi typed in FUN(NN, RPS), (IN b RPS) in
;;; context.  ELT is a procedure of (k x): with (IN k NN) and x = phi(k) (reduced)
;;; in context, it proves the goal (<= x b).
(define (esp-sup-le! phi b elt)
  (let* ((img (list 'IMAGE phi 'NN))
         (ub  (list 'FORALL 'esx_ (list 'IMPLIES (list 'IN 'esx_ img) (list '<= 'esx_ b)))))
    (esp-seq-sup! phi)
    (dk-have! ub
      (lambda ()
        (let* ((x (dk-di-var!))
               (k (esp-img-elt! phi 'NN x)))
          (elt k x))))
    (esp-and! (list 'IN b 'RR-POS-STAR) ub)
    (dk-fact! 'esup-least img b)
    (list '<= (list 'ESUP img) b)))

;;; sequential map (MIT evaluates arguments right to left)  (pms-map)
(define (esp-map f l) (let loop ((l l) (acc '())) (if (null? l) (reverse acc) (loop (cdr l) (cons (f (car l)) acc)))))
;;; the conjuncts of a predicate's defining iff, landed (hypothesis kept)  (pms-parts!)
(define (esp-parts! pred args)
  (let* ((iff (apply dk-cite! (cons pred args)))
         (rhs (caddr iff))
         (cs (let loop ((r rhs) (acc '()))
               (if (and (pair? r) (eq? (car r) 'AND))
                   (loop (caddr r) (cons (cadr r) acc))
                   (reverse (cons r acc))))))
    (esp-map (lambda (c) (dk-project! c (lambda () (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!)))) cs)))
;;; close the focus goal, a conjunct of the predicate's defining iff  (pms-close-by-parts!)
(define (esp-close-by-parts! pred args)
  (let ((iff (apply dk-cite! (cons pred args))))
    (ai iff) (detach! (list 'IMPLIES (cadr iff) (caddr iff))) (dk-split-all!) (ass)))
;;; k in NN: land (IN k RR), (<= 0 k), (IN k RR-POS-STAR)
(define (esp-nn-rps! k)
  (fact 'nn-in-rr k) (fact 'nn-zero-le k) (esp-rps! k))
;;; run THUNK; close the leaf it started on with CLOSER if still open
(define (esp-then! thunk closer)
  (let ((leaf (proof-state-focus *ps*)))
    (thunk)
    (if (not (sequent-node-grounded? leaf)) (closer))))
;;; =====================================================================
;;; (1) order plumbing in [0, +inf]
;;; =====================================================================

;;; rps-monotone-step-implies-le: a sequence in [0, +inf] that increases at each
;;; step is nondecreasing.  (The model: nn-monotone-step-implies-le, for FUN(NN, RR).)
(sp (make-wff
  '(FORALL f (IMPLIES (IN f (FUN NN RR-POS-STAR))
     (IMPLIES (FORALL k (IMPLIES (IN k NN) (<= (f k) (f (succ k)))))
       (FORALL n (IMPLIES (IN n NN)
         (FORALL m (IMPLIES (IN m NN)
           (IMPLIES (<= m n) (<= (f m) (f n))))))))))))
(define esp-typ  (dk-landed-1 (lambda () (di))))
(define esp-f    (cadr esp-typ))
(define esp-step (dk-landed-1 (lambda () (di))))
(fact 'nn-zero-in)
(fact 'fun-apply-type-c esp-f 'NN 'RR-POS-STAR 0)
(define esp-br (use-induction))
;;; base: m <= 0 forces m = 0
(dk-focus! (cdr (assq 'base esp-br)))
(dk-peel-to! '<=)
(let ((m (cadr (cadr (dk-goal)))))
  (fact 'nn-le-zero-is-zero m)
  (subst (list '= m 0)))
(fact 'rr-pos-star-le-refl (list esp-f 0))
(ass)
;;; step: m <= succ n splits into m <= n (IH, then one step) and m = succ n
(dk-focus! (cdr (assq 'step esp-br)))
(define esp-n  (cdr (assq 'var esp-br)))
(define esp-ih (cdr (assq 'ih  esp-br)))
(dk-peel-to! '<=)
(define esp-m (cadr (cadr (dk-goal))))
(fact 'nn-succ-closed esp-n)
(fact 'fun-apply-type-c esp-f 'NN 'RR-POS-STAR esp-m)
(fact 'fun-apply-type-c esp-f 'NN 'RR-POS-STAR esp-n)
(fact 'fun-apply-type-c esp-f 'NN 'RR-POS-STAR (list 'succ esp-n))
(fact 'nn-le-succ-cases esp-n esp-m)
(use-cases (list (list '<= esp-m esp-n) (list '= esp-m (list 'succ esp-n)))
  (lambda ()
    (inst+ esp-ih esp-m)
    (inst+ esp-step esp-n)
    (esp-trans! (list esp-f esp-m) (list esp-f esp-n) (list esp-f (list 'succ esp-n)))
    (ass))
  (lambda ()
    (subst (list '= esp-m (list 'succ esp-n)))
    (fact 'rr-pos-star-le-refl (list esp-f (list 'succ esp-n)))
    (ass)))
(qed 'rps-monotone-step-implies-le)
(topic! 'rps-monotone-step-implies-le 'inequalities)

;;; etimes-mono-star-left: multiplication in [0, +inf] is monotone in its left factor.
(sp (make-wff
  '(FORALL s_ (IMPLIES (IN s_ RR-POS-STAR)
     (FORALL t_ (IMPLIES (IN t_ RR-POS-STAR)
       (FORALL w_ (IMPLIES (IN w_ RR-POS-STAR)
         (IMPLIES (<= s_ t_) (<= (etimes s_ w_) (etimes t_ w_)))))))))))
(dk-peel!)
(esp-star-cases! 't_
  (lambda ()
    (esp-and! '(IN s_ RR-POS-STAR) '(IN t_ RR))
    (fact 'rr-pos-star-le-real-in-rr 's_ 't_)
    (fact 'rr-pos-star-nonneg 's_)
    (let ((h (dk-cite! 'etimes-mono-real-left 's_ 't_)))
      (if (dk-head-is? h 'FORALL) (dk-apply! h 'w_)))
    (if (not (proof-done? *ps*)) (dk-ass!)))
  (lambda ()
    (subst '(= t_ POS-INF))
    (use-em '(= w_ 0)
      (lambda ()
        (subst '(= w_ 0))
        (fact 'etimes-zero-right 's_)
        (subst '(= (etimes s_ 0) 0))
        (fact 'etimes-pos-inf-zero)
        (subst '(= (etimes POS-INF 0) 0))
        (esp-zero-rps!)
        (fact 'rr-pos-star-le-refl 0)
        (ass))
      (lambda ()
        (fact 'etimes-pos-inf-left 'w_)
        (subst '(= (etimes POS-INF w_) POS-INF))
        (esp-et-type! 's_ 'w_)
        (fact 'rr-pos-star-below-pos-inf '(etimes s_ w_))
        (ass)))))
(qed 'etimes-mono-star-left)
(topic! 'etimes-mono-star-left 'inequalities)

;;; etimes-mono-star: multiplication in [0, +inf] is monotone in both factors.
(sp (make-wff
  '(FORALL p_ (IMPLIES (IN p_ RR-POS-STAR)
     (FORALL q_ (IMPLIES (IN q_ RR-POS-STAR)
       (FORALL s_ (IMPLIES (IN s_ RR-POS-STAR)
         (FORALL t_ (IMPLIES (IN t_ RR-POS-STAR)
           (IMPLIES (<= p_ q_) (IMPLIES (<= s_ t_)
             (<= (etimes p_ s_) (etimes q_ t_))))))))))))))
(dk-peel!)
(fact 'etimes-mono-star-left 'p_ 'q_ 's_)
(fact 'etimes-mono-star-left 's_ 't_ 'q_)
(esp-comm! 'q_ 's_)
(esp-comm! 't_ 'q_)
(esp-et-type! 'p_ 's_)
(esp-et-type! 'q_ 's_)
(esp-et-type! 'q_ 't_)
(dk-have! '(<= (etimes q_ s_) (etimes q_ t_))
  (lambda ()
    (subst '(= (etimes q_ s_) (etimes s_ q_)))
    (subst '(= (etimes q_ t_) (etimes t_ q_)))
    (ass)))
(esp-trans! '(etimes p_ s_) '(etimes q_ s_) '(etimes q_ t_))
(if (not (proof-done? *ps*)) (ass))
(qed 'etimes-mono-star)
(topic! 'etimes-mono-star 'inequalities)

;;; esup-etimes-ge-star: w sup m <= sup (w m) for every w in [0, +inf] (esup-etimes-ge
;;; is the case of a real w; for w = +inf the supremum is +inf unless m is 0).
(sp (make-wff
     '(FORALL w (IMPLIES (IN w RR-POS-STAR)
        (FORALL m (IMPLIES (IN m (FUN NN RR-POS-STAR))
          (<= (etimes w (ESUP (IMAGE m NN)))
              (ESUP (IMAGE (VNB-LAMBDA n_ NN (etimes w (m n_))) NN)))))))))
(dk-peel!)
(esp-star-cases! 'w
  (lambda ()
    (dk-cite! 'esup-etimes-ge 'w 'm)
    (if (not (proof-done? *ps*)) (dk-ass!)))
  (lambda ()
    (subst '(= w POS-INF))
    (fact 'pos-inf-in-rr-pos-star)
    (let* ((phi '(VNB-LAMBDA n_ NN (etimes POS-INF (m n_))))
           (sm  (esp-seq-sup! 'm)))
      (dk-have! (list 'IN phi '(FUN NN RR-POS-STAR))
        (lambda ()
          (dk-lam-type!
            (lambda ()
              (let ((k (dk-di-var!)))
                (fact 'fun-apply-type-c 'm 'NN 'RR-POS-STAR k)
                (esp-et-type! 'POS-INF (list 'm k))
                (dk-ass!))))))
      (let ((tt (esp-seq-sup! phi)))
        (use-em (list '= sm 0)
          (lambda ()
            (subst (list '= sm 0))
            (fact 'etimes-pos-inf-zero)
            (subst '(= (etimes POS-INF 0) 0))
            (fact 'rr-pos-star-nonneg tt)
            (ass))
          (lambda ()
            (fact 'rr-pos-star-nonneg sm)
            (esp-pos! sm)
            (esp-zero-rps!)
            (let* ((ex (dk-cite! 'esup-lt-witness '(IMAGE m NN) 0))
                   (y  (dk-skolem! ex))
                   (k  (esp-img-elt! 'm 'NN y))
                   (mk (list 'm k))
                   (e  (list 'etimes 'POS-INF mk)))
              (fact 'fun-apply-type-c 'm 'NN 'RR-POS-STAR k)
              (dk-have! (list '< 0 mk) (lambda () (subst (list '= mk y)) (ass)))
              (esp-nz-of-pos! mk)
              (fact 'etimes-pos-inf-left mk)
              (esp-et-type! 'POS-INF mk)
              (esp-le-sup! phi k e)
              (dk-have! (list '<= 'POS-INF e)
                (lambda ()
                  (subst (list '= e 'POS-INF))
                  (fact 'rr-pos-star-le-refl 'POS-INF)
                  (ass)))
              (esp-trans! 'POS-INF e tt)
              (fact 'etimes-pos-inf-left sm)
              (subst (list '= (list 'etimes 'POS-INF sm) 'POS-INF))
              (ass))))))))
(qed 'esup-etimes-ge-star)
(topic! 'esup-etimes-ge-star 'inequalities)
;;; =====================================================================
;;; (2) THE ESUP PRODUCT LAW.  For nondecreasing u, v : NN -> [0, +inf],
;;;     sup_n u(n) v(n) = (sup_n u(n)) (sup_n v(n)), the product of [0, +inf]
;;;     (0 * inf = 0).  No guard is needed: if sup u = 0 then u = 0 and both sides
;;;     are 0; if sup u > 0 and sup v = +inf, u is eventually >= some c > 0 and the
;;;     products are unbounded.  Monotonicity of BOTH sequences is needed
;;;     (u = 1, 0, 1, 0, ...; v = 0, 1, 0, 1, ...: left 0, right 1).
;;;   <=  each u(n) v(n) <= (sup u)(sup v)               (etimes-mono-star)
;;;   >=  u(m) v(n) <= u(m+n) v(m+n) <= S for all m, n   (monotone)
;;;       hence u(m) sup v <= S                          (esup-etimes-ge-star at u(m))
;;;       hence (sup v)(sup u) <= S                      (esup-etimes-ge-star at sup v)
;;; =====================================================================

(sp (make-wff
     '(FORALL u (FORALL v
        (IMPLIES (IN u (FUN NN RR-POS-STAR))
          (IMPLIES (IN v (FUN NN RR-POS-STAR))
            (IMPLIES (FORALL n (IMPLIES (IN n NN) (<= (u n) (u (succ n)))))
              (IMPLIES (FORALL n (IMPLIES (IN n NN) (<= (v n) (v (succ n)))))
                (= (ESUP (IMAGE (VNB-LAMBDA n_ NN (etimes (u n_) (v n_))) NN))
                   (etimes (ESUP (IMAGE u NN)) (ESUP (IMAGE v NN))))))))))))
(dk-peel!)
(let* ((mu  (dk-fact! 'rps-monotone-step-implies-le 'u))
       (mv  (dk-fact! 'rps-monotone-step-implies-le 'v))
       (sa  (esp-seq-sup! 'u))
       (sb  (esp-seq-sup! 'v))
       (phi '(VNB-LAMBDA n_ NN (etimes (u n_) (v n_))))
       (ab  (list 'etimes sa sb))
       (uv! (lambda (k)
              (fact 'fun-apply-type-c 'u 'NN 'RR-POS-STAR k)
              (fact 'fun-apply-type-c 'v 'NN 'RR-POS-STAR k))))
  (dk-have! (list 'IN phi '(FUN NN RR-POS-STAR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((k (dk-di-var!)))
            (uv! k)
            (esp-et-type! (list 'u k) (list 'v k))
            (dk-ass!))))))
  (esp-et-type! sa sb)
  (let ((ss (esp-seq-sup! phi)))
    ;; <=
    (esp-sup-le! phi ab
      (lambda (k x)
        (uv! k)
        (esp-le-sup! 'u k (list 'u k))
        (esp-le-sup! 'v k (list 'v k))
        (fact 'etimes-mono-star (list 'u k) sa (list 'v k) sb)
        (subst (list '= x (list 'etimes (list 'u k) (list 'v k))))
        (ass)))
    ;; (a) u(m) v(n) <= S
    (let ((ca (list 'FORALL 'pm_ (list 'IMPLIES '(IN pm_ NN)
                (list 'FORALL 'pn_ (list 'IMPLIES '(IN pn_ NN)
                  (list '<= '(etimes (u pm_) (v pn_)) ss)))))))
      (dk-have! ca
        (lambda ()
          (dk-peel!)
          (let* ((g  (dk-goal))
                 (m  (cadr (cadr (cadr g))))
                 (n  (cadr (caddr (cadr g))))
                 (k  (list '+ m n))
                 (ek (list 'etimes (list 'u k) (list 'v k))))
            (esp-and! (list 'IN m 'NN) (list 'IN n 'NN))
            (fact 'nn-add-closed m n)
            (fact 'nn-le-add-right n m)
            (fact 'nn-le-add-left m n)
            (uv! m) (uv! n) (uv! k)
            (dk-apply! mu k m)
            (dk-apply! mv k n)
            (fact 'etimes-mono-star (list 'u m) (list 'u k) (list 'v n) (list 'v k))
            (esp-et-type! (list 'u m) (list 'v n))
            (esp-et-type! (list 'u k) (list 'v k))
            (esp-le-sup! phi k ek)
            (esp-trans! (list 'etimes (list 'u m) (list 'v n)) ek ss)
            (dk-ass!))))
      ;; (b) u(m) sup v <= S
      (let ((cb (list 'FORALL 'pm_ (list 'IMPLIES '(IN pm_ NN)
                  (list '<= (list 'etimes '(u pm_) sb) ss)))))
        (dk-have! cb
          (lambda ()
            (let* ((m   (dk-di-var!))
                   (um  (list 'u m))
                   (psi (list 'VNB-LAMBDA 'n_ 'NN (list 'etimes um '(v n_)))))
              (uv! m)
              (dk-cite! 'esup-etimes-ge-star um 'v)
              (dk-have! (list 'IN psi '(FUN NN RR-POS-STAR))
                (lambda ()
                  (dk-lam-type!
                    (lambda ()
                      (let ((k (dk-di-var!)))
                        (uv! k)
                        (esp-et-type! um (list 'v k))
                        (dk-ass!))))))
              (let ((tm (esp-seq-sup! psi)))
                (esp-sup-le! psi ss
                  (lambda (k x)
                    (dk-apply! (dk-ctx-form ca) m k)
                    (subst (list '= x (list 'etimes um (list 'v k))))
                    (ass)))
                (esp-et-type! um sb)
                (esp-trans! (list 'etimes um sb) tm ss)
                (dk-ass!)))))
        ;; (c) (sup v)(sup u) <= S
        (let ((chi (list 'VNB-LAMBDA 'n_ 'NN (list 'etimes sb '(u n_)))))
          (dk-cite! 'esup-etimes-ge-star sb 'u)
          (dk-have! (list 'IN chi '(FUN NN RR-POS-STAR))
            (lambda ()
              (dk-lam-type!
                (lambda ()
                  (let ((k (dk-di-var!)))
                    (uv! k)
                    (esp-et-type! sb (list 'u k))
                    (dk-ass!))))))
          (let ((tc (esp-seq-sup! chi)))
            (esp-sup-le! chi ss
              (lambda (k x)
                (uv! k)
                (dk-apply! (dk-ctx-form cb) k)
                (esp-comm! (list 'u k) sb)
                (subst (list '= x (list 'etimes sb (list 'u k))))
                (subst (list '= (list 'etimes sb (list 'u k)) (list 'etimes (list 'u k) sb)))
                (ass)))
            (esp-et-type! sb sa)
            (esp-trans! (list 'etimes sb sa) tc ss)
            (esp-comm! sa sb)
            (dk-have! (list '<= ab ss)
              (lambda () (subst (list '= ab (list 'etimes sb sa))) (ass)))
            (esp-and! (list 'IN ss 'RR-POS-STAR) (list 'IN ab 'RR-POS-STAR))
            (esp-and! (list '<= ss ab) (list '<= ab ss))
            (fact 'rr-pos-star-le-antisymm ss ab)
            (if (not (proof-done? *ps*)) (ass))))))))
(qed 'esup-etimes-eq)
(topic! 'esup-etimes-eq 'inequalities)
;;; =====================================================================
;;; (3) sup_n n = +inf, and sup_n n t = +inf * t in [0, +inf]
;;;     (stated for a sequence g with g(n) = n, h with h(n) = n t: no lambda in
;;;     the statement, so no beta under a binder at the point of use)
;;; =====================================================================

;;; esup-nn-identity: the supremum in [0, +inf] of 0, 1, 2, ... is +inf.
(sp (make-wff
     '(FORALL g (IMPLIES (IN g (FUN NN RR-POS-STAR))
        (IMPLIES (FORALL k (IMPLIES (IN k NN) (= (g k) k)))
          (= (ESUP (IMAGE g NN)) POS-INF))))))
(dk-peel!)
(let* ((hk (dk-ctx-form '(FORALL k (IMPLIES (IN k NN) (= (g k) k)))))
       (ss (esp-seq-sup! 'g)))
  (esp-star-cases! ss
    (lambda ()
      (let* ((ex (dk-cite! 'nn-unbounded-in-rr ss))
             (n  (dk-skolem! ex)))
        (fact 'nn-in-rr n)
        (fact 'nn-zero-le n)
        (esp-rps! n)
        (dk-apply! hk n)
        (esp-le-sup! 'g n n)
        (dk-have! 'FALSITY
          (lambda () (dk-absurd! (list 'IN ss 'RR) (list 'IN n 'RR) (list '< ss n) (list '<= n ss))))
        (esp-keep-prop! 'FALSITY)))
    (lambda () (ass))))
(qed 'esup-nn-identity)
(topic! 'esup-nn-identity 'inequalities)

;;; esup-etimes-nn-pos-inf: for t in [0, +inf], sup_n (n t) = +inf * t (= 0 when t = 0).
(sp (make-wff
     '(FORALL t_ (IMPLIES (IN t_ RR-POS-STAR)
        (FORALL h (IMPLIES (IN h (FUN NN RR-POS-STAR))
          (IMPLIES (FORALL k (IMPLIES (IN k NN) (= (h k) (etimes k t_))))
            (= (ESUP (IMAGE h NN)) (etimes POS-INF t_)))))))))
(dk-peel!)
(fact 'pos-inf-in-rr-pos-star)
(let* ((hk (dk-ctx-form '(FORALL k (IMPLIES (IN k NN) (= (h k) (etimes k t_))))))
       (ss (esp-seq-sup! 'h))
       (et '(etimes POS-INF t_))
       (nn-rps! (lambda (k) (fact 'nn-in-rr k) (fact 'nn-zero-le k) (esp-rps! k))))
  (esp-et-type! 'POS-INF 't_)
  ;; <=
  (esp-sup-le! 'h et
    (lambda (k x)
      (dk-apply! hk k)
      (nn-rps! k)
      (fact 'rr-pos-star-below-pos-inf k)
      (fact 'etimes-mono-star-left k 'POS-INF 't_)
      (subst (list '= x (list 'h k)))
      (subst (list '= (list 'h k) (list 'etimes k 't_)))
      (ass)))
  ;; >=: t sup_n n <= sup_n t n
  (let* ((gv (dk-abstract! 'NN 'RR-POS-STAR (lambda (k) k)
               (lambda (kv)
                 (fact 'nn-in-rr kv) (fact 'nn-zero-le kv)
                 (let ((inst (dk-fact! 'rr-pos-star-membership kv)))
                   (esp-keep-prop! inst (list 'IN kv 'RR) (list '<= 0 kv))))))
         (g  (car gv))
         (ve (cdr gv))
         (chi (list 'VNB-LAMBDA 'n_ 'NN (list 'etimes 't_ (list g 'n_))))
         (sg  (list 'ESUP (list 'IMAGE g 'NN))))
    (dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '= (list g 'k) 'k)))
      (lambda ()
        (let ((kv (dk-di-var!)))
          (dk-apply! ve kv)
          (subst (list '== (list g kv) kv))
          (rfl))))
    (fact 'esup-nn-identity g)
    (dk-cite! 'esup-etimes-ge-star 't_ g)
    (dk-have! (list 'IN chi '(FUN NN RR-POS-STAR))
      (lambda ()
        (dk-lam-type!
          (lambda ()
            (let ((k (dk-di-var!)))
              (fact 'fun-apply-type-c g 'NN 'RR-POS-STAR k)
              (esp-et-type! 't_ (list g k))
              (dk-ass!))))))
    (let ((rr_ (esp-seq-sup! chi)))
      (esp-sup-le! chi ss
        (lambda (k x)
          (dk-apply! ve k)
          (nn-rps! k)
          (dk-apply! hk k)
          (esp-comm! 't_ k)
          (fact 'fun-apply-type-c 'h 'NN 'RR-POS-STAR k)
          (esp-le-sup! 'h k (list 'h k))
          (subst (list '= x (list 'etimes 't_ (list g k))))
          (subst (list '== (list g k) k))
          (subst (list '= (list 'etimes 't_ k) (list 'etimes k 't_)))
          (subst (list '= (list 'etimes k 't_) (list 'h k)))
          (ass)))
      (dk-have! (list '<= '(etimes t_ POS-INF) rr_)
        (lambda () (subst (list '= 'POS-INF sg)) (ass)))
      (esp-et-type! 't_ 'POS-INF)
      (esp-trans! '(etimes t_ POS-INF) rr_ ss)
      (esp-comm! 'POS-INF 't_)
      (dk-have! (list '<= et ss)
        (lambda () (subst (list '= et '(etimes t_ POS-INF))) (ass)))
      (esp-and! (list 'IN ss 'RR-POS-STAR) (list 'IN et 'RR-POS-STAR))
      (esp-and! (list '<= ss et) (list '<= et ss))
      (fact 'rr-pos-star-le-antisymm ss et)
      (if (not (proof-done? *ps*)) (ass)))))
(qed 'esup-etimes-nn-pos-inf)
(topic! 'esup-etimes-nn-pos-inf 'inequalities)
;;; =====================================================================
;;; (4) integral-homogeneous-star: the integral of c f is c times the integral of f
;;;     for EVERY c in [0, +inf] (integral-homogeneous: c real).  For c = +inf:
;;;     n f increases to +inf f pointwise (esup-etimes-nn-pos-inf at f(x)), so by
;;;     monotone convergence the integral of +inf f is sup_n n integral(f), which
;;;     is +inf integral(f) (esup-etimes-nn-pos-inf again).
;;; =====================================================================

(sp (make-wff
     '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL c
        (IMPLIES (IS-MEASURE omega cA mu)
          (IMPLIES (IS-MEASURABLE-FN omega cA f)
            (IMPLIES (IN c RR-POS-STAR)
              (= (INTEGRAL omega cA mu (PTWISE-SCALE omega c f))
                 (etimes c (INTEGRAL omega cA mu f)))))))))))))
(dk-peel!)
(esp-star-cases! 'c
  (lambda ()
    (esp-then! (lambda () (dk-cite! 'integral-homogeneous 'omega 'cA 'mu 'f 'c)) dk-ass!))
  (lambda ()
    (subst '(= c POS-INF))
    (fact 'pos-inf-in-rr-pos-star)
    (esp-parts! 'is-measurable-fn '(omega cA f))
    (fact 'sigma-algebra-ambient-set 'omega 'cA)
    (fact 'integral-in 'omega 'cA 'mu 'f)
    (let* ((ii   '(INTEGRAL omega cA mu f))
           (gv   (dk-abstract! 'NN '(FUN omega RR-POS-STAR) (lambda (k) (list 'PTWISE-SCALE 'omega k 'f))
                   (lambda (kv)
                     (fact 'nn-in-rr kv) (fact 'nn-zero-le kv)
                     (fact 'ptwise-scale-measurable 'omega 'cA 'f kv)
                     (esp-close-by-parts! 'is-measurable-fn (list 'omega 'cA (list 'PTWISE-SCALE 'omega kv 'f))))))
           (g    (car gv))
           (ve   (cdr gv))
           (gk=  (lambda (k) (dk-apply! ve k) (list '== (list g k) (list 'PTWISE-SCALE 'omega k 'f))))
           (meas (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN) (list 'IS-MEASURABLE-FN 'omega 'cA (list g 'n_)))))
           (mono (list 'FORALL 'n_ (list 'IMPLIES '(IN n_ NN)
                   (list 'PTWISE-LE 'omega (list g 'n_) (list g '(succ n_))))))
           (psup (list 'PTWISE-SUP 'omega g))
           (pinf '(PTWISE-SCALE omega POS-INF f)))
      (dk-have! meas
        (lambda ()
          (let ((k (dk-di-var!)))
            (subst (gk= k))
            (fact 'nn-in-rr k) (fact 'nn-zero-le k)
            (fact 'ptwise-scale-measurable 'omega 'cA 'f k)
            (dk-ass!))))
      (dk-have! mono
        (lambda ()
          (let* ((k  (dk-di-var!))
                 (k1 (list 'succ k)))
            (fact 'nn-succ-closed k)
            (subst (gk= k))
            (subst (gk= k1))
            (mac 'ptwise-le)
            (let ((x (dk-di-var!)))
              (esp-nn-rps! k)
              (esp-nn-rps! k1)
              (fact 'fun-apply-type-c 'f 'omega 'RR-POS-STAR x)
              (fact 'ptwise-scale-value 'omega k 'f x)
              (fact 'ptwise-scale-value 'omega k1 'f x)
              (subst (list '= (list (list 'PTWISE-SCALE 'omega k 'f) x) (list 'etimes k (list 'f x))))
              (subst (list '= (list (list 'PTWISE-SCALE 'omega k1 'f) x) (list 'etimes k1 (list 'f x))))
              (fact 'nn-le-succ k)
              (fact 'etimes-mono-star-left k k1 (list 'f x))
              (dk-ass!)))))
      (dk-split! (dk-fact! 'monotone-convergence 'omega 'cA 'mu g))
      (esp-parts! 'is-measurable-fn (list 'omega 'cA psup))
      (dk-have! (list 'IN pinf '(FUN omega RR-POS-STAR))
        (lambda ()
          (mac 'PTWISE-SCALE)
          (dk-lam-type!
            (lambda ()
              (let ((x (dk-di-var!)))
                (fact 'fun-apply-type-c 'f 'omega 'RR-POS-STAR x)
                (esp-et-type! 'POS-INF (list 'f x))
                (dk-ass!))))))
      ;; pointwise: (+inf f)(x) = sup_n (n f)(x)
      (dk-have! (list 'FORALL 'icx_ (list 'IMPLIES '(IN icx_ omega) (list '= (list pinf 'icx_) (list psup 'icx_))))
        (lambda ()
          (let* ((x  (dk-di-var!))
                 (fx (list 'f x))
                 (hx (list 'VNB-LAMBDA 'n_ 'NN (list (list g 'n_) x))))
            (fact 'fun-apply-type-c 'f 'omega 'RR-POS-STAR x)
            (fact 'ptwise-scale-value 'omega 'POS-INF 'f x)
            (fact 'ptwise-sup-apply 'omega g x)
            (dk-have! (list 'IN hx '(FUN NN RR-POS-STAR))
              (lambda ()
                (dk-lam-type!
                  (lambda ()
                    (let ((k (dk-di-var!)))
                      (fact 'fun-apply-type-c g 'NN '(FUN omega RR-POS-STAR) k)
                      (fact 'fun-apply-type-c (list g k) 'omega 'RR-POS-STAR x)
                      (dk-ass!))))))
            (dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '= (list hx 'k) (list 'etimes 'k fx))))
              (lambda ()
                (let ((kv (dk-di-var!)))
                  (dk-lam-b!)
                  (subst (gk= kv))
                  (esp-nn-rps! kv)
                  (fact 'ptwise-scale-value 'omega kv 'f x)
                  (esp-et-type! kv fx)
                  (esp-then! (lambda () (subst (list '= (list (list 'PTWISE-SCALE 'omega kv 'f) x) (list 'etimes kv fx))))
                             rfl))))
            (fact 'esup-etimes-nn-pos-inf fx hx)
            (esp-et-type! 'POS-INF fx)
            (esp-then!
              (lambda ()
                (subst (list '= (list pinf x) (list 'etimes 'POS-INF fx)))
                (subst (list '== (list psup x) (list 'ESUP (list 'IMAGE hx 'NN))))
                (subst (list '= (list 'ESUP (list 'IMAGE hx 'NN)) (list 'etimes 'POS-INF fx))))
              rfl))))
      (fact 'integral-congruence-ptwise 'omega 'cA 'mu pinf psup)
      ;; sup_n integral(n f) = sup_n n integral(f) = +inf integral(f)
      (let ((hi (list 'VNB-LAMBDA 'n_ 'NN (list 'INTEGRAL 'omega 'cA 'mu (list g 'n_)))))
        (dk-have! (list 'IN hi '(FUN NN RR-POS-STAR))
          (lambda ()
            (dk-lam-type!
              (lambda ()
                (let ((k (dk-di-var!)))
                  (dk-apply! (dk-ctx-form meas) k)
                  (fact 'integral-in 'omega 'cA 'mu (list g k))
                  (dk-ass!))))))
        (dk-have! (list 'FORALL 'k (list 'IMPLIES '(IN k NN) (list '= (list hi 'k) (list 'etimes 'k ii))))
          (lambda ()
            (let ((kv (dk-di-var!)))
              (dk-lam-b!)
              (subst (gk= kv))
              (fact 'nn-in-rr kv) (fact 'nn-zero-le kv)
              (esp-then! (lambda () (dk-cite! 'integral-homogeneous 'omega 'cA 'mu 'f kv)) dk-ass!))))
        (fact 'esup-etimes-nn-pos-inf ii hi)
        (esp-et-type! 'POS-INF ii)
        (esp-then!
          (lambda ()
            (subst (list '== (list 'INTEGRAL 'omega 'cA 'mu pinf) (list 'INTEGRAL 'omega 'cA 'mu psup)))
            (subst (list '= (list 'INTEGRAL 'omega 'cA 'mu psup) (list 'ESUP (list 'IMAGE hi 'NN))))
            (subst (list '= (list 'ESUP (list 'IMAGE hi 'NN)) (list 'etimes 'POS-INF ii))))
          rfl)))))
(qed 'integral-homogeneous-star)
(topic! 'integral-homogeneous-star 'analysis)
;;; =====================================================================
;;; (5) DEF. 3.8, the rectangle formula for ARBITRARY sides:
;;;     rho(aa x bb) = mu(aa) nu(bb) in [0, +inf], mu(aa), nu(bb) possibly +inf.
;;;     x |-> nu((aa x bb)_x) is nu(bb) 1_aa (the section is bb on aa, empty off it),
;;;     so rho(aa x bb) = integral(nu(bb) 1_aa) = nu(bb) mu(aa) by
;;;     integral-homogeneous-star.  Neither finiteness nor sigma-finiteness is used.
;;;     (The route of the retired finite form in product-measure.scm, with
;;;     integral-homogeneous replaced; its pms-rect-side! value lemma is re-run here.)
;;; =====================================================================

(define esp-pm '(PRODUCT-MEASURE xs cA mu ys cB nu))

(sp (make-wff (forall-guarded '(xs cA mu ys cB nu aa bb)
   '((IS-MEASURE xs cA mu) (IS-MEASURE ys cB nu) (IN aa cA) (IN bb cB))
   (list '= (list esp-pm '(CARTESIAN aa bb)) '(etimes (mu aa) (nu bb))))))
(dk-peel!)
(esp-parts! 'is-measure '(xs cA mu))
(esp-parts! 'is-measure '(ys cB nu))
(list-ref (esp-parts! 'is-sigma-algebra '(xs cA)) 1)
(list-ref (esp-parts! 'is-sigma-algebra '(ys cB)) 1)
(let* ((rc   '(CARTESIAN aa bb))
       (h    (list 'X-SECTION-MEASURE 'xs 'ys 'nu rc))
       (c    '(nu bb))
       (ind  '(INDICATOR xs aa))
       (sc   (list 'PTWISE-SCALE 'xs c ind))
       (v0   (list 'FORALL 'pmv_ (list 'IMPLIES '(IN pmv_ xs)
               (list '= (list h 'pmv_) (list 'etimes c (list ind 'pmv_)))))))
  (fact 'rectangle-in-product-sigma 'xs 'cA 'ys 'cB 'aa 'bb)
  (fact 'x-section-measure-type 'xs 'cA 'mu 'ys 'cB 'nu rc)
  (fact 'fun-apply-type-c 'nu 'cB 'RR-POS-STAR 'bb)
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR 'aa)
  (fact 'subset-mem-fwd 'cB '(POWER ys) 'bb)
  (dk-have! '(SUBSET bb ys)
    (lambda () (mac 'subset-def)
      (let ((zv (dk-di-var!))) (fact 'power-mem-in 'ys 'bb zv) (ass))))
  (dk-have! '(IN 1 RR-POS-STAR)
    (lambda () (mac 'rr-pos-star-membership) (oi-l) (dk-conj-close! (lambda () (if (not (dk-ass!)) (arith))))))
  (fact 'measurable-fn-indicator 'xs 'cA 'aa)
  (esp-parts! 'is-measurable-fn (list 'xs 'cA ind))
  ;; the values: nu((aa x bb)_x) = nu(bb) 1_aa(x)
  (dk-have! v0
    (lambda ()
      (let ((vv (dk-di-var!)))
        (dk-cite! 'x-section-measure-apply 'xs 'ys 'nu rc vv)
        (subst (list '= (list h vv) (list 'nu (list 'X-SECTION 'ys rc vv))))
        (use-em (list 'IN vv 'aa)
          (lambda ()
            (fact 'x-section-rectangle-in 'ys 'aa 'bb vv)
            (subst (list '= (list 'X-SECTION 'ys rc vv) 'bb))
            (fact 'indicator-value-in 'xs 'aa vv)
            (subst (list '= (list ind vv) 1))
            (esp-comm! c 1)
            (subst (list '= (list 'etimes c 1) (list 'etimes 1 c)))
            (fact 'etimes-one-left c)
            (subst (list '= (list 'etimes 1 c) c))
            (rfl))
          (lambda ()
            (fact 'x-section-rectangle-out 'ys 'aa 'bb vv)
            (subst (list '= (list 'X-SECTION 'ys rc vv) 'EMPTY-SET))
            (fact 'indicator-value-out 'xs 'aa vv)
            (subst (list '= (list ind vv) 0))
            (fact 'etimes-zero-right c)
            (subst (list '= (list 'etimes c 0) 0))
            (subst (list '= '(nu EMPTY-SET) 0))
            (rfl))))))
  (dk-have! (list 'IN sc '(FUN xs RR-POS-STAR))
    (lambda ()
      (mac 'PTWISE-SCALE)
      (dk-lam-type!
        (lambda ()
          (let ((x (dk-di-var!)))
            (fact 'fun-apply-type-c ind 'xs 'RR-POS-STAR x)
            (esp-et-type! c (list ind x))
            (dk-ass!))))))
  (dk-have! (list 'FORALL 'icx_ (list 'IMPLIES '(IN icx_ xs) (list '= (list h 'icx_) (list sc 'icx_))))
    (lambda ()
      (let ((vv (dk-di-var!)))
        (dk-apply! (dk-ctx-form v0) vv)
        (mac 'PTWISE-SCALE)
        (if (not (dk-lam-b!)) (dk-ass!)))))
  (fact 'integral-congruence-ptwise 'xs 'cA 'mu h sc)
  (fact 'integral-homogeneous-star 'xs 'cA 'mu ind c)
  (fact 'integral-indicator 'xs 'cA 'mu 'aa)
  (dk-cite! 'product-measure-apply 'xs 'cA 'mu 'ys 'cB 'nu rc)
  (esp-comm! c '(mu aa))
  (esp-then!
    (lambda ()
      (subst (list '== (list esp-pm rc) (list 'INTEGRAL 'xs 'cA 'mu h)))
      (subst (list '== (list 'INTEGRAL 'xs 'cA 'mu h) (list 'INTEGRAL 'xs 'cA 'mu sc)))
      (subst (list '= (list 'INTEGRAL 'xs 'cA 'mu sc) (list 'etimes c (list 'INTEGRAL 'xs 'cA 'mu ind))))
      (subst (list '= (list 'INTEGRAL 'xs 'cA 'mu ind) '(mu aa))))
    dk-ass!))
(qed 'product-measure-rectangle)
(topic! 'product-measure-rectangle 'set-quotient)

(gloss! 'esup-etimes-eq
  "The supremum of the products of two nondecreasing sequences in [0, +inf] is the
   product of their suprema (with 0 * inf = 0).")
(gloss! 'integral-homogeneous-star
  "For c in [0, +inf] and f >= 0 measurable, the integral of c f is c times the integral
   of f; for c = +inf this is monotone convergence applied to n f.")
(gloss! 'product-measure-rectangle
  "Thayer, Construction of Measures, Def. 3.8 (p. 23): the product measure of a measurable
   rectangle A x B is mu(A) nu(B) in [0, +inf], with no finiteness hypothesis.")
