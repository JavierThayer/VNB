;;; real-integral.scm -- THE INTEGRAL OF A REAL-VALUED FUNCTION (MEASURE-4-C,
;;; 2026-10-10).  Vocabulary: structure-library/real-integral.scm (POS-PART,
;;; NEG-PART, ABS-FN, IS-REAL-MEASURABLE-FN, IS-INTEGRABLE, RINTEGRAL).
;;;
;;; SOURCE.  Thayer, Construction of Measures, Ch. 2: Def. 2.12 (p. 11, the
;;; integral by positive and negative parts), Prop. 2.21 (p. 16, the integral
;;; depends only on the function off a null set), Prop. 2.24 (p. 17).  Real f
;;; are total on omega; "almost everywhere" is a clause "except on a null set"
;;; (IS-NULL-SET), the user's decision of 2026-10-09/10.
;;;
;;; THE THEOREMS, in order.
;;;   plumbing     the unfold equations of the four functoids; the values of
;;;                f+, f-, |f|, PTWISE-EPLUS / -ETIMES / -SCALE at a point;
;;;                part-values-at (f+ and f- real, >= 0, f = f+ - f-,
;;;                |f| = f+ + f-) and the two sign cases; the parts are in
;;;                FUN(omega, RR-POS-STAR).
;;;   (A) pos-/neg-part-measurable-of-diff: f = h1 - h2 with h1, h2 real-valued
;;;       measurable => f+, f- measurable (the tail { al < f+ } is
;;;       { al + h2 < h1 }, measurable-fn-lt-set).
;;;   (B) rintegral-decomposition -- THE LEMMA WITH WORK IN IT: f = h1 - h2
;;;       pointwise, h1, h2 real-valued measurable of finite integral =>
;;;       IS-INTEGRABLE(f) and RINTEGRAL(f) = INTEGRAL(h1) - INTEGRAL(h2).
;;;       Proof: f+ <= h1, f- <= h2 give the finiteness; f+ + h2 = f- + h1 as
;;;       functions (dk-fun-ext!), integral-additive on both sides, cancel in RR.
;;;   (C) from (B): integrable iff |f| has finite integral; linearity
;;;       (rintegral-add, rintegral-scale, each with closure of the integrable
;;;       functions); monotonicity, also off a null set; |RINTEGRAL f| <=
;;;       INTEGRAL |f|; for f >= 0, f is IS-MEASURABLE-FN and RINTEGRAL f =
;;;       INTEGRAL f; equality off a null set (Prop. 2.21 for real f); the
;;;       integral over A in cA as RINTEGRAL of x |-> f(x) 1_A(x).
;;;   (D) rintegral-nonneg-on-sets-null (Prop. 2.24).  The notes' A_n =
;;;       { f <= -1/n } is written A_n = { 1 <= (n+1) f- }, a closed tail of a
;;;       scaled f- (measurable-fn-ge), so no reciprocal appears; mu(A_n) <=
;;;       INTEGRAL((n+1) f- 1_A) = (n+1) * 0; { f < 0 } lies in the union of
;;;       the A_n (rr-archimedean-multiple), whose measure is <= ESUM of zeros.
;;;   (E) the preimage form of real measurability, both directions
;;;       (real-measurable-fn-iff-tails).
;;;
;;; LOAD WINDOW.  lo: esum-nn-zero (theorem-library/outer-measure-construction,
;;; load.scm line 3483) and IS-NULL-SET (structure-library/outer-measure-
;;; construction, 3482); the rest is earlier: integral-additive,
;;; integral-le-off-null, measurable-fn-const / -eplus / -eplus-of-values /
;;; -etimes / -etimes-of-values / -lt-set / -of-nonneg-tails
;;; (theorem-library/integral-convergence, 3477), rr-abs-le-of-parts
;;; (regulated-primitive-laws, 3435), integral-in / -monotone / -indicator /
;;; -homogeneous, measurable-fn-ge, indicator-value-in / -out, etimes-closed,
;;; etimes-zero-right (integral-laws, 3387), measure-countably-subadditive
;;; (measure-laws, 3386).  No late tactic (no contra, prep, ineq-supply).  hi:
;;; nothing in the tree cites these names.  Slot: structure-library/real-integral
;;; then this file, immediately after "theorem-library/outer-measure-construction".
;;; Library: measure.
;;; ====================================================================

;;; =====================================================================
;;; (0) file-local kit.  Prefix rin-.  Copied from
;;;     theorem-library/integral-convergence.scm (the icv- helpers, local to
;;;     that file), renamed.
;;; =====================================================================

(define (rin-keep-prop! . keepers)
  (let ((leaf (proof-state-focus *ps*)))
    (apply dk-only! keepers)
    (if (not (sequent-node-grounded? leaf)) (prop))))

(define (rin-conj-close! . opt)
  (let ((closer (if (pair? opt) (car opt) from-context!)))
    (let walk ()
      (let ((g (dk-goal)))
        (if (and (pair? g) (eq? (car g) 'AND))
            (for-each (lambda (k)
                        (if (not (sequent-node-grounded? k))
                            (begin (dk-focus! k) (walk))))
                      (dk-opened (lambda () (di))))
            (closer))))))

;;; (IN tm RR-POS-STAR), with (IN tm RR) and (<= 0 tm) in context.
(define (rin-rps! tm)
  (if (not (dk-asm? (list 'IN tm 'RR-POS-STAR)))
      (dk-have! (list 'IN tm 'RR-POS-STAR)
        (lambda ()
          (let ((inst (dk-fact! 'rr-pos-star-membership tm)))
            (rin-keep-prop! inst (list 'IN tm 'RR) (list '<= 0 tm)))))))

;;; Set equality by elements: lands (= A B).
(define (rin-set-eq! a b fwd! bwd!)
  (dk-have! (list 'FORALL 'ew_ (list 'IFF (list 'IN 'ew_ a) (list 'IN 'ew_ b)))
    (lambda ()
      (let ((w (dk-di-var! (lambda (g) (cadr (cadr g))))))
        (for-each (lambda (l)
                    (dk-focus! l)
                    (if (equal? (dk-goal) (list 'in w b)) (fwd! w) (bwd! w)))
                  (dk-opened (lambda () (di)))))))
  (fact 'class-extensionality a b)
  (list '= a b))

(define (rin-sep-in! closer)
  (for-each (lambda (l)
              (if (not (sequent-node-grounded? l))
                  (begin (dk-focus! l) (closer))))
            (dk-opened (lambda () (sep-mi)))))

;;; the conjuncts of a predicate instance, each landed by projection (kept)
(define (rin-parts! pred args)
  (let* ((iff (apply dk-cite! (cons pred args)))
         (rhs (caddr iff))
         (cs  (let loop ((r rhs) (acc '()))
                (if (and (pair? r) (eq? (car r) 'and))
                    (loop (caddr r) (cons (cadr r) acc))
                    (reverse (cons r acc))))))
    (map (lambda (c) (dk-project! c pred (cons pred args))) cs)))

;;; (= (eplus u v) (+ u v)) for real nonnegative u, v in context
(define (rin-eplus-eq! u v)
  (let ((e (list '= (list 'eplus u v) (list '+ u v))))
    (if (not (dk-asm? e))
        (dk-have! e
          (lambda ()
            (fact 'eplus-real-defined u v)
            (subst (list '= (list 'eplus u v) (list 'binplus u v)))
            (fact 'binplus-apply u v)
            (subst (list '== (list 'binplus u v) (list '+ u v)))
            (fact 'rr-add-closed u v)
            (rfl))))
    e))

(define (rin-absurd! . prems)
  (if (eq? (dk-goal) 'FALSITY)
      (apply dk-absurd! prems)
      (begin
        (dk-have! 'FALSITY (lambda () (apply dk-absurd! prems)))
        (rin-keep-prop! 'FALSITY))))

;;; the eigenvariable typed in OM among the formulas a dk-peel! landed
(define (rin-var-in landed om)
  (let ((hit (filter (lambda (f) (and (pair? f) (eq? (car f) 'in) (equal? (caddr f) om))) landed)))
    (if (null? hit) (error "rin-var-in: no typing landed in" om))
    (cadr (car hit))))
;;; =====================================================================
;;; (1) unfold equations and the values of the parts at a point
;;; =====================================================================

(define (rin-pos f) (list 'POS-PART 'omega f))
(define (rin-neg f) (list 'NEG-PART 'omega f))
(define (rin-pif f x) (list 'IF (list '<= 0 (list f x)) (list f x) 0))
(define (rin-nif f x) (list 'IF (list '<= 0 (list f x)) 0 (list '- (list f x))))

;;; pos-part-unfold
(sp (make-wff '(FORALL omega (FORALL f
  (== (POS-PART omega f) (VNB-LAMBDA ppx_ omega (IF (<= 0 (f ppx_)) (f ppx_) 0)))))))
(di) (mac 'POS-PART) (qrfl)
(qed 'pos-part-unfold)
(topic! 'pos-part-unfold 'plumbing)

;;; neg-part-unfold
(sp (make-wff '(FORALL omega (FORALL f
  (== (NEG-PART omega f) (VNB-LAMBDA npx_ omega (IF (<= 0 (f npx_)) 0 (- (f npx_)))))))))
(di) (mac 'NEG-PART) (qrfl)
(qed 'neg-part-unfold)
(topic! 'neg-part-unfold 'plumbing)

;;; abs-fn-unfold
(sp (make-wff '(FORALL omega (FORALL f
  (== (ABS-FN omega f) (VNB-LAMBDA afx_ omega (abs (f afx_))))))))
(di) (mac 'ABS-FN) (qrfl)
(qed 'abs-fn-unfold)
(topic! 'abs-fn-unfold 'plumbing)

;;; rintegral-unfold
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (== (RINTEGRAL omega cA mu f)
      (- (INTEGRAL omega cA mu (POS-PART omega f)) (INTEGRAL omega cA mu (NEG-PART omega f))))))))))
(di) (mac 'RINTEGRAL) (qrfl)
(qed 'rintegral-unfold)
(topic! 'rintegral-unfold 'plumbing)

;;; pos-part-value
(sp (make-wff '(FORALL omega (FORALL f (FORALL x (IMPLIES (IN x omega)
  (== ((POS-PART omega f) x) (IF (<= 0 (f x)) (f x) 0))))))))
(dk-peel!)
(mac 'POS-PART)
(if (not (dk-lam-b!)) (qrfl))
(qed 'pos-part-value)
(topic! 'pos-part-value 'plumbing)

;;; neg-part-value
(sp (make-wff '(FORALL omega (FORALL f (FORALL x (IMPLIES (IN x omega)
  (== ((NEG-PART omega f) x) (IF (<= 0 (f x)) 0 (- (f x))))))))))
(dk-peel!)
(mac 'NEG-PART)
(if (not (dk-lam-b!)) (qrfl))
(qed 'neg-part-value)
(topic! 'neg-part-value 'plumbing)

;;; abs-fn-value
(sp (make-wff '(FORALL omega (FORALL f (FORALL x (IMPLIES (IN x omega)
  (== ((ABS-FN omega f) x) (abs (f x)))))))))
(dk-peel!)
(mac 'ABS-FN)
(if (not (dk-lam-b!)) (qrfl))
(qed 'abs-fn-value)
(topic! 'abs-fn-value 'plumbing)

;;; ptwise-eplus-value
(sp (make-wff '(FORALL omega (FORALL g1 (FORALL g2 (FORALL x (IMPLIES (IN x omega)
  (== ((PTWISE-EPLUS omega g1 g2) x) (eplus (g1 x) (g2 x))))))))))
(dk-peel!)
(mac 'PTWISE-EPLUS)
(if (not (dk-lam-b!)) (qrfl))
(qed 'ptwise-eplus-value-q)
(topic! 'ptwise-eplus-value-q 'plumbing)

;;; ptwise-etimes-value
(sp (make-wff '(FORALL omega (FORALL g1 (FORALL g2 (FORALL x (IMPLIES (IN x omega)
  (== ((PTWISE-ETIMES omega g1 g2) x) (etimes (g1 x) (g2 x))))))))))
(dk-peel!)
(mac 'PTWISE-ETIMES)
(if (not (dk-lam-b!)) (qrfl))
(qed 'ptwise-etimes-value-q)
(topic! 'ptwise-etimes-value-q 'plumbing)

;;; ptwise-scale-value
(sp (make-wff '(FORALL omega (FORALL k (FORALL g (FORALL x (IMPLIES (IN x omega)
  (== ((PTWISE-SCALE omega k g) x) (etimes k (g x))))))))))
(dk-peel!)
(mac 'PTWISE-SCALE)
(if (not (dk-lam-b!)) (qrfl))
(qed 'ptwise-scale-value-q)
(topic! 'ptwise-scale-value-q 'plumbing)
;;; =====================================================================
;;; (2) the parts at a point, and their typings as functions
;;; =====================================================================

;;; close an arithmetic leaf at a point x where (f x) is real
(define (rin-arith-close! fx)
  (let ((g (dk-goal)))
    (cond ((dk-asm? g) (ass))
          ((equal? g '(IN 0 RR)) (fact 'rr-zero-in) (ass))
          ((and (dk-head-is? g 'IN) (equal? (caddr g) 'RR) (dk-head-is? (cadr g) '-))
           (fact 'rr-neg-closed (cadr (cadr g))) (ass))
          ((dk-head-is? g '<=)
           (let ((ps (filter dk-asm? (list (list 'IN fx 'RR) (list '<= 0 fx) (list '< fx 0)))))
             (apply dk-ineq! ps)))
          ((and (dk-head-is? g '=) (dk-head-is? (cadr g) 'abs))
           (if (dk-asm? (list '<= 0 fx))
               (begin (fact 'rr-abs-of-nonneg fx) (subst (list '= (list 'abs fx) fx)))
               (begin (fact 'rr-abs-of-neg fx) (subst (list '= (list 'abs fx) (list '- fx)))))
           (crs))
          ((dk-head-is? g '=) (crs))
          (#t (error "rin-arith-close!: no closer for" (expression->string g))))))

;;; part-values-at: the two parts at a point, their typings, f = f+ - f-, |f| = f+ + f-
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR)) (FORALL x (IMPLIES (IN x omega)
  (AND (IN ((POS-PART omega f) x) RR)
  (AND (<= 0 ((POS-PART omega f) x))
  (AND (IN ((NEG-PART omega f) x) RR)
  (AND (<= 0 ((NEG-PART omega f) x))
  (AND (= (f x) (- ((POS-PART omega f) x) ((NEG-PART omega f) x)))
       (= (abs (f x)) (+ ((POS-PART omega f) x) ((NEG-PART omega f) x)))))))))))))))
(let* ((landed (dk-peel!))
       (x (rin-var-in landed 'omega))
       (fx (list 'f x)))
  (fact 'fun-apply-type-c 'f 'omega 'RR x)
  (dk-cite! 'pos-part-value 'omega 'f x)
  (dk-cite! 'neg-part-value 'omega 'f x)
  (subst (list '== (list (rin-pos 'f) x) (rin-pif 'f x)))
  (subst (list '== (list (rin-neg 'f) x) (rin-nif 'f x)))
  (dk-case-if! (rin-pif 'f x)
    (lambda (tr v0)
      (dk-if-branch! tr (rin-nif 'f x) #f
        (lambda ()
          (if (not tr) (fact 'rr-not-le-lt 0 fx))
          (rin-conj-close! (lambda () (rin-arith-close! fx))))))))
(qed 'part-values-at)
(topic! 'part-values-at 'plumbing)

;;; land the six facts of part-values-at for f at x; return (P N) the two values
(define (rin-parts-at! f x)
  (let ((px (list (rin-pos f) x)) (nx (list (rin-neg f) x)))
    (if (not (dk-asm? (list '= (list f x) (list '- px nx))))
        (let ((c (dk-cite! 'part-values-at 'omega f x)))
          (fact 'fun-apply-type-c f 'omega 'RR x)
          (if (and (pair? c) (eq? (car c) 'AND)) (dk-split-all! (list c)))))
    (list px nx)))

;;; pos-part-fun
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR))
  (IN (POS-PART omega f) (FUN omega RR-POS-STAR)))))))
(dk-peel!)
(fact 'fun-domain-in-set 'omega 'RR 'f)
(dk-cite! 'pos-part-unfold 'omega 'f)
(subst (list '== (rin-pos 'f) '(VNB-LAMBDA ppx_ omega (IF (<= 0 (f ppx_)) (f ppx_) 0))))
(dk-lam-type!
  (lambda ()
    (let ((x (dk-di-var!)))
      (fact 'fun-apply-type-c 'f 'omega 'RR x)
      (dk-case-if! (rin-pif 'f x)
        (lambda (tr v0)
          (if tr (rin-rps! (list 'f x))
              (begin (fact 'rr-zero-in) (fact 'rr-leq-reflexive 0) (rin-rps! 0)))
          (ass))))))
(qed 'pos-part-fun)
(topic! 'pos-part-fun 'plumbing)

;;; neg-part-fun
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR))
  (IN (NEG-PART omega f) (FUN omega RR-POS-STAR)))))))
(dk-peel!)
(fact 'fun-domain-in-set 'omega 'RR 'f)
(dk-cite! 'neg-part-unfold 'omega 'f)
(subst (list '== (rin-neg 'f) '(VNB-LAMBDA npx_ omega (IF (<= 0 (f npx_)) 0 (- (f npx_))))))
(dk-lam-type!
  (lambda ()
    (let* ((x (dk-di-var!)) (fx (list 'f x)))
      (fact 'fun-apply-type-c 'f 'omega 'RR x)
      (dk-case-if! (rin-nif 'f x)
        (lambda (tr v0)
          (if tr
              (begin (fact 'rr-zero-in) (fact 'rr-leq-reflexive 0) (rin-rps! 0))
              (begin (fact 'rr-not-le-lt 0 fx)
                     (fact 'rr-neg-closed fx)
                     (dk-have! (list '<= 0 (list '- fx)) (lambda () (dk-ineq! (list 'IN fx 'RR) (list '< fx 0))))
                     (rin-rps! (list '- fx))))
          (ass))))))
(qed 'neg-part-fun)
(topic! 'neg-part-fun 'plumbing)

;;; abs-fn-fun
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR))
  (IN (ABS-FN omega f) (FUN omega RR-POS-STAR)))))))
(dk-peel!)
(fact 'fun-domain-in-set 'omega 'RR 'f)
(dk-cite! 'abs-fn-unfold 'omega 'f)
(subst (list '== '(ABS-FN omega f) '(VNB-LAMBDA afx_ omega (abs (f afx_)))))
(dk-lam-type!
  (lambda ()
    (let* ((x (dk-di-var!)) (fx (list 'f x)))
      (fact 'fun-apply-type-c 'f 'omega 'RR x)
      (fact 'rr-abs-closed fx)
      (fact 'rr-abs-nonneg fx)
      (rin-rps! (list 'abs fx))
      (ass))))
(qed 'abs-fn-fun)
(topic! 'abs-fn-fun 'plumbing)
;;; =====================================================================
;;; (3) the parts in the two cases of the sign of f(x)
;;; =====================================================================

;;; part-values-nonneg
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR)) (FORALL x (IMPLIES (IN x omega) (IMPLIES (<= 0 (f x))
  (AND (= ((POS-PART omega f) x) (f x)) (= ((NEG-PART omega f) x) 0))))))))))
(let* ((landed (dk-peel!)) (x (rin-var-in landed 'omega)))
  (fact 'fun-apply-type-c 'f 'omega 'RR x)
  (fact 'rr-neg-closed (list 'f x))
  (dk-cite! 'pos-part-value 'omega 'f x)
  (dk-cite! 'neg-part-value 'omega 'f x)
  (subst (list '== (list (rin-pos 'f) x) (rin-pif 'f x)))
  (subst (list '== (list (rin-neg 'f) x) (rin-nif 'f x)))
  (dk-if-branch! #t (rin-pif 'f x) #f
    (lambda ()
      (dk-if-branch! #t (rin-nif 'f x) #f
        (lambda () (rin-conj-close! (lambda () (rfl))))))))
(qed 'part-values-nonneg)
(topic! 'part-values-nonneg 'plumbing)

;;; part-values-neg
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR)) (FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (<= 0 (f x)))
  (AND (= ((POS-PART omega f) x) 0) (= ((NEG-PART omega f) x) (- (f x))))))))))))
(let* ((landed (dk-peel!)) (x (rin-var-in landed 'omega)))
  (fact 'fun-apply-type-c 'f 'omega 'RR x)
  (fact 'rr-neg-closed (list 'f x))
  (dk-cite! 'pos-part-value 'omega 'f x)
  (dk-cite! 'neg-part-value 'omega 'f x)
  (subst (list '== (list (rin-pos 'f) x) (rin-pif 'f x)))
  (subst (list '== (list (rin-neg 'f) x) (rin-nif 'f x)))
  (dk-if-branch! #f (rin-pif 'f x) #f
    (lambda ()
      (dk-if-branch! #f (rin-nif 'f x) #f
        (lambda () (rin-conj-close! (lambda () (rfl))))))))
(qed 'part-values-neg)
(topic! 'part-values-neg 'plumbing)

;;; Split on the sign of (f x) at x in omega, f in FUN(omega, RR) in context:
;;; lands the six facts of part-values-at, the case's two value equations and,
;;; in the negative case, (< (f x) 0); runs (BODY TRUE?).
(define (rin-sign-cases! f x body)
  (let ((fx (list f x)))
    (fact 'fun-apply-type-c f 'omega 'RR x)
    (rin-parts-at! f x)
    (use-em (list '<= 0 fx)
      (lambda ()
        (let ((c (dk-cite! 'part-values-nonneg 'omega f x)))
          (if (and (pair? c) (eq? (car c) 'AND)) (dk-split! c)))
        (body #t))
      (lambda ()
        (fact 'rr-not-le-lt 0 fx)
        (let ((c (dk-cite! 'part-values-neg 'omega f x)))
          (if (and (pair? c) (eq? (car c) 'AND)) (dk-split! c)))
        (body #f)))))

;;; the arithmetic premises in context, by formula, for dk-ineq!
(define (rin-ineq-goal! cands)
  (apply dk-ineq! (filter dk-asm? cands)))

;;; =====================================================================
;;; (4) the parts of a difference of two real-valued measurable functions
;;;     are measurable
;;; =====================================================================

;;; (= (W x) (+ al (h x))) for W = PTWISE-EPLUS(omega, x |-> al, h), h x real >= 0
(define (rin-w-at! w al h x)
  (let ((hx (list h x)))
    (fact 'fun-apply-type-c h 'omega 'RR-POS-STAR x)
    (fact 'rr-pos-star-nonneg hx)
    (rin-eplus-eq! al hx)
    (dk-have! (list 'AND (list 'IN al 'RR) (list 'IN hx 'RR)))
    (fact 'rr-add-closed al hx)
    (dk-have! (list '= (list w x) (list '+ al hx))
      (lambda ()
        (mac 'PTWISE-EPLUS)
        (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop))))
        (if (not (sequent-node-grounded? (proof-state-focus *ps*)))
            (begin (subst (list '= (list 'eplus al hx) (list '+ al hx))) (rfl)))))))

;;; The proof of IS-MEASURABLE-FN of the part PART ('pos or 'neg) of f, after
;;; the peel of the statement below.
(define (rin-part-meas! part)
  (let* ((pf (if (eq? part 'pos) (rin-pos 'f) (rin-neg 'f)))
         (big (if (eq? part 'pos) 'h1 'h2))     ; f+ > al  iff  al + h2 < h1
         (small (if (eq? part 'pos) 'h2 'h1))   ; f- > al  iff  al + h1 < h2
         (hdiff '(FORALL x (IMPLIES (IN x omega) (= (f x) (- (h1 x) (h2 x))))))
         (hr1 '(FORALL x (IMPLIES (IN x omega) (IN (h1 x) RR))))
         (hr2 '(FORALL x (IMPLIES (IN x omega) (IN (h2 x) RR)))))
    (rin-parts! 'IS-MEASURABLE-FN '(omega cA h1))
    (rin-parts! 'IS-MEASURABLE-FN '(omega cA h2))
    (fact 'sigma-algebra-ambient-set 'omega 'cA)
    (fact (if (eq? part 'pos) 'pos-part-fun 'neg-part-fun) 'omega 'f)
    (dk-have! (list 'FORALL 'al_ (list 'IMPLIES '(IN al_ RR) (list 'IMPLIES '(<= 0 al_)
                (list 'IN (list 'SEP 'x_ 'omega (list '< 'al_ (list pf 'x_))) 'cA))))
      (lambda ()
        (dk-peel!)
        (let* ((tl (cadr (dk-goal))) (al (cadr (cadddr tl)))
               (cf (list 'VNB-LAMBDA 'cx_ 'omega al))
               (w (list 'PTWISE-EPLUS 'omega cf small))
               (lt (list 'SEP 'x_ 'omega (list '< (list w 'x_) (list big 'x_))))
               (facts! (lambda (x)
                         (dk-apply! hdiff x) (dk-apply! hr1 x) (dk-apply! hr2 x)
                         (rin-w-at! w al small x)))
               (prems (lambda (x)
                        (let ((fx (list 'f x)) (px (list pf x)))
                          (list (list 'IN al 'RR) '(<= 0 al) (list '<= 0 al)
                                (list 'IN fx 'RR) (list 'IN (list 'h1 x) 'RR) (list 'IN (list 'h2 x) 'RR)
                                (list 'IN px 'RR)
                                (list '= fx (list '- (list 'h1 x) (list 'h2 x)))
                                (list '= px fx) (list '= px 0) (list '= px (list '- fx))
                                (list '< fx 0) (list '<= 0 fx)
                                (list '< al px)
                                (list '< (list '+ al (list small x)) (list big x)))))))
          (fact 'rr-leq-reflexive al)
          (rin-rps! al)
          (fact 'measurable-fn-const 'omega 'cA al)
          (fact 'measurable-fn-eplus 'omega 'cA cf small)
          (fact 'measurable-fn-lt-set 'omega 'cA big w)
          (rin-set-eq! tl lt
            (lambda (x)
              (sep-me (list 'IN x tl))
              (facts! x)
              (rin-sign-cases! 'f x
                (lambda (tr)
                  (rin-sep-in!
                    (lambda ()
                      (cond ((dk-asm? (dk-goal)) (ass))
                            (#t (subst (list '= (list w x) (list '+ al (list small x))))
                                (rin-ineq-goal! (prems x)))))))))
            (lambda (x)
              (sep-me (list 'IN x lt))
              (facts! x)
              (dk-have! (list '< (list '+ al (list small x)) (list big x))
                (lambda () (subst (list '= (list '+ al (list small x)) (list w x))) (dk-ass!)))
              (rin-sign-cases! 'f x
                (lambda (tr)
                  (rin-sep-in!
                    (lambda ()
                      (cond ((dk-asm? (dk-goal)) (ass))
                            (#t (rin-ineq-goal! (prems x))))))))))
          (subst (list '= tl lt))
          (dk-ass!))))
    (fact 'measurable-fn-of-nonneg-tails 'omega 'cA pf)
    (dk-ass!)))

;;; pos-part-measurable-of-diff
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f (FORALL h1 (FORALL h2
  (IMPLIES (IN f (FUN omega RR))
  (IMPLIES (IS-MEASURABLE-FN omega cA h1)
  (IMPLIES (IS-MEASURABLE-FN omega cA h2)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h1 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h2 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (= (f x) (- (h1 x) (h2 x)))))
    (IS-MEASURABLE-FN omega cA (POS-PART omega f)))))))))))))))
(dk-peel!)
(rin-part-meas! 'pos)
(qed 'pos-part-measurable-of-diff)
(topic! 'pos-part-measurable-of-diff 'analysis)

;;; neg-part-measurable-of-diff
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f (FORALL h1 (FORALL h2
  (IMPLIES (IN f (FUN omega RR))
  (IMPLIES (IS-MEASURABLE-FN omega cA h1)
  (IMPLIES (IS-MEASURABLE-FN omega cA h2)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h1 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h2 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (= (f x) (- (h1 x) (h2 x)))))
    (IS-MEASURABLE-FN omega cA (NEG-PART omega f)))))))))))))))
(dk-peel!)
(rin-part-meas! 'neg)
(qed 'neg-part-measurable-of-diff)
(topic! 'neg-part-measurable-of-diff 'analysis)
;;; =====================================================================
;;; (5) THE DECOMPOSITION LEMMA: f = h1 - h2 with h1, h2 real-valued,
;;;     measurable, of finite integral => f integrable and
;;;     RINTEGRAL(f) = INTEGRAL(h1) - INTEGRAL(h2)
;;; =====================================================================

;;; (= ((PTWISE-EPLUS omega g1 g2) x) (+ (g1 x) (g2 x))), g1 x, g2 x real >= 0 in context
(define (rin-pe-at! g1 g2 x)
  (let* ((w (list 'PTWISE-EPLUS 'omega g1 g2)) (ax (list g1 x)) (bx (list g2 x)))
    (rin-eplus-eq! ax bx)
    (dk-have! (list 'AND (list 'IN ax 'RR) (list 'IN bx 'RR)))
    (fact 'rr-add-closed ax bx)
    (dk-cite! 'ptwise-eplus-value-q 'omega g1 g2 x)
    (dk-have! (list '= (list w x) (list '+ ax bx))
      (lambda ()
        (subst (list '== (list w x) (list 'eplus ax bx)))
        (subst (list '= (list 'eplus ax bx) (list '+ ax bx)))
        (rfl)))
    (list '= (list w x) (list '+ ax bx))))

;;; the arithmetic facts that may be in context at a point x, for dk-ineq!
(define (rin-pt-prems f x . more)
  (let* ((fx (list f x)) (px (list (rin-pos f) x)) (nx (list (rin-neg f) x)))
    (append
      (list (list 'IN fx 'RR) (list 'IN px 'RR) (list 'IN nx 'RR)
            (list '<= 0 px) (list '<= 0 nx)
            (list '= fx (list '- px nx))
            (list '= px fx) (list '= px 0) (list '= nx 0) (list '= nx (list '- fx))
            (list '< fx 0) (list '<= 0 fx))
      more)))

;;; h x real and >= 0, from (FORALL x (IN x omega) => (IN (h x) RR)) and h in FUN(omega, RR-POS-STAR)
(define (rin-real-at! h x)
  (let ((hr (list 'FORALL 'x (list 'IMPLIES '(IN x omega) (list 'IN (list h 'x) 'RR)))))
    (if (not (dk-asm? (list 'IN (list h x) 'RR))) (dk-apply! hr x))
    (fact 'fun-apply-type-c h 'omega 'RR-POS-STAR x)
    (fact 'rr-pos-star-nonneg (list h x))))

;;; INTEGRAL(g) in RR and >= 0 from IS-MEASURABLE-FN(g) <= ... the integral of
;;; a measurable bound hb with INTEGRAL(hb) in RR, (PTWISE-LE omega g hb) in context
(define (rin-int-finite-below! g hb)
  (let ((ig (list 'INTEGRAL 'omega 'cA 'mu g)) (ib (list 'INTEGRAL 'omega 'cA 'mu hb)))
    (fact 'integral-monotone 'omega 'cA 'mu g hb)
    (fact 'integral-in 'omega 'cA 'mu g)
    (dk-have! (list 'AND (list 'IN ig 'RR-POS-STAR) (list 'IN ib 'RR)))
    (fact 'rr-pos-star-le-real-in-rr ig ib)
    (fact 'rr-pos-star-nonneg ig)))

;;; INTEGRAL(g) in RR-POS-STAR and >= 0, and in RR when that is in context
(define (rin-int-facts! g)
  (let ((ig (list 'INTEGRAL 'omega 'cA 'mu g)))
    (fact 'integral-in 'omega 'cA 'mu g)
    (fact 'rr-pos-star-nonneg ig)))

;;; rintegral-decomposition
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL h1 (FORALL h2
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IN f (FUN omega RR))
  (IMPLIES (IS-MEASURABLE-FN omega cA h1)
  (IMPLIES (IS-MEASURABLE-FN omega cA h2)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h1 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IN (h2 x) RR)))
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (= (f x) (- (h1 x) (h2 x)))))
  (IMPLIES (IN (INTEGRAL omega cA mu h1) RR)
  (IMPLIES (IN (INTEGRAL omega cA mu h2) RR)
    (AND (IS-INTEGRABLE omega cA mu f)
         (= (RINTEGRAL omega cA mu f)
            (- (INTEGRAL omega cA mu h1) (INTEGRAL omega cA mu h2)))))))))))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
       (hdiff '(FORALL x (IMPLIES (IN x omega) (= (f x) (- (h1 x) (h2 x))))))
       (ip (list 'INTEGRAL 'omega 'cA 'mu pf)) (in (list 'INTEGRAL 'omega 'cA 'mu nf))
       (i1 '(INTEGRAL omega cA mu h1)) (i2 '(INTEGRAL omega cA mu h2))
       (aa (list 'PTWISE-EPLUS 'omega pf 'h2)) (bb (list 'PTWISE-EPLUS 'omega nf 'h1)))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-parts! 'IS-MEASURABLE-FN '(omega cA h1))
  (rin-parts! 'IS-MEASURABLE-FN '(omega cA h2))
  (fact 'pos-part-measurable-of-diff 'omega 'cA 'f 'h1 'h2)
  (fact 'neg-part-measurable-of-diff 'omega 'cA 'f 'h1 'h2)
  (fact 'pos-part-fun 'omega 'f)
  (fact 'neg-part-fun 'omega 'f)
  ;; f+ <= h1 and f- <= h2
  (for-each
    (lambda (g hb)
      (dk-have! (list 'PTWISE-LE 'omega g hb)
        (lambda ()
          (mac 'PTWISE-LE)
          (let ((w (dk-di-var!)))
            (dk-apply! hdiff w)
            (rin-real-at! 'h1 w)
            (rin-real-at! 'h2 w)
            (rin-sign-cases! 'f w
              (lambda (tr)
                (rin-ineq-goal! (rin-pt-prems 'f w
                                  (list 'IN '(h1 w) 'RR)
                                  (list 'IN (list 'h1 w) 'RR) (list 'IN (list 'h2 w) 'RR)
                                  (list '<= 0 (list 'h1 w)) (list '<= 0 (list 'h2 w))
                                  (list '= (list 'f w) (list '- (list 'h1 w) (list 'h2 w)))))))))))
    (list pf nf) (list 'h1 'h2))
  (rin-int-finite-below! pf 'h1)
  (rin-int-finite-below! nf 'h2)
  (rin-int-facts! 'h1)
  (rin-int-facts! 'h2)
  ;; f+ + h2 = f- + h1 as functions
  (fact 'measurable-fn-eplus 'omega 'cA pf 'h2)
  (fact 'measurable-fn-eplus 'omega 'cA nf 'h1)
  (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA aa))
  (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA bb))
  (dk-fun-ext! aa bb 'omega 'RR-POS-STAR #f #f
    (lambda (w)
      (dk-apply! hdiff w)
      (rin-real-at! 'h1 w)
      (rin-real-at! 'h2 w)
      (rin-sign-cases! 'f w
        (lambda (tr)
          (rin-pe-at! pf 'h2 w)
          (rin-pe-at! nf 'h1 w)
          (subst (list '= (list aa w) (list '+ (list pf w) (list 'h2 w))))
          (subst (list '= (list bb w) (list '+ (list nf w) (list 'h1 w))))
          (rin-ineq-goal! (rin-pt-prems 'f w
                            (list 'IN (list 'h1 w) 'RR) (list 'IN (list 'h2 w) 'RR)
                            (list '= (list 'f w) (list '- (list 'h1 w) (list 'h2 w)))))))))
  (fact 'integral-additive 'omega 'cA 'mu pf 'h2)
  (fact 'integral-additive 'omega 'cA 'mu nf 'h1)
  (rin-eplus-eq! ip i2)
  (rin-eplus-eq! in i1)
  (dk-have! (list '= (list '+ ip i2) (list '+ in i1))
    (lambda ()
      (subst (list '= (list '+ ip i2) (list 'eplus ip i2)))
      (subst (list '= (list '+ in i1) (list 'eplus in i1)))
      (subst (list '= (list 'eplus ip i2) (list 'INTEGRAL 'omega 'cA 'mu aa)))
      (subst (list '= (list 'eplus in i1) (list 'INTEGRAL 'omega 'cA 'mu bb)))
      (subst (list '= aa bb))
      (fact 'integral-in 'omega 'cA 'mu bb)
      (fact 'rr-pos-star-le-refl (list 'INTEGRAL 'omega 'cA 'mu bb))
      (rfl)))
  (dk-have! '(IS-REAL-MEASURABLE-FN omega cA f)
    (lambda () (mac 'IS-REAL-MEASURABLE-FN) (rin-conj-close! (lambda () (ass)))))
  (dk-have! '(IS-INTEGRABLE omega cA mu f)
    (lambda () (mac 'IS-INTEGRABLE) (rin-conj-close! (lambda () (ass)))))
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
  (rin-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (subst (list '== '(RINTEGRAL omega cA mu f) (list '- ip in)))
            (dk-ineq! (list 'IN ip 'RR) (list 'IN in 'RR) (list 'IN i1 'RR) (list 'IN i2 'RR)
                      (list '= (list '+ ip i2) (list '+ in i1))))))))
(qed 'rintegral-decomposition)
(topic! 'rintegral-decomposition 'analysis)
;;; =====================================================================
;;; (6) small integral facts: the zero function, scaling is measurable,
;;;     the absolute value function
;;; =====================================================================

;;; (= a b) for a, b in RR-POS-STAR with (<= a b), (<= b a) in context
(define (rin-rps-antisym! a b)
  (dk-have! (list 'AND (list 'IN a 'RR-POS-STAR) (list 'IN b 'RR-POS-STAR)))
  (dk-have! (list 'AND (list '<= a b) (list '<= b a)))
  (fact 'rr-pos-star-le-antisymm a b)
  (list '= a b))

;;; (FORALL x (IMPLIES (IN x omega) (BODY x))) proved at a fresh point by PT!
(define (rin-forall-pt! body-of pt!)
  (let ((claim (list 'FORALL 'x (list 'IMPLIES '(IN x omega) (body-of 'x)))))
    (dk-have! claim (lambda () (pt! (dk-di-var!))))
    claim))

;;; (= (etimes u v) (* u v)) for real nonnegative u, v in context
(define (rin-etimes-eq! u v)
  (let ((e (list '= (list 'etimes u v) (list '* u v))))
    (if (not (dk-asm? e))
        (dk-have! e
          (lambda ()
            (fact 'etimes-real-defined u v)
            (subst (list '= (list 'etimes u v) (list 'bintimes u v)))
            (fact 'bintimes-apply u v)
            (subst (list '== (list 'bintimes u v) (list '* u v)))
            (dk-have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
            (fact 'rr-mul-closed u v)
            (rfl))))
    e))

(define rin-zero-fn '(VNB-LAMBDA cx_ omega 0))

;;; integral-zero-fn
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (IMPLIES (IS-MEASURE omega cA mu)
  (= (INTEGRAL omega cA mu (VNB-LAMBDA cx_ omega 0)) 0)))))))
(dk-peel!)
(let* ((ind '(INDICATOR omega EMPTY-SET))
       (iz (list 'INTEGRAL 'omega 'cA 'mu rin-zero-fn))
       (ii (list 'INTEGRAL 'omega 'cA 'mu ind)))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (fact 'rr-zero-in) (fact 'rr-leq-reflexive 0) (rin-rps! 0)
  (fact 'measurable-fn-const 'omega 'cA 0)
  (fact 'sigma-algebra-empty-in 'omega 'cA)
  (fact 'measurable-fn-indicator 'omega 'cA 'EMPTY-SET)
  (dk-have! (list 'PTWISE-LE 'omega rin-zero-fn ind)
    (lambda ()
      (mac 'PTWISE-LE)
      (let ((x (dk-di-var!)))
        (fact 'empty-set-has-no-members x)
        (dk-cite! 'indicator-value-out 'omega 'EMPTY-SET x)
        (subst (list '= (list ind x) 0))
        (if (not (dk-lam-b!)) (dk-ass!)))))
  (fact 'integral-monotone 'omega 'cA 'mu rin-zero-fn ind)
  (fact 'integral-indicator 'omega 'cA 'mu 'EMPTY-SET)
  (dk-rewrite-h! (list '<= iz ii) ii '(mu EMPTY-SET))
  (dk-rewrite-h! (list '<= iz '(mu EMPTY-SET)) '(mu EMPTY-SET) 0)
  (fact 'integral-in 'omega 'cA 'mu rin-zero-fn)
  (fact 'rr-pos-star-nonneg iz)
  (rin-rps-antisym! iz 0)
  (dk-ass!))
(qed 'integral-zero-fn)
(topic! 'integral-zero-fn 'analysis)

;;; ptwise-scale-measurable
(sp (make-wff '(FORALL omega (FORALL cA (FORALL g (FORALL k
  (IMPLIES (IS-MEASURABLE-FN omega cA g) (IMPLIES (IN k RR) (IMPLIES (<= 0 k)
    (IS-MEASURABLE-FN omega cA (PTWISE-SCALE omega k g)))))))))))
(dk-peel!)
(let* ((sc '(PTWISE-SCALE omega k g)) (cf '(VNB-LAMBDA cx_ omega k)))
  (rin-parts! 'IS-MEASURABLE-FN '(omega cA g))
  (fact 'sigma-algebra-ambient-set 'omega 'cA)
  (rin-rps! 'k)
  (fact 'measurable-fn-const 'omega 'cA 'k)
  (dk-have! (list 'IN sc '(FUN omega RR-POS-STAR))
    (lambda ()
      (mac 'PTWISE-SCALE)
      (dk-lam-type!
        (lambda ()
          (let ((x (dk-di-var!)))
            (fact 'fun-apply-type-c 'g 'omega 'RR-POS-STAR x)
            (dk-have! (list 'AND '(IN k RR-POS-STAR) (list 'IN (list 'g x) 'RR-POS-STAR)))
            (fact 'etimes-closed 'k (list 'g x))
            (ass))))))
  (rin-forall-pt! (lambda (x) (list '= (list sc x) (list 'etimes (list cf x) (list 'g x))))
    (lambda (x)
      (fact 'fun-apply-type-c 'g 'omega 'RR-POS-STAR x)
      (dk-have! (list 'AND '(IN k RR-POS-STAR) (list 'IN (list 'g x) 'RR-POS-STAR)))
      (fact 'etimes-closed 'k (list 'g x))
      (mac 'PTWISE-SCALE)
      (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop))))
      (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (rfl))))
  (fact 'measurable-fn-etimes-of-values 'omega 'cA cf 'g sc)
  (dk-ass!))
(qed 'ptwise-scale-measurable)
(topic! 'ptwise-scale-measurable 'analysis)

;;; (PTWISE-EPLUS omega g1 g2) in FUN(omega, RR-POS-STAR), g1, g2 typed so
(define (rin-pe-fun! g1 g2)
  (let ((pe (list 'PTWISE-EPLUS 'omega g1 g2)))
    (dk-have! (list 'IN pe '(FUN omega RR-POS-STAR))
      (lambda ()
        (mac 'PTWISE-EPLUS)
        (dk-lam-type!
          (lambda ()
            (let ((x (dk-di-var!)))
              (fact 'fun-apply-type-c g1 'omega 'RR-POS-STAR x)
              (fact 'fun-apply-type-c g2 'omega 'RR-POS-STAR x)
              (dk-have! (list 'AND (list 'IN (list g1 x) 'RR-POS-STAR) (list 'IN (list g2 x) 'RR-POS-STAR)))
              (fact 'eplus-closed (list g1 x) (list g2 x))
              (ass))))))))

;;; abs-fn-eq-parts
(sp (make-wff '(FORALL omega (FORALL f (IMPLIES (IN f (FUN omega RR))
  (= (ABS-FN omega f) (PTWISE-EPLUS omega (POS-PART omega f) (NEG-PART omega f))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f)) (pe (list 'PTWISE-EPLUS 'omega pf nf)))
  (fact 'fun-domain-in-set 'omega 'RR 'f)
  (fact 'pos-part-fun 'omega 'f)
  (fact 'neg-part-fun 'omega 'f)
  (fact 'abs-fn-fun 'omega 'f)
  (rin-pe-fun! pf nf)
  (dk-fun-ext! '(ABS-FN omega f) pe 'omega 'RR-POS-STAR #f #f
    (lambda (v)
      (rin-parts-at! 'f v)
      (rin-pe-at! pf nf v)
      (dk-cite! 'abs-fn-value 'omega 'f v)
      (subst (list '== (list '(ABS-FN omega f) v) (list 'abs (list 'f v))))
      (subst (list '= (list pe v) (list '+ (list pf v) (list nf v))))
      (dk-ass!))))
(qed 'abs-fn-eq-parts)
(topic! 'abs-fn-eq-parts 'analysis)

;;; integral-abs-fn
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (IMPLIES (IS-MEASURE omega cA mu) (IMPLIES (IS-REAL-MEASURABLE-FN omega cA f)
    (AND (IS-MEASURABLE-FN omega cA (ABS-FN omega f))
         (= (INTEGRAL omega cA mu (ABS-FN omega f))
            (eplus (INTEGRAL omega cA mu (POS-PART omega f)) (INTEGRAL omega cA mu (NEG-PART omega f)))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f)) (pe (list 'PTWISE-EPLUS 'omega pf nf)))
  (rin-parts! 'IS-REAL-MEASURABLE-FN '(omega cA f))
  (fact 'abs-fn-eq-parts 'omega 'f)
  (fact 'measurable-fn-eplus 'omega 'cA pf nf)
  (fact 'integral-additive 'omega 'cA 'mu pf nf)
  (subst (list '= '(ABS-FN omega f) pe))
  (rin-conj-close! (lambda () (dk-ass!))))
(qed 'integral-abs-fn)
(topic! 'integral-abs-fn 'analysis)

;;; integrable-iff-abs-finite
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (IMPLIES (IS-MEASURE omega cA mu) (IMPLIES (IS-REAL-MEASURABLE-FN omega cA f)
    (IFF (IS-INTEGRABLE omega cA mu f)
         (IN (INTEGRAL omega cA mu (ABS-FN omega f)) RR))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
       (ip (list 'INTEGRAL 'omega 'cA 'mu pf)) (in (list 'INTEGRAL 'omega 'cA 'mu nf))
       (ia '(INTEGRAL omega cA mu (ABS-FN omega f))))
  (let ((c (dk-cite! 'integral-abs-fn 'omega 'cA 'mu 'f))) (dk-split! c))
  (dk-have! '(IS-REAL-MEASURABLE-FN omega cA f))
  (rin-parts! 'IS-REAL-MEASURABLE-FN '(omega cA f))
  (rin-int-facts! pf)
  (rin-int-facts! nf)
  (dk-iff! (lambda (g) (equal? g (list 'IN ia 'RR)))
    (lambda ()
      (rin-parts! 'IS-INTEGRABLE '(omega cA mu f))
      (rin-eplus-eq! ip in)
      (subst (list '= ia (list 'eplus ip in)))
      (subst (list '= (list 'eplus ip in) (list '+ ip in)))
      (dk-have! (list 'AND (list 'IN ip 'RR) (list 'IN in 'RR)))
      (fact 'rr-add-closed ip in)
      (dk-ass!))
    (lambda ()
      (dk-have! (list 'AND (list 'IN ip 'RR-POS-STAR) (list 'IN in 'RR-POS-STAR)))
      (dk-have! (list 'AND (list 'IN in 'RR-POS-STAR) (list 'IN ip 'RR-POS-STAR)))
      (fact 'eplus-le-left ip in)
      (fact 'eplus-le-left in ip)
      (fact 'eplus-comm in ip)
      (dk-rewrite-h! (list '<= ip (list 'eplus ip in)) (list 'eplus ip in) ia)
      (dk-rewrite-h! (list '<= in (list 'eplus in ip)) (list 'eplus in ip) (list 'eplus ip in))
      (dk-rewrite-h! (list '<= in (list 'eplus ip in)) (list 'eplus ip in) ia)
      (fact 'integral-in 'omega 'cA 'mu '(ABS-FN omega f))
      (dk-have! (list 'AND (list 'IN ip 'RR-POS-STAR) (list 'IN ia 'RR)))
      (dk-have! (list 'AND (list 'IN in 'RR-POS-STAR) (list 'IN ia 'RR)))
      (fact 'rr-pos-star-le-real-in-rr ip ia)
      (fact 'rr-pos-star-le-real-in-rr in ia)
      (mac 'IS-INTEGRABLE)
      (rin-conj-close! (lambda () (dk-ass!))))))
(qed 'integrable-iff-abs-finite)
(topic! 'integrable-iff-abs-finite 'analysis)
;;; =====================================================================
;;; (7) LINEARITY
;;; =====================================================================

;;; the facts of IS-INTEGRABLE(omega, cA, mu, fv), landed and kept
(define (rin-integrable-setup! fv)
  (let ((pf (rin-pos fv)) (nf (rin-neg fv)))
    (rin-parts! 'IS-INTEGRABLE (list 'omega 'cA 'mu fv))
    (rin-parts! 'IS-REAL-MEASURABLE-FN (list 'omega 'cA fv))
    (fact 'fun-domain-in-set 'omega 'RR fv)
    (fact 'pos-part-fun 'omega fv)
    (fact 'neg-part-fun 'omega fv)
    (rin-int-facts! pf)
    (rin-int-facts! nf)))

;;; (= (s x) val) for an applied VNB-LAMBDA s, val typed in context
(define (rin-lam-at! s x val)
  (let ((e (list '= (list s x) val)))
    (if (not (dk-asm? e))
        (dk-have! e (lambda () (if (not (dk-lam-b!)) (rfl)))))
    e))

;;; Apply rintegral-decomposition to ft = h1 - h2: (IN ft (FUN omega RR)),
;;; IS-MEASURABLE-FN of h1 and h2, and the integrals' finiteness must be in
;;; context; R1! / R2! prove (IN (h x) RR) at x, EQ! proves (= (ft x) (- (h1 x) (h2 x))).
;;; Lands IS-INTEGRABLE(ft) and its RINTEGRAL equation.
(define (rin-apply-decomp! ft h1 h2 r1! r2! eq!)
  (rin-forall-pt! (lambda (x) (list 'IN (list h1 x) 'RR)) r1!)
  (rin-forall-pt! (lambda (x) (list 'IN (list h2 x) 'RR)) r2!)
  (rin-forall-pt! (lambda (x) (list '= (list ft x) (list '- (list h1 x) (list h2 x)))) eq!)
  (let ((c (dk-cite! 'rintegral-decomposition 'omega 'cA 'mu ft h1 h2)))
    (if (not (and (pair? c) (eq? (car c) 'AND)))
        (error "rin-apply-decomp!: an antecedent was not in context" (expression->string c)))
    (dk-split! c)))

;;; IN (INTEGRAL (PTWISE-EPLUS g1 g2)) RR with its value + in context, g1, g2
;;; measurable of finite nonnegative integral
(define (rin-int-pe! g1 g2)
  (let* ((pe (list 'PTWISE-EPLUS 'omega g1 g2))
         (i1 (list 'INTEGRAL 'omega 'cA 'mu g1)) (i2 (list 'INTEGRAL 'omega 'cA 'mu g2))
         (ie (list 'INTEGRAL 'omega 'cA 'mu pe)))
    (fact 'measurable-fn-eplus 'omega 'cA g1 g2)
    (fact 'integral-additive 'omega 'cA 'mu g1 g2)
    (rin-eplus-eq! i1 i2)
    (dk-have! (list 'AND (list 'IN i1 'RR) (list 'IN i2 'RR)))
    (fact 'rr-add-closed i1 i2)
    (dk-have! (list '= ie (list '+ i1 i2))
      (lambda () (subst (list '= ie (list 'eplus i1 i2))) (dk-ass!)))
    (dk-have! (list 'IN ie 'RR)
      (lambda () (subst (list '= ie (list '+ i1 i2))) (dk-ass!)))))

(define rin-sum '(VNB-LAMBDA sx_ omega (+ (f sx_) (g sx_))))

;;; rintegral-add
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL g
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IS-INTEGRABLE omega cA mu g)
    (AND (IS-INTEGRABLE omega cA mu (VNB-LAMBDA sx_ omega (+ (f sx_) (g sx_))))
         (= (RINTEGRAL omega cA mu (VNB-LAMBDA sx_ omega (+ (f sx_) (g sx_))))
            (+ (RINTEGRAL omega cA mu f) (RINTEGRAL omega cA mu g))))))))))))))
(dk-peel!)
(let* ((s rin-sum)
       (pf (rin-pos 'f)) (nf (rin-neg 'f)) (pg (rin-pos 'g)) (ng (rin-neg 'g))
       (h1 (list 'PTWISE-EPLUS 'omega pf pg)) (h2 (list 'PTWISE-EPLUS 'omega nf ng))
       (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
       (rint (lambda (u) (list 'RINTEGRAL 'omega 'cA 'mu u)))
       (pt! (lambda (x)
              (rin-parts-at! 'f x) (rin-parts-at! 'g x)
              (rin-pe-at! pf pg x) (rin-pe-at! nf ng x))))
  (rin-integrable-setup! 'f)
  (rin-integrable-setup! 'g)
  (rin-int-pe! pf pg)
  (rin-int-pe! nf ng)
  (dk-have! (list 'IN s '(FUN omega RR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((x (dk-di-var!)))
            (fact 'fun-apply-type-c 'f 'omega 'RR x)
            (fact 'fun-apply-type-c 'g 'omega 'RR x)
            (dk-have! (list 'AND (list 'IN (list 'f x) 'RR) (list 'IN (list 'g x) 'RR)))
            (fact 'rr-add-closed (list 'f x) (list 'g x))
            (ass))))))
  (rin-apply-decomp! s h1 h2
    (lambda (x) (pt! x) (subst (list '= (list h1 x) (list '+ (list pf x) (list pg x)))) (dk-ass!))
    (lambda (x) (pt! x) (subst (list '= (list h2 x) (list '+ (list nf x) (list ng x)))) (dk-ass!))
    (lambda (x)
      (pt! x)
      (fact 'fun-apply-type-c 'f 'omega 'RR x)
      (fact 'fun-apply-type-c 'g 'omega 'RR x)
      (dk-have! (list 'AND (list 'IN (list 'f x) 'RR) (list 'IN (list 'g x) 'RR)))
      (fact 'rr-add-closed (list 'f x) (list 'g x))
      (rin-lam-at! s x (list '+ (list 'f x) (list 'g x)))
      (subst (list '= (list s x) (list '+ (list 'f x) (list 'g x))))
      (subst (list '= (list h1 x) (list '+ (list pf x) (list pg x))))
      (subst (list '= (list h2 x) (list '+ (list nf x) (list ng x))))
      (rin-ineq-goal! (append (rin-pt-prems 'f x) (rin-pt-prems 'g x)))))
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'g)
  (rin-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (subst (list '= (rint s) (list '- (int h1) (int h2))))
            (subst (list '== (rint 'f) (list '- (int pf) (int nf))))
            (subst (list '== (rint 'g) (list '- (int pg) (int ng))))
            (subst (list '= (int h1) (list '+ (int pf) (int pg))))
            (subst (list '= (int h2) (list '+ (int nf) (int ng))))
            (crs))))))
(qed 'rintegral-add)
(topic! 'rintegral-add 'analysis)

;;; ---------------------------------------------------------------------
;;; scalar multiples

;;; (= ((PTWISE-SCALE omega k g) x) (* k (g x))), k, g x real >= 0 in context
(define (rin-sc-at! k g x)
  (let* ((sc (list 'PTWISE-SCALE 'omega k g)) (gx (list g x)))
    (rin-etimes-eq! k gx)
    (dk-have! (list 'AND (list 'IN k 'RR) (list 'IN gx 'RR)))
    (fact 'rr-mul-closed k gx)
    (dk-cite! 'ptwise-scale-value-q 'omega k g x)
    (dk-have! (list '= (list sc x) (list '* k gx))
      (lambda ()
        (subst (list '== (list sc x) (list 'etimes k gx)))
        (subst (list '= (list 'etimes k gx) (list '* k gx)))
        (rfl)))
    (list '= (list sc x) (list '* k gx))))

;;; INTEGRAL(PTWISE-SCALE k g) = k * INTEGRAL(g), in RR; g measurable, finite integral
(define (rin-int-sc! k g)
  (let* ((sc (list 'PTWISE-SCALE 'omega k g))
         (ig (list 'INTEGRAL 'omega 'cA 'mu g)) (is (list 'INTEGRAL 'omega 'cA 'mu sc)))
    (fact 'ptwise-scale-measurable 'omega 'cA g k)
    (fact 'integral-homogeneous 'omega 'cA 'mu g k)
    (rin-etimes-eq! k ig)
    (dk-have! (list 'AND (list 'IN k 'RR) (list 'IN ig 'RR)))
    (fact 'rr-mul-closed k ig)
    (dk-have! (list '= is (list '* k ig))
      (lambda () (subst (list '= is (list 'etimes k ig))) (dk-ass!)))
    (dk-have! (list 'IN is 'RR)
      (lambda () (subst (list '= is (list '* k ig))) (dk-ass!)))))

(define rin-scl '(VNB-LAMBDA sx_ omega (* c (f sx_))))

;;; the case (k, first part, second part): c >= 0 is (c, f+, f-), c < 0 is (-c, f-, f+)
(define (rin-scale-case! k pa pb)
  (let* ((s rin-scl)
         (pf (rin-pos 'f)) (nf (rin-neg 'f))
         (h1 (list 'PTWISE-SCALE 'omega k pa)) (h2 (list 'PTWISE-SCALE 'omega k pb))
         (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
         (rint (lambda (u) (list 'RINTEGRAL 'omega 'cA 'mu u)))
         (pt! (lambda (x)
                (rin-parts-at! 'f x)
                (rin-sc-at! k pa x) (rin-sc-at! k pb x))))
    (rin-int-sc! k pa)
    (rin-int-sc! k pb)
    (rin-apply-decomp! s h1 h2
      (lambda (x) (pt! x) (subst (list '= (list h1 x) (list '* k (list pa x)))) (dk-ass!))
      (lambda (x) (pt! x) (subst (list '= (list h2 x) (list '* k (list pb x)))) (dk-ass!))
      (lambda (x)
        (pt! x)
        (fact 'fun-apply-type-c 'f 'omega 'RR x)
        (dk-have! (list 'AND '(IN c RR) (list 'IN (list 'f x) 'RR)))
        (fact 'rr-mul-closed 'c (list 'f x))
        (rin-lam-at! s x (list '* 'c (list 'f x)))
        (subst (list '= (list s x) (list '* 'c (list 'f x))))
        (subst (list '= (list h1 x) (list '* k (list pa x))))
        (subst (list '= (list h2 x) (list '* k (list pb x))))
        (subst (list '= (list 'f x) (list '- (list pf x) (list nf x))))
        (crs)))
    (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
    (rin-conj-close!
      (lambda ()
        (if (dk-asm? (dk-goal))
            (ass)
            (begin
              (subst (list '= (rint s) (list '- (int h1) (int h2))))
              (subst (list '== (rint 'f) (list '- (int pf) (int nf))))
              (subst (list '= (int h1) (list '* k (int pa))))
              (subst (list '= (int h2) (list '* k (int pb))))
              (crs)))))))

;;; rintegral-scale
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL c
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IN c RR)
    (AND (IS-INTEGRABLE omega cA mu (VNB-LAMBDA sx_ omega (* c (f sx_))))
         (= (RINTEGRAL omega cA mu (VNB-LAMBDA sx_ omega (* c (f sx_))))
            (* c (RINTEGRAL omega cA mu f))))))))))))))
(dk-peel!)
(rin-integrable-setup! 'f)
(dk-have! (list 'IN rin-scl '(FUN omega RR))
  (lambda ()
    (dk-lam-type!
      (lambda ()
        (let ((x (dk-di-var!)))
          (fact 'fun-apply-type-c 'f 'omega 'RR x)
          (dk-have! (list 'AND '(IN c RR) (list 'IN (list 'f x) 'RR)))
          (fact 'rr-mul-closed 'c (list 'f x))
          (ass))))))
(use-em '(<= 0 c)
  (lambda () (rin-scale-case! 'c (rin-pos 'f) (rin-neg 'f)))
  (lambda ()
    (fact 'rr-not-le-lt 0 'c)
    (fact 'rr-neg-closed 'c)
    (dk-have! '(<= 0 (- c)) (lambda () (dk-ineq! '(IN c RR) '(< c 0))))
    (rin-scale-case! '(- c) (rin-neg 'f) (rin-pos 'f))))
(qed 'rintegral-scale)
(topic! 'rintegral-scale 'analysis)
;;; =====================================================================
;;; (8) MONOTONICITY (also off a null set), |RINTEGRAL f| <= INTEGRAL |f|,
;;;     the nonnegative case, equality off a null set (Prop. 2.21),
;;;     the integral over a set
;;; =====================================================================

;;; IS-NULL-SET(omega, cA, mu, ns) in context: lands (IN nb cA), (SUBSET ns nb),
;;; (= (mu nb) 0) for a fresh nb, returned
(define (rin-null-witness! ns)
  (let* ((iff (dk-cite! 'is-null-set 'omega 'cA 'mu ns))
         (rhs (caddr iff)))
    (dk-have! rhs (lambda () (rin-keep-prop! iff (list 'IS-NULL-SET 'omega 'cA 'mu ns))))
    (dk-skolem! (dk-ctx-form rhs))))

;;; (SUBSET a b), (IN x a) in context: lands (IN x b)
(define (rin-subset-elim! a b x)
  (dk-have! (list 'IN x b)
    (lambda ()
      (let* ((iff (dk-cite! 'subset-def a b)) (rhs (caddr iff)))
        (dk-have! rhs (lambda () (rin-keep-prop! iff (list 'SUBSET a b))))
        (dk-apply! (dk-ctx-form rhs) x)
        (dk-ass!)))))

;;; (NOT (IN x nb)), (SUBSET ns nb) in context: lands (NOT (IN x ns))
(define (rin-not-in-ns! ns nb x)
  (dk-have! (list 'NOT (list 'IN x ns))
    (lambda ()
      (di)
      (rin-subset-elim! ns nb x)
      (rin-keep-prop! (list 'IN x nb) (list 'NOT (list 'IN x nb))))))

;;; (FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x nb)) (<= (u x) (v x))))) by PT!
;;; (run at x with (NOT (IN x nb)) in context), then INTEGRAL(u) <= INTEGRAL(v)
(define (rin-off-null-le! nb u v pt!)
  (let ((claim (list 'FORALL 'x (list 'IMPLIES '(IN x omega)
                 (list 'IMPLIES (list 'NOT (list 'IN 'x nb)) (list '<= (list u 'x) (list v 'x)))))))
    (dk-have! claim (lambda () (let ((x (dk-di-var!))) (di) (pt! x))))
    (fact 'integral-le-off-null 'omega 'cA 'mu nb u v)))

;;; rintegral-mono-off-null
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL g (FORALL ns
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IS-INTEGRABLE omega cA mu g)
  (IMPLIES (IS-NULL-SET omega cA mu ns)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x ns)) (<= (f x) (g x)))))
    (<= (RINTEGRAL omega cA mu f) (RINTEGRAL omega cA mu g)))))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f)) (pg (rin-pos 'g)) (ng (rin-neg 'g))
       (aa (list 'PTWISE-EPLUS 'omega pf ng)) (bb (list 'PTWISE-EPLUS 'omega pg nf))
       (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
       (hle '(FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x ns)) (<= (f x) (g x)))))))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-integrable-setup! 'f)
  (rin-integrable-setup! 'g)
  (rin-int-pe! pf ng)
  (rin-int-pe! pg nf)
  (let ((nb (rin-null-witness! 'ns)))
    (rin-off-null-le! nb aa bb
      (lambda (x)
        (rin-not-in-ns! 'ns nb x)
        (dk-apply! hle x)
        (rin-parts-at! 'f x) (rin-parts-at! 'g x)
        (rin-pe-at! pf ng x) (rin-pe-at! pg nf x)
        (subst (list '= (list aa x) (list '+ (list pf x) (list ng x))))
        (subst (list '= (list bb x) (list '+ (list pg x) (list nf x))))
        (rin-ineq-goal! (append (rin-pt-prems 'f x) (rin-pt-prems 'g x)
                                (list (list '<= (list 'f x) (list 'g x)))))))
    (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
    (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'g)
    (subst (list '== '(RINTEGRAL omega cA mu f) (list '- (int pf) (int nf))))
    (subst (list '== '(RINTEGRAL omega cA mu g) (list '- (int pg) (int ng))))
    (let ((h1 (dk-rewrite-h! (list '<= (int aa) (int bb)) (int aa) (list '+ (int pf) (int ng)))))
      (dk-rewrite-h! h1 (int bb) (list '+ (int pg) (int nf))))
    (dk-ineq! (list 'IN (int pf) 'RR) (list 'IN (int nf) 'RR) (list 'IN (int pg) 'RR) (list 'IN (int ng) 'RR)
              (list '<= (list '+ (int pf) (int ng)) (list '+ (int pg) (int nf))))))
(qed 'rintegral-mono-off-null)
(topic! 'rintegral-mono-off-null 'analysis)

;;; IS-NULL-SET(omega, cA, mu, EMPTY-SET), IS-MEASURE parts in context
(define (rin-empty-null!)
  (dk-have! '(IS-NULL-SET omega cA mu EMPTY-SET)
    (lambda ()
      (fact 'sigma-algebra-empty-in 'omega 'cA)
      (fact 'subset-refl 'EMPTY-SET)
      (mac 'IS-NULL-SET)
      (ew 'EMPTY-SET)
      (rin-conj-close! (lambda () (dk-ass!))))))

;;; rintegral-monotone
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL g
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IS-INTEGRABLE omega cA mu g)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (<= (f x) (g x))))
    (<= (RINTEGRAL omega cA mu f) (RINTEGRAL omega cA mu g)))))))))))))
(dk-peel!)
(rin-parts! 'IS-MEASURE '(omega cA mu))
(rin-empty-null!)
(dk-have! '(FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x EMPTY-SET)) (<= (f x) (g x)))))
  (lambda ()
    (let ((x (dk-di-var!)))
      (di)
      (dk-apply! '(FORALL x (IMPLIES (IN x omega) (<= (f x) (g x)))) x)
      (dk-ass!))))
(fact 'rintegral-mono-off-null 'omega 'cA 'mu 'f 'g 'EMPTY-SET)
(dk-ass!)
(qed 'rintegral-monotone)
(topic! 'rintegral-monotone 'analysis)

;;; rintegral-abs-le
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
    (<= (abs (RINTEGRAL omega cA mu f)) (INTEGRAL omega cA mu (ABS-FN omega f)))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
       (ip (list 'INTEGRAL 'omega 'cA 'mu pf)) (in (list 'INTEGRAL 'omega 'cA 'mu nf))
       (ia '(INTEGRAL omega cA mu (ABS-FN omega f)))
       (d (list '- ip in)) (sm (list '+ ip in)))
  (rin-integrable-setup! 'f)
  (let ((c (dk-cite! 'integral-abs-fn 'omega 'cA 'mu 'f))) (dk-split! c))
  (rin-eplus-eq! ip in)
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
  (subst (list '== '(RINTEGRAL omega cA mu f) d))
  (subst (list '= ia (list 'eplus ip in)))
  (subst (list '= (list 'eplus ip in) sm))
  (fact 'rr-sub-in-rr ip in)
  (dk-have! (list 'AND (list 'IN ip 'RR) (list 'IN in 'RR)))
  (fact 'rr-add-closed ip in)
  (dk-have! (list '<= (list '- sm) d)
    (lambda () (dk-ineq! (list 'IN ip 'RR) (list 'IN in 'RR) (list '<= 0 ip) (list '<= 0 in))))
  (dk-have! (list '<= d sm)
    (lambda () (dk-ineq! (list 'IN ip 'RR) (list 'IN in 'RR) (list '<= 0 ip) (list '<= 0 in))))
  (fact 'rr-abs-le-of-parts d sm)
  (dk-ass!))
(qed 'rintegral-abs-le)
(topic! 'rintegral-abs-le 'analysis)

;;; rintegral-of-nonneg
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (<= 0 (f x))))
    (AND (IS-MEASURABLE-FN omega cA f)
         (= (RINTEGRAL omega cA mu f) (INTEGRAL omega cA mu f))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f)) (cz rin-zero-fn)
       (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
       (hpos '(FORALL x (IMPLIES (IN x omega) (<= 0 (f x)))))
       (at! (lambda (x)
              (dk-apply! hpos x)
              (fact 'fun-apply-type-c 'f 'omega 'RR x)
              (rin-parts-at! 'f x)
              (let ((c (dk-cite! 'part-values-nonneg 'omega 'f x))) (dk-split! c)))))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-integrable-setup! 'f)
  (fact 'rr-zero-in) (fact 'rr-leq-reflexive 0) (rin-rps! 0)
  (fact 'measurable-fn-const 'omega 'cA 0)
  (dk-have! '(IN f (FUN omega RR-POS-STAR))
    (lambda ()
      (dk-have! '(IN f (FUN omega))
        (lambda ()
          (mac-h 'fun-codomain-iff (dk-ctx-form '(IN f (FUN omega RR))))
          (dk-split-all!)
          (ass)))
      (mac 'fun-codomain-iff)
      (rin-conj-close!
        (lambda ()
          (if (dk-asm? (dk-goal))
              (ass)
              (let ((x (dk-di-var!)))
                (at! x)
                (rin-rps! (list 'f x))
                (dk-ass!)))))))
  (rin-forall-pt! (lambda (x) (list '= (list 'f x) (list 'eplus (list pf x) (list cz x))))
    (lambda (x)
      (at! x)
      (rin-lam-at! cz x 0)
      (rin-rps! (list 'f x))
      (fact 'eplus-zero-right (list 'f x))
      (subst (list '= (list cz x) 0))
      (subst (list '= (list pf x) (list 'f x)))
      (subst (list '= (list 'eplus (list 'f x) 0) (list 'f x)))
      (rfl)))
  (fact 'measurable-fn-eplus-of-values 'omega 'cA pf cz 'f)
  (for-each
    (lambda (u v)
      (dk-have! (list 'PTWISE-LE 'omega u v)
        (lambda ()
          (mac 'PTWISE-LE)
          (let ((x (dk-di-var!)))
            (at! x)
            (if (equal? v cz)
                (begin (rin-lam-at! cz x 0) (subst (list '= (list cz x) 0))))
            (rin-ineq-goal! (rin-pt-prems 'f x '(IN 0 RR)))))))
    (list 'f pf nf) (list pf 'f cz))
  (fact 'integral-monotone 'omega 'cA 'mu 'f pf)
  (fact 'integral-monotone 'omega 'cA 'mu pf 'f)
  (fact 'integral-monotone 'omega 'cA 'mu nf cz)
  (fact 'integral-zero-fn 'omega 'cA 'mu)
  (rin-int-facts! 'f)
  (rin-int-facts! cz)
  (rin-rps-antisym! (int pf) (int 'f))
  (dk-rewrite-h! (list '<= (int nf) (int cz)) (int cz) 0)
  (rin-rps-antisym! (int nf) 0)
  (dk-have! (list 'IN (int 'f) 'RR) (lambda () (subst (list '= (int 'f) (int pf))) (dk-ass!)))
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
  (rin-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (subst (list '== '(RINTEGRAL omega cA mu f) (list '- (int pf) (int nf))))
            (dk-ineq! (list 'IN (int pf) 'RR) (list 'IN (int nf) 'RR) (list 'IN (int 'f) 'RR)
                      (list '= (int pf) (int 'f)) (list '= (int nf) 0)))))))
(qed 'rintegral-of-nonneg)
(topic! 'rintegral-of-nonneg 'analysis)

;;; rintegral-ae-eq (Prop. 2.21 for a real f)
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL g (FORALL ns
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IS-REAL-MEASURABLE-FN omega cA g)
  (IMPLIES (IS-NULL-SET omega cA mu ns)
  (IMPLIES (FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x ns)) (= (f x) (g x)))))
    (AND (IS-INTEGRABLE omega cA mu g)
         (= (RINTEGRAL omega cA mu g) (RINTEGRAL omega cA mu f))))))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f)) (pg (rin-pos 'g)) (ng (rin-neg 'g))
       (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
       (heq '(FORALL x (IMPLIES (IN x omega) (IMPLIES (NOT (IN x ns)) (= (f x) (g x)))))))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-integrable-setup! 'f)
  (rin-parts! 'IS-REAL-MEASURABLE-FN '(omega cA g))
  (fact 'pos-part-fun 'omega 'g)
  (fact 'neg-part-fun 'omega 'g)
  (rin-int-facts! pg)
  (rin-int-facts! ng)
  (let ((nb (rin-null-witness! 'ns)))
    (for-each
      (lambda (u v)
        (rin-off-null-le! nb u v
          (lambda (x)
            (rin-not-in-ns! 'ns nb x)
            (dk-apply! heq x)
            (rin-sign-cases! 'f x
              (lambda (tr1)
                (rin-sign-cases! 'g x
                  (lambda (tr2)
                    (rin-ineq-goal! (append (rin-pt-prems 'f x) (rin-pt-prems 'g x)
                                            (list (list '= (list 'f x) (list 'g x))))))))))))
      (list pf pg nf ng) (list pg pf ng nf)))
  (rin-rps-antisym! (int pg) (int pf))
  (rin-rps-antisym! (int ng) (int nf))
  (dk-have! (list 'IN (int pg) 'RR) (lambda () (subst (list '= (int pg) (int pf))) (dk-ass!)))
  (dk-have! (list 'IN (int ng) 'RR) (lambda () (subst (list '= (int ng) (int nf))) (dk-ass!)))
  (dk-have! '(IS-INTEGRABLE omega cA mu g)
    (lambda () (mac 'IS-INTEGRABLE) (rin-conj-close! (lambda () (dk-ass!)))))
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'f)
  (dk-cite! 'rintegral-unfold 'omega 'cA 'mu 'g)
  (rin-conj-close!
    (lambda ()
      (if (dk-asm? (dk-goal))
          (ass)
          (begin
            (subst (list '== '(RINTEGRAL omega cA mu g) (list '- (int pg) (int ng))))
            (subst (list '== '(RINTEGRAL omega cA mu f) (list '- (int pf) (int nf))))
            (dk-ineq! (list 'IN (int pf) 'RR) (list 'IN (int nf) 'RR)
                      (list 'IN (int pg) 'RR) (list 'IN (int ng) 'RR)
                      (list '= (int pg) (int pf)) (list '= (int ng) (int nf))))))))
(qed 'rintegral-ae-eq)
(topic! 'rintegral-ae-eq 'analysis)
;;; ---------------------------------------------------------------------
;;; the integral over a set A in cA: RINTEGRAL of x |-> f(x) * INDICATOR(omega, A)(x)

;;; split on (IN x a): land (= ((INDICATOR omega a) x) V), its typing in RR and
;;; 0 <= it; run (K V) with V = 1 (inside) or 0 (outside)
(define (rin-ind-cases! a x k)
  (let ((ix (list (list 'INDICATOR 'omega a) x)))
    (use-em (list 'IN x a)
      (lambda ()
        (dk-cite! 'indicator-value-in 'omega a x)
        (fact 'rr-one-in)
        (dk-have! (list 'IN ix 'RR) (lambda () (subst (list '= ix 1)) (dk-ass!)))
        (dk-have! (list '<= 0 ix) (lambda () (subst (list '= ix 1)) (dk-ineq!)))
        (k 1))
      (lambda ()
        (dk-cite! 'indicator-value-out 'omega a x)
        (fact 'rr-zero-in)
        (dk-have! (list 'IN ix 'RR) (lambda () (subst (list '= ix 0)) (dk-ass!)))
        (dk-have! (list '<= 0 ix) (lambda () (subst (list '= ix 0)) (dk-ineq!)))
        (k 0)))))

;;; (= ((PTWISE-ETIMES omega g1 g2) x) (* (g1 x) (g2 x))), g1 x, g2 x real >= 0 in context
(define (rin-pt-at! g1 g2 x)
  (let* ((w (list 'PTWISE-ETIMES 'omega g1 g2)) (ax (list g1 x)) (bx (list g2 x)))
    (rin-etimes-eq! ax bx)
    (dk-have! (list 'AND (list 'IN ax 'RR) (list 'IN bx 'RR)))
    (fact 'rr-mul-closed ax bx)
    (dk-cite! 'ptwise-etimes-value-q 'omega g1 g2 x)
    (dk-have! (list '= (list w x) (list '* ax bx))
      (lambda ()
        (subst (list '== (list w x) (list 'etimes ax bx)))
        (subst (list '= (list 'etimes ax bx) (list '* ax bx)))
        (rfl)))
    (list '= (list w x) (list '* ax bx))))

(define (rin-rstr a) (list 'VNB-LAMBDA 'rx_ 'omega (list '* '(f rx_) (list (list 'INDICATOR 'omega a) 'rx_))))

;;; rintegral-restrict
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f (FORALL aa
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (IN aa cA)
    (AND (IS-INTEGRABLE omega cA mu (VNB-LAMBDA rx_ omega (* (f rx_) ((INDICATOR omega aa) rx_))))
         (= (RINTEGRAL omega cA mu (VNB-LAMBDA rx_ omega (* (f rx_) ((INDICATOR omega aa) rx_))))
            (- (INTEGRAL omega cA mu (PTWISE-ETIMES omega (POS-PART omega f) (INDICATOR omega aa)))
               (INTEGRAL omega cA mu (PTWISE-ETIMES omega (NEG-PART omega f) (INDICATOR omega aa))))))))))))))))
(dk-peel!)
(let* ((s (rin-rstr 'aa)) (ind '(INDICATOR omega aa))
       (pf (rin-pos 'f)) (nf (rin-neg 'f))
       (h1 (list 'PTWISE-ETIMES 'omega pf ind)) (h2 (list 'PTWISE-ETIMES 'omega nf ind))
       (pt! (lambda (x k)
              (rin-parts-at! 'f x)
              (rin-ind-cases! 'aa x
                (lambda (v)
                  (rin-pt-at! pf ind x) (rin-pt-at! nf ind x)
                  (k v))))))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-integrable-setup! 'f)
  (fact 'measurable-fn-indicator 'omega 'cA 'aa)
  (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA ind))
  (fact 'measurable-fn-etimes 'omega 'cA pf ind)
  (fact 'measurable-fn-etimes 'omega 'cA nf ind)
  (for-each
    (lambda (h g)
      (dk-have! (list 'PTWISE-LE 'omega h g)
        (lambda ()
          (mac 'PTWISE-LE)
          (let ((x (dk-di-var!)))
            (pt! x
              (lambda (v)
                (subst (list '= (list h x) (list '* (list g x) (list ind x))))
                (subst (list '= (list ind x) v))
                (rin-ineq-goal! (rin-pt-prems 'f x)))))))
      (rin-int-finite-below! h g))
    (list h1 h2) (list pf nf))
  (dk-have! (list 'IN s '(FUN omega RR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((x (dk-di-var!)))
            (fact 'fun-apply-type-c 'f 'omega 'RR x)
            (rin-ind-cases! 'aa x
              (lambda (v)
                (dk-have! (list 'AND (list 'IN (list 'f x) 'RR) (list 'IN (list ind x) 'RR)))
                (fact 'rr-mul-closed (list 'f x) (list ind x))
                (ass))))))))
  (rin-apply-decomp! s h1 h2
    (lambda (x) (pt! x (lambda (v) (subst (list '= (list h1 x) (list '* (list pf x) (list ind x)))) (dk-ass!))))
    (lambda (x) (pt! x (lambda (v) (subst (list '= (list h2 x) (list '* (list nf x) (list ind x)))) (dk-ass!))))
    (lambda (x)
      (pt! x
        (lambda (v)
          (dk-have! (list 'AND (list 'IN (list 'f x) 'RR) (list 'IN (list ind x) 'RR)))
          (fact 'rr-mul-closed (list 'f x) (list ind x))
          (rin-lam-at! s x (list '* (list 'f x) (list ind x)))
          (subst (list '= (list s x) (list '* (list 'f x) (list ind x))))
          (subst (list '= (list h1 x) (list '* (list pf x) (list ind x))))
          (subst (list '= (list h2 x) (list '* (list nf x) (list ind x))))
          (subst (list '= (list 'f x) (list '- (list pf x) (list nf x))))
          (crs)))))
  (rin-conj-close! (lambda () (dk-ass!))))
(qed 'rintegral-restrict)
(topic! 'rintegral-restrict 'analysis)
;;; =====================================================================
;;; (9) PROP. 2.24: if the integral of f over every A in cA is >= 0, then
;;;     { x : f(x) < 0 } is a null set.  The notes' route: A_n = { f <= -1/n }
;;;     has measure 0, and { f < 0 } is the union of the A_n.  Here
;;;     A_n = { x : 1 <= (n+1) f-(x) }, which is the same set and is measurable
;;;     by measurable-fn-ge applied to the scaled negative part.
;;; =====================================================================

(define (rin-sn k) (list 'PTWISE-SCALE 'omega (list '+ k 1) (rin-neg 'f)))
(define (rin-an k) (list 'SEP 'gx_ 'omega (list '<= 1 (list (rin-sn k) 'gx_))))
(define rin-fam (list 'VNB-LAMBDA 'n_ 'NN (rin-an 'n_)))
(define rin-nla (list 'BIG-UNION 'n_ 'NN (list rin-fam 'n_)))
(define rin-negset '(SEP nx_ omega (< (f nx_) 0)))

;;; c = k + 1 for k in NN: lands (IN c RR), (<= 0 c), (< 0 c), (IN c RR-POS-STAR)
(define (rin-succ-facts! k)
  (let ((c (list '+ k 1)))
    (fact 'nn-in-rr k)
    (fact 'nn-zero-le k)
    (fact 'rr-one-in)
    (dk-have! (list 'AND (list 'IN k 'RR) '(IN 1 RR)))
    (fact 'rr-add-closed k 1)
    (dk-have! (list '<= 0 c) (lambda () (dk-ineq! (list 'IN k 'RR) (list '<= 0 k))))
    (dk-have! (list '< 0 c) (lambda () (dk-ineq! (list 'IN k 'RR) (list '<= 0 k))))
    (rin-rps! c)
    c))

;;; the measure of A_k is 0: proved at the eigenvariable k (in NN)
(define (rin-ak-null! k)
  (let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
         (c (rin-succ-facts! k))
         (sk (rin-sn k)) (ak (rin-an k))
         (ind (list 'INDICATOR 'omega ak))
         (g (rin-rstr ak))
         (h1 (list 'PTWISE-ETIMES 'omega pf ind)) (h2 (list 'PTWISE-ETIMES 'omega nf ind))
         (sc (list 'PTWISE-SCALE 'omega c h2))
         (cz rin-zero-fn)
         (int (lambda (u) (list 'INTEGRAL 'omega 'cA 'mu u)))
         (hA '(FORALL aa (IMPLIES (IN aa cA)
                (<= 0 (RINTEGRAL omega cA mu (VNB-LAMBDA rx_ omega (* (f rx_) ((INDICATOR omega aa) rx_))))))))
         (pt! (lambda (x k2)
                (rin-parts-at! 'f x)
                (rin-ind-cases! ak x
                  (lambda (v)
                    (rin-pt-at! pf ind x) (rin-pt-at! nf ind x)
                    (k2 v)))))
         ;; x in A_k: lands (<= 1 (* c (f- x)))
         (in-ak! (lambda (x)
                   (let ((nx (list nf x)))
                     (dk-have! (list '<= 1 (list sk x)) (lambda () (sep-me (list 'IN x ak)) (dk-ass!)))
                     (rin-sc-at! c nf x)
                     (dk-rewrite-h! (list '<= 1 (list sk x)) (list sk x) (list '* c nx))))))
    (fact 'ptwise-scale-measurable 'omega 'cA nf c)
    (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA sk))
    (fact 'measurable-fn-ge 'omega 'cA sk 1)
    (dk-apply! hA ak)
    (let ((r (dk-cite! 'rintegral-restrict 'omega 'cA 'mu 'f ak))) (dk-split! r))
    (fact 'measurable-fn-indicator 'omega 'cA ak)
    (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA ind))
    (fact 'measurable-fn-etimes 'omega 'cA pf ind)
    (fact 'measurable-fn-etimes 'omega 'cA nf ind)
    (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA h2))
    (fact 'rr-zero-in)
    (fact 'rr-leq-reflexive 0)
    (rin-rps! 0)
    (fact 'measurable-fn-const 'omega 'cA 0)
    ;; INTEGRAL(f+ * 1_A) = 0: f+ vanishes on A_k
    (dk-have! (list 'PTWISE-LE 'omega h1 cz)
      (lambda ()
        (mac 'PTWISE-LE)
        (let ((x (dk-di-var!)))
          (pt! x
            (lambda (v)
              (rin-lam-at! cz x 0)
              (subst (list '= (list cz x) 0))
              (subst (list '= (list h1 x) (list '* (list pf x) (list ind x))))
              (subst (list '= (list ind x) v))
              (if (equal? v 0)
                  (rin-ineq-goal! (rin-pt-prems 'f x))
                  (begin
                    (in-ak! x)
                    (rin-sign-cases! 'f x
                      (lambda (tr)
                        (if tr
                            (dk-rewrite-h! (list '<= 1 (list '* c (list nf x))) (list nf x) 0))
                        (rin-ineq-goal! (rin-pt-prems 'f x (list 'IN k 'RR)
                                          (list '<= 1 (list '* c 0)))))))))))))
    (fact 'integral-monotone 'omega 'cA 'mu h1 cz)
    (fact 'integral-zero-fn 'omega 'cA 'mu)
    (rin-int-facts! h1)
    (rin-int-facts! cz)
    (dk-rewrite-h! (list '<= (int h1) (int cz)) (int cz) 0)
    (fact 'rr-leq-reflexive 0)
    (rin-rps! 0)
    (rin-rps-antisym! (int h1) 0)
    ;; INTEGRAL(f- * 1_A) is finite, hence 0
    (dk-have! (list 'PTWISE-LE 'omega h2 nf)
      (lambda ()
        (mac 'PTWISE-LE)
        (let ((x (dk-di-var!)))
          (pt! x
            (lambda (v)
              (subst (list '= (list h2 x) (list '* (list nf x) (list ind x))))
              (subst (list '= (list ind x) v))
              (rin-ineq-goal! (rin-pt-prems 'f x)))))))
    (rin-int-finite-below! h2 nf)
    (dk-have! (list 'IN (int h1) 'RR) (lambda () (subst (list '= (int h1) 0)) (dk-ass!)))
    (dk-have! (list '<= 0 (list '- (int h1) (int h2)))
      (lambda () (subst (list '= (list '- (int h1) (int h2)) (list 'RINTEGRAL 'omega 'cA 'mu g))) (dk-ass!)))
    (dk-have! (list '= (int h2) 0)
      (lambda () (dk-ineq! (list 'IN (int h1) 'RR) (list 'IN (int h2) 'RR) (list '= (int h1) 0)
                           (list '<= 0 (int h2)) (list '<= 0 (list '- (int h1) (int h2))))))
    ;; mu(A_k) = INTEGRAL(1_A) <= INTEGRAL(c (f- 1_A)) = c * 0
    (fact 'ptwise-scale-measurable 'omega 'cA h2 c)
    (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA sc))
    (dk-have! (list 'PTWISE-LE 'omega ind sc)
      (lambda ()
        (mac 'PTWISE-LE)
        (let ((x (dk-di-var!)))
          (pt! x
            (lambda (v)
              (if (equal? v 0)
                  (begin
                    (subst (list '= (list ind x) 0))
                    (fact 'fun-apply-type-c sc 'omega 'RR-POS-STAR x)
                    (fact 'rr-pos-star-nonneg (list sc x))
                    (dk-ass!))
                  (let ((nx (list nf x)) (h2x (list h2 x)))
                    (in-ak! x)
                    (dk-have! (list 'IN h2x 'RR) (lambda () (subst (list '= h2x (list '* nx (list ind x)))) (dk-ass!)))
                    (fact 'fun-apply-type-c h2 'omega 'RR-POS-STAR x)
                    (fact 'rr-pos-star-nonneg h2x)
                    (rin-sc-at! c h2 x)
                    (dk-have! (list '= (list '* c (list '* nx 1)) (list '* c nx)) (lambda () (crs)))
                    (subst (list '= (list sc x) (list '* c h2x)))
                    (subst (list '= h2x (list '* nx (list ind x))))
                    (subst (list '= (list ind x) 1))
                    (subst (list '= (list '* c (list '* nx 1)) (list '* c nx)))
                    (dk-ass!))))))))
    (fact 'integral-monotone 'omega 'cA 'mu ind sc)
    (fact 'integral-indicator 'omega 'cA 'mu ak)
    (fact 'integral-homogeneous 'omega 'cA 'mu h2 c)
    (fact 'etimes-zero-right c)
    (let* ((r1 (dk-rewrite-h! (list '<= (int ind) (int sc)) (int ind) (list 'mu ak)))
           (r2 (dk-rewrite-h! r1 (int sc) (list 'etimes c (int h2))))
           (r3 (dk-rewrite-h! r2 (int h2) 0)))
      (dk-rewrite-h! r3 (list 'etimes c 0) 0))
    (rin-parts! 'IS-MEASURE '(omega cA mu))
    (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR ak)
    (fact 'rr-pos-star-nonneg (list 'mu ak))
    (rin-rps-antisym! (list 'mu ak) 0)
    (rin-conj-close! (lambda () (dk-ass!)))))

;;; rintegral-nonneg-on-sets-null (Prop. 2.24)
(sp (make-wff '(FORALL omega (FORALL cA (FORALL mu (FORALL f
  (IMPLIES (IS-MEASURE omega cA mu)
  (IMPLIES (IS-INTEGRABLE omega cA mu f)
  (IMPLIES (FORALL aa (IMPLIES (IN aa cA)
             (<= 0 (RINTEGRAL omega cA mu (VNB-LAMBDA rx_ omega (* (f rx_) ((INDICATOR omega aa) rx_)))))))
    (IS-NULL-SET omega cA mu (SEP nx_ omega (< (f nx_) 0))))))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
       (gg (list 'VNB-LAMBDA 'n_ 'NN (list 'mu (list rin-fam 'n_))))
       (perk (list 'FORALL 'kq_ (list 'IMPLIES '(IN kq_ NN)
               (list 'AND (list 'IN (rin-an 'kq_) 'cA) (list '= (list 'mu (rin-an 'kq_)) 0))))))
  (rin-parts! 'IS-MEASURE '(omega cA mu))
  (rin-integrable-setup! 'f)
  (dk-have! perk (lambda () (rin-ak-null! (dk-di-var!))))
  ;; the family n |-> A_n, its union, and the measure of the union
  (dk-have! (list 'IN rin-fam '(FUN NN cA))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((k (dk-di-var!)))
            (let ((c (dk-apply! perk k))) (dk-split-all!))
            (dk-ass!))))))
  (fact 'sigma-algebra-union-closed 'omega 'cA rin-fam)
  (fact 'measure-countably-subadditive 'omega 'cA 'mu rin-fam)
  (dk-have! (list 'IN gg '(FUN NN RR-POS-STAR))
    (lambda ()
      (dk-lam-type!
        (lambda ()
          (let ((k (dk-di-var!)))
            (fact 'fun-apply-type-c rin-fam 'NN 'cA k)
            (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR (list rin-fam k))
            (dk-ass!))))))
  (dk-have! (list 'FORALL 'ozn (list 'IMPLIES '(IN ozn NN) (list '= (list gg 'ozn) 0)))
    (lambda ()
      (let ((k (dk-di-var!)))
        (dk-apply! perk k)
        (dk-split-all!)
        (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop))))
        (if (not (sequent-node-grounded? (proof-state-focus *ps*))) (dk-ass!)))))
  (fact 'esum-nn-zero gg)
  (dk-rewrite-h! (list '<= (list 'mu rin-nla) (list 'esum gg)) (list 'esum gg) 0)
  (fact 'fun-apply-type-c 'mu 'cA 'RR-POS-STAR rin-nla)
  (fact 'rr-pos-star-nonneg (list 'mu rin-nla))
  (fact 'rr-zero-in) (fact 'rr-leq-reflexive 0) (rin-rps! 0)
  (rin-rps-antisym! (list 'mu rin-nla) 0)
  ;; { f < 0 } lies in the union
  (dk-have! (list 'SUBSET rin-negset rin-nla)
    (lambda ()
      (mac 'subset-def)
      (let* ((x (dk-di-var!)) (fx (list 'f x)) (nx (list nf x)))
        (sep-me (list 'IN x rin-negset))
        (rin-parts-at! 'f x)
        (dk-have! (list 'NOT (list '<= 0 fx))
          (lambda () (di) (rin-absurd! (list 'IN fx 'RR) (list '< fx 0) (list '<= 0 fx))))
        (let ((c (dk-cite! 'part-values-neg 'omega 'f x))) (dk-split! c))
        (dk-have! (list '< 0 nx) (lambda () (rin-ineq-goal! (rin-pt-prems 'f x))))
        (fact 'rr-pos-rr-of-lt nx)
        (fact 'rr-archimedean-multiple nx 1)
        (let* ((ex (dk-pick (lambda (f) (and (pair? f) (eq? (car f) 'forsome))) "the archimedean witness"))
               (n (dk-skolem! ex))
               (c (rin-succ-facts! n)))
          (fact 'rr-mul-closed n nx)
          (dk-have! (list 'AND (list 'IN n 'RR) (list 'IN nx 'RR)))
          (fact 'rr-mul-closed n nx)
          (rin-sc-at! c nf x)
          (dk-have! (list '= (list '* c nx) (list '+ (list '* n nx) nx)) (lambda () (crs)))
          (for-each
            (lambda (l)
              (if (not (sequent-node-grounded? l))
                  (begin
                    (dk-focus! l)
                    (if (dk-asm? (dk-goal))
                        (ass)
                        (begin
                          (let loop () (if (dk--redex? (dk-goal)) (begin (dk-lam-b!) (loop))))
                          (rin-sep-in!
                            (lambda ()
                              (if (dk-asm? (dk-goal))
                                  (ass)
                                  (begin
                                    (subst (list '= (list (rin-sn n) x) (list '* c nx)))
                                    (subst (list '= (list '* c nx) (list '+ (list '* n nx) nx)))
                                    (dk-ineq! (list 'IN (list '* n nx) 'RR) (list 'IN nx 'RR)
                                              (list '<= 1 (list '* n nx)) (list '< 0 nx)))))))))))
            (dk-opened (lambda () (bu-mi n))))))))
  (mac 'IS-NULL-SET)
  (ew rin-nla)
  (rin-conj-close! (lambda () (dk-ass!))))
(qed 'rintegral-nonneg-on-sets-null)
(topic! 'rintegral-nonneg-on-sets-null 'analysis)
;;; =====================================================================
;;; (10) the preimage form of real measurability: { x : al < f(x) } is
;;;      measurable for every real al.  For al >= 0 it is the tail of f+;
;;;      for al < 0 it is the complement of { -al <= f- }.
;;; =====================================================================

;;; real-measurable-fn-tails
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f
  (IMPLIES (IS-REAL-MEASURABLE-FN omega cA f)
    (FORALL al (IMPLIES (IN al RR) (IN (SEP x_ omega (< al (f x_))) cA)))))))))
(dk-peel!)
(let* ((pf (rin-pos 'f)) (nf (rin-neg 'f))
       (tl '(SEP x_ omega (< al (f x_))))
       (prems (lambda (x . more)
                (append (rin-pt-prems 'f x '(IN al RR) '(<= 0 al) '(< al 0) '(IN (- al) RR)
                                      (list '< 'al (list 'f x)) (list '< 'al (list pf x))
                                      (list '< (list nf x) '(- al)))
                        more))))
  (rin-parts! 'IS-REAL-MEASURABLE-FN '(omega cA f))
  (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA pf))
  (rin-parts! 'IS-MEASURABLE-FN (list 'omega 'cA nf))
  (fact 'sigma-algebra-ambient-set 'omega 'cA)
  (fact 'rr-zero-in)
  (use-em '(<= 0 al)
    (lambda ()
      (let ((tp (list 'SEP 'x_ 'omega (list '< 'al (list pf 'x_)))))
        (dk-apply! (or (dk-ctx-form (list 'FORALL 'alpha_ (list 'IMPLIES '(IN alpha_ RR)
                         (list 'IN (list 'SEP 'x_ 'omega (list '< 'alpha_ (list pf 'x_))) 'cA))))
                       (error "rin: the tails of f+ are not in context"))
                   'al)
        (rin-set-eq! tl tp
          (lambda (x)
            (sep-me (list 'IN x tl))
            (rin-sign-cases! 'f x
              (lambda (tr)
                (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x))))))))
          (lambda (x)
            (sep-me (list 'IN x tp))
            (rin-sign-cases! 'f x
              (lambda (tr)
                (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x)))))))))
        (subst (list '= tl tp))
        (dk-ass!)))
    (lambda ()
      (fact 'rr-not-le-lt 0 'al)
      (fact 'rr-neg-closed 'al)
      (fact 'measurable-fn-ge 'omega 'cA nf '(- al))
      (let* ((ge (list 'SEP 'gx_ 'omega (list '<= '(- al) (list nf 'gx_))))
             (comp (list 'COMPLEMENT-IN 'omega ge)))
        (fact 'sigma-algebra-complement-closed 'omega 'cA ge)
        (rin-set-eq! tl comp
          (lambda (x)
            (sep-me (list 'IN x tl))
            (rin-sign-cases! 'f x
              (lambda (tr)
                (mac 'complement-in-membership)
                (rin-conj-close!
                  (lambda ()
                    (if (dk-asm? (dk-goal))
                        (ass)
                        (begin
                          (di)
                          (sep-me (list 'IN x ge))
                          (apply rin-absurd! (filter dk-asm? (prems x (list '<= '(- al) (list nf x))))))))))))
          (lambda (x)
            (mac-h 'complement-in-membership (list 'IN x comp))
            (dk-split-all!)
            (rin-parts-at! 'f x)
            (use-em (list '<= '(- al) (list nf x))
              (lambda ()
                (dk-have! (list 'IN x ge) (lambda () (rin-sep-in! (lambda () (dk-ass!)))))
                (rin-keep-prop! (list 'IN x ge) (list 'NOT (list 'IN x ge))))
              (lambda ()
                (fact 'rr-not-le-lt '(- al) (list nf x))
                (rin-sign-cases! 'f x
                  (lambda (tr)
                    (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x)))))))))))
        (subst (list '= tl comp))
        (dk-ass!)))))
(qed 'real-measurable-fn-tails)
(topic! 'real-measurable-fn-tails 'analysis)
;;; the converse: a real function whose tails { al < f } are all measurable is
;;; real measurable.  f+ has the tails of f above 0; for f- the lower tail
;;; { f < -al } is the complement of { -al <= f } = { 1 <= (f + al + 1)+ },
;;; a closed tail of the positive part of a shifted function (measurable-fn-ge).

(define rin-tails '(FORALL al (IMPLIES (IN al RR) (IN (SEP x_ omega (< al (f x_))) cA))))

;;; pos-part-measurable-of-tails
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f
  (IMPLIES (IS-SIGMA-ALGEBRA omega cA)
  (IMPLIES (IN f (FUN omega RR))
  (IMPLIES (FORALL al (IMPLIES (IN al RR) (IN (SEP x_ omega (< al (f x_))) cA)))
    (IS-MEASURABLE-FN omega cA (POS-PART omega f))))))))))
(dk-peel!)
(let ((pf (rin-pos 'f)))
  (fact 'pos-part-fun 'omega 'f)
  (fact 'sigma-algebra-ambient-set 'omega 'cA)
  (dk-have! (list 'FORALL 'al_ (list 'IMPLIES '(IN al_ RR) (list 'IMPLIES '(<= 0 al_)
              (list 'IN (list 'SEP 'x_ 'omega (list '< 'al_ (list pf 'x_))) 'cA))))
    (lambda ()
      (dk-peel!)
      (let* ((tp (cadr (dk-goal))) (al (cadr (cadddr tp)))
             (tl (list 'SEP 'x_ 'omega (list '< al '(f x_))))
             (prems (lambda (x) (rin-pt-prems 'f x (list 'IN al 'RR) (list '<= 0 al)
                                  (list '< al (list 'f x)) (list '< al (list pf x))))))
        (dk-apply! rin-tails al)
        (rin-set-eq! tp tl
          (lambda (x)
            (sep-me (list 'IN x tp))
            (rin-sign-cases! 'f x
              (lambda (tr) (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x))))))))
          (lambda (x)
            (sep-me (list 'IN x tl))
            (rin-sign-cases! 'f x
              (lambda (tr) (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x)))))))))
        (subst (list '= tp tl))
        (dk-ass!))))
  (fact 'measurable-fn-of-nonneg-tails 'omega 'cA pf)
  (dk-ass!))
(qed 'pos-part-measurable-of-tails)
(topic! 'pos-part-measurable-of-tails 'analysis)

;;; real-measurable-of-tails
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f
  (IMPLIES (IS-SIGMA-ALGEBRA omega cA)
  (IMPLIES (IN f (FUN omega RR))
  (IMPLIES (FORALL al (IMPLIES (IN al RR) (IN (SEP x_ omega (< al (f x_))) cA)))
    (IS-REAL-MEASURABLE-FN omega cA f)))))))))
(dk-peel!)
(let ((pf (rin-pos 'f)) (nf (rin-neg 'f)))
  (fact 'pos-part-measurable-of-tails 'omega 'cA 'f)
  (fact 'neg-part-fun 'omega 'f)
  (fact 'sigma-algebra-ambient-set 'omega 'cA)
  (fact 'fun-domain-in-set 'omega 'RR 'f)
  (fact 'rr-zero-in)
  (fact 'rr-one-in)
  (dk-have! (list 'FORALL 'al_ (list 'IMPLIES '(IN al_ RR) (list 'IMPLIES '(<= 0 al_)
              (list 'IN (list 'SEP 'x_ 'omega (list '< 'al_ (list nf 'x_))) 'cA))))
    (lambda ()
      (dk-peel!)
      (let* ((tn (cadr (dk-goal))) (al (cadr (cadddr tn)))
             (c (list '- (list '- al) 1))
             (s (list 'VNB-LAMBDA 'sx_ 'omega (list '- '(f sx_) c)))
             (ps (rin-pos s))
             (gs (list 'SEP 'gx_ 'omega (list '<= 1 (list ps 'gx_))))
             (comp (list 'COMPLEMENT-IN 'omega gs))
             (s-at! (lambda (x)          ; f at x, s at x and their parts, s x = f x - c
                      (rin-parts-at! 'f x)
                      (rin-parts-at! s x)
                      (fact 'rr-sub-in-rr (list 'f x) c)
                      (rin-lam-at! s x (list '- (list 'f x) c))))
             (prems (lambda (x . more)
                      (append (rin-pt-prems 'f x) (rin-pt-prems s x)
                              (list (list 'IN al 'RR) (list '<= 0 al) (list 'IN c 'RR)
                                    (list '= c (list '- (list '- al) 1))
                                    (list '= (list s x) (list '- (list 'f x) c))
                                    (list '< al (list nf x)) (list '<= 1 (list ps x)) (list '< (list ps x) 1))
                              more))))
        (fact 'rr-neg-closed al)
        (fact 'rr-sub-in-rr (list '- al) 1)
        (dk-have! (list '= c (list '- (list '- al) 1)) (lambda () (rfl)))
        (dk-have! (list 'IN s '(FUN omega RR))
          (lambda ()
            (dk-lam-type!
              (lambda ()
                (let ((x (dk-di-var!)))
                  (fact 'fun-apply-type-c 'f 'omega 'RR x)
                  (fact 'rr-sub-in-rr (list 'f x) c)
                  (ass))))))
        ;; the tails of s are tails of f
        (dk-have! (list 'FORALL 'al (list 'IMPLIES '(IN al RR) (list 'IN (list 'SEP 'x_ 'omega (list '< 'al (list s 'x_))) 'cA)))
          (lambda ()
            (dk-peel!)
            (let* ((ts (cadr (dk-goal))) (bt (cadr (cadddr ts)))
                   (bc (list '+ bt c))
                   (tf (list 'SEP 'x_ 'omega (list '< bc '(f x_)))))
              (dk-have! (list 'AND (list 'IN bt 'RR) (list 'IN c 'RR)))
              (fact 'rr-add-closed bt c)
              (dk-apply! rin-tails bc)
              (rin-set-eq! ts tf
                (lambda (x)
                  (sep-me (list 'IN x ts))
                  (s-at! x)
                  (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass)
                                              (rin-ineq-goal! (prems x (list 'IN bt 'RR) (list '< bt (list s x))))))))
                (lambda (x)
                  (sep-me (list 'IN x tf))
                  (s-at! x)
                  (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass)
                                              (rin-ineq-goal! (prems x (list 'IN bt 'RR) (list 'IN bc 'RR)
                                                                     (list '< bc (list 'f x)))))))))
              (subst (list '= ts tf))
              (dk-ass!))))
        (fact 'pos-part-measurable-of-tails 'omega 'cA s)
        (fact 'measurable-fn-ge 'omega 'cA ps 1)
        (fact 'sigma-algebra-complement-closed 'omega 'cA gs)
        (rin-set-eq! tn comp
          (lambda (x)
            (sep-me (list 'IN x tn))
            (s-at! x)
            (mac 'complement-in-membership)
            (rin-conj-close!
              (lambda ()
                (if (dk-asm? (dk-goal))
                    (ass)
                    (begin
                      (di)
                      (sep-me (list 'IN x gs))
                      (rin-sign-cases! 'f x
                        (lambda (tr1)
                          (rin-sign-cases! s x
                            (lambda (tr2)
                              (apply rin-absurd! (filter dk-asm? (prems x))))))))))))
          (lambda (x)
            (mac-h 'complement-in-membership (list 'IN x comp))
            (dk-split-all!)
            (s-at! x)
            (use-em (list '<= 1 (list ps x))
              (lambda ()
                (dk-have! (list 'IN x gs) (lambda () (rin-sep-in! (lambda () (dk-ass!)))))
                (rin-keep-prop! (list 'IN x gs) (list 'NOT (list 'IN x gs))))
              (lambda ()
                (fact 'rr-not-le-lt 1 (list ps x))
                (rin-sign-cases! 'f x
                  (lambda (tr1)
                    (rin-sign-cases! s x
                      (lambda (tr2)
                        (rin-sep-in! (lambda () (if (dk-asm? (dk-goal)) (ass) (rin-ineq-goal! (prems x)))))))))))))
        (subst (list '= tn comp))
        (dk-ass!))))
  (fact 'measurable-fn-of-nonneg-tails 'omega 'cA nf)
  (mac 'IS-REAL-MEASURABLE-FN)
  (rin-conj-close! (lambda () (dk-ass!))))
(qed 'real-measurable-of-tails)
(topic! 'real-measurable-of-tails 'analysis)

;;; real-measurable-fn-iff-tails
(sp (make-wff '(FORALL omega (FORALL cA (FORALL f
  (IMPLIES (IS-SIGMA-ALGEBRA omega cA)
  (IMPLIES (IN f (FUN omega RR))
    (IFF (IS-REAL-MEASURABLE-FN omega cA f)
         (FORALL al (IMPLIES (IN al RR) (IN (SEP x_ omega (< al (f x_))) cA)))))))))))
(dk-peel!)
(dk-iff! (lambda (g) (dk-head-is? g 'FORALL))
  (lambda () (fact 'real-measurable-fn-tails 'omega 'cA 'f) (dk-ass!))
  (lambda () (fact 'real-measurable-of-tails 'omega 'cA 'f) (dk-ass!)))
(qed 'real-measurable-fn-iff-tails)
(topic! 'real-measurable-fn-iff-tails 'analysis)
