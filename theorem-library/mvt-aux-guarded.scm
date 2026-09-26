;;; theorem-library/mvt-aux-guarded.scm -- the four MVT auxiliary-function
;;; supports, GUARDED and PROVEN.
;;;
;;;   mvt-aux-cont   f continuous at x  =>  z |-> f(z)(b-a) - z(f(b)-f(a))  continuous at x
;;;   mvt-aux-diff   f'(x) = L          =>  that map has derivative L(b-a) - (f(b)-f(a)) at x
;;;   gmvt-aux-cont  f, g continuous at x  =>  z |-> f(z)(g(b)-g(a)) - g(z)(f(b)-f(a))  continuous at x
;;;   gmvt-aux-diff  f'(x) = L, g'(x) = M  =>  that map has derivative L(g(b)-g(a)) - M(f(b)-f(a)) at x
;;;
;;; STATEMENT CHANGE (the user's decision, 2026-09-14).  The four supports as they
;;; stood (mvt-proof.scm:51-65, generalized-mvt-proof.scm:16-35) quantified the
;;; endpoints a, b with NO guard, and are FALSE as written: for b not in RR the
;;; body f(z)(b-a) - ... is undefined at every z, the lambda is the empty function,
;;; and neither IN AUX (FUN RR RR) nor the continuity/derivative claim holds.
;;; Each statement below is the original with `(IN a RR)' and `(IN b RR)' added as
;;; the two leading antecedents, immediately after the binders; everything else is
;;; byte-identical.  The band's install-theorem! therefore prints "DIFFERENT
;;; statement" at each qed -- expected.  No `(IN f (FUN RR RR))' guard is needed:
;;; both IS-DIFF-AT and IS-CONTINUOUS-AT carry f's typing as a conjunct.
;;;
;;; PLAN, one driver for all four.  Each auxiliary is a linear combination
;;;     c1 * f1(z) + c2 * f2(z)
;;; with c1, c2 real constants (built from a, b, f(a), f(b), g(a), g(b)) and f1, f2
;;; the given maps -- for the MVT pair, f2 is the identity lambda.  Continuity:
;;; `const-continuous-at' x2, `product-continuous-at' x2, `sum-continuous-at',
;;; then `cont-transfer-ptwise-eq' to the literal auxiliary (pointwise agreement
;;; is beta + `crs').  Derivative: `deriv-scalar-mult' x2, `deriv-sum', then
;;; `diff-transfer-ptwise-eq' the same way, and the value identity is one `crs'.
;;; Writing the second term as (-(f(b)-f(a))) * z rather than -(... * z) avoids
;;; `deriv-neg' and `sub-continuous-at' altogether.
;;;
;;; LOAD WINDOW: after theorem-library/deriv-polynomial (deriv-scalar-mult, the
;;; latest citation) and before theorem-library/mvt-proof (the earliest citer).
;;; Everything else cited is earlier still: continuity-basics, continuity-sum,
;;; continuity-product, continuity-transfer, differentiation, diff-transfer,
;;; deriv-sum-product, binary-minus-laws (rr-sub-in-rr), fun-apply-type-proof.
;;; Helper prefix: mag-.
;;; ====================================================================

;;; --- the two auxiliaries, VERBATIM from the citing files ---
(define mag-aux  '(VNB-LAMBDA z RR (- (* (f z) (- b a)) (* z (- (f b) (f a))))))
(define mag-gaux '(VNB-LAMBDA z RR (- (* (f z) (- (g b) (g a))) (* (g z) (- (f b) (f a))))))
(define mag-ident '(VNB-LAMBDA x RR x))

;;; --- the four GUARDED statements ---
(define mag-mvt-aux-diff-stmt
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x (list 'FORALL 'L
    (list 'IMPLIES '(IN a RR)
    (list 'IMPLIES '(IN b RR)
    (list 'IMPLIES '(IS-DIFF-AT f x L)
      (list 'IS-DIFF-AT mag-aux 'x '(- (* L (- b a)) (- (f b) (f a)))))))))))))

(define mag-mvt-aux-cont-stmt
  (list 'FORALL 'f (list 'FORALL 'a (list 'FORALL 'b (list 'FORALL 'x
    (list 'IMPLIES '(IN a RR)
    (list 'IMPLIES '(IN b RR)
    (list 'IMPLIES '(IS-CONTINUOUS-AT RR-MS RR-MS f x)
      (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS mag-aux 'x)))))))))

(define mag-gmvt-aux-cont-stmt
  `(FORALL f (FORALL g (FORALL a (FORALL b (FORALL x
     (IMPLIES (IN a RR)
     (IMPLIES (IN b RR)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS f x)
     (IMPLIES (IS-CONTINUOUS-AT RR-MS RR-MS g x)
       (IS-CONTINUOUS-AT RR-MS RR-MS ,mag-gaux x)))))))))))

(define mag-gmvt-aux-diff-stmt
  `(FORALL f (FORALL g (FORALL a (FORALL b (FORALL x (FORALL L (FORALL M
     (IMPLIES (IN a RR)
     (IMPLIES (IN b RR)
     (IMPLIES (IS-DIFF-AT f x L)
     (IMPLIES (IS-DIFF-AT g x M)
       (IS-DIFF-AT ,mag-gaux x (- (* L (- (g b) (g a))) (* M (- (f b) (f a)))))))))))))))))

;;; --- helpers ---

;; read a conjunct of an IS-DIFF-AT hypothesis on a have! lane: `mac-h' REPLACES
;; the assumption it unfolds, and the main branch needs the folded form for the
;; rule citations below.
(define (mag-diff-proj! hyp claim)
  (have! claim (lambda () (mac-h 'IS-DIFF-AT hyp) (dk-split-all!) (ass))))

;; the same off an IS-CONTINUOUS-AT hypothesis; the unfold speaks of PTS(RR-MS),
;; so the conjunct is slotted down to RR before `ass'.
(define (mag-cont-proj! fn pt claim pts-form)
  (have! claim
    (lambda ()
      (mac-h 'is-continuous-at (list 'IS-CONTINUOUS-AT 'RR-MS 'RR-MS fn pt))
      (dk-split-all!)
      (slot-h 'PTS pts-form)
      (ass))))

;; (IN lam (FUN RR RR)) for a lambda over RR whose body `in-rr' can type from the
;; context (f in FUN(RR,RR), a, b in RR).  dk-lam-t! closes the sethood leaf and
;; focuses the pointwise one; peel the binder, then in-rr.
(define (mag-lam-typing! lam)
  (have! (list 'IN lam '(FUN RR RR))
    (lambda () (dk-lam-t!) (dk-peel!) (in-rr))))

;; the pointwise agreement  lam(w) REL s(w)  for every real w, REL being `=' (the
;; continuity transfer) or `==' (the derivative transfer).  Both sides are beta
;; redexes licensed by the landed (IN w RR); after the reduction the equation is a
;; commutative-ring identity in f1(w), f2(w), w and the constants.
(define (mag-agree! rel lam s fns)
  (have! (list 'FORALL 'w_ (list 'IMPLIES '(IN w_ RR) (list rel (list lam 'w_) (list s 'w_))))
    (lambda ()
      (let ((w (dk-di-var!)))
        (for-each (lambda (fn) (if (symbol? fn) (fact 'fun-apply-type-c fn 'RR 'RR w))) fns)
        (lam-b)
        (if (eq? rel '=)
            (crs)
            (let ((lhs (cadr (dk-goal))) (rhs (caddr (dk-goal))))
              (have! (list '= lhs rhs) (lambda () (crs)))
              (subst (list '= lhs rhs))
              (qrfl)))))))

;; CONTINUITY of lam = z |-> c1*f1(z) + c2*f2(z) at pt.  Context: f1, f2
;; continuous at pt (f2 may be the identity lambda, whose continuity is cited
;; beforehand), c1, c2, pt in RR, lam in FUN(RR,RR), and the typings crs wants.
(define (mag-cont-combo! lam pt c1 f1 c2 f2)
  (let* ((k1 (list 'VNB-LAMBDA 'x 'RR c1))
         (k2 (list 'VNB-LAMBDA 'x 'RR c2))
         (p1 (list 'VNB-LAMBDA 'x 'RR (list '* (list k1 'x) (list f1 'x))))
         (p2 (list 'VNB-LAMBDA 'x 'RR (list '* (list k2 'x) (list f2 'x))))
         (s  (list 'VNB-LAMBDA 'x 'RR (list '+ (list p1 'x) (list p2 'x)))))
    (fact 'const-continuous-at c1 pt)
    (fact 'const-continuous-at c2 pt)
    (fact 'product-continuous-at k1 f1 pt)
    (fact 'product-continuous-at k2 f2 pt)
    (fact 'sum-continuous-at p1 p2 pt)
    (mag-agree! '= lam s (list f1 f2))
    (fact 'cont-transfer-ptwise-eq lam s pt)
    (ass)))

;; DERIVATIVE of lam = z |-> c1*f1(z) + c2*f2(z) at pt, goal value goal-val.
;; Context: IS-DIFF-AT f1 pt v1, IS-DIFF-AT f2 pt v2, c1, c2, pt, v1, v2 in RR,
;; lam in FUN(RR,RR), and the typings crs wants.
(define (mag-diff-combo! lam pt c1 f1 v1 c2 f2 v2 goal-val)
  (let* ((pa (list 'VNB-LAMBDA 'x 'RR (list '* c1 (list f1 'x))))
         (pb (list 'VNB-LAMBDA 'x 'RR (list '* c2 (list f2 'x))))
         (s  (list 'VNB-LAMBDA 'x 'RR (list '+ (list pa 'x) (list pb 'x))))
         (va (list '* c1 v1))
         (vb (list '* c2 v2))
         (vs (list '+ va vb)))
    (fact 'deriv-scalar-mult c1 f1 pt v1)
    (fact 'deriv-scalar-mult c2 f2 pt v2)
    (have! (list 'AND (list 'IS-DIFF-AT pa pt va) (list 'IS-DIFF-AT pb pt vb)))
    (fact 'deriv-sum pa pb pt va vb)
    (mag-agree! '== lam s (list f1 f2))
    (fact 'diff-transfer-ptwise-eq lam s pt vs)
    (have! (list '= goal-val vs) (lambda () (crs)))
    (subst (list '= goal-val vs))
    (ass)))

;; the real constants every proof below needs: f(a), f(b), the two differences
;; and the negated one.  fn is a map already typed in FUN(RR,RR).
(define (mag-type-consts! fn a b)
  (fact 'fun-apply-type-c fn 'RR 'RR a)
  (fact 'fun-apply-type-c fn 'RR 'RR b)
  (fact 'rr-sub-in-rr (list fn b) (list fn a))
  (fact 'rr-neg-closed (list '- (list fn b) (list fn a))))

;;; ====================================================================
;;; (1) mvt-aux-diff
;;; ====================================================================
(sp (make-wff mag-mvt-aux-diff-stmt))
(dk-peel!)
;; everything off the GOAL  (IS-DIFF-AT lam pt val)
(let* ((g0  (dk-goal))
       (lam (cadr g0))
       (pt  (caddr g0))
       (val (cadddr g0))
       (bod (cadddr lam))                    ; (- (* (f z) (- b a)) (* z (- (f b) (f a))))
       (f   (car (cadr (cadr bod))))
       (b   (cadr (caddr (cadr bod))))
       (a   (caddr (caddr (cadr bod))))
       (L   (cadr (cadr val)))
       (hyp (list 'IS-DIFF-AT f pt L)))
  (mag-diff-proj! hyp (list 'IN f '(FUN RR RR)))
  (mag-diff-proj! hyp (list 'IN pt 'RR))
  (mag-diff-proj! hyp (list 'IN L 'RR))
  (fact 'rr-sub-in-rr b a)                            ; (IN (- b a) RR)
  (mag-type-consts! f a b)
  (fact 'deriv-identity pt)                           ; IS-DIFF-AT (x |-> x) pt 1
  (fact 'rr-one-in)
  (mag-lam-typing! lam)
  (mag-diff-combo! lam pt
                   (list '- b a) f L
                   (list '- (list '- (list f b) (list f a))) mag-ident 1
                   val))
(qed 'mvt-aux-diff)

;;; ====================================================================
;;; (2) mvt-aux-cont
;;; ====================================================================
(sp (make-wff mag-mvt-aux-cont-stmt))
(dk-peel!)
;; off the GOAL  (IS-CONTINUOUS-AT RR-MS RR-MS lam pt)
(let* ((g0  (dk-goal))
       (lam (list-ref g0 3))
       (pt  (list-ref g0 4))
       (bod (cadddr lam))
       (f   (car (cadr (cadr bod))))
       (b   (cadr (caddr (cadr bod))))
       (a   (caddr (caddr (cadr bod)))))
  (mag-cont-proj! f pt (list 'IN f '(FUN RR RR)) (list 'IN f '(FUN (PTS RR-MS) (PTS RR-MS))))
  (mag-cont-proj! f pt (list 'IN pt 'RR) (list 'IN pt '(PTS RR-MS)))
  (fact 'rr-sub-in-rr b a)
  (mag-type-consts! f a b)
  (fact 'identity-continuous-at pt)
  (mag-lam-typing! lam)
  (mag-cont-combo! lam pt
                   (list '- b a) f
                   (list '- (list '- (list f b) (list f a))) mag-ident))
(qed 'mvt-aux-cont)

;;; ====================================================================
;;; (3) gmvt-aux-diff
;;; ====================================================================
(sp (make-wff mag-gmvt-aux-diff-stmt))
(dk-peel!)
;; off the GOAL  (IS-DIFF-AT lam pt val), lam's body
;;   (- (* (f z) (- (g b) (g a))) (* (g z) (- (f b) (f a))))
(let* ((g0  (dk-goal))
       (lam (cadr g0))
       (pt  (caddr g0))
       (val (cadddr g0))
       (bod (cadddr lam))
       (f   (car (cadr (cadr bod))))
       (g   (car (cadr (caddr bod))))
       (b   (cadr (cadr (caddr (cadr bod)))))     ; out of (- (g b) (g a))
       (a   (cadr (caddr (caddr (cadr bod)))))
       (L   (cadr (cadr val)))
       (M   (cadr (caddr val)))
       (hf  (list 'IS-DIFF-AT f pt L))
       (hg  (list 'IS-DIFF-AT g pt M)))
  (mag-diff-proj! hf (list 'IN f '(FUN RR RR)))
  (mag-diff-proj! hg (list 'IN g '(FUN RR RR)))
  (mag-diff-proj! hf (list 'IN pt 'RR))
  (mag-diff-proj! hf (list 'IN L 'RR))
  (mag-diff-proj! hg (list 'IN M 'RR))
  (mag-type-consts! f a b)
  (mag-type-consts! g a b)
  (mag-lam-typing! lam)
  (mag-diff-combo! lam pt
                   (list '- (list g b) (list g a)) f L
                   (list '- (list '- (list f b) (list f a))) g M
                   val))
(qed 'gmvt-aux-diff)

;;; ====================================================================
;;; (4) gmvt-aux-cont
;;; ====================================================================
(sp (make-wff mag-gmvt-aux-cont-stmt))
(dk-peel!)
(let* ((g0  (dk-goal))
       (lam (list-ref g0 3))
       (pt  (list-ref g0 4))
       (bod (cadddr lam))
       (f   (car (cadr (cadr bod))))
       (g   (car (cadr (caddr bod))))
       (b   (cadr (cadr (caddr (cadr bod)))))     ; out of (- (g b) (g a))
       (a   (cadr (caddr (caddr (cadr bod))))))
  (mag-cont-proj! f pt (list 'IN f '(FUN RR RR)) (list 'IN f '(FUN (PTS RR-MS) (PTS RR-MS))))
  (mag-cont-proj! g pt (list 'IN g '(FUN RR RR)) (list 'IN g '(FUN (PTS RR-MS) (PTS RR-MS))))
  (mag-cont-proj! f pt (list 'IN pt 'RR) (list 'IN pt '(PTS RR-MS)))
  (mag-type-consts! f a b)
  (mag-type-consts! g a b)
  (mag-lam-typing! lam)
  (mag-cont-combo! lam pt
                   (list '- (list g b) (list g a)) f
                   (list '- (list '- (list f b) (list f a))) g))
(qed 'gmvt-aux-cont)
