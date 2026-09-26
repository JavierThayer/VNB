;;; cc-int-estimate.scm -- THE NOTES' ESTIMATE (45).
;;;
;;;   complex-analysis.pdf 3.1, equation (45):
;;;
;;;       | integral_a^b f(t) dt |  <=  integral_a^b |f(t)| dt
;;;
;;; THE NOTES' ARGUMENT, AND WHERE IT IS CARRIED OUT HERE.  The notes multiply
;;; the integral by eta = conjugate( integral f ) and use that (44) is complex
;;; linear in f:
;;;
;;;       Re( {integral f} eta ) = integral Re{f eta} <= integral |f| |eta|
;;;                              = |eta| integral |f|.
;;;
;;; Every step of that computation is kept, but the multiplication by eta is
;;; done POINTWISE, under the integral sign, where it is a fact about two
;;; complex NUMBERS (`cc-re-inner-bound' below) instead of a fact about the
;;; integral.  The reason is not taste: Re( CC-INT(eta phi) ) is only equal to
;;; PW-INT( Re(eta phi) ) once a PW-antiderivative of Re(eta phi) is EXHIBITED,
;;; and exhibiting it is exactly the real linear combination
;;; `pw-antiderivative-linear' (batch 18-A) integrates below.  So the
;;; complex-scalar law `cc-int-complex-mul' would be used only to re-derive, in
;;; the complex idiom, the identity this file gets from the real one; the
;;; estimate needs no complex linearity of the integral itself.  With
;;; X = PW-INT(Re f) and Y = PW-INT(Im f), eta is X - Y i and the chain is
;;;
;;;    X^2 + Y^2 = PW-INT( X Re(f) + Y Im(f) )        [pw-antiderivative-linear]
;;;             <= PW-INT( |J| |f| )                  [pw-int-monotone, pointwise
;;;                                                    by cc-re-inner-bound]
;;;              = |J| PW-INT(|f|)                    [pw-antiderivative-real-mul]
;;; and |J|^2 = X^2 + Y^2 (`cc-magnitude-sq'), so |J| <= PW-INT(|f|) after the
;;; cancellation, which is split on |J| = 0 because the library has no
;;; cancellation law for a nonstrict product inequality.
;;;
;;; THE STATEMENT CHECKS.  PW-INT and CC-INT are IOTA terms: they are DEFINED
;;; only where a PW-antiderivative exists, so a strict `=' or `<=' on them is
;;; underdetermined unless existence is assumed.  The statement therefore
;;; carries THREE PW-antiderivative hypotheses -- one for each coordinate of f
;;; (which is what makes CC-INT(f, a, b) defined, and is exactly what
;;; `cc-int-value' and `cc-int-in-cc' require) and one for the given |f|.  The
;;; notes get all three from "f piecewise continuous"; the library has no
;;; theorem yet that a piecewise-continuous function has a PW-antiderivative, so
;;; they are hypotheses.  |f| is a FUNCTION `pabs_' on [a,b] with the pointwise
;;; equation pabs_(t) == magnitude(f(t)), not a term built by a lambda, so that
;;; the user may supply whichever function object is at hand; `==' (not `=')
;;; because the equation is only claimed on [a,b].
;;;
;;; WINDOW.  Citations: theorem-library/pw-int-order.scm (`pw-int-monotone',
;;; `pw-int-nonneg', this batch), theorem-library/pw-int-laws-3.scm
;;; (`pw-antiderivative-linear', batch 18-A), pw-int-laws-2.scm (`cc-int-value',
;;; `cc-int-in-cc', `pw-antiderivative-real-mul'), plus the old CC and RR
;;; toolkits.  The slot is after ALL of those, i.e. after pw-int-order.
;;;
;;; Helper prefix: cie-.

;;; ---- file-local driver helpers --------------------------------------

(define (cie-head g) (and (pair? g) (car g)))

;;; A goal that mentions (ABS x) at the top, closed by splitting the sign of x
;;; and rewriting `abs' away in each case: `ineq' does not know `abs' well
;;; enough even for `x <= abs(x)'.  PREMS are the other premises, named by
;;; FORMULA; the case atom is added to them.
(define (cie-abs-split! x prems)
  (dk-real! 0)
  (dk-have! (list 'AND (list 'IN 0 'RR) (list 'IN x 'RR)))
  (let ((tot (dk-fact! 'rr-leq-total 0 x)))
    (dk-each-leaf! (lambda () (ai tot))
      (lambda ()
        (if (dk-ctx-form (list '<= 0 x))
            (begin (dk-read-off! 'rr-abs-of-nonneg x)
                   (apply dk-ineq! (cons (list '<= 0 x) prems)))
            (begin (dk-read-off! 'rr-abs-of-nonpos x)
                   (apply dk-ineq! (cons (list '<= x 0) prems))))))))

(define (cie-abs-ge! x) (cie-abs-split! x (list (list 'IN x 'RR))))

;;; =====================================================================
;;; (1) THE SQUARE OF THE MODULUS.
;;;     magnitude(z)^2 = re(z)^2 + im(z)^2 -- `magnitude-def' with the root
;;;     removed by `sqrt-sq', whose nonnegativity side condition is two
;;;     `rr-sq-nonneg'.
;;; =====================================================================
(sp (make-wff '(FORALL cqz_ (IMPLIES (IN cqz_ CC)
     (= (* (magnitude cqz_) (magnitude cqz_))
        (+ (* (real-part cqz_) (real-part cqz_))
           (* (imag-part cqz_) (imag-part cqz_))))))))
(dk-peel!)
(fact 'real-part-in-rr 'cqz_)
(fact 'imag-part-in-rr 'cqz_)
(fact 'rr-sq-nonneg '(real-part cqz_))
(fact 'rr-sq-nonneg '(imag-part cqz_))
(have! (list 'AND '(IN (real-part cqz_) RR) '(IN (real-part cqz_) RR)))
(fact 'rr-mul-closed '(real-part cqz_) '(real-part cqz_))
(have! (list 'AND '(IN (imag-part cqz_) RR) '(IN (imag-part cqz_) RR)))
(fact 'rr-mul-closed '(imag-part cqz_) '(imag-part cqz_))
(define cie-sq '(+ (* (real-part cqz_) (real-part cqz_))
                   (* (imag-part cqz_) (imag-part cqz_))))
(dk-have! (list '<= 0 cie-sq)
  (lambda ()
    (dk-ineq! '(<= 0 (* (real-part cqz_) (real-part cqz_)))
              '(<= 0 (* (imag-part cqz_) (imag-part cqz_)))
              '(IN (* (real-part cqz_) (real-part cqz_)) RR)
              '(IN (* (imag-part cqz_) (imag-part cqz_)) RR))))
(have! (list 'AND '(IN (* (real-part cqz_) (real-part cqz_)) RR)
                  '(IN (* (imag-part cqz_) (imag-part cqz_)) RR)))
(fact 'rr-add-closed '(* (real-part cqz_) (real-part cqz_))
                     '(* (imag-part cqz_) (imag-part cqz_)))
(mac 'magnitude-def)
;; `sqrt-sq' has a CONJUNCTIVE antecedent (a in rr and 0 <= a), which `fact'
;; will not split.
(have! (list 'AND (list 'IN cie-sq 'RR) (list '<= 0 cie-sq)))
(fact 'sqrt-sq cie-sq)
(ass)
(qed 'cc-magnitude-sq)
(topic! 'cc-magnitude-sq 'analysis)
(alias! 'cc-magnitude-sq "the square of the modulus is the sum of the squares of the coordinates")

;;; =====================================================================
;;; (2) THE REAL INNER PRODUCT OF TWO COMPLEX NUMBERS IS AT MOST THE
;;;     PRODUCT OF THEIR MODULI -- Cauchy-Schwarz in the plane, got from
;;;     Re(w' z) <= |w' z| for w' the conjugate of w.
;;; =====================================================================
(sp (make-wff '(FORALL cqw_ (IMPLIES (IN cqw_ CC)
     (FORALL cqz_ (IMPLIES (IN cqz_ CC)
       (<= (+ (* (real-part cqw_) (real-part cqz_))
              (* (imag-part cqw_) (imag-part cqz_)))
           (* (magnitude cqw_) (magnitude cqz_)))))))))
(dk-peel!)
(define cie-rw '(real-part cqw_))
(define cie-iw '(imag-part cqw_))
(define cie-eta (list '+ cie-rw (list '* (list '- cie-iw) '+i)))
(fact 'real-part-in-rr 'cqw_)
(fact 'imag-part-in-rr 'cqw_)
(fact 'real-part-in-rr 'cqz_)
(fact 'imag-part-in-rr 'cqz_)
(fact 'rr-neg-closed cie-iw)
(fact 'rr-subset-cc cie-rw)
(fact 'rr-subset-cc (list '- cie-iw))
(have! (list 'AND (list 'IN (list '- cie-iw) 'CC) '(IN +i CC)))
(fact 'cc-mul-closed (list '- cie-iw) '+i)
(have! (list 'AND (list 'IN cie-rw 'CC)
             (list 'IN (list '* (list '- cie-iw) '+i) 'CC)))
(fact 'cc-add-closed cie-rw (list '* (list '- cie-iw) '+i))
;; the coordinates of eta
(dk-have! (list '= cie-eta cie-eta) (lambda () (rfl)))
(dk-split-all!
 (list (dk-fact! 'cc-re-im-of cie-eta cie-rw (list '- cie-iw))))
;; |eta| = |w|, by sqrt-unique on the squares
(fact 'cc-magnitude-closed cie-eta)
(fact 'cc-magnitude-closed 'cqw_)
(fact 'cc-magnitude-nonneg cie-eta)
(fact 'cc-magnitude-nonneg 'cqw_)
(fact 'cc-magnitude-sq cie-eta)
(fact 'cc-magnitude-sq 'cqw_)
(dk-have! (list '= (list '* (list 'magnitude cie-eta) (list 'magnitude cie-eta))
                   (list '* '(magnitude cqw_) '(magnitude cqw_)))
  (lambda ()
    (subst (list '= (list '* (list 'magnitude cie-eta) (list 'magnitude cie-eta))
                 (list '+ (list '* (list 'real-part cie-eta) (list 'real-part cie-eta))
                          (list '* (list 'imag-part cie-eta) (list 'imag-part cie-eta)))))
    (subst (list '= (list '* '(magnitude cqw_) '(magnitude cqw_))
                 (list '+ (list '* cie-rw cie-rw) (list '* cie-iw cie-iw))))
    (subst (list '= (list 'real-part cie-eta) cie-rw))
    (subst (list '= (list 'imag-part cie-eta) (list '- cie-iw)))
    (crs)))
;; `sqrt-unique' has two CONJUNCTIVE antecedents; `fact' will not split them.
(have! (list 'AND (list 'IN (list 'magnitude cie-eta) 'RR)
                  '(IN (magnitude cqw_) RR)))
(have! (list 'AND (list '<= 0 (list 'magnitude cie-eta))
                  '(<= 0 (magnitude cqw_))))
(fact 'sqrt-unique (list 'magnitude cie-eta) '(magnitude cqw_))
;; Re(eta z) is the inner product
(have! (list 'AND (list 'IN cie-eta 'CC) '(IN cqz_ CC)))
(fact 'cc-mul-closed cie-eta 'cqz_)
(define cie-p (list 'real-part (list '* cie-eta 'cqz_)))
(fact 'cc-re-mul cie-eta 'cqz_)
(dk-have! (list '= cie-p (list '+ (list '* cie-rw '(real-part cqz_))
                                  (list '* cie-iw '(imag-part cqz_))))
  (lambda ()
    (subst (list '= cie-p
                 (list '- (list '* (list 'real-part cie-eta) '(real-part cqz_))
                          (list '* (list 'imag-part cie-eta) '(imag-part cqz_)))))
    (subst (list '= (list 'real-part cie-eta) cie-rw))
    (subst (list '= (list 'imag-part cie-eta) (list '- cie-iw)))
    (crs)))
;; and it is bounded by the product of the moduli
(fact 'cc-magnitude-mul cie-eta 'cqz_)
(fact 'cc-abs-re-le-magnitude (list '* cie-eta 'cqz_))
(fact 'real-part-in-rr (list '* cie-eta 'cqz_))
(dk-have! (list '<= cie-p (list 'abs cie-p)) (lambda () (cie-abs-ge! cie-p)))
(fact 'cc-magnitude-closed (list '* cie-eta 'cqz_))
(fact 'cc-magnitude-closed 'cqz_)
(fact 'rr-abs-closed cie-p)
(dk-le-trans! cie-p (list 'abs cie-p) (list 'magnitude (list '* cie-eta 'cqz_)))
(subst (list '= (list '+ (list '* cie-rw '(real-part cqz_))
                         (list '* cie-iw '(imag-part cqz_)))
             cie-p))
(subst (list '= '(magnitude cqw_) (list 'magnitude cie-eta)))
(subst (list '= (list '* (list 'magnitude cie-eta) '(magnitude cqz_))
             (list 'magnitude (list '* cie-eta 'cqz_))))
(ass)
(qed 'cc-re-inner-bound)
(topic! 'cc-re-inner-bound 'inequalities)
(alias! 'cc-re-inner-bound
        "the real inner product of two complex numbers is at most the product of their moduli")

;;; =====================================================================
;;; (3) THE ESTIMATE (45).
;;; =====================================================================

(define cie-cc '(CCINT a b))
(define (cie-relam f) (list 'VNB-LAMBDA 'pat_ cie-cc (list 'real-part (list f 'pat_))))
(define (cie-imlam f) (list 'VNB-LAMBDA 'pat_ cie-cc (list 'imag-part (list f 'pat_))))

;;; (IN LAM (FUN [a,b] RR)) by `lam-t'; PTWISE! closes the pointwise leaf.
(define (cie-type-lam! lam ptwise!)
  (dk-have! (list 'IN lam (list 'FUN cie-cc 'RR))
    (lambda ()
      (for-each
       (lambda (leaf)
         (dk-focus! leaf)
         (if (eq? (cie-head (dk-goal)) 'FORALL)
             (let ((z (dk-di-var!))) (ptwise! z))
             (ass)))
       (dk-opened (lambda () (lam-t)))))))

(define (cie-value-eq! lam rhs-of)
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ cie-cc)
              (list '== (list lam 'pay_) (rhs-of 'pay_))))
    (lambda () (dk-di-var!) (dk-lam-b!) (qrfl))))

;;; (IN (* u v) RR) from the two typings.
(define (cie-mul-in-rr! u v)
  (dk-have! (list 'AND (list 'IN u 'RR) (list 'IN v 'RR)))
  (fact 'rr-mul-closed u v))

(sp (make-wff '(FORALL pphi_ (FORALL pwf_ (FORALL paw_ (FORALL pabs_
     (FORALL pbh_ (FORALL a (FORALL b
       (IMPLIES (IN pphi_ (FUN (CCINT a b) CC))
       (IMPLIES (IS-PRIMITIVE pwf_
                  (VNB-LAMBDA pat_ (CCINT a b) (real-part (pphi_ pat_))) a b)
       (IMPLIES (IS-PRIMITIVE paw_
                  (VNB-LAMBDA pat_ (CCINT a b) (imag-part (pphi_ pat_))) a b)
       (IMPLIES (IS-PRIMITIVE pbh_ pabs_ a b)
       (IMPLIES (FORALL pay_ (IMPLIES (IN pay_ (CCINT a b))
                               (== (pabs_ pay_) (magnitude (pphi_ pay_)))))
                (<= (magnitude (CC-INT pphi_ a b))
                    (PW-INT pabs_ a b))))))))))))))))
(dk-peel!)
(define cie-re (cie-relam 'pphi_))
(define cie-im (cie-imlam 'pphi_))
(define cie-jj '(CC-INT pphi_ a b))
(define cie-xx (list 'PW-INT cie-re 'a 'b))
(define cie-yy (list 'PW-INT cie-im 'a 'b))
(define cie-kk '(PW-INT pabs_ a b))
(define cie-mm (list 'magnitude cie-jj))
(define cie-ptw
  (dk-pick (lambda (fm) (and (pair? fm) (eq? (car fm) 'FORALL)
                             (dk-contains? fm 'magnitude)))
           "the pointwise modulus equation"))
(dk-split-all! (list (dk-fact! 'primitive-endpoints 'pwf_ cie-re 'a 'b)))
(fact 'rr-is-set)
(fact 'ccint-subset-rr 'a 'b)
(fact 'subclass-of-set-is-set cie-cc 'RR)
(fact 'pw-int-in-rr 'pwf_ cie-re 'a 'b)
(fact 'pw-int-in-rr 'paw_ cie-im 'a 'b)
(fact 'pw-int-in-rr 'pbh_ 'pabs_ 'a 'b)
(fact 'primitive-in-fun 'pwf_ cie-re 'a 'b)
(fact 'primitive-in-fun 'paw_ cie-im 'a 'b)
(fact 'primitive-in-fun 'pbh_ 'pabs_ 'a 'b)
(fact 'primitive-integrand-in-fun 'pbh_ 'pabs_ 'a 'b)
(fact 'cc-int-in-cc 'a 'b 'pphi_ 'pwf_ 'paw_)
(fact 'cc-magnitude-closed cie-jj)
(fact 'cc-magnitude-nonneg cie-jj)
;; ---- the coordinates of the integral are the two real integrals ----
(fact 'cc-int-value 'a 'b 'pphi_ 'pwf_ 'paw_)
(fact 'pw-int-value 'pwf_ cie-re 'a 'b)
(fact 'pw-int-value 'paw_ cie-im 'a 'b)
(dk-have! (list '= cie-jj (list '+ cie-xx (list '* cie-yy '+i)))
  (lambda ()
    (subst (list '= cie-jj (list '+ '(- (pwf_ b) (pwf_ a))
                                   (list '* '(- (paw_ b) (paw_ a)) '+i))))
    (subst (list '= cie-xx '(- (pwf_ b) (pwf_ a))))
    (subst (list '= cie-yy '(- (paw_ b) (paw_ a))))
    (rfl)))
(dk-split-all! (list (dk-fact! 'cc-re-im-of cie-jj cie-xx cie-yy)))
;; ---- |J|^2 = X^2 + Y^2 ----
(fact 'cc-magnitude-sq cie-jj)
;; `rfl' is strict: the two sides must be CERTIFIED DEFINED, and a product of
;; two PW-INT terms is not certified by their typings alone.
(cie-mul-in-rr! cie-xx cie-xx)
(cie-mul-in-rr! cie-yy cie-yy)
(have! (list 'AND (list 'IN (list '* cie-xx cie-xx) 'RR)
                  (list 'IN (list '* cie-yy cie-yy) 'RR)))
(fact 'rr-add-closed (list '* cie-xx cie-xx) (list '* cie-yy cie-yy))
(dk-have! (list '= (list '* cie-mm cie-mm)
                   (list '+ (list '* cie-xx cie-xx) (list '* cie-yy cie-yy)))
  (lambda ()
    (subst (list '= (list '* cie-mm cie-mm)
                 (list '+ (list '* (list 'real-part cie-jj) (list 'real-part cie-jj))
                          (list '* (list 'imag-part cie-jj) (list 'imag-part cie-jj)))))
    (subst (list '= (list 'real-part cie-jj) cie-xx))
    (subst (list '= (list 'imag-part cie-jj) cie-yy))
    (rfl)))
;; ---- the integrand X Re(f) + Y Im(f) and its primitive ----
(let* ((hh (list 'VNB-LAMBDA 'pct_ cie-cc
                 (list '+ (list '* cie-xx '(pwf_ pct_))
                          (list '* cie-yy '(paw_ pct_)))))
       (th (list 'VNB-LAMBDA 'pct_ cie-cc
                 (list '+ (list '* cie-xx (list 'real-part '(pphi_ pct_)))
                          (list '* cie-yy (list 'imag-part '(pphi_ pct_))))))
       (bd (list 'VNB-LAMBDA 'pct_ cie-cc (list '* cie-mm '(pabs_ pct_))))
       (mh (list 'VNB-LAMBDA 'pct_ cie-cc (list '* cie-mm '(pbh_ pct_)))))
  (cie-type-lam! hh
    (lambda (z)
      (fact 'fun-apply-type-c 'pwf_ cie-cc 'RR z)
      (fact 'fun-apply-type-c 'paw_ cie-cc 'RR z)
      (cie-mul-in-rr! cie-xx (list 'pwf_ z))
      (cie-mul-in-rr! cie-yy (list 'paw_ z))
      (have! (list 'AND (list 'IN (list '* cie-xx (list 'pwf_ z)) 'RR)
                        (list 'IN (list '* cie-yy (list 'paw_ z)) 'RR)))
      (fact 'rr-add-closed (list '* cie-xx (list 'pwf_ z))
                           (list '* cie-yy (list 'paw_ z)))
      (ass)))
  (cie-type-lam! th
    (lambda (z)
      (fact 'fun-apply-type-c 'pphi_ cie-cc 'CC z)
      (fact 'real-part-in-rr (list 'pphi_ z))
      (fact 'imag-part-in-rr (list 'pphi_ z))
      (cie-mul-in-rr! cie-xx (list 'real-part (list 'pphi_ z)))
      (cie-mul-in-rr! cie-yy (list 'imag-part (list 'pphi_ z)))
      (have! (list 'AND (list 'IN (list '* cie-xx (list 'real-part (list 'pphi_ z))) 'RR)
                        (list 'IN (list '* cie-yy (list 'imag-part (list 'pphi_ z))) 'RR)))
      (fact 'rr-add-closed (list '* cie-xx (list 'real-part (list 'pphi_ z)))
                           (list '* cie-yy (list 'imag-part (list 'pphi_ z))))
      (ass)))
  (cie-type-lam! bd
    (lambda (z)
      (fact 'fun-apply-type-c 'pabs_ cie-cc 'RR z)
      (cie-mul-in-rr! cie-mm (list 'pabs_ z))
      (ass)))
  (cie-type-lam! mh
    (lambda (z)
      (fact 'fun-apply-type-c 'pbh_ cie-cc 'RR z)
      (cie-mul-in-rr! cie-mm (list 'pbh_ z))
      (ass)))
  (cie-value-eq! hh (lambda (y) (list '+ (list '* cie-xx (list 'pwf_ y))
                                         (list '* cie-yy (list 'paw_ y)))))
  (cie-value-eq! th (lambda (y) (list '+ (list '* cie-xx (list cie-re y))
                                         (list '* cie-yy (list cie-im y)))))
  (cie-value-eq! bd (lambda (y) (list '* cie-mm (list 'pabs_ y))))
  (cie-value-eq! mh (lambda (y) (list '* cie-mm (list 'pbh_ y))))
  ;; X F + Y G is a primitive of X Re(f) + Y Im(f), and the integral is X^2+Y^2
  (dk-split!
   (dk-apply! (dk-apply! (dk-apply! (dk-fact! 'pw-antiderivative-linear 'a 'b)
                                    cie-xx cie-yy)
                         'pwf_ 'paw_ cie-re cie-im)
              hh th))
  ;; |J| H is a primitive of |J| |f|, and the integral is |J| PW-INT(|f|)
  (dk-split!
   (dk-apply! (dk-apply! (dk-fact! 'pw-antiderivative-real-mul 'a 'b)
                         'pbh_ 'pabs_ cie-mm)
              mh bd))
  ;; ---- the pointwise estimate ----
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ cie-cc)
              (list '<= (list th 'pay_) (list bd 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (dk-lam-b!)
        (fact 'fun-apply-type-c 'pphi_ cie-cc 'CC z)
        (fact 'cc-re-inner-bound cie-jj (list 'pphi_ z))
        (dk-apply! cie-ptw z)
        (subst (list '= cie-xx (list 'real-part cie-jj)))
        (subst (list '= cie-yy (list 'imag-part cie-jj)))
        (subst (list '== (list 'pabs_ z) (list 'magnitude (list 'pphi_ z))))
        (ass))))
  ;; ---- |f| is nonnegative, so its integral is ----
  (dk-have! (list 'FORALL 'pay_ (list 'IMPLIES (list 'IN 'pay_ cie-cc)
              (list '<= 0 (list 'pabs_ 'pay_))))
    (lambda ()
      (let ((z (dk-di-var!)))
        (fact 'fun-apply-type-c 'pphi_ cie-cc 'CC z)
        (fact 'cc-magnitude-nonneg (list 'pphi_ z))
        (dk-apply! cie-ptw z)
        (subst (list '== (list 'pabs_ z) (list 'magnitude (list 'pphi_ z))))
        (ass))))
  (fact 'pw-int-nonneg 'pbh_ 'pabs_ 'a 'b)
  (dk-apply! (dk-fact! 'pw-int-monotone hh th mh bd) 'a 'b)
  (fact 'pw-int-in-rr hh th 'a 'b)
  (fact 'pw-int-in-rr mh bd 'a 'b)
  ;; ---- |J|^2 <= |J| PW-INT(|f|), then the cancellation ----
  (cie-mul-in-rr! cie-mm cie-mm)
  (cie-mul-in-rr! cie-mm cie-kk)
  (dk-have! (list '<= (list '* cie-mm cie-mm) (list '* cie-mm cie-kk))
    (lambda ()
      (dk-ineq! (list '<= (list 'PW-INT th 'a 'b) (list 'PW-INT bd 'a 'b))
                (list '= (list 'PW-INT th 'a 'b)
                      (list '+ (list '* cie-xx cie-xx) (list '* cie-yy cie-yy)))
                (list '= (list 'PW-INT bd 'a 'b) (list '* cie-mm cie-kk))
                (list '= (list '* cie-mm cie-mm)
                      (list '+ (list '* cie-xx cie-xx) (list '* cie-yy cie-yy)))
                (list 'IN (list 'PW-INT th 'a 'b) 'RR)
                (list 'IN (list 'PW-INT bd 'a 'b) 'RR)
                (list 'IN (list '* cie-mm cie-mm) 'RR)
                (list 'IN (list '* cie-mm cie-kk) 'RR))))
  (use-em (list '= cie-mm 0)
    ;; |J| = 0: the integral of a nonnegative integrand is nonnegative
    (lambda ()
      (subst (list '= cie-mm 0))
      (ass))
    ;; |J| /= 0: cancel it
    (lambda ()
      (dk-have! (list 'AND (list 'IN cie-mm 'RR) (list 'IN cie-kk 'RR)))
      (let ((tot (dk-fact! 'rr-leq-total cie-mm cie-kk)))
        (dk-each-leaf! (lambda () (ai tot))
          (lambda ()
            (if (dk-ctx-form (list '<= cie-mm cie-kk))
                (ass)
                (begin
                  (fact 'rr-mul-le-right cie-kk cie-mm cie-mm)
                  (cie-mul-in-rr! cie-kk cie-mm)
                  (dk-have! (list '= (list '* cie-mm cie-kk) (list '* cie-kk cie-mm))
                    (lambda () (crs)))
                  (dk-have! (list '<= (list '* cie-mm cie-kk) (list '* cie-mm cie-mm))
                    (lambda ()
                      (dk-ineq! (list '<= (list '* cie-kk cie-mm) (list '* cie-mm cie-mm))
                                (list '= (list '* cie-mm cie-kk) (list '* cie-kk cie-mm))
                                (list 'IN (list '* cie-kk cie-mm) 'RR)
                                (list 'IN (list '* cie-mm cie-mm) 'RR)
                                (list 'IN (list '* cie-mm cie-kk) 'RR))))
                  (dk-have! (list 'AND (list 'IN (list '* cie-mm cie-mm) 'RR)
                                    (list 'IN (list '* cie-mm cie-kk) 'RR)))
                  (dk-have! (list 'AND (list '<= (list '* cie-mm cie-mm) (list '* cie-mm cie-kk))
                                    (list '<= (list '* cie-mm cie-kk) (list '* cie-mm cie-mm))))
                  (fact 'rr-leq-antisymmetric (list '* cie-mm cie-mm) (list '* cie-mm cie-kk))
                  (fact 'rr-cancel-mul-left cie-mm cie-mm cie-kk)
                  (fact 'rr-leq-reflexive cie-kk)
                  (subst (list '= cie-mm cie-kk))
                  (ass))))))))) 
(qed 'cc-int-abs-bound)
(topic! 'cc-int-abs-bound 'analysis)
(alias! 'cc-int-abs-bound
        "equation (45)"
        "the modulus of a complex integral is at most the integral of the modulus")
