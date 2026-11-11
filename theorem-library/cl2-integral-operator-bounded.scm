;;; cl2-integral-operator-bounded.scm -- wave of 2026-11-09/10 (agent TH3-L2C), wired 2026-11-10 from scratchpad/th3-1109/l2c/kc-d.scm.
;;; Library: operator-algebras.

;;; kc-d.scm -- the complex kernel operator is BOUNDED, with ||T_K|| <= ||K||_2
;;; (th-main 3.40, the complex kernel K = k1 + i k2 on CL2-HILBERT).
;;;   * cl2-int-op-linear:  T = CL2-INT-OP(xs, cA, mu, ys, cB, nu, k1, k2) is a linear operator
;;;     CL2-HILBERT(ys) -> CL2-HILBERT(xs);
;;;   * cl2-int-op-norm-bound: ||T z|| <= SQRT(||k1||^2 + ||k2||^2) ||z||;
;;;   * cl2-int-op-bounded: T is in BOUNDED-OPS and OPNORM(T) <= SQRT(||k1||^2 + ||k2||^2),
;;;     where ||k_j||^2 = int_{X x Y} k_j^2 d(mu x nu), i.e. ||K||_2^2 = ||k1||^2 + ||k2||^2.
;;;
;;; LOAD WINDOW: after kc-b and BA-BH's ba-ops-vocab and ba-bh (bop-intro, opnorm-spec,
;;; ip-norm-*).  Library: the join of measure and the operator vocabulary (cross-cutting).

(define (kcd-qed! name)
  (if (proof-done? *ps*)
      (begin (qed name) (topic! name 'analysis))
      (begin
        (display "\n*** kc-d: ") (display name) (display " did NOT close.  Open goals:\n")
        (for-each (lambda (l)
                    (display "   GOAL: ") (display (expression->string (dk-goal-of l))) (newline)
                    (for-each (lambda (a) (display "      asm: ") (display (expression->string a)) (newline))
                              (dk-asms-of l)))
                  (dk-open-leaves))
        (error "kc-d: unfinished" name))))
(define (kcd-open?) (not (proof-done? *ps*)))
(define kcd-xy '(CARTESIAN xs ys))
(define kcd-ps '(PRODUCT-SIGMA xs cA ys cB))
(define kcd-rho '(PRODUCT-MEASURE xs cA mu ys cB nu))
(define (kcd-l2k k) (list 'IN k (list 'L2-SET kcd-xy kcd-ps kcd-rho)))
(define kcd-hyps (list '(IS-MEASURE xs cA mu) '(IS-MEASURE ys cB nu) '(IS-SIGMA-FINITE xs cA mu)
                       '(IS-SIGMA-FINITE ys cB nu) (kcd-l2k 'k1) (kcd-l2k 'k2)))
(define kcd-T '(CL2-INT-OP xs cA mu ys cB nu k1 k2))
(define kcd-HX '(CL2-HILBERT xs cA mu))
(define kcd-HY '(CL2-HILBERT ys cB nu))
(define (kcd-ksq k) (list 'VNB-LAMBDA 'lx_ kcd-xy (list '* (list k 'lx_) (list k 'lx_))))
(define (kcd-kn k) (list 'INTEGRAL kcd-xy kcd-ps kcd-rho (kcd-ksq k)))
(define kcd-M2 (list '+ (kcd-kn 'k1) (kcd-kn 'k2)))
(define kcd-M (list 'SQRT kcd-M2))
(define kcd-args '(xs cA mu ys cB nu k1 k2))

;;; the Hilbert spaces, and ||K||^2 a nonnegative real
(define (kcd-base!)
  (dk-cite! 'cl2-hilbert-is-hilbert-space 'xs 'cA 'mu)
  (dk-cite! 'cl2-hilbert-is-hilbert-space 'ys 'cB 'nu)
  (dk-cite! 'hilbert-space-is-cips kcd-HX)
  (dk-cite! 'hilbert-space-is-cips kcd-HY)
  (fact 'product-sigma-is-sigma-algebra 'xs 'cA 'ys 'cB)
  (fact 'product-measure-is-measure 'xs 'cA 'mu 'ys 'cB 'nu)
  (for-each (lambda (k)
              (dk-split! (dk-cite! 'l2-square-integral kcd-xy kcd-ps kcd-rho k))
              (fact 'integral-in kcd-xy kcd-ps kcd-rho (kcd-ksq k))
              (fact 'rr-pos-star-nonneg (kcd-kn k)))
            '(k1 k2))
  (fact 'rr-add-in-rr (kcd-kn 'k1) (kcd-kn 'k2))
  (dk-have! (list '<= 0 kcd-M2) (lambda () (dk-ineq! (list '<= 0 (kcd-kn 'k1)) (list '<= 0 (kcd-kn 'k2)))))
  (dk-have! (list 'AND (list 'IN kcd-M2 'RR) (list '<= 0 kcd-M2)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-split! (dk-cite! 'sqrt-nonneg kcd-M2)))

;;; T is linear
(sp (make-wff (forall-guarded kcd-args kcd-hyps (list 'IS-LINEAR-OP kcd-HY kcd-HX kcd-T))))
(dk-peel!)
(apply dk-cite! (cons 'cl2-int-op-fun kcd-args))
(mac 'is-linear-op)
(dk-conj-close!
  (lambda ()
    (let ((g (dk-goal)))
      (cond
        ((dk-asm? g) (ass))
        ((and (dk-head-is? g '=) (equal? (cadr g) (caddr g))) (rfl))
        ((dk-head-is? g 'IN) (apply dk-cite! (cons 'cl2-int-op-fun kcd-args)) (if (kcd-open?) (ass)))
        ((dk-contains? g (list 'VADD kcd-HY))
         (let* ((lk (dk-peel!)) (vs (map cadr (filter (dk-head? 'IN) lk))))
           (apply dk-cite! (append (list 'cl2-int-op-add) kcd-args vs))
           (if (kcd-open?) (ass))))
        (#t
         (let* ((lk (dk-peel!)) (vs (map cadr (filter (dk-head? 'IN) lk))))
           (apply dk-cite! (append (list 'cl2-int-op-act) kcd-args vs))
           (if (kcd-open?) (ass))))))))
(for-each (lambda (l) (if (kcd-open?) (begin (dk-focus! l) (rfl)))) (dk-open-leaves))
(kcd-qed! 'cl2-int-op-linear)

;;; ||T z|| <= SQRT(||K||^2) ||z||
(sp (make-wff (forall-guarded (append kcd-args '(z_)) (append kcd-hyps (list (list 'IN 'z_ (list 'VEC kcd-HY))))
   (list '<= (list 'IP-NORM kcd-HX (list kcd-T 'z_)) (list '* kcd-M (list 'IP-NORM kcd-HY 'z_))))))
(dk-peel!)
(kcd-base!)
(let* ((tz (list kcd-T 'z_))
       (a (list (list 'IP kcd-HY) 'z_ 'z_))
       (b (list (list 'IP kcd-HX) tz tz))
       (ma (list '* kcd-M2 a)))
  (apply dk-cite! (cons 'cl2-int-op-fun kcd-args))
  (fact 'fun-apply-type-c kcd-T (list 'VEC kcd-HY) (list 'VEC kcd-HX) 'z_)
  (dk-cite! 'cips-ip-self-real kcd-HY 'z_)
  (dk-cite! 'cips-ip-self-nonneg kcd-HY 'z_)
  (dk-cite! 'cips-ip-self-real kcd-HX tz)
  (dk-cite! 'cips-ip-self-nonneg kcd-HX tz)
  (apply dk-cite! (append (list 'cl2-int-op-ip-bound) kcd-args '(z_)))
  (fact 'rr-mul-in-rr kcd-M2 a)
  (subst (dk-cite! 'ip-norm-unfold kcd-HX tz))
  (subst (dk-cite! 'ip-norm-unfold kcd-HY 'z_))
  (dk-have! (list 'AND (list 'IN a 'RR) (list '<= 0 a)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-have! (list 'AND (list 'IN kcd-M2 'RR) (list '<= 0 kcd-M2)) (lambda () (dk-conj-close! dk-ass!)))
  (let ((sm (dk-cite! 'sqrt-mul kcd-M2 a)))
    (subst (list '= (list '* kcd-M (list 'SQRT a)) (list 'SQRT ma))))
  (dk-have! (list 'AND (list 'IN b 'RR) (list '<= 0 b)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-have! (list 'AND (list 'IN ma 'RR) (list '<= b ma)) (lambda () (dk-conj-close! dk-ass!)))
  (dk-cite! 'sqrt-mono b ma)
  (if (kcd-open?) (ass)))
(kcd-qed! 'cl2-int-op-norm-bound)

