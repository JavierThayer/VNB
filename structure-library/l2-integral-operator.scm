;;; l2-integral-operator.scm -- wave of 2026-11-09/10 (agent TH3-L2C), wired 2026-11-10 from scratchpad/th3-1109/l2c/kc-vocab.scm.
;;; Library: measure.

;;; kc-vocab.scm -- THE L^2 INTEGRAL OPERATOR (TH3-L2C, 2026-11-10).  Vocabulary only: no proof.
;;;
;;; WHY NEW VOCABULARY (the measure pause makes an exception for L^2 integral operators, and
;;; this file records the reason as WAVE-TH3-COMMON asks).  th-main 3.40 / 3.41 speak of THE
;;; operator T_K on L^2; without a name for it every statement would carry a 30-node term.
;;;
;;; KERNEL-APPLY(xs, ys, cB, nu, k, f) is TH3-L2B's canonical representative G of
;;;     x |-> int_Y k(x, y) f(y) dnu(y)
;;; (l2b-e.scm, tle-g): the inner integrals of the positive and negative parts of
;;; F(x, y) = k(x, y) f(y), each truncated to 0 where it is infinite, subtracted.  It is a total
;;; real function on xs; off a mu-null set it equals the integral (kernel-operator-l2).
;;;
;;; CL2-INT-OP(xs, cA, mu, ys, cB, nu, k1, k2) is the operator T_K of the COMPLEX kernel
;;; K = k1 + i k2 (k1, k2 real kernels in L^2(X x Y)) from CL2-HILBERT(ys, cB, nu) to
;;; CL2-HILBERT(xs, cA, mu).  A vector of CL2-HILBERT is a pair [class f1, class f2] read as
;;; f1 + i f2 (l2c-vocab.scm), and
;;;     T_K [f1, f2] = [ K1 f1 - K2 f2 , K1 f2 + K2 f1 ]     (K_j f = KERNEL-APPLY(k_j, f)),
;;; the real and imaginary parts of int (k1 + i k2)(x, y) (f1 + i f2)(y) dnu(y).  The
;;; representative of a class is its CHOICE; that the value does not depend on it is the
;;; theorem cl2-int-op-classes.
;;;
;;; Binders sgx_ / kpw_ are those of l2b-e.scm's statement of kernel-operator-l2, so that the
;;; unfold equation produces its term literally.  kcz_ is used by no other file.
;;; LOAD WINDOW: after l2c-vocab (CL2-HILBERT).  Library: measure.

(define kcv-ff '(VNB-LAMBDA kpw_ (CARTESIAN kaxs_ kays_) (* (kak_ kpw_) (kaf_ (NTH 2 kpw_)))))
(define (kcv-xsi part) (list 'X-SECTION-INTEGRAL 'kaxs_ 'kays_ 'kacb_ 'kanu_ (list part '(CARTESIAN kaxs_ kays_) kcv-ff)))
(def-functoid 'KERNEL-APPLY '(kaxs_ kays_ kacb_ kanu_ kak_ kaf_)
  (list 'VNB-LAMBDA 'sgx_ 'kaxs_
        (list '- (list 'IF (list 'IN (list (kcv-xsi 'POS-PART) 'sgx_) 'RR) (list (kcv-xsi 'POS-PART) 'sgx_) 0)
                 (list 'IF (list 'IN (list (kcv-xsi 'NEG-PART) 'sgx_) 'RR) (list (kcv-xsi 'NEG-PART) 'sgx_) 0))))

(define kcv-l2x '(L2-SPACE kcxs_ kcca_ kcmu_))
(define kcv-st (list 'SIP-SETOID kcv-l2x))
(define (kcv-ka k f) (list 'KERNEL-APPLY 'kcxs_ 'kcys_ 'kccb_ 'kcnu_ k f))
(def-functoid 'CL2-INT-OP '(kcxs_ kcca_ kcmu_ kcys_ kccb_ kcnu_ kck1_ kck2_)
  (list 'VNB-LAMBDA 'kcz_ '(VEC (CL2-HILBERT kcys_ kccb_ kcnu_))
    (list 'LIST
      (list 'CLASS kcv-st (list (list 'VADD kcv-l2x) (kcv-ka 'kck1_ '(CHOICE (NTH 1 kcz_)))
                                (list (list 'VNEG kcv-l2x) (kcv-ka 'kck2_ '(CHOICE (NTH 2 kcz_))))))
      (list 'CLASS kcv-st (list (list 'VADD kcv-l2x) (kcv-ka 'kck1_ '(CHOICE (NTH 2 kcz_)))
                                (kcv-ka 'kck2_ '(CHOICE (NTH 1 kcz_))))))))

(notation! 'KERNEL-APPLY 'kind 'functoid 'arity 6
           'english "x |-> the integral over $2 of $5(x, y) $6(y) d$4(y)" 'tex "\\int {$5}(\\cdot, y)\\, {$6}(y)\\, d{$4}(y)")
(notation! 'CL2-INT-OP 'kind 'functoid 'arity 8
           'english "the integral operator with kernel $7 + i $8" 'tex "T_{{$7} + i {$8}}")
