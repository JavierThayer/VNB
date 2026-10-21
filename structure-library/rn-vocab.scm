;;; rn-vocab.scm -- E = R^n WITH THE SUP NORM, calculus.pdf ch. 2 s. 8 (32), (36)-(37), (44).
;;; DEFINITIONS ONLY.  CALC-2, 2026-10-19: OPTION A of the representation question, chosen by the user
;;; 2026-10-19 (a point of R^n is a function on INTERVAL(1, n)).
;;;
;;; REPRESENTATION (option A).  A point of R^n is a FUNCTION on the index set
;;; INTERVAL(1, n) = {i in NN : 1 <= i <= n}:
;;;
;;;     VEC(RN(n))  =  FUN(INTERVAL(1, n), RR)
;;;
;;; The i-th coordinate eta_i of the notes is the application eta(i); no new name.
;;; The operations are pointwise lambdas, the scalars are the reals pinned as
;;; NORMED-VECTOR-SPACE requires (the ring view of RR-NORMED-FIELD), exactly as
;;; RR-NVS (theorem-library/rr-nvs-exemplification.scm) does for n = 1.
;;;
;;;     RN-MAXABS(x, k)   max(|x(1)|, ..., |x(k)|), and 0 for k = 0  (primitive
;;;                       recursion on k, def-by-nn-recursion; meaningful for k <= n)
;;;     RN(n)             the 7-tuple instance of NORMED-VECTOR-SPACE, norm (32):
;;;                       ||eta|| = RN-MAXABS(eta, n)
;;;     RN-UNIT(n, i)     the unit basis vector e_i: j |-> 1 if j = i, else 0
;;;     RN-TRUNC(n, x, k) the first k coordinates of x, the rest 0: the notes' eta_k =
;;;                       sum_{i <= k} eta_i e_i in the proof of Prop. 2.29
;;;     HAS-DIR-DERIV(m, f, a, eta, L)
;;;                       Def 2.23 read LOCALLY, as the notes read it: the curve
;;;                       f_{a,eta}(t) = f(a + t.eta) (SEG-CURVE, directional-derivative.scm)
;;;                       has derivative L at 0 in the sense of HAS-DERIV-AT
;;;                       (interval-calculus.scm), which asks nothing of the curve
;;;                       outside a neighbourhood of 0.  For f in FUN(U, RR), U open,
;;;                       the curve is defined exactly where a + t.eta lies in U, so
;;;                       the predicate is FALSE (not undefined) when no segment
;;;                       around a in direction eta lies in U.  Over ANY normed vector
;;;                       space m; R^n is the case m = RN(n).
;;;
;;; Load window: after theorem-library/directional-derivative (SEG-CURVE) and
;;; structure-library/interval-calculus (HAS-DERIV-AT, OOINT).  Library: analysis.

(def-by-nn-recursion 'RN-MAXABS '(rnmx_)
  '0
  '(rnmk_ rnmv_)
  '(max rnmv_ (abs (rnmx_ (succ rnmk_)))))

(notation! 'RN-MAXABS 'kind 'functoid 'arity 2
           'english "the largest of the absolute values of the first $2 coordinates of $1")

(def-functoid 'RN '(n)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD)
         (FUN (INTERVAL 1 n) RR)
         (VNB-LAMBDA (LIST rnax_ rnay_)
                     (CARTESIAN (FUN (INTERVAL 1 n) RR) (FUN (INTERVAL 1 n) RR))
                     (VNB-LAMBDA rnai_ (INTERVAL 1 n) (+ (rnax_ rnai_) (rnay_ rnai_))))
         (VNB-LAMBDA rnzi_ (INTERVAL 1 n) 0)
         (VNB-LAMBDA rnnx_ (FUN (INTERVAL 1 n) RR)
                     (VNB-LAMBDA rnni_ (INTERVAL 1 n) (- (rnnx_ rnni_))))
         (VNB-LAMBDA (LIST rnsr_ rnsx_)
                     (CARTESIAN RR (FUN (INTERVAL 1 n) RR))
                     (VNB-LAMBDA rnsi_ (INTERVAL 1 n) (* rnsr_ (rnsx_ rnsi_))))
         (VNB-LAMBDA rnvx_ (FUN (INTERVAL 1 n) RR) (RN-MAXABS rnvx_ n))))

(notation! 'RN 'kind 'functoid 'arity 1
           'english "the space of real $1-tuples with the sup norm")

(def-functoid 'RN-UNIT '(n i)
  '(VNB-LAMBDA rnuj_ (INTERVAL 1 n) (IF (= rnuj_ i) 1 0)))

(notation! 'RN-UNIT 'kind 'functoid 'arity 2
           'english "the unit basis vector $2 of the space of real $1-tuples")

(def-functoid 'RN-TRUNC '(n x k)
  '(VNB-LAMBDA rntj_ (INTERVAL 1 n) (IF (<= rntj_ k) (x rntj_) 0)))

(notation! 'RN-TRUNC 'kind 'functoid 'arity 3
           'english "the vector of the first $3 coordinates of $2 in the space of real $1-tuples")

(def-predicate 'HAS-DIR-DERIV '(m f a eta L)
  '(HAS-DERIV-AT (SEG-CURVE m f a eta) 0 L))

(notation! 'HAS-DIR-DERIV 'kind 'predicate 'arity 5
           'english "$2 has directional derivative $5 at $3 in the direction $4")
