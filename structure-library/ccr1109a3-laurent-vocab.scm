;;; ccr1109a3-laurent-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-A3), wired 2026-11-10 from scratchpad/ccr1109a3/ccr1109a3-laurent-vocab.scm.
;;; Library: analysis.

;;; ccr1109a3-laurent-vocab.scm -- CCR.pdf section 1.5: formal Laurent series K((x)).  DEFINITIONS ONLY.
;;; Agent CCR-1109-A2 (2026-11-09), revised by CCR-1109-A3 the same day.  THIS FILE REPLACES
;;; scratchpad/ccr1109a2/ccr1109a2-laurent-vocab.scm (load one of them, never both).
;;; Destination: structure-library/ccr1109a3-laurent-vocab.scm.
;;; Library: analysis (LAURENT-ABS uses RPOW-STAR; the rest is algebra).
;;; Load window: after structure-library/polynomial (MONALG-MUL, FINSUPP, SUPP), numeric-instances
;;; (the COMM-MONOID shape used by declare-instance!) and theorem-library/rpow-star (RPOW-STAR).
;;;
;;; A Laurent series over a ring K is a function f : ZZ -> CARR(K) whose support is bounded below.  The
;;; operations are those of the monoid algebra K[ZZ] (polynomial.scm): pointwise sum and negation, the
;;; indicator of 0 as the one, and the convolution
;;;     (f g)(n) = FINSUM over { (p, q) in supp f x supp g : p + q = n } of f(p) g(q).
;;; CHANGE FROM A2: LAURENT-MUL is now LITERALLY MONALG-MUL at ZZ-ADD-MONOID = [ZZ, +, 0] (defined here),
;;; which is the same convolution with the monoid's operation in place of `+'.  The point is that every
;;; multiplicative law of K((x)) is then a law of MONALG-MUL read through truncation
;;; (theorem-library/ccr1109a3-laurent-ring.scm), with no FINSUM manipulation of its own.  A2's
;;; LAURENT-SUPP is kept (unused by the laws).  LAURENT-TRUNC(K, f, N) is the truncation of f above N.
;;; The order of f /= 0 is the least index of a non-zero coefficient (an IOTA); |f| = r^ord(f) for
;;; f /= 0 and |0| = 0, with 0 < r < 1 a parameter.

;; ZZ under addition, the exponent monoid of Laurent series (NN-ADD-MONOID's shape)
(declare-instance! 'ZZ-ADD-MONOID 'COMM-MONOID 'zz-add-monoid-def
  '(ZZ (VNB-LAMBDA (LIST x_ y_) (CARTESIAN ZZ ZZ) (+ x_ y_))
       0))
(register-definitional-structure! 'ZZ-ADD-MONOID 'COMM-MONOID)

(def-predicate 'IS-LAURENT '(lrk_ lrf_)
  '(AND (IN lrf_ (FUN ZZ (CARR lrk_)))
        (FORSOME lrb_ (AND (IN lrb_ ZZ)
          (FORALL lrj_ (IMPLIES (IN lrj_ ZZ) (IMPLIES (< lrj_ lrb_) (= (lrf_ lrj_) (ZERO lrk_)))))))))
(notation! 'IS-LAURENT 'kind 'predicate 'arity 2 'english "$2 is a Laurent series over $1")

(def-functoid 'LAURENT-SET '(lrk_) '(SEP lrf_ (FUN ZZ (CARR lrk_)) (IS-LAURENT lrk_ lrf_)))
(notation! 'LAURENT-SET 'kind 'functoid 'arity 1 'english "the formal Laurent series $1((x))")

(def-functoid 'LAURENT-SUPP '(lrk_ lrf_) '(SEP lrj_ ZZ (NOT (= (lrf_ lrj_) (ZERO lrk_)))))
(notation! 'LAURENT-SUPP 'kind 'functoid 'arity 2 'english "the support of the Laurent series $2")

(def-functoid 'LAURENT-ADD '(lrk_ lrf_ lrg_) '(VNB-LAMBDA lrj_ ZZ ((ADD lrk_) (lrf_ lrj_) (lrg_ lrj_))))
(notation! 'LAURENT-ADD 'kind 'functoid 'arity 3 'english "the sum of the Laurent series $2 and $3")
(def-functoid 'LAURENT-NEG '(lrk_ lrf_) '(VNB-LAMBDA lrj_ ZZ ((NEG lrk_) (lrf_ lrj_))))
(notation! 'LAURENT-NEG 'kind 'functoid 'arity 2 'english "the negative of the Laurent series $2")
(def-functoid 'LAURENT-ZERO '(lrk_) '(VNB-LAMBDA lrj_ ZZ (ZERO lrk_)))
(notation! 'LAURENT-ZERO 'kind 'functoid 'arity 1 'english "the zero Laurent series over $1")
(def-functoid 'LAURENT-ONE '(lrk_) '(VNB-LAMBDA lrj_ ZZ (IF (= lrj_ 0) (ONE lrk_) (ZERO lrk_))))
(notation! 'LAURENT-ONE 'kind 'functoid 'arity 1 'english "the unit Laurent series over $1")

(def-functoid 'LAURENT-MUL '(lrk_ lrf_ lrg_) '(MONALG-MUL lrk_ ZZ-ADD-MONOID lrf_ lrg_))
(notation! 'LAURENT-MUL 'kind 'functoid 'arity 3 'english "the product of the Laurent series $2 and $3")

;; the ring 6-tuple, MONALG's shape
(def-functoid 'LAURENT-RING '(lrk_)
  '(LIST (LAURENT-SET lrk_)
         (VNB-LAMBDA (LIST lrf_ lrg_) (CARTESIAN (LAURENT-SET lrk_) (LAURENT-SET lrk_)) (LAURENT-ADD lrk_ lrf_ lrg_))
         (VNB-LAMBDA (LIST lrf_ lrg_) (CARTESIAN (LAURENT-SET lrk_) (LAURENT-SET lrk_)) (LAURENT-MUL lrk_ lrf_ lrg_))
         (VNB-LAMBDA lrf_ (LAURENT-SET lrk_) (LAURENT-NEG lrk_ lrf_))
         (LAURENT-ZERO lrk_)
         (LAURENT-ONE lrk_)))
(notation! 'LAURENT-RING 'kind 'functoid 'arity 1 'english "the ring of formal Laurent series $1((x))")

;; the order: the least index of a non-zero coefficient (for f /= 0)
(def-functoid 'LAURENT-ORD '(lrk_ lrf_)
  '(IOTA lro_ (AND (IN lro_ ZZ) (AND (NOT (= (lrf_ lro_) (ZERO lrk_)))
          (FORALL lrj_ (IMPLIES (IN lrj_ ZZ) (IMPLIES (< lrj_ lro_) (= (lrf_ lrj_) (ZERO lrk_)))))))))
(notation! 'LAURENT-ORD 'kind 'functoid 'arity 2 'english "the order of the Laurent series $2")

;; |f| = r^ord(f), |0| = 0
(def-functoid 'LAURENT-ABS '(lrk_ lrr_ lrf_)
  '(IF (= lrf_ (LAURENT-ZERO lrk_)) 0 (RPOW-STAR lrr_ (LAURENT-ORD lrk_ lrf_))))
(notation! 'LAURENT-ABS 'kind 'functoid 'arity 3 'english "the absolute value $2^ord($3) of the Laurent series $3")

;; the truncation of f above N: f(j) for j <= N, 0 beyond.  A Laurent series truncated is finitely supported.
(def-functoid 'LAURENT-TRUNC '(lrk_ lrf_ lrt_) '(VNB-LAMBDA lrj_ ZZ (IF (<= lrj_ lrt_) (lrf_ lrj_) (ZERO lrk_))))
(notation! 'LAURENT-TRUNC 'kind 'functoid 'arity 3 'english "the truncation of $2 above $3")

;;; -----------------------------------------------------------------------
;;; THE INVERSE (CCR 1.35: K((x)) is a field when K is).  For f with order o and a = f(o)^-1 the inverse is
;;; built coefficient by coefficient, each coefficient chosen from the PREFIX already built -- a
;;; course-of-values recursion, carried by an ordinary NN recursion whose value is the whole prefix:
;;;   P_0      = a x^(-o)
;;;   P_(m+1)  = P_m + c_m x^(m+1-o),   c_m = -(a (f P_m)(m+1))
;;; so that (f P_m)(n) is the unit's coefficient for every n <= m; the inverse reads its coefficient at j
;;; off the prefix P_(j+o), and agrees with every P_M up to M - o.
;;; -----------------------------------------------------------------------
;; the monomial c x^t
(def-functoid 'LAURENT-MONO '(lrk_ lrc_ lrt_) '(VNB-LAMBDA lrj_ ZZ (IF (= lrj_ lrt_) lrc_ (ZERO lrk_))))
(notation! 'LAURENT-MONO 'kind 'functoid 'arity 3 'english "the monomial $2 x^$3")
;; the prefixes of the inverse of f (order o, a the inverse of f(o)); installs laurent-inv-pre-zero / -succ
(def-by-nn-recursion 'LAURENT-INV-PRE '(lrk_ lrf_ lro_ lra_)
  '(LAURENT-MONO lrk_ lra_ (- lro_))
  '(lrm_ lrv_)
  '(LAURENT-ADD lrk_ lrv_
     (LAURENT-MONO lrk_ ((NEG lrk_) ((MUL lrk_) lra_ ((LAURENT-MUL lrk_ lrf_ lrv_) (+ lrm_ 1))))
                   (+ (+ lrm_ 1) (- lro_)))))
(notation! 'LAURENT-INV-PRE 'kind 'functoid 'arity 5 'english "the prefix of length $5 of the inverse of $2")
;; the inverse itself: its coefficient at j is the one the prefix P_(j+o) fixed
(def-functoid 'LAURENT-INV-SER '(lrk_ lrf_ lro_ lra_)
  '(VNB-LAMBDA lrj_ ZZ (IF (<= (- lro_) lrj_) ((LAURENT-INV-PRE lrk_ lrf_ lro_ lra_ (+ lrj_ lro_)) lrj_) (ZERO lrk_))))
(notation! 'LAURENT-INV-SER 'kind 'functoid 'arity 4 'english "the inverse series of $2")

;;; K((x)) as a normed field: the ring's six slots and the order valuation |f| = r^ord(f) (0 < r < 1 for an NV field)
(def-functoid 'LAURENT-NF '(lrk_ lrr_)
  '(LIST (CARR (LAURENT-RING lrk_)) (ADD (LAURENT-RING lrk_)) (MUL (LAURENT-RING lrk_)) (NEG (LAURENT-RING lrk_))
         (ZERO (LAURENT-RING lrk_)) (ONE (LAURENT-RING lrk_))
         (VNB-LAMBDA lrf_ (CARR (LAURENT-RING lrk_)) (LAURENT-ABS lrk_ lrr_ lrf_))))
(notation! 'LAURENT-NF 'kind 'functoid 'arity 2 'english "the normed field $1((x)) with |f| = $2^ord(f)")
