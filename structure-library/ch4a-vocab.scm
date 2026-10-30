;;; ch4a-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ch4a/ch4a-vocab.scm.
;;; Library: complex-analysis.

;;; ch4a-vocab.scm -- complex-analysis 4.1 (Laurent series): vocabulary (CH4-A, 2026-10-28).
;;; Destination: structure-library/.  Library: complex-analysis.
;;; ANNULUS(a, r, s)        the open annulus {z in CC : r < |z - a| < s}  (A(a, 0, r) is the punctured ball)
;;; CLOSED-ANNULUS(a, r, s) {z in CC : r <= |z - a| <= s}
;;; LAURENT-SUM(c, a, z)    sum_{k in ZZ} c(k) (z - a)^k for a two-sided coefficient family c in FUN(ZZ, CC),
;;;                         the sum of the two power series of the notes' proof of 4.1:
;;;                         sum_{k >= 0} c(k) (z - a)^k  +  w sum_{l >= 0} c(-(l + 1)) w^l,   w = 1/(z - a)
;;; The upper radius of convergence is CPS-RADIUS(k |-> c(k)); the lower one is 1 / CPS-RADIUS(l |-> c(-(l+1)))
;;; (the notes' A_-^{-1}; the shift by one index does not change a radius).  Load window: after cc-power-series.
(def-functoid 'ANNULUS '(anla_ anlr_ anls_)
  '(SEP anlz_ CC (AND (< anlr_ (magnitude (- anlz_ anla_))) (< (magnitude (- anlz_ anla_)) anls_))))
(notation! 'ANNULUS 'kind 'functoid 'arity 3 'english "the open annulus about $1 between the radii $2 and $3")
(def-functoid 'CLOSED-ANNULUS '(anla_ anlr_ anls_)
  '(SEP anlz_ CC (AND (<= anlr_ (magnitude (- anlz_ anla_))) (<= (magnitude (- anlz_ anla_)) anls_))))
(notation! 'CLOSED-ANNULUS 'kind 'functoid 'arity 3 'english "the closed annulus about $1 between the radii $2 and $3")
(def-functoid 'LAURENT-SUM '(lsc_ lsa_ lsz_)
  '(+ (CC-SERIES-LIMIT (VNB-LAMBDA lsk_ NN (* (lsc_ lsk_) (power (- lsz_ lsa_) lsk_))))
      (* (recip (- lsz_ lsa_))
         (CC-SERIES-LIMIT (VNB-LAMBDA lsk_ NN (* (lsc_ (- (+ lsk_ 1))) (power (recip (- lsz_ lsa_)) lsk_)))))))
(notation! 'LAURENT-SUM 'kind 'functoid 'arity 3 'english "the sum of the Laurent series with coefficients $1 about $2 at $3")
;;; LAURENT-COEFS(f, c, rho): the two-sided coefficient family of the Laurent expansion of f about c, read on the
;;; circle of radius rho (the notes' (106) in line-integral form): for k in ZZ,
;;;   k >= 0:  c_k = 1/(2 pi i) int_{|w - c| = rho} f(w) (1/(w - c))^(k+1) dw
;;;   k < 0:   c_k = 1/(2 pi i) int_{|w - c| = rho} f(w) (w - c)^(-(k+1)) dw
;;; The integrand is a function on the circle's trace.  Proposition 4.5 (laurent-expansion) shows that the
;;; family does not depend on rho in the annulus of holomorphy, and that f is its LAURENT-SUM there.
(def-functoid 'LAURENT-COEFS '(lcf_ lcc_ lcr_)
  '(VNB-LAMBDA lck_ ZZ
     (IF (<= 0 lck_)
         (* (recip (* (* 2 PI) +i))
            (LINE-INT (VNB-LAMBDA lcw_ (TRACE (CIRCLE-PATH lcc_ lcr_) 0 (* 2 PI))
                                  (* (lcf_ lcw_) (power (recip (- lcw_ lcc_)) (succ lck_))))
                      (CIRCLE-PATH lcc_ lcr_) (CIRCLE-DERIV lcc_ lcr_) 0 (* 2 PI)))
         (* (recip (* (* 2 PI) +i))
            (LINE-INT (VNB-LAMBDA lcw_ (TRACE (CIRCLE-PATH lcc_ lcr_) 0 (* 2 PI))
                                  (* (lcf_ lcw_) (power (- lcw_ lcc_) (- (+ lck_ 1)))))
                      (CIRCLE-PATH lcc_ lcr_) (CIRCLE-DERIV lcc_ lcr_) 0 (* 2 PI))))))
(notation! 'LAURENT-COEFS 'kind 'functoid 'arity 3 'english "the Laurent coefficients of $1 about $2 read on the circle of radius $3")
