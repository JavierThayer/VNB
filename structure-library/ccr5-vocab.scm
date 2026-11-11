;;; ccr5-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-D), wired 2026-11-10 from scratchpad/ccr1109d/ccr5-vocab.scm.
;;; Library: complex-analysis.

;;; ccr5-vocab.scm -- THE DUAL OF K+ AND BICHARACTERS OF A LOCAL NV FIELD (CCR.pdf chapter 5, 5.10-5.15;
;;; chapter 6, 6.5, 6.11-6.13).  DEFINITIONS ONLY; the laws are in theorem-library/ccr5-dual.scm.
;;; Agent CCR-1109-D, 2026-11-09.  Destination: structure-library/ccr5-vocab.scm.  Library: complex-analysis
;;; (beside ccr4-vocab, which is there).  Load window: after ccr2-vocab, ccr4-vocab, metric-topology, metric-subspace,
;;; compactness.
;;;
;;;   IS-LOCAL-UNIFORMIZER(K, uw)    Z(K) is compact and uw is a uniformizing parameter of K: M(Z(K)) = (uw),
;;;                                  uw /= 0 (the local NV field of Definition 2.15 with the parameter of
;;;                                  Definition 4.3, as in 4.7, 4.8, 4.12 of theorem-library/ccr2-nv)
;;;   IS-LOCALLY-CONSTANT-FN(K, f)   every x has a ball B(x, r), r > 0, on which f is constant
;;;   CHAR-CONVERGES(K, cs, chi)     cs : NN -> functions converges to chi uniformly on every compact subset
;;;                                  of K (the topology of the dual (53), on sequences: Proposition 5.10)
;;;   BICHAR-POLAR(K, w, V)          pol_w V = {eta in K : w(eta, xi) = 1 for all xi in V}       ((62))
;;;   IS-UNIPOLAR(K, w)              a bilinear bicharacter for which Z(K) is self-polar      (Def. 6.13)
;;;   IS-DUALIZING-CHARACTER(K, chi) chi non-trivial and every character is Psi_chi(a)   (Remark 6.4)
;;;   IS-FAITHFUL-BICHARACTER(K, w)  every character is xi |-> w(xi, x) and eta |-> w(y, eta) for unique
;;;                                  x, y, and the characters separate the points of K       (Def. 6.5)
;;; Binders c5*_.

(def-predicate 'IS-LOCAL-UNIFORMIZER '(c5k_ c5u_)
  '(AND (IS-COMPACT-NV-DOMAIN c5k_ (NV-INTEGERS c5k_))
   (AND (IN c5u_ (NV-INTEGERS c5k_))
   (AND (= (NV-MAXIMAL c5k_ (NV-INTEGERS c5k_)) (NV-PRINCIPAL c5k_ (NV-INTEGERS c5k_) c5u_))
        (NOT (= c5u_ (ZERO c5k_)))))))
(notation! 'IS-LOCAL-UNIFORMIZER 'kind 'predicate 'arity 2
           'english "$1 has compact integers and $2 is a uniformizing parameter of $1")

(def-predicate 'IS-LOCALLY-CONSTANT-FN '(c5k_ c5f_)
  '(FORALL c5x_ (IMPLIES (IN c5x_ (CARR c5k_))
     (FORSOME c5r_ (AND (POS-RR c5r_)
       (FORALL c5y_ (IMPLIES (IN c5y_ (CARR c5k_))
         (IMPLIES (<= ((FNRM c5k_) ((ADD c5k_) c5y_ ((NEG c5k_) c5x_))) c5r_) (= (c5f_ c5y_) (c5f_ c5x_))))))))))
(notation! 'IS-LOCALLY-CONSTANT-FN 'kind 'predicate 'arity 2 'english "$2 is locally constant on $1")

(def-predicate 'CHAR-CONVERGES '(c5k_ c5s_ c5c_)
  '(FORALL c5e_ (IMPLIES (SUBSET c5e_ (CARR c5k_))
     (IMPLIES (IS-COMPACT (SUBSPACE-MS (NF-METRIC-SPACE c5k_) c5e_))
       (FORALL c5p_ (IMPLIES (POS-RR c5p_)
         (FORSOME c5n_ (AND (IN c5n_ NN)
           (FORALL c5m_ (IMPLIES (IN c5m_ NN) (IMPLIES (<= c5n_ c5m_)
             (FORALL c5x_ (IMPLIES (IN c5x_ c5e_)
               (< (magnitude (- ((c5s_ c5m_) c5x_) (c5c_ c5x_))) c5p_))))))))))))))
(notation! 'CHAR-CONVERGES 'kind 'predicate 'arity 3
           'english "$2 converges to $3 uniformly on the compact subsets of $1")

(def-functoid 'BICHAR-POLAR '(c5k_ c5w_ c5v_)
  '(SEP c5h_ (CARR c5k_) (FORALL c5x_ (IMPLIES (IN c5x_ c5v_) (= (c5w_ c5h_ c5x_) 1)))))
(notation! 'BICHAR-POLAR 'kind 'functoid 'arity 3 'english "the polar of $3 with respect to $2")

(def-predicate 'IS-UNIPOLAR '(c5k_ c5w_)
  '(AND (IS-BILINEAR-BICHARACTER c5k_ c5w_)
        (= (BICHAR-POLAR c5k_ c5w_ (NV-INTEGERS c5k_)) (NV-INTEGERS c5k_))))
(notation! 'IS-UNIPOLAR 'kind 'predicate 'arity 2 'english "$2 is a unipolar bicharacter on $1")

(def-predicate 'IS-FAITHFUL-BICHARACTER '(c5k_ c5w_)
  '(AND (IS-BICHARACTER c5k_ c5w_)
   (AND (FORALL c5c_ (IMPLIES (IS-ADD-CHARACTER c5k_ c5c_)
          (AND (FORSOME c5x_ (AND (IN c5x_ (CARR c5k_))
                 (AND (= c5c_ (VNB-LAMBDA c5h_ (CARR c5k_) (c5w_ c5h_ c5x_)))
                      (FORALL c5y_ (IMPLIES (IN c5y_ (CARR c5k_))
                        (IMPLIES (= c5c_ (VNB-LAMBDA c5h_ (CARR c5k_) (c5w_ c5h_ c5y_))) (= c5y_ c5x_)))))))
               (FORSOME c5x_ (AND (IN c5x_ (CARR c5k_))
                 (AND (= c5c_ (VNB-LAMBDA c5h_ (CARR c5k_) (c5w_ c5x_ c5h_)))
                      (FORALL c5y_ (IMPLIES (IN c5y_ (CARR c5k_))
                        (IMPLIES (= c5c_ (VNB-LAMBDA c5h_ (CARR c5k_) (c5w_ c5y_ c5h_))) (= c5y_ c5x_))))))))))
        (FORALL c5x_ (IMPLIES (IN c5x_ (CARR c5k_)) (IMPLIES (NOT (= c5x_ (ZERO c5k_)))
          (FORSOME c5c_ (AND (IS-ADD-CHARACTER c5k_ c5c_) (NOT (= (c5c_ c5x_) 1))))))))))
(notation! 'IS-FAITHFUL-BICHARACTER 'kind 'predicate 'arity 2 'english "$2 is a faithful bicharacter on $1")

;;; IS-DUALIZING-CHARACTER(K, chi): chi is non-trivial and every character of K+ is Psi_chi(a), a in K -- the
;;; self-duality of Remark 6.4 ("the only property of K used"), the conclusion of Proposition 5.13
(def-predicate 'IS-DUALIZING-CHARACTER '(c5k_ c5c_)
  '(AND (IS-NONTRIVIAL-CHARACTER c5k_ c5c_)
        (FORALL c5t_ (IMPLIES (IS-ADD-CHARACTER c5k_ c5t_)
          (FORSOME c5a_ (AND (IN c5a_ (CARR c5k_)) (= c5t_ (DUALITY-MAP c5k_ c5c_ c5a_))))))))
(notation! 'IS-DUALIZING-CHARACTER 'kind 'predicate 'arity 2
           'english "$2 is a non-trivial character of $1 of which every character of $1 is a dilate")
