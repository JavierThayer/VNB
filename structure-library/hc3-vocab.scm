;;; hc3-vocab.scm -- wave of 2026-11-09/10 (agent HAAR-C3), wired 2026-11-10 from scratchpad/haarc3-1109/hc3-vocab.scm.
;;; Library: analysis.

;;; hc3-vocab.scm -- the opposite group, the averaging operators of a compact metric group, the Haar mean and
;;; the Haar integral (compact-groups notes, Theorem 1.9 and Corollary 1.10; th-main Lemma 3.80, Prop 3.81,
;;; Cor 3.82).  DEFINITIONS ONLY.  Agent HAAR-C3, 2026-11-09 (new definitions, the user's to confirm).
;;; DESTINATION: structure-library/hc3-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/hc-vocab (IS-HAAR-INTEGRAL), hc2-vocab (CK-NVS), isom2-vocab
;;; (METRIC-GROUP, MAKE-METRIC-GROUP) and cvx-vocab (CONV-HULL).  Nothing is cited.
;;;
;;;   OPP-GROUP(g)            the opposite group of the group g: the same carrier, identity and inverse, and the
;;;                           product (p, q) |-> q p.
;;;   OPP-METRIC-GROUP(G)     the opposite metric group: the opposite group of G with the distance of G.  Its
;;;                           metric space is the metric space of G (theorem opp-mg-ms), and its LEFT translates
;;;                           x |-> f(b *' x) are the RIGHT translates x |-> f(x b) of G (opp-mg-ltrans-eq): every
;;;                           statement about left translations, applied to OPP-METRIC-GROUP(G), is the same
;;;                           statement about right translations of G.  This replaces the "right-hull mirror".
;;;   HAAR-AVERAGES(G)        the averaging operators of G: the maps A : C(G) -> C(G) that are additive,
;;;                           real-homogeneous, 1-Lipschitz for the supremum distance, fix the constants, send
;;;                           every u into the convex hull of its left translates, and commute with every right
;;;                           translation.  Each left translation is one (haar-ltrans-avg) and a convex
;;;                           combination of two is one (haar-avg-comb); so every point of the convex hull of the
;;;                           left translates of f is A f for some A in HAAR-AVERAGES(G) (haar-hull-rep): the
;;;                           "finite weighted average of translates" of th-main Lemma 3.80, without a finite sum.
;;;   HAAR-MEAN(G, f)         the real c whose constant function lies in the closed convex hull K(f) of the left
;;;                           translates of f (IOTA; unique by haar-constants-agree, th-main Lemma 3.80).
;;;   HAAR-INTEGRAL(G)        the Haar integral of G: the unique mu with IS-HAAR-INTEGRAL(G, mu) (IOTA; it is
;;;                           f |-> HAAR-MEAN(G, f): haar-integral-is-haar, haar-integral-value).
;;;
;;; The terms K(f), the left translate x |-> f(a x) and the constant x |-> c are written exactly as in
;;; theorem-library/haar-c2.scm (binders hqa_, hix_), so that its theorems apply literally.
;;; BINDERS: ogg_ ogp_ ogq_ omg_ hag_ haq_ hau_ hav_ har_ hac_ hab_ hmg_ hmf_ hmc_ hng_ hnu_ (and hqa_, hix_ as said).

(def-functoid 'OPP-GROUP '(ogg_)
  '(LIST (CARR ogg_)
         (VNB-LAMBDA (LIST ogp_ ogq_) (CARTESIAN (CARR ogg_) (CARR ogg_)) ((OPR ogg_) ogq_ ogp_))
         (IDEN ogg_)
         (INV ogg_)))
(notation! 'OPP-GROUP 'kind 'functoid 'arity 1 'english "the opposite group of $1"
           'tex "{$1}^{\\mathrm{op}}")

(def-functoid 'OPP-METRIC-GROUP '(omg_)
  '(MAKE-METRIC-GROUP (METRIC-GROUP-MS omg_) (OPP-GROUP (METRIC-GROUP-GROUP omg_))))
(notation! 'OPP-METRIC-GROUP 'kind 'functoid 'arity 1 'english "the opposite metric group of $1"
           'tex "{$1}^{\\mathrm{op}}")

(def-functoid 'HAAR-AVERAGES '(hag_)
  (list 'SEP 'haq_ '(FUN (CONT-FNS (METRIC-GROUP-MS hag_)) (CONT-FNS (METRIC-GROUP-MS hag_)))
    (conjuncts->and
      (list
        '(FORALL hau_ (IMPLIES (IN hau_ (CONT-FNS (METRIC-GROUP-MS hag_)))
           (FORALL hav_ (IMPLIES (IN hav_ (CONT-FNS (METRIC-GROUP-MS hag_)))
             (= (haq_ ((VADD (CK-NVS (METRIC-GROUP-MS hag_))) hau_ hav_)) ((VADD (CK-NVS (METRIC-GROUP-MS hag_))) (haq_ hau_) (haq_ hav_)))))))
        '(FORALL har_ (IMPLIES (IN har_ RR)
           (FORALL hau_ (IMPLIES (IN hau_ (CONT-FNS (METRIC-GROUP-MS hag_)))
             (= (haq_ ((ACT (CK-NVS (METRIC-GROUP-MS hag_))) har_ hau_)) ((ACT (CK-NVS (METRIC-GROUP-MS hag_))) har_ (haq_ hau_)))))))
        '(FORALL hau_ (IMPLIES (IN hau_ (CONT-FNS (METRIC-GROUP-MS hag_)))
           (FORALL hav_ (IMPLIES (IN hav_ (CONT-FNS (METRIC-GROUP-MS hag_)))
             (<= ((DIST (NVS-METRIC-SPACE (CK-NVS (METRIC-GROUP-MS hag_)))) (haq_ hau_) (haq_ hav_)) ((DIST (NVS-METRIC-SPACE (CK-NVS (METRIC-GROUP-MS hag_)))) hau_ hav_))))))
        '(FORALL hac_ (IMPLIES (IN hac_ RR)
           (= (haq_ (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hag_)) hac_)) (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hag_)) hac_))))
        '(FORALL hau_ (IMPLIES (IN hau_ (CONT-FNS (METRIC-GROUP-MS hag_)))
           (IN (haq_ hau_)
               (CONV-HULL (CK-NVS (METRIC-GROUP-MS hag_))
                 (IMAGE (VNB-LAMBDA hqa_ (PTS (METRIC-GROUP-MS hag_)) (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hag_)) (hau_ ((OPR hag_) hqa_ hix_)))) (PTS (METRIC-GROUP-MS hag_)))))))
        '(FORALL hab_ (IMPLIES (IN hab_ (PTS (METRIC-GROUP-MS hag_)))
           (FORALL hau_ (IMPLIES (IN hau_ (CONT-FNS (METRIC-GROUP-MS hag_)))
             (= (haq_ (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hag_)) (hau_ ((OPR hag_) hix_ hab_))))
                (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hag_)) ((haq_ hau_) ((OPR hag_) hix_ hab_))))))))))))
(notation! 'HAAR-AVERAGES 'kind 'functoid 'arity 1
           'english "the averaging operators of the compact metric group $1")

(def-functoid 'HAAR-MEAN '(hmg_ hmf_)
  '(IOTA hmc_ (AND (IN hmc_ RR)
     (IN (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hmg_)) hmc_)
         (CLOSURE (NVS-METRIC-SPACE (CK-NVS (METRIC-GROUP-MS hmg_)))
           (CONV-HULL (CK-NVS (METRIC-GROUP-MS hmg_))
             (IMAGE (VNB-LAMBDA hqa_ (PTS (METRIC-GROUP-MS hmg_))
                      (VNB-LAMBDA hix_ (PTS (METRIC-GROUP-MS hmg_)) (hmf_ ((OPR hmg_) hqa_ hix_))))
                    (PTS (METRIC-GROUP-MS hmg_)))))))))
(notation! 'HAAR-MEAN 'kind 'functoid 'arity 2
           'english "the Haar mean of $2 on the compact metric group $1"
           'tex "\\int_{$1} {$2}")

(def-functoid 'HAAR-INTEGRAL '(hng_)
  '(IOTA hnu_ (IS-HAAR-INTEGRAL hng_ hnu_)))
(notation! 'HAAR-INTEGRAL 'kind 'functoid 'arity 1
           'english "the Haar integral of the compact metric group $1")
