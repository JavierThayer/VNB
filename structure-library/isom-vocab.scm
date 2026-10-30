;;; isom-vocab.scm -- vocabulary for calculus.pdf ch. 3, sections 6 and 8: uniform and
;;; pointwise convergence of a sequence of functions between METRIC spaces (Prop 3.33),
;;; and the group of isometric isomorphisms of a metric space with its sup metric
;;; (Props 3.37, 3.38).  DEFINITIONS ONLY; the laws are proven in the isom-*.scm files.
;;; Agent ISOM, 2026-10-26 (NEW DEFINITIONS, the user's to confirm).
;;;
;;;   CONVERGES-UNIFORMLY-TO(s, t, fam, g)
;;;       s, t metric spaces, fam a sequence of functions pts(s) -> pts(t), g a function
;;;       pts(s) -> pts(t), and for every eps > 0 some n in NN has
;;;       d_t(fam(k)(x), g(x)) <= eps for every k >= n and every x in pts(s).
;;;       The tree's CONVERGES-UNIFORMLY is for real-valued functions only (target RR).
;;;
;;;   CONVERGES-PTWISE-TO(s, t, fam, g)
;;;       the same typing, and for every x in pts(s) the sequence fam(k)(x) converges to
;;;       g(x) in t, spelled as CONVERGES-TO spells it (eps > 0, a threshold n in NN,
;;;       d_t(fam(k)(x), g(x)) <= eps for k >= n), so that no lambda has to be formed.
;;;
;;; STATEMENT CHECKS.  (1) IS-METRIC-SPACE of both spaces is a conjunct of each.  (2) No
;;; FORSOME witness is formed outside the body; no IOTA or CHOICE in any body.  (3)
;;; BINDERS: cvus_ cvut_ cvuf_ cvug_ cvue_ cvun_ cvuk_ cvux_ and the cvp?_ twins; no other
;;; body or driver in the tree binds a cvu?_ or cvp?_ name, and none folds onto a class
;;; name, an accessor or a registered constant.
;;;
;;; Dependencies: metric-space.scm (IS-METRIC-SPACE, PTS, DIST).  Load slot: after
;;; structure-library/metric-space (any slot in the analysis library).

(def-predicate 'CONVERGES-UNIFORMLY-TO '(cvus_ cvut_ cvuf_ cvug_)
  '(AND (IS-METRIC-SPACE cvus_)
   (AND (IS-METRIC-SPACE cvut_)
   (AND (IN cvuf_ (FUN NN (FUN (PTS cvus_) (PTS cvut_))))
   (AND (IN cvug_ (FUN (PTS cvus_) (PTS cvut_)))
        (FORALL cvue_ (IMPLIES (POS-RR cvue_)
          (FORSOME cvun_ (AND (IN cvun_ NN)
            (FORALL cvuk_ (IMPLIES (IN cvuk_ NN)
              (IMPLIES (<= cvun_ cvuk_)
                (FORALL cvux_ (IMPLIES (IN cvux_ (PTS cvus_))
                  (<= ((DIST cvut_) ((cvuf_ cvuk_) cvux_) (cvug_ cvux_)) cvue_)))))))))))))))

(notation! 'CONVERGES-UNIFORMLY-TO 'kind 'predicate 'arity 4
           'english "the sequence $3 converges uniformly to $4 as functions from $1 to $2")

(def-predicate 'CONVERGES-PTWISE-TO '(cvps_ cvpt_ cvpf_ cvpg_)
  '(AND (IS-METRIC-SPACE cvps_)
   (AND (IS-METRIC-SPACE cvpt_)
   (AND (IN cvpf_ (FUN NN (FUN (PTS cvps_) (PTS cvpt_))))
   (AND (IN cvpg_ (FUN (PTS cvps_) (PTS cvpt_)))
        (FORALL cvpx_ (IMPLIES (IN cvpx_ (PTS cvps_))
          (FORALL cvpe_ (IMPLIES (POS-RR cvpe_)
            (FORSOME cvpn_ (AND (IN cvpn_ NN)
              (FORALL cvpk_ (IMPLIES (IN cvpk_ NN)
                (IMPLIES (<= cvpn_ cvpk_)
                  (<= ((DIST cvpt_) ((cvpf_ cvpk_) cvpx_) (cvpg_ cvpx_)) cvpe_)))))))))))))))

(notation! 'CONVERGES-PTWISE-TO 'kind 'predicate 'arity 4
           'english "the sequence $3 converges pointwise to $4 as functions from $1 to $2")

;;;   IS-EQUICONTINUOUS-SET(s, t, E)
;;;       s, t metric spaces, E a set of functions pts(s) -> pts(t), equicontinuous at
;;;       every point: for x in pts(s) and eps > 0 some delta > 0 has
;;;       d_t(f(x), f(y)) < eps for every f in E and every y with d_s(x, y) < delta.
;;;       The notes' "E is an equicontinuous set of functions X --> Y" (sec. 6), with
;;;       the neighbourhood V of x taken to be a ball.  The tree's IS-EQUICONTINUOUS is
;;;       the same condition for a SEQUENCE fam(k).  BINDERS: eqss_ eqst_ eqse_ eqsx_
;;;       eqsp_ eqsd_ eqsf_ eqsy_.

(def-predicate 'IS-EQUICONTINUOUS-SET '(eqss_ eqst_ eqse_)
  '(AND (IS-METRIC-SPACE eqss_)
   (AND (IS-METRIC-SPACE eqst_)
   (AND (SUBSET eqse_ (FUN (PTS eqss_) (PTS eqst_)))
        (FORALL eqsx_ (IMPLIES (IN eqsx_ (PTS eqss_))
          (FORALL eqsp_ (IMPLIES (POS-RR eqsp_)
            (FORSOME eqsd_ (AND (POS-RR eqsd_)
              (FORALL eqsf_ (IMPLIES (IN eqsf_ eqse_)
                (FORALL eqsy_ (IMPLIES (IN eqsy_ (PTS eqss_))
                  (IMPLIES (< ((DIST eqss_) eqsx_ eqsy_) eqsd_)
                    (< ((DIST eqst_) (eqsf_ eqsx_) (eqsf_ eqsy_)) eqsp_))))))))))))))))

(notation! 'IS-EQUICONTINUOUS-SET 'kind 'predicate 'arity 3
           'english "$3 is an equicontinuous set of functions from $1 to $2")

;;; ---------------------------------------------------------------------------
;;; Section 8 of the notes: the group of isometries with the sup metric.
;;;
;;;   SUP-DIST(s, t, f, g)
;;;       the supremum over x in pts(s) of d_t(f(x), g(x)), taken in [0, +inf]
;;;       (ESUP of the image), so that it is defined for any two functions; it is a
;;;       real number when the distances are bounded (sup-dist-bound,
;;;       theorem-library/isom-supdist.scm).  The notes' (54), d_Gamma(phi, psi).
;;;
;;;   ISOMETRY-GROUP(s)
;;;       the bijections phi of pts(s) onto itself that are isometries from s to s:
;;;       the notes' Gamma, "the group of isometric isomorphisms phi : X --> X".
;;;
;;;   ISOMETRY-GROUP-MS(s)
;;;       ISOMETRY-GROUP(s) with the distance SUP-DIST(s, s, -, -), as a two-slot list
;;;       (the shape of BDD-METRIC).  A metric space when s is compact
;;;       (isometry-group-ms-is-metric-space); the group structure is not built.
;;;
;;; BINDERS: sds_ sdt_ sdf_ sdg_ sdx_, igs_ igf_, ims_ imu_ imv_ -- no other body or
;;; driver in the tree binds these names.

(def-functoid 'SUP-DIST '(sds_ sdt_ sdf_ sdg_)
  '(ESUP (IMAGE (VNB-LAMBDA sdx_ (PTS sds_) ((DIST sdt_) (sdf_ sdx_) (sdg_ sdx_)))
                (PTS sds_))))

(notation! 'SUP-DIST 'kind 'functoid 'arity 4
           'english "the supremum over the points x of $1 of the distance in $2 from $3(x) to $4(x)")

(def-functoid 'ISOMETRY-GROUP '(igs_)
  '(SEP igf_ (BIJECTION (PTS igs_) (PTS igs_)) (IS-ISOMETRY igs_ igs_ igf_)))

(notation! 'ISOMETRY-GROUP 'kind 'functoid 'arity 1
           'english "the group of isometries of $1 onto itself")

(def-functoid 'ISOMETRY-GROUP-MS '(ims_)
  '(LIST (ISOMETRY-GROUP ims_)
         (VNB-LAMBDA (LIST imu_ imv_) (CARTESIAN (ISOMETRY-GROUP ims_) (ISOMETRY-GROUP ims_))
           (SUP-DIST ims_ ims_ imu_ imv_))))

(notation! 'ISOMETRY-GROUP-MS 'kind 'functoid 'arity 1
           'english "the group of isometries of $1 with the sup metric")
