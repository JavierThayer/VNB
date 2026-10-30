;;; isom2-vocab.scm -- the group structure of the isometry group (calculus.pdf ch. 3
;;; sec. 8: "In fact, Gamma is a compact metric group") and the metric group.
;;; DEFINITIONS ONLY; laws in theorem-library/isom2-group.scm.  Agent ISOM, 2026-10-26
;;; (NEW DEFINITIONS, the user's to confirm).
;;;
;;;   ISOMETRY-GROUP-GRP(s)
;;;       the GROUP (group.scm: CARR, OPR, IDEN, INV) on ISOMETRY-GROUP(s): the product
;;;       of u and v is u o v, x |-> u(v(x)); the identity is x |-> x on pts(s); the
;;;       inverse of u is INVERSE-BIJ(u, pts(s), pts(s)).
;;;
;;;   IS-GROUP-METRIC(ms, grp)   (2026-10-26: was IS-METRIC-GROUP(ms, grp); the metric group
;;;       itself is now the STRUCTURE METRIC-GROUP, at the end of this file)
;;;       "ms is a group metric for grp": a metric space ms and a group grp on the same points, the product continuous as
;;;       a map of two variables (for u, v and eps > 0 some delta > 0 has
;;;       d(u v, u' v') <= eps whenever d(u, u') <= delta and d(v, v') <= delta) and the
;;;       inverse continuous from ms to ms.  The textbook "metric group" (a topological
;;;       group whose topology is given by a metric); the tree has no topological group.
;;;
;;; BINDERS: igs_ igu_ igv_ igx_ igi_, mgm_ mgg_ mgu_ mgv_ mge_ mgd_ mgp_ mgq_ -- not bound
;;; anywhere else in the tree.  Dependencies: isom-vocab.scm (ISOMETRY-GROUP), group.scm,
;;; bijection.scm (INVERSE-BIJ), metric-continuity.scm (IS-CONTINUOUS).

(def-functoid 'ISOMETRY-GROUP-GRP '(igs_)
  '(LIST (ISOMETRY-GROUP igs_)
         (VNB-LAMBDA (LIST igu_ igv_) (CARTESIAN (ISOMETRY-GROUP igs_) (ISOMETRY-GROUP igs_))
           (VNB-LAMBDA igx_ (PTS igs_) (igu_ (igv_ igx_))))
         (VNB-LAMBDA igx_ (PTS igs_) igx_)
         (VNB-LAMBDA igi_ (ISOMETRY-GROUP igs_) (INVERSE-BIJ igi_ (PTS igs_) (PTS igs_)))))

(notation! 'ISOMETRY-GROUP-GRP 'kind 'functoid 'arity 1
           'english "the group of isometries of $1 onto itself under composition")

(def-predicate 'IS-GROUP-METRIC '(mgm_ mgg_)
  '(AND (IS-METRIC-SPACE mgm_)
   (AND (IS-GROUP mgg_)
   (AND (= (PTS mgm_) (CARR mgg_))
   (AND (FORALL mgu_ (IMPLIES (IN mgu_ (CARR mgg_))
          (FORALL mgv_ (IMPLIES (IN mgv_ (CARR mgg_))
            (FORALL mge_ (IMPLIES (POS-RR mge_)
              (FORSOME mgd_ (AND (POS-RR mgd_)
                (FORALL mgp_ (IMPLIES (IN mgp_ (CARR mgg_))
                  (FORALL mgq_ (IMPLIES (IN mgq_ (CARR mgg_))
                    (IMPLIES (<= ((DIST mgm_) mgu_ mgp_) mgd_)
                      (IMPLIES (<= ((DIST mgm_) mgv_ mgq_) mgd_)
                        (<= ((DIST mgm_) ((OPR mgg_) mgu_ mgv_) ((OPR mgg_) mgp_ mgq_)) mge_)))))))))))))))
        (IS-CONTINUOUS mgm_ mgm_ (INV mgg_)))))))

(notation! 'IS-GROUP-METRIC 'kind 'predicate 'arity 2
           'english "$1 is a metric for the group $2 making its operations continuous")

;;; -----------------------------------------------------------------------
;;; METRIC-GROUP -- the metric group as ONE structure (2026-10-26), in the pattern of TOP-GROUP
;;; (tb11/tg-vocab.scm): CARR, OPR, IDEN, INV at GROUP's indices 1-4 and the distance as an op
;;; GDIST at index 5 (DIST cannot be reused: it is slot 2 of METRIC-SPACE, where this structure has
;;; OPR).  Laws: GROUP's properties, the metric property of GDIST on CARR, continuity of the product
;;; as a map of two variables, and continuity of the inverse written as IS-CONTINUOUS-AT reads
;;; (metric-continuity.scm).  The generated arrows preserve the operations and the distance: the
;;; isometric homomorphisms.
;;;   METRIC-GROUP-MS(G)    = [CARR G, GDIST G]                  : METRIC-GROUP -> METRIC-SPACE
;;;   METRIC-GROUP-GROUP(G) = [CARR G, OPR G, IDEN G, INV G]     : METRIC-GROUP -> GROUP
;;;   MAKE-METRIC-GROUP(ms, g) = [CARR g, OPR g, IDEN g, INV g, DIST ms]
;;; BINDERS: mgu_ mgv_ mge_ mgd_ mgp_ mgq_ (as in IS-GROUP-METRIC), mga_ mgb_ mgr_ mmm_ mmg_.
(declare-structure METRIC-GROUP
  (instance-var s)
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (op INV CARR CARR)
  (op GDIST (CARTESIAN CARR CARR) RR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR)
  (property has-inverses OPR IDEN INV CARR)
  (property is-metric GDIST CARR)
  (law (FORALL mgu_ (IMPLIES (IN mgu_ (CARR s))
         (FORALL mgv_ (IMPLIES (IN mgv_ (CARR s))
           (FORALL mge_ (IMPLIES (POS-RR mge_)
             (FORSOME mgd_ (AND (POS-RR mgd_)
               (FORALL mgp_ (IMPLIES (IN mgp_ (CARR s))
                 (FORALL mgq_ (IMPLIES (IN mgq_ (CARR s))
                   (IMPLIES (<= ((GDIST s) mgu_ mgp_) mgd_)
                     (IMPLIES (<= ((GDIST s) mgv_ mgq_) mgd_)
                       (<= ((GDIST s) ((OPR s) mgu_ mgv_) ((OPR s) mgp_ mgq_)) mge_))))))))))))))))
  (law (FORALL mga_ (IMPLIES (IN mga_ (CARR s))
         (FORALL mge_ (IMPLIES (POS-RR mge_)
           (FORSOME mgd_ (AND (POS-RR mgd_)
             (FORALL mgb_ (IMPLIES (IN mgb_ (CARR s))
               (IMPLIES (<= ((GDIST s) mga_ mgb_) mgd_)
                 (<= ((GDIST s) ((INV s) mga_) ((INV s) mgb_)) mge_))))))))))))
(notation! 'IS-METRIC-GROUP 'noun "metric group" 'article "a")
(notation! 'GDIST 'kind 'accessor 'arity 1 'english "the distance of $1")
(notation! 'IS-HOM-METRIC-GROUP 'kind 'predicate 'arity 3
           'english "$3 is an isometric homomorphism from $1 to $2")
(def-constructed-functor 'METRIC-GROUP-MS 'METRIC-GROUP 'METRIC-SPACE '(mgr_)
  '(LIST (CARR mgr_) (GDIST mgr_)))
(def-constructed-functor 'METRIC-GROUP-GROUP 'METRIC-GROUP 'GROUP '(mgr_)
  '(LIST (CARR mgr_) (OPR mgr_) (IDEN mgr_) (INV mgr_)))
(notation! 'METRIC-GROUP-MS 'kind 'functoid 'arity 1 'english "the metric space of $1")
(notation! 'METRIC-GROUP-GROUP 'kind 'functoid 'arity 1 'english "the group of $1")
(def-functoid 'MAKE-METRIC-GROUP '(mmm_ mmg_)
  '(LIST (CARR mmg_) (OPR mmg_) (IDEN mmg_) (INV mmg_) (DIST mmm_)))
(notation! 'MAKE-METRIC-GROUP 'kind 'functoid 'arity 2 'english "the group $2 with the distance of $1")
