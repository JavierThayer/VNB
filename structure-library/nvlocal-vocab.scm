;;; nvlocal-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ccrqp/nvlocal-vocab.scm.
;;; Library: analysis.

;;; nvlocal-vocab.scm -- LOCAL NV FIELDS (CCR.pdf Definition 2.15).  DEFINITIONS ONLY; the laws are in
;;; theorem-library/qp-laws.scm (section 15).  Agent CCR-QP, 2026-10-28.  Destination: structure-library/.
;;; Library: analysis (beside ccr2-vocab / ccr3-vocab).  Load window: after ccr2-vocab, metric-topology,
;;; metric-subspace.
;;;
;;; Definition 2.15: K is a local NV field if it is non-discrete and locally compact.  "Discrete" and "locally
;;; compact" are the textbook notions for the metric space of K:
;;;   IS-DISCRETE-MS(s): every point x has an open ball B(x, r), r > 0, containing no other point;
;;;   IS-LOCALLY-COMPACT(s): every point x has a closed ball of some radius r > 0 that is compact.

(def-predicate 'IS-DISCRETE-MS '(dms_)
  '(FORALL dmx_ (IMPLIES (IN dmx_ (PTS dms_))
     (FORSOME dmr_ (AND (POS-RR dmr_) (FORALL dmy_ (IMPLIES (IN dmy_ (BALL dms_ dmx_ dmr_)) (= dmy_ dmx_))))))))
(notation! 'IS-DISCRETE-MS 'kind 'predicate 'arity 1 'english "$1 is discrete")

;;; CUT 2026-10-30 (integration): IS-LOCALLY-COMPACT is defined, with the same body up to a binder name,
;;; in structure-library/ca51-vocab.scm (loaded earlier); that definition is used.


(def-predicate 'IS-LOCAL-NV-FIELD '(lck_)
  '(AND (IS-NV-FIELD lck_)
        (AND (NOT (IS-DISCRETE-MS (NF-METRIC-SPACE lck_))) (IS-LOCALLY-COMPACT (NF-METRIC-SPACE lck_)))))
(notation! 'IS-LOCAL-NV-FIELD 'kind 'predicate 'arity 1 'english "$1 is a local NV field")

;;; The residue ring A / M(A) of an NV domain A of K (CCR.pdf Proposition 2.7, Definition 2.20): the ringoid
;;; [A, +, *, -, 0, 1 restricted to A; ideal M(A)] and its quotient ring.
(def-functoid 'NV-RES-RINGOID '(rsk_ rsa_)
  '(LIST rsa_
         (VNB-LAMBDA (LIST rsu_ rsv_) (CARTESIAN rsa_ rsa_) ((ADD rsk_) rsu_ rsv_))
         (VNB-LAMBDA (LIST rsu_ rsv_) (CARTESIAN rsa_ rsa_) ((MUL rsk_) rsu_ rsv_))
         (VNB-LAMBDA rsu_ rsa_ ((NEG rsk_) rsu_))
         (ZERO rsk_) (ONE rsk_) (NV-MAXIMAL rsk_ rsa_)))
(notation! 'NV-RES-RINGOID 'kind 'functoid 'arity 2 'english "the ring $2 with its ideal M($2)")
(def-functoid 'NV-RESIDUE '(rsk_ rsa_) '(RINGOID-QUOTIENT-RING (NV-RES-RINGOID rsk_ rsa_)))
(notation! 'NV-RESIDUE 'kind 'functoid 'arity 2 'english "the residue ring $2 / M($2)")

;; a ring isomorphism: a bijective ring homomorphism (used for "the residue field is F_p")
(def-predicate 'IS-RING-ISO '(rib_ ric_ rif_)
  '(AND (IS-HOM-RING rib_ ric_ rif_)
        (AND (FORALL riu_ (IMPLIES (IN riu_ (CARR rib_)) (FORALL riv_ (IMPLIES (IN riv_ (CARR rib_))
               (IMPLIES (= (rif_ riu_) (rif_ riv_)) (= riu_ riv_))))))
             (FORALL riw_ (IMPLIES (IN riw_ (CARR ric_)) (FORSOME riz_ (AND (IN riz_ (CARR rib_)) (= (rif_ riz_) riw_))))))))
(notation! 'IS-RING-ISO 'kind 'predicate 'arity 3 'english "$3 is a ring isomorphism from $1 onto $2")

;; an additive subgroup of the field K (Corollary 4.13)
(def-predicate 'IS-ADD-SUBGROUP '(asgk_ asgu_)
  '(AND (FORALL asx_ (IMPLIES (IN asx_ asgu_) (IN asx_ (CARR asgk_))))
   (AND (IN (ZERO asgk_) asgu_)
   (AND (FORALL asx_ (IMPLIES (IN asx_ asgu_) (FORALL asy_ (IMPLIES (IN asy_ asgu_) (IN ((ADD asgk_) asx_ asy_) asgu_)))))
        (FORALL asx_ (IMPLIES (IN asx_ asgu_) (IN ((NEG asgk_) asx_) asgu_)))))))
(notation! 'IS-ADD-SUBGROUP 'kind 'predicate 'arity 2 'english "$2 is an additive subgroup of $1")
