;;; cg1-vocab.scm -- vocabulary for the compact-groups notes, chapter 5 section 2 (CG-1).
;;; DEFINITIONS ONLY.  Agent ISOM, 2026-10-26 (new definitions, the user's to confirm).
;;;
;;;   IS-CONNECTED-T(s, A)
;;;       A is a connected subset of the topological space s: A lies in PTS s and no two open
;;;       sets u, v cover A with A, u, v having no common point while A meets both.  The
;;;       topological counterpart of the metric IS-CONNECTED (metric-connected.scm).
;;;   CONNECTED-COMPONENT(s, x)
;;;       the union of the connected subsets of s containing x (the notes' "largest connected
;;;       subset containing the identity").
;;;   IS-SUBGROUP(g, H), IS-NORMAL-SUBGROUP(g, H)
;;;       H inside CARR g contains e and is closed under the product and the inverse; normal:
;;;       also under conjugation u h u^-1.
;;; BINDERS: cts_ cta_ ctu_ ctv_ ctx_ ccs_ ccx_ ccc_ sgg_ sgh_ sga_ sgb_ sgu_.
(def-predicate 'IS-CONNECTED-T '(cts_ cta_)
  '(AND (SUBSET cta_ (PTS cts_))
     (FORALL ctu_ (IMPLIES (IN ctu_ (OPENS cts_)) (FORALL ctv_ (IMPLIES (IN ctv_ (OPENS cts_))
       (IMPLIES (SUBSET cta_ (UNION ctu_ ctv_))
         (IMPLIES (FORALL ctx_ (IMPLIES (IN ctx_ cta_) (NOT (AND (IN ctx_ ctu_) (IN ctx_ ctv_)))))
           (IMPLIES (FORSOME ctx_ (AND (IN ctx_ cta_) (IN ctx_ ctu_)))
             (NOT (FORSOME ctx_ (AND (IN ctx_ cta_) (IN ctx_ ctv_)))))))))))))
(notation! 'IS-CONNECTED-T 'kind 'predicate 'arity 2 'english "$2 is a connected subset of $1")

(def-functoid 'CONNECTED-COMPONENT '(ccs_ ccx_)
  '(BIG-UNION ccc_ (SEP ccc_ (POWER (PTS ccs_)) (AND (IS-CONNECTED-T ccs_ ccc_) (IN ccx_ ccc_))) ccc_))
(notation! 'CONNECTED-COMPONENT 'kind 'functoid 'arity 2 'english "the connected component of $2 in $1")

;;; IS-SUBGROUP / IS-NORMAL-SUBGROUP: MOVED 2026-10-27 (integration) to structure-library/cg2-vocab.scm,
;;; library algebra, so that the algebra files (cg2-setprod, group-cosets) may use them.  Same text.

