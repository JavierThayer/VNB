;;; tg-vocab.scm -- topological groups (topological-vector-space.pdf Appendix A.3, TB-11).
;;; DEFINITIONS ONLY.  Agent ISOM, 2026-10-26 (new definitions, the user's to confirm).
;;;
;;;   IS-GROUP-TOPOLOGY(s, g)   (2026-10-26: was IS-TOP-GROUP(s, g); the topological group
;;;       itself is now the STRUCTURE TOP-GROUP, at the end of this file)
;;;       "s is a group topology for g": a TOP-SPACE s and a GROUP g on the same points,
;;;       such that (x, y) |-> x y^-1 is continuous: for every x, y
;;;       and open W containing x y^-1 there are opens U containing x and V containing y with
;;;       U V^-1 inside W (continuity at (x, y), stated with neighbourhoods since the tree
;;;       has no product topology).
;;;   GRP-MONOID(g)
;;;       the monoid underlying the group g: [CARR, OPR, IDEN].
;;;   HAS-COUNTABLE-NBHD-BASE(s, x)
;;;       x has a countable fundamental system of neighbourhoods: a sequence N of open
;;;       sets containing x such that every open set containing x contains some N(k).
;;;   IS-LEFT-INVARIANT(md, g)
;;;       Definition A.3 for the distance of md and the group g: d(a x, a y) = d(x, y).
;;; BINDERS: tgs_ tgg_ tga_ tgb_ tgw_ tgu_ tgv_ tgp_ tgq_ gmg_ cbs_ cbx_ cbn_ cbk_ cbw_
;;;          lim_ lig_ lia_ lix_ liy_.

(def-predicate 'IS-GROUP-TOPOLOGY '(tgs_ tgg_)
  '(AND (IS-TOP-SPACE tgs_) (AND (IS-GROUP tgg_) (AND (= (PTS tgs_) (CARR tgg_))
     (FORALL tga_ (IMPLIES (IN tga_ (CARR tgg_)) (FORALL tgb_ (IMPLIES (IN tgb_ (CARR tgg_))
       (FORALL tgw_ (IMPLIES (IN tgw_ (OPENS tgs_)) (IMPLIES (IN ((OPR tgg_) tga_ ((INV tgg_) tgb_)) tgw_)
         (FORSOME tgu_ (AND (IN tgu_ (OPENS tgs_)) (AND (IN tga_ tgu_)
           (FORSOME tgv_ (AND (IN tgv_ (OPENS tgs_)) (AND (IN tgb_ tgv_)
             (FORALL tgp_ (IMPLIES (IN tgp_ tgu_) (FORALL tgq_ (IMPLIES (IN tgq_ tgv_)
               (IN ((OPR tgg_) tgp_ ((INV tgg_) tgq_)) tgw_))))))))))))))))))))))
(notation! 'IS-GROUP-TOPOLOGY 'kind 'predicate 'arity 2 'english "$1 is a group topology for the group $2")

;;; GRP-MONOID: MOVED 2026-10-27 (integration) to structure-library/cg2-vocab.scm (library algebra, loaded
;;; before this file), so that the algebra file tg-group.scm may use it.  Same text.

(def-predicate 'HAS-COUNTABLE-NBHD-BASE '(cbs_ cbx_)
  '(FORSOME cbn_ (AND (IN cbn_ (FUN NN (OPENS cbs_)))
     (AND (FORALL cbk_ (IMPLIES (IN cbk_ NN) (IN cbx_ (cbn_ cbk_))))
          (FORALL cbw_ (IMPLIES (IN cbw_ (OPENS cbs_)) (IMPLIES (IN cbx_ cbw_)
            (FORSOME cbk_ (AND (IN cbk_ NN) (SUBSET (cbn_ cbk_) cbw_))))))))))
(notation! 'HAS-COUNTABLE-NBHD-BASE 'kind 'predicate 'arity 2
           'english "$2 has a countable fundamental system of neighbourhoods in $1")

(def-predicate 'IS-LEFT-INVARIANT '(lim_ lig_)
  '(FORALL lia_ (IMPLIES (IN lia_ (CARR lig_)) (FORALL lix_ (IMPLIES (IN lix_ (CARR lig_))
     (FORALL liy_ (IMPLIES (IN liy_ (CARR lig_))
       (= ((DIST lim_) ((OPR lig_) lia_ lix_) ((OPR lig_) lia_ liy_)) ((DIST lim_) lix_ liy_)))))))))
(notation! 'IS-LEFT-INVARIANT 'kind 'predicate 'arity 2 'english "the distance of $1 is left invariant under $2")

;;;   IS-BK-SEQUENCE(s, g, vs)
;;;       the neighbourhoods (145)-(146) of the proof of A.6: vs is a sequence of open sets,
;;;       vs(0) the whole space, each vs(k) symmetric and containing e, and
;;;       vs(k+1) vs(k+1) vs(k+1) inside vs(k).
;;;   BK-GAUGE(vs, x)
;;;       (147): the infimum over the k with x in vs(k) of (1/2)^k; it is (1/2)^k on
;;;       vs(k) \ vs(k+1) and 0 on the intersection of all vs(k).
;;; BINDERS: bss_ bsg_ bsv_ bsk_ bsp_ bsq_ bsr_ bgv_ bgx_ bgr_ bgk_.
(def-predicate 'IS-BK-SEQUENCE '(bss_ bsg_ bsv_)
  '(AND (IN bsv_ (FUN NN (OPENS bss_))) (AND (= (bsv_ 0) (PTS bss_))
     (FORALL bsk_ (IMPLIES (IN bsk_ NN)
       (AND (IN (IDEN bsg_) (bsv_ bsk_))
         (AND (FORALL bsp_ (IMPLIES (IN bsp_ (bsv_ bsk_)) (IN ((INV bsg_) bsp_) (bsv_ bsk_))))
           (FORALL bsp_ (IMPLIES (IN bsp_ (bsv_ (succ bsk_))) (FORALL bsq_ (IMPLIES (IN bsq_ (bsv_ (succ bsk_)))
             (FORALL bsr_ (IMPLIES (IN bsr_ (bsv_ (succ bsk_)))
               (IN ((OPR bsg_) ((OPR bsg_) bsp_ bsq_) bsr_) (bsv_ bsk_)))))))))))))))
(notation! 'IS-BK-SEQUENCE 'kind 'predicate 'arity 3
           'english "$3 is a sequence of symmetric open neighbourhoods of the identity of $2 in $1 with cubes nested")
(def-functoid 'BK-GAUGE '(bgv_ bgx_)
  '(EINF (SEP bgr_ RR (FORSOME bgk_ (AND (IN bgk_ NN) (AND (IN bgx_ (bgv_ bgk_)) (= bgr_ (power 1/2 bgk_))))))))
(notation! 'BK-GAUGE 'kind 'functoid 'arity 2 'english "the gauge of $2 relative to the neighbourhoods $1")

;;;   BK-F(g, vs, x)
;;;       (136) for the gauge: the subadditive regularisation (SUBADD-REG, tb11-vocab.scm) of
;;;       BK-GAUGE(vs, .) on the monoid of g.
;;;   BK-METRIC(g, vs)
;;;       the metric of A.6 on the points of g: d(x, y) = f(y^-1 x) + f(x^-1 y), f = BK-F(g, vs, .).
;;;       (The notes take f(y^-1 x) alone and prove f symmetric; the symmetrised sum gives the
;;;       same balls up to a factor 2 and needs no reversal of factorisations.)
;;; BINDERS: bfg_ bfv_ bfx_ bfz_ bmg_ bmv_ bmx_ bmy_.
(def-functoid 'BK-F '(bfg_ bfv_ bfx_)
  '(SUBADD-REG (GRP-MONOID bfg_) (VNB-LAMBDA bfz_ (CARR bfg_) (BK-GAUGE bfv_ bfz_)) bfx_))
(notation! 'BK-F 'kind 'functoid 'arity 3 'english "the regularised gauge of $3 for $1 and $2")
(def-functoid 'BK-METRIC '(bmg_ bmv_)
  '(LIST (CARR bmg_)
         (VNB-LAMBDA (LIST bmx_ bmy_) (CARTESIAN (CARR bmg_) (CARR bmg_))
           (+ (BK-F bmg_ bmv_ ((OPR bmg_) ((INV bmg_) bmy_) bmx_)) (BK-F bmg_ bmv_ ((OPR bmg_) ((INV bmg_) bmx_) bmy_))))))
(notation! 'BK-METRIC 'kind 'functoid 'arity 2 'english "the Birkhoff-Kakutani metric of $1 for $2")

;;; -----------------------------------------------------------------------
;;; TOP-GROUP -- the topological group as ONE structure (the notes' "a group G equipped
;;; with a topology such that (x, y) |-> x y^-1 is continuous"), 2026-10-26.
;;;
;;; Slots: CARR, OPR, IDEN, INV at GROUP's indices 1-4 (one name, one slot), and the
;;; topology as a FAMILY slot TOPOLOGY at index 5.  OPENS cannot be reused: it is slot 2
;;; of TOP-SPACE, where TOP-GROUP has OPR.  Laws: GROUP's three properties, TOP-SPACE's
;;; four laws over (CARR s) and (TOPOLOGY s), and continuity of (x, y) |-> x y^-1 at every
;;; point, with neighbourhoods (the tree has no product topology).  The family slot makes
;;; the generated arrows the CONTINUOUS HOMOMORPHISMS (preservation for the ops, pullback
;;; of TOPOLOGY).
;;;
;;; The underlying space and group are CONSTRUCTED functors (they rename TOPOLOGY to
;;; OPENS, so they are not selections), which owe their typing and functoriality as
;;; theorems and give `slot' its projections:
;;;   TOP-GROUP-SPACE(G) = [CARR G, TOPOLOGY G]                 : TOP-GROUP -> TOP-SPACE
;;;   TOP-GROUP-GROUP(G) = [CARR G, OPR G, IDEN G, INV G]       : TOP-GROUP -> GROUP
;;; and the way back from a group topology:
;;;   MAKE-TOP-GROUP(s, g) = [CARR g, OPR g, IDEN g, INV g, OPENS s].
;;; BINDERS: tgr_ mks_ mkg_ u v fam (the last three as in TOP-SPACE's laws).
(declare-structure TOP-GROUP
  (instance-var s)
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (constant IDEN CARR)
  (op INV CARR CARR)
  (family TOPOLOGY CARR)
  (property is-associative OPR CARR)
  (property is-identity OPR IDEN CARR)
  (property has-inverses OPR IDEN INV CARR)
  (law (IN EMPTY-SET (TOPOLOGY s)))
  (law (IN (CARR s) (TOPOLOGY s)))
  (law (FORALL u (IMPLIES (IN u (TOPOLOGY s))
         (FORALL v (IMPLIES (IN v (TOPOLOGY s))
           (IN (INTERSECTION u v) (TOPOLOGY s)))))))
  (law (FORALL fam (IMPLIES (SUBSET fam (TOPOLOGY s))
         (IN (BIG-UNION u fam u) (TOPOLOGY s)))))
  (law (FORALL tga_ (IMPLIES (IN tga_ (CARR s)) (FORALL tgb_ (IMPLIES (IN tgb_ (CARR s))
         (FORALL tgw_ (IMPLIES (IN tgw_ (TOPOLOGY s)) (IMPLIES (IN ((OPR s) tga_ ((INV s) tgb_)) tgw_)
           (FORSOME tgu_ (AND (IN tgu_ (TOPOLOGY s)) (AND (IN tga_ tgu_)
             (FORSOME tgv_ (AND (IN tgv_ (TOPOLOGY s)) (AND (IN tgb_ tgv_)
               (FORALL tgp_ (IMPLIES (IN tgp_ tgu_) (FORALL tgq_ (IMPLIES (IN tgq_ tgv_)
                 (IN ((OPR s) tgp_ ((INV s) tgq_)) tgw_))))))))))))))))))))
(notation! 'IS-TOP-GROUP 'noun "topological group" 'article "a")
(notation! 'TOPOLOGY 'kind 'accessor 'arity 1 'english "the topology of $1")
(notation! 'IS-HOM-TOP-GROUP 'kind 'predicate 'arity 3
           'english "$3 is a continuous homomorphism from $1 to $2")

(def-constructed-functor 'TOP-GROUP-SPACE 'TOP-GROUP 'TOP-SPACE '(tgr_)
  '(LIST (CARR tgr_) (TOPOLOGY tgr_)))
(def-constructed-functor 'TOP-GROUP-GROUP 'TOP-GROUP 'GROUP '(tgr_)
  '(LIST (CARR tgr_) (OPR tgr_) (IDEN tgr_) (INV tgr_)))
(notation! 'TOP-GROUP-SPACE 'kind 'functoid 'arity 1 'english "the topological space of $1")
(notation! 'TOP-GROUP-GROUP 'kind 'functoid 'arity 1 'english "the group of $1")
(def-functoid 'MAKE-TOP-GROUP '(mks_ mkg_)
  '(LIST (CARR mkg_) (OPR mkg_) (IDEN mkg_) (INV mkg_) (OPENS mks_)))
(notation! 'MAKE-TOP-GROUP 'kind 'functoid 'arity 2 'english "the group $2 with the topology of $1")
