;;; tych-vocab.scm -- THE PRODUCT OF AN ARBITRARY FAMILY OF TOPOLOGICAL SPACES (definitions only).
;;; Agent TYCH (worker-08), 2026-10-26 (NEW DEFINITIONS, the user's to confirm).
;;; DESTINATION: structure-library/top-product.scm.  Library: analysis (top-space, cardinality).
;;;
;;;   IS-TOP-FAMILY(ix, tf)     ix is a set and every tf(i), i in ix, is a TOP-SPACE (the IS-MS-SEQUENCE convention:
;;;                             the family is applied pointwise, tf is not typed as a function).
;;;   TPROD-PTS(ix, tf)         the points: functions x on ix with x(i) in PTS(tf i).
;;;   TPROD-CONSTR(ix, tf)      the subbasic constraints: pairs [i, V] with i in ix and V in OPENS(tf i).
;;;   TPROD-BOX(ix, tf, bb)     the points meeting every constraint of bb: x(i) in V for [i, V] in bb.
;;;   IS-TPROD-OPEN(ix, tf, u)  u contains, around each of its points, the box of a FINITE set of constraints.
;;;   TPRODUCT-TOP(ix, tf)      [TPROD-PTS, {u : IS-TPROD-OPEN}]: the product (Tychonoff) topology.
;;;   TPROJ(ix, tf, i)          the i-th projection x |-> x(i).
;;;   HAS-FINITE-SUBCOVER(s, c) some finite subfamily of c covers PTS(s).
;;; A basic open set is the box of a finite set of constraints, so the empty set of constraints gives the whole
;;; product and the union of two finite sets gives the intersection of two boxes: no function on a finite index set
;;; has to be assembled.  Binders tp*_ are used by nothing else.

(def-predicate 'IS-TOP-FAMILY '(ix tf)
  '(AND (IN ix SET) (FORALL tpi_ (IMPLIES (IN tpi_ ix) (IS-TOP-SPACE (tf tpi_))))))
(def-functoid 'TPROD-PTS '(ix tf)
  '(SEP tpx_ (FUN ix (BIG-UNION tpj_ ix (PTS (tf tpj_))))
     (FORALL tpi_ (IMPLIES (IN tpi_ ix) (IN (tpx_ tpi_) (PTS (tf tpi_)))))))
(def-functoid 'TPROD-CONSTR '(ix tf)
  '(SEP tpb_ (CARTESIAN ix (BIG-UNION tpj_ ix (OPENS (tf tpj_))))
     (IN (NTH 2 tpb_) (OPENS (tf (NTH 1 tpb_))))))
(def-functoid 'TPROD-BOX '(ix tf bb)
  '(SEP tpy_ (TPROD-PTS ix tf)
     (FORALL tpc_ (IMPLIES (IN tpc_ bb) (IN (tpy_ (NTH 1 tpc_)) (NTH 2 tpc_))))))
(def-predicate 'IS-TPROD-OPEN '(ix tf u)
  '(AND (SUBSET u (TPROD-PTS ix tf))
        (FORALL tpw_ (IMPLIES (IN tpw_ u)
          (FORSOME tpf_ (AND (SUBSET tpf_ (TPROD-CONSTR ix tf)) (AND (IN (CARD tpf_) NN)
            (AND (IN tpw_ (TPROD-BOX ix tf tpf_)) (SUBSET (TPROD-BOX ix tf tpf_) u)))))))))
(def-functoid 'TPRODUCT-TOP '(ix tf)
  '(LIST (TPROD-PTS ix tf) (SEP tpu_ (POWER (TPROD-PTS ix tf)) (IS-TPROD-OPEN ix tf tpu_))))
(def-functoid 'TPROJ '(ix tf i)
  '(VNB-LAMBDA tpz_ (TPROD-PTS ix tf) (tpz_ i)))
(def-predicate 'HAS-FINITE-SUBCOVER '(s c)
  '(FORSOME tpg_ (AND (SUBSET tpg_ c) (AND (IN (CARD tpg_) NN) (== (BIG-UNION tpv_ tpg_ tpv_) (PTS s))))))

(notation! 'IS-TOP-FAMILY 'kind 'predicate 'arity 2 'english "$2 is a family of topological spaces indexed by $1")
(notation! 'TPROD-PTS 'kind 'functoid 'arity 2 'english "the product of the points of the family $2")
(notation! 'TPROD-CONSTR 'kind 'functoid 'arity 2 'english "the subbasic constraints of the product of $2")
(notation! 'TPROD-BOX 'kind 'functoid 'arity 3 'english "the box of the constraints $3")
(notation! 'IS-TPROD-OPEN 'kind 'predicate 'arity 3 'english "$3 is open in the product of the family $2")
(notation! 'TPRODUCT-TOP 'kind 'functoid 'arity 2 'english "the product topology of the family $2")
(notation! 'TPROJ 'kind 'functoid 'arity 3 'english "the projection onto the factor $3")
(notation! 'HAS-FINITE-SUBCOVER 'kind 'predicate 'arity 2 'english "a finite subfamily of $2 covers $1")
