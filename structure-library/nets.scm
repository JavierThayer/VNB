;;; nets-vocab.scm -- DIRECTED SETS, NETS AND SUBNETS in a topological space; Cauchy nets and completeness in a
;;; topological vector space (topological-vector-space.pdf Def 4.1).  Definitions only.  Agent NETS (worker-08),
;;; 2026-10-26 (NEW DEFINITIONS, the user's to confirm).  DESTINATION: structure-library/nets.scm.
;;; Library: analysis.  Load window: after structure-library/top-space and the TVS vocabulary (IS-TVS).
;;;
;;;   DIRECTED-SET          a structure [PTS, DLEQ]: a nonempty set with a reflexive, transitive relation DLEQ
;;;                         (a set of pairs [i, j], read "i <= j") in which any two points have an upper bound.
;;;                         Antisymmetry is NOT required (a directed PREorder, the standard notion for nets).
;;;   IS-EVENTUALLY-IN(d, x, u)    some i0 in PTS(d) with x(j) in u for every j >= i0.
;;;   NET-CONVERGES-TO(t, d, x, a) x : PTS(d) -> PTS(t) is eventually in every open set of t containing a.
;;;   IS-COFINAL-MONOTONE(e, d, h) h : PTS(e) -> PTS(d) is monotone and its image is cofinal in d.
;;;   IS-SUBNET(d, x, e, y)        y = x o h pointwise for a cofinal monotone h (the standard notion
;;;                                ["Willard"-style subnets with a monotone map]).
;;;   NN-DIRECTED                  [NN, {[m, n] : m <= n}], the naturals as a directed set: a sequence is a net.
;;;   IS-CAUCHY-NET(m, t, d, x)    Def 4.1: for every open neighbourhood V of 0, x(j) - x(k) in V for j, k >= some i0.
;;;   IS-COMPLETE-SUBSET(m, t, a)  Def 4.1: every Cauchy net in a converges to a point of a.
;;;
;;; The order is spelled DLEQ, not REL: REL is SETOID's (read "equivalence relation"), and an accessor name lives at one
;;; slot index library-wide (DLEQ is at slot 2, as REL).  Binders dsa_ ... are used by nothing else.

(declare-structure DIRECTED-SET
  (instance-var s)
  (carriers PTS)
  (relation DLEQ PTS)
  (law (FORSOME dsn_ (IN dsn_ (PTS s))))
  (law (FORALL dsa_ (IMPLIES (IN dsa_ (PTS s)) (IN (LIST dsa_ dsa_) (DLEQ s)))))
  (law (FORALL dsa_ (IMPLIES (IN dsa_ (PTS s)) (FORALL dsb_ (IMPLIES (IN dsb_ (PTS s)) (FORALL dsc_ (IMPLIES (IN dsc_ (PTS s))
         (IMPLIES (IN (LIST dsa_ dsb_) (DLEQ s)) (IMPLIES (IN (LIST dsb_ dsc_) (DLEQ s)) (IN (LIST dsa_ dsc_) (DLEQ s)))))))))))
  (law (FORALL dsa_ (IMPLIES (IN dsa_ (PTS s)) (FORALL dsb_ (IMPLIES (IN dsb_ (PTS s))
         (FORSOME dsc_ (AND (IN dsc_ (PTS s)) (AND (IN (LIST dsa_ dsc_) (DLEQ s)) (IN (LIST dsb_ dsc_) (DLEQ s)))))))))))

(def-predicate 'IS-EVENTUALLY-IN '(d x u)
  '(FORSOME evi_ (AND (IN evi_ (PTS d))
     (FORALL evj_ (IMPLIES (IN evj_ (PTS d)) (IMPLIES (IN (LIST evi_ evj_) (DLEQ d)) (IN (x evj_) u)))))))

(def-predicate 'NET-CONVERGES-TO '(t d x a)
  '(AND (IS-TOP-SPACE t)
   (AND (IS-DIRECTED-SET d)
   (AND (IN x (FUN (PTS d) (PTS t)))
   (AND (IN a (PTS t))
        (FORALL ncu_ (IMPLIES (IN ncu_ (OPENS t)) (IMPLIES (IN a ncu_) (IS-EVENTUALLY-IN d x ncu_)))))))))

(def-predicate 'IS-COFINAL-MONOTONE '(e d h)
  '(AND (IN h (FUN (PTS e) (PTS d)))
   (AND (FORALL cmi_ (IMPLIES (IN cmi_ (PTS e)) (FORALL cmj_ (IMPLIES (IN cmj_ (PTS e))
          (IMPLIES (IN (LIST cmi_ cmj_) (DLEQ e)) (IN (LIST (h cmi_) (h cmj_)) (DLEQ d)))))))
        (FORALL cmk_ (IMPLIES (IN cmk_ (PTS d))
          (FORSOME cml_ (AND (IN cml_ (PTS e)) (IN (LIST cmk_ (h cml_)) (DLEQ d)))))))))

(def-predicate 'IS-SUBNET '(d x e y)
  '(AND (IS-DIRECTED-SET d)
   (AND (IS-DIRECTED-SET e)
        (FORSOME snh_ (AND (IS-COFINAL-MONOTONE e d snh_)
          (FORALL snj_ (IMPLIES (IN snj_ (PTS e)) (= (y snj_) (x (snh_ snj_))))))))))

(def-constant 'NN-DIRECTED
  '(nn-directed-def (= NN-DIRECTED (LIST NN (SEP ndp_ (CARTESIAN NN NN) (<= (NTH 1 ndp_) (NTH 2 ndp_)))))))

(def-predicate 'IS-CAUCHY-NET '(m t d x)
  '(AND (IS-DIRECTED-SET d)
   (AND (IN x (FUN (PTS d) (VEC m)))
        (FORALL cnu_ (IMPLIES (IN cnu_ (OPENS t)) (IMPLIES (IN (VZERO m) cnu_)
          (FORSOME cni_ (AND (IN cni_ (PTS d))
            (FORALL cnj_ (IMPLIES (IN cnj_ (PTS d)) (IMPLIES (IN (LIST cni_ cnj_) (DLEQ d))
              (FORALL cnk_ (IMPLIES (IN cnk_ (PTS d)) (IMPLIES (IN (LIST cni_ cnk_) (DLEQ d))
                (IN ((VADD m) (x cnj_) ((VNEG m) (x cnk_))) cnu_)))))))))))))))

(def-predicate 'IS-COMPLETE-SUBSET '(m t a)
  '(AND (SUBSET a (VEC m))
        (FORALL csd_ (FORALL csx_ (IMPLIES (IS-CAUCHY-NET m t csd_ csx_)
          (IMPLIES (FORALL csi_ (IMPLIES (IN csi_ (PTS csd_)) (IN (csx_ csi_) a)))
            (FORSOME csl_ (AND (IN csl_ a) (NET-CONVERGES-TO t csd_ csx_ csl_)))))))))

(notation! 'IS-EVENTUALLY-IN 'kind 'predicate 'arity 3 'english "the net $2 on $1 is eventually in $3")
(notation! 'NET-CONVERGES-TO 'kind 'predicate 'arity 4 'english "the net $3 on $2 converges to $4 in $1")
(notation! 'IS-COFINAL-MONOTONE 'kind 'predicate 'arity 3 'english "$3 is a cofinal monotone map from $1 to $2")
(notation! 'IS-SUBNET 'kind 'predicate 'arity 4 'english "the net $4 on $3 is a subnet of the net $2 on $1")
(notation! 'NN-DIRECTED 'kind 'constant 'arity 0 'english "the natural numbers as a directed set")
(notation! 'IS-CAUCHY-NET 'kind 'predicate 'arity 4 'english "the net $4 on $3 is Cauchy in the topological vector space $1, $2")
(notation! 'IS-COMPLETE-SUBSET 'kind 'predicate 'arity 3 'english "$3 is complete in the topological vector space $1, $2")

;;; topological-vector-space.pdf Appendix A.5 (Ascoli): equicontinuous sets of real functions on a topological space,
;;; and the pointwise limits of nets of their members.  Binders eqx_ eqe_ eqv_ eqf_ eqy_ pwf_ pwd_ pwp_ pwx_ pwl_.
;;;   IS-EQUICONTINUOUS-SET(t, ee)  ee is a set of functions PTS(t) -> RR, equicontinuous at every point.
;;;   PTWISE-NET-LIMITS(t, ee)      the functions PTS(t) -> RR that are pointwise limits of a net of members of ee
;;;                                 (convergence of the net of values at each point, in METRIC-TOP(RR-MS)).
;;; RENAMED 2026-10-27 (integration): was IS-EQUICONTINUOUS-SET, the name ISOM's isom-vocab.scm gives to the
;;; METRIC notion (three parameters); this one is the topological notion for real-valued maps.
;;; NBGSEP (2026-10-28): the net's index set pwd_ is guarded by `pwd_ in DIRECTED-SET' (the class of the
;;; structure, equivalent to IS-DIRECTED-SET by directed-set-class), so the SEP is predicative.
(def-predicate 'IS-EQUICONTINUOUS-T '(t ee)
  '(AND (SUBSET ee (FUN (PTS t) RR))
        (FORALL eqx_ (IMPLIES (IN eqx_ (PTS t)) (FORALL eqe_ (IMPLIES (POS-RR eqe_)
          (FORSOME eqv_ (AND (IN eqv_ (OPENS t)) (AND (IN eqx_ eqv_)
            (FORALL eqf_ (IMPLIES (IN eqf_ ee) (FORALL eqy_ (IMPLIES (IN eqy_ eqv_)
              (< (abs (- (eqf_ eqx_) (eqf_ eqy_))) eqe_))))))))))))))
(def-functoid 'PTWISE-NET-LIMITS '(t ee)
  '(SEP pwf_ (FUN (PTS t) RR)
     (FORSOME pwd_ (FORSOME pwp_ (AND (IN pwd_ DIRECTED-SET) (AND (IS-DIRECTED-SET pwd_) (AND (IN pwp_ (FUN (PTS pwd_) ee))
       (FORALL pwx_ (IMPLIES (IN pwx_ (PTS t))
         (NET-CONVERGES-TO (METRIC-TOP RR-MS) pwd_ (VNB-LAMBDA pwl_ (PTS pwd_) ((pwp_ pwl_) pwx_)) (pwf_ pwx_)))))))))))
(notation! 'IS-EQUICONTINUOUS-T 'kind 'predicate 'arity 2 'english "$2 is an equicontinuous set of real functions on $1")
(notation! 'PTWISE-NET-LIMITS 'kind 'functoid 'arity 2 'english "the pointwise limits of nets in $2")

;;;   NET-UNIF-CONV-ON(d, p, f, k)  the net p : PTS(d) -> functions converges to f uniformly on the set k.
(def-predicate 'NET-UNIF-CONV-ON '(d p f k)
  '(FORALL uce_ (IMPLIES (POS-RR uce_)
     (FORSOME uci_ (AND (IN uci_ (PTS d))
       (FORALL ucj_ (IMPLIES (IN ucj_ (PTS d)) (IMPLIES (IN (LIST uci_ ucj_) (DLEQ d))
         (FORALL ucy_ (IMPLIES (IN ucy_ k) (< (abs (- ((p ucj_) ucy_) (f ucy_))) uce_)))))))))))
(notation! 'NET-UNIF-CONV-ON 'kind 'predicate 'arity 4 'english "the net $2 on $1 converges to $3 uniformly on $4")
