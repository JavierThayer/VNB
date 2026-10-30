;;; tb-vocab.scm -- vocabulary for TB-0 (topological-vector-space.pdf ch. 1 s. 1-2): topological vector
;;; spaces and the topology of an ARBITRARY separating family of seminorms.  DEFINITIONS ONLY.
;;; Agent TB-01, 2026-10-26 (new definitions under the rule "missing vocabulary is not a stopping point").
;;; DESTINATION: structure-library/tvs-vocab.scm, after structure-library/frechet-open-mapping (IS-SEMINORM,
;;; the module vocabulary) and structure-library/top-space (TOP-SPACE, IS-HAUSDORFF).  Library: analysis.
;;;
;;; The notes work over RR "by default" and remark that the complex case reduces to it; here the scalars
;;; are a normed field fld (RR-NORMED-FIELD for the notes' statements), as IS-SEMINORM already is.
;;;
;;;   IS-SEMINORM-FAMILY-ON(fld, m, ix, pf)  a family {p_i}_{i in ix} of seminorms on the module m over fld
;;;                          (pf : ix -> FUN(VEC m, RR)), SEPARATING: x /= 0 has some p_i(x) /= 0.  The
;;;                          index set ix is arbitrary (IS-SEMINORM-FAMILY of frechet-open-mapping.scm is
;;;                          the countable case, ix = NN).
;;;   SN-BALL(m, pf, ff, x, eps)  x + V_{ff, eps} of (3)/(5): the y with p_i(y - x) <= eps for i in ff
;;;                          (max(p_i1, ..., p_in) <= eps is "each p_i <= eps").
;;;   IS-SN-OPEN(m, ix, pf, u)    Def 1.3: every x in u has a basic neighbourhood x + V_{ff, eps} inside u,
;;;                          ff a FINITE subset of ix (a set with CARD in NN), eps > 0.
;;;   SEMINORM-TOP(m, ix, pf)     the topology defined by the family, shaped as a TOP-SPACE [VEC m, opens].
;;;   IS-TVS(fld, m, t)      a topological vector space over fld: t a Hausdorff topology on VEC m in which
;;;                          addition VEC x VEC -> VEC and scalar multiplication K x VEC -> VEC are
;;;                          continuous; continuity of each is stated at every point by neighbourhoods
;;;                          (product topology on the source; the scalar field carries its absolute value).
;;;
;;; BINDERS end in a tag nothing else uses (snby_, sni_, snx_, snf_, sne_, snu_, tvx_ ...).

(def-predicate 'IS-SEMINORM-FAMILY-ON '(fld m ix pf)
  (conjuncts->and
    (list
      '(IS-NORMED-FIELD fld)
      '(IS-MODULE m)
      '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING fld))
      '(IN ix SET)
      '(IN pf (FUN ix (FUN (VEC m) RR)))
      (forall-guarded 'sni_ '(IN sni_ ix) '(IS-SEMINORM fld m (pf sni_)))
      (forall-guarded 'snx_ '(IN snx_ (VEC m))
        '(IMPLIES (FORALL sni_ (IMPLIES (IN sni_ ix) (= ((pf sni_) snx_) 0)))
                  (= snx_ (VZERO m)))))))
(notation! 'IS-SEMINORM-FAMILY-ON 'kind 'predicate 'arity 4
           'english "$4 is a separating family of seminorms on $2 over $1 indexed by $3")

(def-functoid 'SN-BALL '(m pf ff x eps)
  '(SEP snby_ (VEC m)
     (FORALL sni_ (IMPLIES (IN sni_ ff) (<= ((pf sni_) ((VADD m) snby_ ((VNEG m) x))) eps)))))
(notation! 'SN-BALL 'kind 'functoid 'arity 5
           'english "the basic neighbourhood of $4 of radius $5 for the seminorms $3 of the family $2")

(def-predicate 'IS-SN-OPEN '(m ix pf u)
  '(AND (SUBSET u (VEC m))
        (FORALL snx_ (IMPLIES (IN snx_ u)
          (FORSOME snf_ (AND (IN snf_ SET) (AND (IN (CARD snf_) NN) (AND (SUBSET snf_ ix)
            (FORSOME sne_ (AND (POS-RR sne_) (SUBSET (SN-BALL m pf snf_ snx_ sne_) u)))))))))))
(notation! 'IS-SN-OPEN 'kind 'predicate 'arity 4
           'english "$4 is open in the topology defined by the seminorms $3")

(def-functoid 'SEMINORM-TOP '(m ix pf)
  '(LIST (VEC m) (SEP snu_ (POWER (VEC m)) (IS-SN-OPEN m ix pf snu_))))
(notation! 'SEMINORM-TOP 'kind 'functoid 'arity 3
           'english "the vector space $1 with the topology defined by the family of seminorms $3")

(def-predicate 'IS-TVS '(fld m t)
  (conjuncts->and
    (list
      '(IS-NORMED-FIELD fld)
      '(IS-MODULE m)
      '(= (SCAL m) (NORMED-FIELD-AS-COMMUTATIVE-RING fld))
      '(IS-HAUSDORFF t)
      '(== (PTS t) (VEC m))
      ;; addition is continuous at every (x, y)
      (forall-guarded '(tvx_ tvy_ tvu_)
        '((IN tvx_ (VEC m)) (IN tvy_ (VEC m)) (IN tvu_ (OPENS t)) (IN ((VADD m) tvx_ tvy_) tvu_))
        '(FORSOME tvv_ (AND (IN tvv_ (OPENS t)) (AND (IN tvx_ tvv_)
           (FORSOME tvw_ (AND (IN tvw_ (OPENS t)) (AND (IN tvy_ tvw_)
             (FORALL tva_ (IMPLIES (IN tva_ tvv_) (FORALL tvb_ (IMPLIES (IN tvb_ tvw_)
               (IN ((VADD m) tva_ tvb_) tvu_))))))))))))
      ;; scalar multiplication is continuous at every (r, x)
      (forall-guarded '(tvr_ tvx_ tvu_)
        '((IN tvr_ (CARR (SCAL m))) (IN tvx_ (VEC m)) (IN tvu_ (OPENS t)) (IN ((ACT m) tvr_ tvx_) tvu_))
        '(FORSOME tvd_ (AND (POS-RR tvd_)
           (FORSOME tvw_ (AND (IN tvw_ (OPENS t)) (AND (IN tvx_ tvw_)
             (FORALL tvs_ (IMPLIES (IN tvs_ (CARR (SCAL m)))
               (IMPLIES (< ((FNRM fld) ((ADD (SCAL m)) tvs_ ((NEG (SCAL m)) tvr_))) tvd_)
                 (FORALL tva_ (IMPLIES (IN tva_ tvw_) (IN ((ACT m) tvs_ tva_) tvu_)))))))))))))))
(notation! 'IS-TVS 'kind 'predicate 'arity 3
           'english "$3 is a topological vector space structure on $2 over $1")

;;;   SN-OBALL(m, pf, ff, x, r)   an OPEN basic neighbourhood: the y with p_i(y - x) + e <= r for all i in ff,
;;;                          for one e > 0 (i.e. max_{i in ff} p_i(y - x) < r, with no finite maximum
;;;                          formed).  Open in SEMINORM-TOP (sn-oball-open); auxiliary to Prop 1.4.
;;;                          The margin is guarded `e in RR' (implied by POS-RR) so that the SEP is
;;;                          predicative (NBG separation, a320cb6f).
(def-functoid 'SN-OBALL '(m pf ff x r)
  '(SEP snoy_ (VEC m)
     (FORSOME snoe_ (AND (IN snoe_ RR) (AND (POS-RR snoe_)
       (FORALL sni_ (IMPLIES (IN sni_ ff)
         (<= (+ ((pf sni_) ((VADD m) snoy_ ((VNEG m) x))) snoe_) r))))))))
(notation! 'SN-OBALL 'kind 'functoid 'arity 5
           'english "the open basic neighbourhood of $4 of radius $5 for the seminorms $3 of the family $2")

;;;   IS-EXTREMAL-SUBSET(v, b, a)   Def 2.37: b is a nonempty convex subset of a, and every segment of a with
;;;                          an interior point theta x + (1 - theta) y (0 < theta < 1) in b has both ends in b.
;;;                          Convexity is IS-CONVEX-SUBSET (sip-hilbert-vocab.scm); v a real vector space.
(def-predicate 'IS-EXTREMAL-SUBSET '(v b a)
  (conjuncts->and
    (list
      '(IS-CONVEX-SUBSET v b)
      '(FORSOME exz_ (IN exz_ b))
      '(SUBSET b a)
      (forall-guarded '(exx_ exy_ ext_)
        '((IN exx_ a) (IN exy_ a) (IN ext_ RR) (< 0 ext_) (< ext_ 1)
          (IN ((VADD v) ((ACT v) ext_ exx_) ((ACT v) (- 1 ext_) exy_)) b))
        '(AND (IN exx_ b) (IN exy_ b))))))
(notation! 'IS-EXTREMAL-SUBSET 'kind 'predicate 'arity 3
           'english "$2 is an extremal subset of $3 in the real vector space $1")
