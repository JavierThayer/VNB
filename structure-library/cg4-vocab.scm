;;; cg4-vocab.scm -- compact-groups notes, sections 1 and 5 (CG-4 session).  DEFINITIONS ONLY.
;;; Agent ISOM, 2026-10-26 (new definitions, the user's to confirm).
;;;
;;;   IS-EXTREME-POINT(m, K, x)   x is an extreme point of K in the real vector space m: x is in K
;;;       and whenever x = (1 - t) u + t v with u, v in K and 0 < t < 1, u = x and v = x.
;;;   PTS-LEFT-COSETS(s, g, H)    the left cosets x H (x in CARR g) as subsets of PTS s; x H is
;;;       written { z : x^-1 z in H }.
;;; BINDERS: epm_ epk_ epx_ epu_ epv_ ept_ lcs_ lcg_ lch_ lcu_ lcx_ lcz_.
(def-predicate 'IS-EXTREME-POINT '(epm_ epk_ epx_)
  '(AND (IN epx_ epk_)
     (FORALL epu_ (IMPLIES (IN epu_ epk_) (FORALL epv_ (IMPLIES (IN epv_ epk_)
       (FORALL ept_ (IMPLIES (IN ept_ RR) (IMPLIES (< 0 ept_) (IMPLIES (< ept_ 1)
         (IMPLIES (= epx_ ((VADD epm_) ((ACT epm_) (- 1 ept_) epu_) ((ACT epm_) ept_ epv_)))
           (AND (= epu_ epx_) (= epv_ epx_)))))))))))))
(notation! 'IS-EXTREME-POINT 'kind 'predicate 'arity 3 'english "$3 is an extreme point of $2 in $1")
(def-functoid 'PTS-LEFT-COSETS '(lcs_ lcg_ lch_)
  '(SEP lcu_ (POWER (PTS lcs_)) (FORSOME lcx_ (AND (IN lcx_ (CARR lcg_))
     (= lcu_ (SEP lcz_ (PTS lcs_) (IN ((OPR lcg_) ((INV lcg_) lcx_) lcz_) lch_)))))))
(notation! 'PTS-LEFT-COSETS 'kind 'functoid 'arity 3 'english "the left cosets of $3 in the group $2 on $1")

;;;   IS-ONE-PARAMETER-GROUP(s, g, psi)   psi : RR -> CARR g, psi(r + u) = psi(r) psi(u), and psi
;;;       continuous (neighbourhood form: for t real and W open containing psi(t), some delta > 0
;;;       has psi(v) in W whenever |v - t| < delta).
;;;   IS-GROUP-SEGMENT(s, g, al, phi)     the notes' one-parameter group segment: al > 0,
;;;       phi : [0, al] -> CARR g continuous, phi(r + u) = phi(r) phi(u) for r, u, r + u in
;;;       [0, al].  (The notes write "r, s, r + s < alpha"; the domain is the closed [0, alpha].)
;;; Both read the topology through (s, g), the group-topology pair (tb11/tg-vocab.scm).
;;; BINDERS: ops_ opg_ opp_ oqr_ oqu_ oqt_ oqw_ oqd_ oqv_ gss_ gsg_ gsa_ gsp_ gsr_ gsu_ gst_ gsw_ gsd_ gsv_.
(def-predicate 'IS-ONE-PARAMETER-GROUP '(ops_ opg_ opp_)
  '(AND (IN opp_ (FUN RR (CARR opg_)))
   (AND (FORALL oqr_ (IMPLIES (IN oqr_ RR) (FORALL oqu_ (IMPLIES (IN oqu_ RR)
          (= (opp_ (+ oqr_ oqu_)) ((OPR opg_) (opp_ oqr_) (opp_ oqu_)))))))
        (FORALL oqt_ (IMPLIES (IN oqt_ RR) (FORALL oqw_ (IMPLIES (IN oqw_ (OPENS ops_)) (IMPLIES (IN (opp_ oqt_) oqw_)
          (FORSOME oqd_ (AND (POS-RR oqd_) (FORALL oqv_ (IMPLIES (IN oqv_ RR)
            (IMPLIES (< (abs (- oqv_ oqt_)) oqd_) (IN (opp_ oqv_) oqw_))))))))))))))
(notation! 'IS-ONE-PARAMETER-GROUP 'kind 'predicate 'arity 3 'english "$3 is a one-parameter group of $2 on $1")
(def-predicate 'IS-GROUP-SEGMENT '(gss_ gsg_ gsa_ gsp_)
  '(AND (POS-RR gsa_) (AND (IN gsp_ (FUN (CCINT 0 gsa_) (CARR gsg_)))
   (AND (FORALL gsr_ (IMPLIES (IN gsr_ (CCINT 0 gsa_)) (FORALL gsu_ (IMPLIES (IN gsu_ (CCINT 0 gsa_))
          (IMPLIES (<= (+ gsr_ gsu_) gsa_) (= (gsp_ (+ gsr_ gsu_)) ((OPR gsg_) (gsp_ gsr_) (gsp_ gsu_))))))))
        (FORALL gst_ (IMPLIES (IN gst_ (CCINT 0 gsa_)) (FORALL gsw_ (IMPLIES (IN gsw_ (OPENS gss_)) (IMPLIES (IN (gsp_ gst_) gsw_)
          (FORSOME gsd_ (AND (POS-RR gsd_) (FORALL gsv_ (IMPLIES (IN gsv_ (CCINT 0 gsa_))
            (IMPLIES (< (abs (- gsv_ gst_)) gsd_) (IN (gsp_ gsv_) gsw_)))))))))))))))
(notation! 'IS-GROUP-SEGMENT 'kind 'predicate 'arity 4 'english "$4 is a one-parameter group segment of length $3 in $2 on $1")

;;;   GPOW(g, x, n)           x^n in the group g, n in NN: x^0 = e, x^(n+1) = x x^n (def-by-nn-recursion;
;;;                           gpow-zero / gpow-succ).  (MPOW over GRP-MONOID is the same object read
;;;                           through the monoid view; this one reads the group's accessors directly.)
;;;   OPG-REP(g, al, phi, t, y)   y is the value at t of the extension of the segment phi: for t >= 0,
;;;                           t = n al + r with n in NN, 0 <= r < al, y = phi(al)^n phi(r); for t < 0
;;;                           the inverse of the value at -t.
;;;   OPG-VAL(g, al, phi, t)  the y in CARR g with OPG-REP (a definite description; the typing
;;;                           conjunct makes the description certify itself once it denotes);  OPG-EXT(g, al, phi) the
;;;                           function t |-> OPG-VAL(g, al, phi, t) on RR -- the notes' psi.
;;; BINDERS: gpg_ gpx_ gpn_ gpv_ rpg_ rpa_ rpp_ rpt_ rpy_ rpn_ rpr_ rvt_ rvy_.
;;; GPOW: MOVED 2026-10-27 (integration) to structure-library/cg2-vocab.scm, library algebra (an
;;; algebra vocabulary file: cg4-gpow and group-zpow are algebra).  Same text.

(def-predicate 'OPG-REP '(rpg_ rpa_ rpp_ rpt_ rpy_)
  '(OR (AND (<= 0 rpt_) (FORSOME rpn_ (AND (IN rpn_ NN) (FORSOME rpr_ (AND (IN rpr_ RR) (AND (<= 0 rpr_) (AND (< rpr_ rpa_)
          (AND (= rpt_ (+ (* rpn_ rpa_) rpr_))
               (= rpy_ ((OPR rpg_) (GPOW rpg_ (rpp_ rpa_) rpn_) (rpp_ rpr_)))))))))))
       (AND (< rpt_ 0) (FORSOME rpn_ (AND (IN rpn_ NN) (FORSOME rpr_ (AND (IN rpr_ RR) (AND (<= 0 rpr_) (AND (< rpr_ rpa_)
          (AND (= (- 0 rpt_) (+ (* rpn_ rpa_) rpr_))
               (= rpy_ ((INV rpg_) ((OPR rpg_) (GPOW rpg_ (rpp_ rpa_) rpn_) (rpp_ rpr_))))))))))))))
(notation! 'OPG-REP 'kind 'predicate 'arity 5 'english "$5 is the value at $4 of the extension of the segment $3 of length $2 in $1")
(def-functoid 'OPG-VAL '(rpg_ rpa_ rpp_ rvt_)
  '(IOTA rvy_ (AND (IN rvy_ (CARR rpg_)) (OPG-REP rpg_ rpa_ rpp_ rvt_ rvy_))))
(notation! 'OPG-VAL 'kind 'functoid 'arity 4 'english "the value at $4 of the extension of the segment $3 of length $2 in $1")
(def-functoid 'OPG-EXT '(rpg_ rpa_ rpp_)
  '(VNB-LAMBDA rvt_ RR (OPG-VAL rpg_ rpa_ rpp_ rvt_)))
(notation! 'OPG-EXT 'kind 'functoid 'arity 3 'english "the extension of the segment $3 of length $2 in $1 to a one-parameter group")

;;;   IS-LOCAL-HOM(s1, g1, s2, g2, V, f)   Definition 5.37: f is a local homomorphism from the topological
;;;       group (s1, g1) to (s2, g2) on the open neighbourhood V of e: f : V -> CARR g2 continuous
;;;       (neighbourhood form), and some open W containing e with W = W^-1 has x y in V and
;;;       f(x y) = f(x) f(y) for x, y in W (the notes' "W^2 inside V").
;;; BINDERS: lhs1_ lhg1_ lhs2_ lhg2_ lhv_ lhf_ lhx_ lho_ lhu_ lhy_ lhw_.
(def-predicate 'IS-LOCAL-HOM '(lhs1_ lhg1_ lhs2_ lhg2_ lhv_ lhf_)
  '(AND (IN lhv_ (OPENS lhs1_)) (AND (IN (IDEN lhg1_) lhv_) (AND (IN lhf_ (FUN lhv_ (CARR lhg2_))) (AND (FORALL lhx_ (IMPLIES (IN lhx_ lhv_) (FORALL lho_ (IMPLIES (IN lho_ (OPENS lhs2_)) (IMPLIES (IN (lhf_ lhx_) lho_) (FORSOME lhu_ (AND (IN lhu_ (OPENS lhs1_)) (AND (IN lhx_ lhu_) (FORALL lhy_ (IMPLIES (IN lhy_ lhu_) (IMPLIES (IN lhy_ lhv_) (IN (lhf_ lhy_) lho_)))))))))))) (FORSOME lhw_ (AND (IN lhw_ (OPENS lhs1_)) (AND (IN (IDEN lhg1_) lhw_) (AND (FORALL lhx_ (IMPLIES (IN lhx_ lhw_) (IN ((INV lhg1_) lhx_) lhw_))) (FORALL lhx_ (IMPLIES (IN lhx_ lhw_) (FORALL lhy_ (IMPLIES (IN lhy_ lhw_) (AND (IN ((OPR lhg1_) lhx_ lhy_) lhv_) (= (lhf_ ((OPR lhg1_) lhx_ lhy_)) ((OPR lhg2_) (lhf_ lhx_) (lhf_ lhy_)))))))))))))))))
(notation! 'IS-LOCAL-HOM 'kind 'predicate 'arity 6 'english "$6 is a local homomorphism on $5 from the group $2 on $1 to the group $4 on $3")
