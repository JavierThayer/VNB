;;; mb67-vocab.scm -- vocabulary for construction of measures, chapter 5 sections 1.4-1.6: the Baire space N^N
;;; as a metric space, Lusin sets, standard Borel spaces (M-B67, 2026-10-26).  Destination: structure-library/.
;;; Library: measure.
;;;
;;;   BAIRE-MS            the Baire space N^N = FUN(NN, NN) with the prefix ultrametric of (419) for the constant
;;;                       weight 2: d(x, y) = 2^-m(x, y), m(x, y) the length of the common prefix (ULTRA-SEQ-MS of
;;;                       scratchpad/mb12, M-B1B2)
;;;   SND-ITER(m, k)      the k-th iterate of NNSND at m (primitive recursion)
;;;   BAIRE-CODE(m)       the sequence decoded from the natural m: k |-> NNFST(SND-ITER(m, k)); every finite
;;;                       prefix is the prefix of some BAIRE-CODE(m), so the codes are dense in BAIRE-MS
;;;   SEQ-TAIL(z)         the shifted sequence j |-> z(j+1)
;;;   SEQ-CONS(k, v)      the sequence k, v(0), v(1), ...
;;;   SEQ-PROJ(k, z)      the k-th section j |-> z(NNPAIR(k, j)): N^N = (N^N)^N through the pairing of NN
;;;   SUM-PTS(ts), SUM-MS(ts)   the disjoint sum of a sequence ts of metric spaces: the pairs [k, x] with x a point
;;;                       of ts(k), at distance the bounded metric d_k/(1 + d_k) of ts(k) within one summand and
;;;                       1 across summands (the notes' sum, with each d_k first made bounded by 1)
;;;   IS-COUNTABLY-SEPARATED(ys, cb)   (before Proposition 5.36) cb is a sigma-algebra on ys and some sequence of
;;;                       members of cb separates the points of ys: for x /= y one of them contains exactly one
;;;   GRAPH-OF(xs, ys, phi)   the graph {w in xs x ys : phi(w_1) = w_2} of a map phi from xs to ys
;;;   IS-STANDARD-BOREL(xs, ca)   (section 1.8) the measurable space (xs, ca) is isomorphic to the Borel structure of
;;;                       a Polish space: a bijection onto its points, measurable, carrying ca into the Borel sets
;;;                       (so its inverse is measurable too)
;;;   BOREL-SEPARATED(s, a, b)   some Borel set of s contains a and misses b (section 1.6)
;;;   CYL(w, n)           the cylinder of the sequences of naturals agreeing with w below n
;;;   UPD(w, n, m)        the sequence agreeing with w below n and equal to m from n on
;;;   SUM-SET(xss), SUM-SIGMA(xss, cas)   (Proposition 5.35) the disjoint union of a sequence of measurable spaces:
;;;                       the pairs [k, x] with x in xss(k), and the sets whose every section at k lies in cas(k)
;;;   RESTRICT-SIGMA(ca, e)  (Proposition 5.34) the members of ca contained in e: for e in ca, the measurable
;;;                       structure of the space relativized to e (the trace {a /\ e : a in ca})
;;;   IS-LUSIN(s, e)      Definition 5.19: e is the image of a complete separable metric space t under a continuous
;;;                       injective map into the subspace e of s (the form of Proposition 5.14 with injectivity)
;;;
;;; Load window: after scratchpad/mb12/mb12-vocab.scm (ULTRA-SEQ-MS, PREFIX-PROD), nn-pairing (NNFST, NNSND).
(def-constant 'BAIRE-MS
  (list 'baire-ms-def '(== BAIRE-MS (ULTRA-SEQ-MS NN (VNB-LAMBDA bwk_ NN 2)))))
(notation! 'BAIRE-MS 'kind 'constant 'arity 0 'english "the Baire space of sequences of naturals")
(def-by-nn-recursion 'SND-ITER '(sim_)
  'sim_
  '(sin_ siv_)
  '(NNSND siv_))
(notation! 'SND-ITER 'kind 'functoid 'arity 2 'english "the $2-th iterate of the second unpairing at $1")
(def-functoid 'BAIRE-CODE '(bcm_)
  '(VNB-LAMBDA bck_ NN (NNFST (SND-ITER bcm_ bck_))))
(notation! 'BAIRE-CODE 'kind 'functoid 'arity 1 'english "the sequence of naturals coded by $1")
(def-functoid 'SEQ-TAIL '(stz_)
  '(VNB-LAMBDA stj_ NN (stz_ (succ stj_))))
(notation! 'SEQ-TAIL 'kind 'functoid 'arity 1 'english "the tail of the sequence $1")
(def-functoid 'SEQ-CONS '(sck_ scv_)
  '(VNB-LAMBDA scj_ NN (IF (= scj_ 0) sck_ (scv_ (NN-MINUS scj_ 1)))))
(notation! 'SEQ-CONS 'kind 'functoid 'arity 2 'english "the sequence $1 followed by $2")
(def-functoid 'SEQ-PROJ '(spk_ spz_)
  '(VNB-LAMBDA spj_ NN (spz_ (NNPAIR spk_ spj_))))
(notation! 'SEQ-PROJ 'kind 'functoid 'arity 2 'english "the $1-th section of the sequence $2")
(def-predicate 'IS-LUSIN '(s e)
  '(FORSOME lzt_ (AND (IS-COMPLETE lzt_) (AND (IS-SEPARABLE lzt_)
     (FORSOME lzh_ (AND (IS-CONTINUOUS lzt_ (SUBSPACE-MS s e) lzh_) (AND (= (IMAGE lzh_ (PTS lzt_)) e)
       (FORALL lzx_ (IMPLIES (IN lzx_ (PTS lzt_)) (FORALL lzy_ (IMPLIES (IN lzy_ (PTS lzt_))
         (IMPLIES (= (lzh_ lzx_) (lzh_ lzy_)) (= lzx_ lzy_)))))))))))))
(notation! 'IS-LUSIN 'kind 'predicate 'arity 2 'english "$2 is a Lusin subset of $1")
(def-predicate 'IS-COUNTABLY-SEPARATED '(ys cb)
  '(AND (IS-SIGMA-ALGEBRA ys cb)
        (FORSOME csf_ (AND (IN csf_ (FUN NN cb))
          (FORALL csx_ (IMPLIES (IN csx_ ys) (FORALL csy_ (IMPLIES (IN csy_ ys) (IMPLIES (NOT (= csx_ csy_))
            (FORSOME csk_ (AND (IN csk_ NN)
              (OR (AND (IN csx_ (csf_ csk_)) (NOT (IN csy_ (csf_ csk_))))
                  (AND (IN csy_ (csf_ csk_)) (NOT (IN csx_ (csf_ csk_))))))))))))))))
(notation! 'IS-COUNTABLY-SEPARATED 'kind 'predicate 'arity 2 'english "the measurable space ($1, $2) is countably separated")
(def-functoid 'GRAPH-OF '(gfx_ gfy_ gff_)
  '(SEP grp_ (CARTESIAN gfx_ gfy_) (= (gff_ (NTH 1 grp_)) (NTH 2 grp_))))
(notation! 'GRAPH-OF 'kind 'functoid 'arity 3 'english "the graph of $3 from $1 to $2")
(def-predicate 'IS-STANDARD-BOREL '(xs ca)
  '(FORSOME sbs_ (AND (IS-POLISH sbs_)
     (FORSOME sbf_ (AND (IN sbf_ (BIJECTION xs (PTS sbs_)))
       (AND (IS-MEASURABLE-MAP xs ca (PTS sbs_) (BOREL-SETS sbs_) sbf_)
            (FORALL sba_ (IMPLIES (IN sba_ ca) (IN (IMAGE sbf_ sba_) (BOREL-SETS sbs_))))))))))
(notation! 'IS-STANDARD-BOREL 'kind 'predicate 'arity 2 'english "the measurable space ($1, $2) is a standard Borel space")
(def-functoid 'SUM-PTS '(smt_)
  '(SEP smp_ (CARTESIAN NN (BIG-UNION smk_ NN (PTS (smt_ smk_)))) (IN (NTH 2 smp_) (PTS (smt_ (NTH 1 smp_))))))
(notation! 'SUM-PTS 'kind 'functoid 'arity 1 'english "the points of the disjoint sum of $1")
(def-functoid 'SUM-MS '(smt_)
  '(LIST (SUM-PTS smt_)
         (VNB-LAMBDA (LIST smu_ smv_) (CARTESIAN (SUM-PTS smt_) (SUM-PTS smt_))
           (IF (= (NTH 1 smu_) (NTH 1 smv_)) ((DIST (BDD-METRIC (smt_ (NTH 1 smu_)))) (NTH 2 smu_) (NTH 2 smv_)) 1))))
(notation! 'SUM-MS 'kind 'functoid 'arity 1 'english "the disjoint sum of the metric spaces $1")
(def-predicate 'BOREL-SEPARATED '(s a b)
  '(FORSOME bsc_ (AND (IN bsc_ (BOREL-SETS s)) (AND (SUBSET a bsc_) (FORALL bsx_ (IMPLIES (IN bsx_ b) (NOT (IN bsx_ bsc_))))))))
(notation! 'BOREL-SEPARATED 'kind 'predicate 'arity 3 'english "$2 and $3 are separated by a Borel set of $1")
(def-functoid 'CYL '(cyw_ cyn_)
  '(SEP cyz_ (FUN NN NN) (FORALL cyj_ (IMPLIES (IN cyj_ NN) (IMPLIES (< cyj_ cyn_) (= (cyz_ cyj_) (cyw_ cyj_)))))))
(notation! 'CYL 'kind 'functoid 'arity 2 'english "the sequences of naturals agreeing with $1 below $2")
(def-functoid 'UPD '(upw_ upn_ upm_)
  '(VNB-LAMBDA upj_ NN (IF (< upj_ upn_) (upw_ upj_) upm_)))
(notation! 'UPD 'kind 'functoid 'arity 3 'english "$1 below $2, then $3")
(def-functoid 'RESTRICT-SIGMA '(rsc_ rse_)
  '(SEP rsa_ rsc_ (SUBSET rsa_ rse_)))
(notation! 'RESTRICT-SIGMA 'kind 'functoid 'arity 2 'english "the members of $1 contained in $2")
;;; RENAMED 2026-10-27 (integration): this was SUM-SET, which the tree already defines (structure-library/
;;; finsum.scm, SUM-SET(r, S, f) = FINSUM(...)); renamed with rename-sym.py here and in mb67-s35.scm.
(def-functoid 'DISJOINT-SUM-SET '(ssx_)
  '(SEP ssp_ (CARTESIAN NN (BIG-UNION ssk_ NN (ssx_ ssk_))) (IN (NTH 2 ssp_) (ssx_ (NTH 1 ssp_)))))
(notation! 'DISJOINT-SUM-SET 'kind 'functoid 'arity 1 'english "the disjoint union of the sets $1")
(def-functoid 'SUM-SIGMA '(sgx_ sgc_)
  '(SEP sga_ (POWER (DISJOINT-SUM-SET sgx_)) (FORALL sgk_ (IMPLIES (IN sgk_ NN)
     (IN (SEP sgy_ (sgx_ sgk_) (IN (LIST sgk_ sgy_) sga_)) (sgc_ sgk_))))))
(notation! 'SUM-SIGMA 'kind 'functoid 'arity 2 'english "the sum of the sigma-algebras $2 on the sets $1")
