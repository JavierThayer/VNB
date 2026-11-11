;;; ba-optop-vocab.scm -- wave of 2026-11-09/10 (agent BA-OT1), wired 2026-11-10 from scratchpad/baot1-1109/ba-optop-vocab.scm.
;;; Library: operator-algebras.

;;; ba-optop-vocab.scm -- THE OPERATOR TOPOLOGIES ON L(H): strong, weak, ultrastrong, ultraweak,
;;; the scalar field as a seminormed space, the continuous duals, vector functionals, the weak
;;; topology of a set of functionals, and the closure in a topological space.
;;; F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf), chapter 5 s.1-5.
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-OT1, 2026-11-10.  Destination: structure-library/ba-optop-vocab.scm.
;;; Library: operator-algebras (BA-MAP-REPORT.md s.3.9).
;;; Load window: after structure-library/ba-ops-vocab (BOUNDED-OPS, BH-VADD, BH-ACT, BOP-ZERO,
;;; BH-VNEG, OPNORM), structure-library/tvs-vocab (SEMINORM-TOP), structure-library/la-z3-vocab
;;; (RING-AS-MODULE), structure-library/extended-sum (ESUM), structure-library/cc-power-series
;;; (CC-SERIES-LIMIT), structure-library/frechet-open-mapping (IS-LINEAR-MAP).
;;;
;;; THE DESIGN (BA-MAP-REPORT.md s.3.8).  Every topology of the chapter is a SEMINORM-TOP of the
;;; tree (tvs-vocab.scm) on the module L(H), so `seminorm-top-is-tvs' makes each a topological
;;; vector space over CC-NORMED-FIELD once its family is shown to be a separating family of
;;; seminorms.  The module is BH-MODULE(v), the first six slots of BH-ALGEBRA(v) (ba-ops-vocab.scm):
;;; the CC ring view, BOUNDED-OPS(v, v), +, 0, -, scalar multiplication.
;;;   SOT(v)  index VEC(v),                  p_xi(T)        = ||T xi||                    (106)
;;;   WOT(v)  index VEC(v) x VEC(v),         p_(xi,eta)(T)  = |<T xi | eta>|              (114)
;;;   NORM-OPTOP(v)  index {0},              p(T)           = ||T||  (the norm topology)
;;;   UST(v)  index SQ-SUMMABLE-SEQS(v),     p_xi~(T)       = (sum_k ||T xi_k||^2)^(1/2)  (119)
;;;   UWT(v)  index pairs of such sequences, p_(xi~,eta~)(T) = |sum_k <T xi_k | eta_k>|   (128)
;;; A pair index p of WOT is read by NTH 1 / NTH 2 inside the seminorm, never by a destructuring
;;; lambda: SEMINORM-TOP applies the family to its index variable, (pf i), and a destructuring
;;; lambda reduces only when applied to two arguments.  The ultrastrong and ultraweak indices are
;;; sequences over NN, as the notes write them (BA-MAP s.4, decided); the ultraweak sum is the
;;; series CC-SERIES-LIMIT (it converges absolutely when both sequences are square-summable).
;;;
;;; THE SCALARS.  A linear functional is continuous INTO CC-SN-TOP, the topology of the
;;; one-seminorm family z |-> |z| on CC-SN-MODULE = RING-AS-MODULE of the CC ring view, so that a
;;; continuity question between two seminorm topologies is the tree's `sn-cont-of-bound'.
;;; STRONG-DUAL(v) is the notes' L.(H) (Def 5.2), WEAK-DUAL(v) the dual for the weak operator
;;; topology, ULTRA-DUAL(v) the notes' L*(H) (Def 5.15).  VEC-FUNCTIONAL(v, xi, eta) is
;;; T |-> <T xi | eta>, the summand of (108).
;;;
;;; WEAK-PAIRING-TOP(m, fs) is w<E, F> of the notes (before Prop 5.6) for a set fs of linear
;;; functionals on the module m: the seminorm topology of the family phi |-> |phi(.)|.
;;; TOP-CLOSURE(t, a): the adherence of a in the topological space t (Remark 5.9); the tree had
;;; IS-TOP-CLOSED (top-closed.scm) but no closure operator of a TOP-SPACE.
;;;
;;; Binders: ot*_ (otv_ otx_ oty_ ott_ otp_ otk_ ots_ otz_ otf_ otu_ ota_ otq_), used by no other
;;; file; no lambda binder repeats a functoid parameter (CNVS2-REPORT F2).

;;; --------------------------------------------------------------------------------------------
;;; THE MODULE L(H)
(def-functoid 'BH-MODULE '(otv_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) (BOUNDED-OPS otv_ otv_)
         (BH-VADD otv_) (BOP-ZERO otv_ otv_) (BH-VNEG otv_) (BH-ACT otv_)))

;;; --------------------------------------------------------------------------------------------
;;; THE SCALAR FIELD AS A SEMINORMED SPACE
(def-constant 'CC-SN-MODULE
  (list 'cc-sn-module-def
        '(== CC-SN-MODULE (RING-AS-MODULE (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD)))))
(def-constant 'CC-SN-PF
  (list 'cc-sn-pf-def
        '(== CC-SN-PF (VNB-LAMBDA otk_ (PAIR 0 0) (VNB-LAMBDA otz_ CC (magnitude otz_))))))
(def-constant 'CC-SN-TOP
  (list 'cc-sn-top-def
        '(== CC-SN-TOP (SEMINORM-TOP CC-SN-MODULE (PAIR 0 0) CC-SN-PF))))

;;; --------------------------------------------------------------------------------------------
;;; THE STRONG, WEAK AND NORM TOPOLOGIES
(def-functoid 'SOT-PF '(otv_)
  '(VNB-LAMBDA otx_ (VEC otv_)
     (VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_) (IP-NORM otv_ (ott_ otx_)))))
(def-functoid 'SOT '(otv_)
  '(SEMINORM-TOP (BH-MODULE otv_) (VEC otv_) (SOT-PF otv_)))

(def-functoid 'WOT-PF '(otv_)
  '(VNB-LAMBDA otp_ (CARTESIAN (VEC otv_) (VEC otv_))
     (VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_)
       (magnitude ((IP otv_) (ott_ (NTH 1 otp_)) (NTH 2 otp_))))))
(def-functoid 'WOT '(otv_)
  '(SEMINORM-TOP (BH-MODULE otv_) (CARTESIAN (VEC otv_) (VEC otv_)) (WOT-PF otv_)))

(def-functoid 'NORM-OPTOP-PF '(otv_)
  '(VNB-LAMBDA otk_ (PAIR 0 0)
     (VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_) (OPNORM otv_ otv_ ott_))))
(def-functoid 'NORM-OPTOP '(otv_)
  '(SEMINORM-TOP (BH-MODULE otv_) (PAIR 0 0) (NORM-OPTOP-PF otv_)))

;;; --------------------------------------------------------------------------------------------
;;; THE ULTRASTRONG AND ULTRAWEAK TOPOLOGIES (sequences indexed by NN, as the notes)
(def-functoid 'SQ-SUMMABLE-SEQS '(otv_)
  '(SEP ots_ (FUN NN (VEC otv_))
     (IN (ESUM (VNB-LAMBDA otk_ NN (* (IP-NORM otv_ (ots_ otk_)) (IP-NORM otv_ (ots_ otk_))))) RR)))
(def-functoid 'UST-PF '(otv_)
  '(VNB-LAMBDA ots_ (SQ-SUMMABLE-SEQS otv_)
     (VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_)
       (SQRT (ESUM (VNB-LAMBDA otk_ NN
                     (* (IP-NORM otv_ (ott_ (ots_ otk_))) (IP-NORM otv_ (ott_ (ots_ otk_))))))))))
(def-functoid 'UST '(otv_)
  '(SEMINORM-TOP (BH-MODULE otv_) (SQ-SUMMABLE-SEQS otv_) (UST-PF otv_)))

(def-functoid 'UWT-PF '(otv_)
  '(VNB-LAMBDA otp_ (CARTESIAN (SQ-SUMMABLE-SEQS otv_) (SQ-SUMMABLE-SEQS otv_))
     (VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_)
       (magnitude (CC-SERIES-LIMIT
                    (VNB-LAMBDA otk_ NN ((IP otv_) (ott_ ((NTH 1 otp_) otk_)) ((NTH 2 otp_) otk_))))))))
(def-functoid 'UWT '(otv_)
  '(SEMINORM-TOP (BH-MODULE otv_) (CARTESIAN (SQ-SUMMABLE-SEQS otv_) (SQ-SUMMABLE-SEQS otv_))
                 (UWT-PF otv_)))

;;; --------------------------------------------------------------------------------------------
;;; FUNCTIONALS AND DUALS
;;; T |-> <T xi | eta>
(def-functoid 'VEC-FUNCTIONAL '(otv_ otx_ oty_)
  '(VNB-LAMBDA ott_ (BOUNDED-OPS otv_ otv_) ((IP otv_) (ott_ otx_) oty_)))

;;; the linear functionals on L(H) continuous for the topology otu_ (a topology on BOUNDED-OPS)
(def-functoid 'OP-DUAL '(otv_ otu_)
  '(SEP otf_ (FUN (BOUNDED-OPS otv_ otv_) CC)
     (AND (IS-LINEAR-MAP (BH-MODULE otv_) CC-SN-MODULE otf_)
          (IS-HOM-TOP-SPACE otu_ CC-SN-TOP otf_))))
(def-functoid 'STRONG-DUAL '(otv_) '(OP-DUAL otv_ (SOT otv_)))
(def-functoid 'WEAK-DUAL '(otv_) '(OP-DUAL otv_ (WOT otv_)))
(def-functoid 'ULTRA-DUAL '(otv_) '(OP-DUAL otv_ (UST otv_)))
(def-functoid 'ULTRAWEAK-DUAL '(otv_) '(OP-DUAL otv_ (UWT otv_)))

;;; w<E, F>: the weak topology on the module m of a set fs of linear functionals on m
(def-functoid 'WEAK-PAIRING-PF '(otq_ ota_)
  '(VNB-LAMBDA otf_ ota_ (VNB-LAMBDA otx_ (VEC otq_) (magnitude (otf_ otx_)))))
(def-functoid 'WEAK-PAIRING-TOP '(otq_ ota_)
  '(SEMINORM-TOP otq_ ota_ (WEAK-PAIRING-PF otq_ ota_)))

;;; --------------------------------------------------------------------------------------------
;;; THE CLOSURE OF A SUBSET OF A TOPOLOGICAL SPACE (adherent points)
(def-functoid 'TOP-CLOSURE '(otq_ ota_)
  '(SEP otx_ (PTS otq_)
     (FORALL otu_ (IMPLIES (IN otu_ (OPENS otq_))
       (IMPLIES (IN otx_ otu_) (FORSOME oty_ (AND (IN oty_ ota_) (IN oty_ otu_))))))))

;;; --------------------------------------------------------------------------------------------
;;; Notation
(notation! 'BH-MODULE 'kind 'functoid 'arity 1 'english "the vector space of bounded operators on $1" 'tex "L({$1})")
(notation! 'CC-SN-MODULE 'kind 'constant 'arity 0 'english "the complex numbers as a vector space over themselves" 'tex "\\mathbb{C}")
(notation! 'CC-SN-PF 'kind 'constant 'arity 0 'english "the absolute value as a family of seminorms on the complex numbers")
(notation! 'CC-SN-TOP 'kind 'constant 'arity 0 'english "the complex numbers with the topology of the absolute value" 'tex "\\mathbb{C}")
(notation! 'SOT-PF 'kind 'functoid 'arity 1 'english "the seminorms T |-> ||T xi|| of the strong operator topology on $1")
(notation! 'SOT 'kind 'functoid 'arity 1 'english "the strong operator topology on the bounded operators on $1" 'tex "L({$1})_{s}")
(notation! 'WOT-PF 'kind 'functoid 'arity 1 'english "the seminorms T |-> |<T xi | eta>| of the weak operator topology on $1")
(notation! 'WOT 'kind 'functoid 'arity 1 'english "the weak operator topology on the bounded operators on $1" 'tex "L({$1})_{w}")
(notation! 'NORM-OPTOP-PF 'kind 'functoid 'arity 1 'english "the operator norm as a family of seminorms on the bounded operators on $1")
(notation! 'NORM-OPTOP 'kind 'functoid 'arity 1 'english "the norm topology on the bounded operators on $1" 'tex "L({$1})")
(notation! 'SQ-SUMMABLE-SEQS 'kind 'functoid 'arity 1 'english "the square-summable sequences in $1")
(notation! 'UST-PF 'kind 'functoid 'arity 1 'english "the seminorms of the ultrastrong operator topology on $1")
(notation! 'UST 'kind 'functoid 'arity 1 'english "the ultrastrong operator topology on the bounded operators on $1" 'tex "L({$1})_{us}")
(notation! 'UWT-PF 'kind 'functoid 'arity 1 'english "the seminorms of the ultraweak operator topology on $1")
(notation! 'UWT 'kind 'functoid 'arity 1 'english "the ultraweak operator topology on the bounded operators on $1" 'tex "L({$1})_{uw}")
(notation! 'VEC-FUNCTIONAL 'kind 'functoid 'arity 3 'english "the functional T |-> <T $2 | $3>" 'tex "\\omega_{{$2},{$3}}")
(notation! 'OP-DUAL 'kind 'functoid 'arity 2 'english "the linear functionals on the bounded operators on $1 continuous for $2")
(notation! 'STRONG-DUAL 'kind 'functoid 'arity 1 'english "the strongly continuous linear functionals on the bounded operators on $1" 'tex "L_{\\bullet}({$1})")
(notation! 'WEAK-DUAL 'kind 'functoid 'arity 1 'english "the weakly continuous linear functionals on the bounded operators on $1")
(notation! 'ULTRA-DUAL 'kind 'functoid 'arity 1 'english "the ultrastrongly continuous linear functionals on the bounded operators on $1" 'tex "L_{*}({$1})")
(notation! 'ULTRAWEAK-DUAL 'kind 'functoid 'arity 1 'english "the ultraweakly continuous linear functionals on the bounded operators on $1")
(notation! 'WEAK-PAIRING-PF 'kind 'functoid 'arity 2 'english "the seminorms x |-> |f(x)| for f in $2")
(notation! 'WEAK-PAIRING-TOP 'kind 'functoid 'arity 2 'english "the weak topology on $1 of the functionals $2" 'tex "w\\langle {$1}, {$2}\\rangle")
(notation! 'TOP-CLOSURE 'kind 'functoid 'arity 2 'english "the closure of $2 in $1" 'tex "\\overline{$2}")
