;;; sip-hilbert-vocab.scm -- REAL HILBERT SPACES: the norm and the metric of a
;;; semi-inner-product space, completeness, the orthogonal complement and the
;;; orthogonal projection.  Vocabulary only: no proof, no support.  (SIP-D,
;;; 2026-10-19; scratchpad/triage/SIP-D.md.)  The proofs are theorem-library/sip-d1.scm
;;; (prefix `sipd-').
;;;
;;; Source: the user's notes topological-vector-space.pdf, Ch. 1 s.3: Proposition 1.19
;;; (xi |-> <xi|xi>^{1/2} is a norm on a pre-Hilbert space), (23) ("If H is complete
;;; under the norm ... H is a Hilbert space") and Proposition 1.20 (the closest point).
;;; REAL IS THE DEFAULT (the notes: "all Hilbert spaces are real"); the complex
;;; IS-HILBERT-SPACE of structure-library/hilbert-space.scm is NOT changed and is reached
;;; through the complexification COMPLEXIFY (sip-complex-vocab.scm) by bridge theorems.
;;;
;;;   SIP-NORMED-AG(v)    the additive group of v with x |-> SQRT(<x,x>): the analogue of
;;;                       IP-NORMED-AG (complex-inner-product.scm).  A normed abelian
;;;                       group when v is a pre-Hilbert space (sip-normed-ag-is-normed-ag).
;;;   SIP-METRIC-SPACE(v) NAG-METRIC-SPACE(SIP-NORMED-AG(v)): points VEC(v), distance
;;;                       d(x, y) = SQRT(<x - y, x - y>) (sip-metric-space-dist).
;;;   IS-REAL-HILBERT-SPACE(v)  v is a pre-Hilbert space and SIP-METRIC-SPACE(v) is
;;;                       complete.
;;;   SIP-PERP(v, ks)     { eta in VEC(v) : <eta, xi> = 0 for every xi in ks }, PERP's order.
;;;   IS-CONVEX-SUBSET(v, cs)  the notes' Definition 2.1 (convex set of vectors).
;;;   IS-REAL-ORTHOGONAL-PROJECTION(v, ks, pk)  pk maps every vector x to a point pk(x) of
;;;                       ks with x - pk(x) in SIP-PERP(v, ks): IS-ORTHOGONAL-PROJECTION's
;;;                       property, for the real form.
;;;
;;; A SUBSPACE is IS-SUBMODULE(v, ks) applied to the space itself, as hilbert-space.scm
;;; does: IS-SUBMODULE reads only VEC, VZERO, VADD, VNEG, ACT and CARR(SCAL ...), which sit
;;; at MODULE's indices in a SEMI-INNER-PRODUCT-SPACE.
;;;
;;; Binders: `shn_' (the norm's lambda), `spp_' / `spk_' (SIP-PERP), `sop_' (the
;;; projection), named so that nothing else binds them.  The set parameter is `ks' (case
;;; folding: K and k are one symbol).
;;;
;;; Dependencies: sip-vocab.scm (SEMI-INNER-PRODUCT-SPACE, PRE-HILBERT-SPACE, RIP),
;;; normed-ag-metric (NAG-METRIC-SPACE), metric-completeness (IS-COMPLETE).
;;; LOAD WINDOW: after structure-library/sip-vocab and structure-library/hilbert-space;
;;; before theorem-library/sip-d1.  Library: analysis.

(def-functoid 'SIP-NORMED-AG '(v)
  '(LIST (VEC v) (VADD v) (VZERO v) (VNEG v)
         (VNB-LAMBDA shn_ (VEC v) (SQRT ((RIP v) shn_ shn_)))))

(def-functoid 'SIP-METRIC-SPACE '(v)
  '(NAG-METRIC-SPACE (SIP-NORMED-AG v)))

(def-predicate 'IS-REAL-HILBERT-SPACE '(v)
  '(AND (IS-PRE-HILBERT-SPACE v)
        (IS-COMPLETE (SIP-METRIC-SPACE v))))

(def-functoid 'SIP-PERP '(v ks)
  '(SEP spp_ (VEC v)
        (FORALL spk_ (IMPLIES (IN spk_ ks) (= ((RIP v) spp_ spk_) 0)))))

(def-predicate 'IS-REAL-ORTHOGONAL-PROJECTION '(v ks pk)
  '(AND (IN pk (FUN (VEC v) (VEC v)))
        (FORALL sop_ (IMPLIES (IN sop_ (VEC v))
          (AND (IN (pk sop_) ks)
               (IN ((VADD v) sop_ ((VNEG v) (pk sop_))) (SIP-PERP v ks)))))))

;;; IS-CONVEX-SUBSET(v, cs): the notes' Definition 2.1 -- cs is a set of vectors with
;;; (1 - t) a + t b in cs for a, b in cs and real 0 <= t <= 1.  It reads VEC, VADD and ACT only.
;;; Binders `sxa_' / `sxb_' / `sxt_' (IS-CONVEX-CC's are `cvx_' / `cvy_' / `cvt_').
(def-predicate 'IS-CONVEX-SUBSET '(v cs)
  '(AND (SUBSET cs (VEC v))
        (FORALL sxa_ (IMPLIES (IN sxa_ cs) (FORALL sxb_ (IMPLIES (IN sxb_ cs)
          (FORALL sxt_ (IMPLIES (IN sxt_ RR) (IMPLIES (<= 0 sxt_) (IMPLIES (<= sxt_ 1)
            (IN ((VADD v) ((ACT v) (- 1 sxt_) sxa_) ((ACT v) sxt_ sxb_)) cs)))))))))))

;;; ---- notation ----------------------------------------------------------------------------
(notation! 'SIP-NORMED-AG 'kind 'functoid 'arity 1
           'english "the normed additive group of $1")
(notation! 'SIP-METRIC-SPACE 'kind 'functoid 'arity 1
           'english "the metric space of $1")
(notation! 'IS-REAL-HILBERT-SPACE 'kind 'predicate 'arity 1
           'noun "real Hilbert space" 'article "a")
(notation! 'SIP-PERP 'kind 'functoid 'arity 2
           'english "the orthogonal complement of $2 in $1"
           'tex "{$2}^{\\perp}")
(notation! 'IS-CONVEX-SUBSET 'kind 'predicate 'arity 2
           'english "$2 is a convex set of vectors of $1")
(notation! 'IS-REAL-ORTHOGONAL-PROJECTION 'kind 'predicate 'arity 3
           'english "$3 is the orthogonal projection of $1 onto $2")
