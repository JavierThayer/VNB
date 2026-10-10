;;; hilbert-space.scm -- HILBERT SPACES: the metric space of a complex inner
;;; product space, completeness, and the orthogonal complement.  Vocabulary only:
;;; no proof, no support.  Agent HILBERT-1, 2026-10-10
;;; (scratchpad/triage/HILBERT-1.md).  The proofs are
;;; theorem-library/hilbert-projection.scm (prefix `hpr-') and
;;; theorem-library/hilbert-riesz.scm (prefix `hrz-').
;;;
;;; Source: Thayer, "Analise Funcional e Teoria Espectral" (reference
;;; `thayer-spectral'), Def. 1.28 (a Hilbert space is a pre-Hilbert space complete
;;; in the norm of its inner product) and Def. 2.18 (K perp).
;;;
;;;   IP-METRIC-SPACE(v)  the metric space of the inner product space v:
;;;                       NAG-METRIC-SPACE(IP-NORMED-AG(v)), whose points are
;;;                       VEC(v) and whose distance is d(x, y) = SQRT(<x-y, x-y>)
;;;                       (hpr-ms-pts, hpr-ms-dist).  A name for a composite the
;;;                       tree already has, so that "closed", "complete",
;;;                       "converges" read in one word.
;;;   IS-HILBERT-SPACE(v) v is a complex inner product space and
;;;                       IP-METRIC-SPACE(v) is complete.
;;;   PERP(v, ks)         { eta in VEC(v) : <eta, xi> = 0 for every xi in ks }.
;;;                       The book's order: eta on the LEFT of the bracket.
;;;   IS-ORTHOGONAL-PROJECTION(v, ks, pk)   the book's P_K, as a property of a map
;;;   IS-CC-LINEAR-FUNCTIONAL(v, f)          f : VEC(v) -> CC additive, CC-homogeneous
;;;
;;; A SUBSPACE is the tree's IS-SUBMODULE(v, ks) applied to the inner product
;;; space ITSELF, not to its module view COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE(v):
;;; IS-SUBMODULE reads only the accessors VEC, VZERO, VADD, VNEG, ACT and
;;; CARR(SCAL ...), which sit at the same slot indices in both tuples, and it does
;;; not demand IS-MODULE of its first argument.  So IS-SUBMODULE(v, ks) says
;;; exactly what IS-SUBMODULE(COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE(v), ks) says,
;;; without the five slot read-offs.
;;;
;;; Binders: `prp_' and `prk_' (PERP), named so that nothing else binds them.  The
;;; set parameter is `ks', never `K' (case folding: K and k are one symbol).
;;;
;;; Dependencies: complex-inner-product.scm (IS-COMPLEX-INNER-PRODUCT-SPACE, IP,
;;; IP-NORMED-AG), normed-ag-metric.scm (NAG-METRIC-SPACE), metric-completeness.scm
;;; (IS-COMPLETE).

(def-functoid 'IP-METRIC-SPACE '(v)
  '(NAG-METRIC-SPACE (IP-NORMED-AG v)))

(def-predicate 'IS-HILBERT-SPACE '(v)
  '(AND (IS-COMPLEX-INNER-PRODUCT-SPACE v)
        (IS-COMPLETE (IP-METRIC-SPACE v))))

(def-functoid 'PERP '(v ks)
  '(SEP prp_ (VEC v)
        (FORALL prk_ (IMPLIES (IN prk_ ks) (= ((IP v) prp_ prk_) 0)))))

;;; IS-ORTHOGONAL-PROJECTION(v, ks, pk): pk maps every vector xi to a point
;;; pk(xi) of ks with xi - pk(xi) in PERP(v, ks) -- the book's P_K of Prop. 2.19,
;;; as a PROPERTY of a map rather than a defined operator.  For ks a closed
;;; subspace of a Hilbert space such a map exists and is unique
;;; (orthogonal-projection-exists / -unique), so "THE orthogonal projection" is
;;; well defined without IOTA; Prop. 2.19 (ii)-(iii) are stated for any map with
;;; the property.
(def-predicate 'IS-ORTHOGONAL-PROJECTION '(v ks pk)
  '(AND (IN pk (FUN (VEC v) (VEC v)))
        (FORALL opz_ (IMPLIES (IN opz_ (VEC v))
          (AND (IN (pk opz_) ks)
               (IN ((VADD v) opz_ ((VNEG v) (pk opz_))) (PERP v ks)))))))

;;; IS-CC-LINEAR-FUNCTIONAL(v, f): f : VEC(v) -> CC is additive and
;;; CC-homogeneous.  The tree's IS-K-LINEAR (seminorm-hahn-banach.scm) says the
;;; same of IS-K-LINEAR(COMPLEX-INNER-PRODUCT-SPACE-AS-MODULE(v), f), but through
;;; the module view and the ring operations ADD / MUL of the scalar ring, so that
;;; every use would first read five slots off the view and the CC-NORMED-FIELD
;;; ring; and dual-space.scm (DUAL, DUAL-NORM) is the dual of a REAL normed vector
;;; space.  Riesz (Thm. 2.22) is stated with this predicate plus
;;; IS-CONTINUOUS(IP-METRIC-SPACE(v), CC-MS, f).
(def-predicate 'IS-CC-LINEAR-FUNCTIONAL '(v f)
  '(AND (IN f (FUN (VEC v) CC))
   (AND (FORALL hlx_ (IMPLIES (IN hlx_ (VEC v))
          (FORALL hly_ (IMPLIES (IN hly_ (VEC v))
            (= (f ((VADD v) hlx_ hly_)) (+ (f hlx_) (f hly_)))))))
        (FORALL hlc_ (IMPLIES (IN hlc_ CC)
          (FORALL hlx_ (IMPLIES (IN hlx_ (VEC v))
            (= (f ((ACT v) hlc_ hlx_)) (* hlc_ (f hlx_))))))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IP-METRIC-SPACE 'kind 'functoid 'arity 1
           'english "the metric space of the inner product space $1")
(notation! 'IS-HILBERT-SPACE 'kind 'predicate 'arity 1
           'noun "Hilbert space" 'article "a")
(notation! 'PERP 'kind 'functoid 'arity 2
           'english "the orthogonal complement of $2 in $1"
           'tex "{$2}^{\\perp}")
(notation! 'IS-ORTHOGONAL-PROJECTION 'kind 'predicate 'arity 3
           'english "$3 is the orthogonal projection of $1 onto $2")
(notation! 'IS-CC-LINEAR-FUNCTIONAL 'kind 'predicate 'arity 2
           'english "$2 is a linear functional on $1")
