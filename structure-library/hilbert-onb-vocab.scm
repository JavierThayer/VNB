;;; hilbert-onb-vocab.scm -- wave of 2026-11-09/10 (agent BA-ONB), wired 2026-11-10 from scratchpad/baonb-1109/hilbert-onb-vocab.scm.
;;; Library: analysis.

;;; hilbert-onb-vocab.scm -- ORTHONORMAL SETS, FAMILIES AND BASES of a complex inner
;;; product space.  Vocabulary only: no proof, no support.  Agent BA-ONB, 2026-11-09
;;; (scratchpad/triage/BA-ONB.md).  The proofs are theorem-library/hilbert-onb.scm
;;; (prefix `onb-').
;;;
;;; DESTINATION: structure-library/hilbert-onb-vocab.scm.  Library: analysis (the
;;; BA-MAP report s.3.9: orthonormal bases are of general interest and belong to
;;; analysis, not to operator-algebras; ba-hs-vocab.scm, which HS-OPS / TRACE-CLASS
;;; will live in, imports this file rather than owning the ONB part).
;;; Load window: after structure-library/hilbert-space (IS-HILBERT-SPACE) and
;;; structure-library/complex-inner-product (IP, VEC, VZERO); before
;;; theorem-library/hilbert-onb.
;;;
;;; Source: Thayer, "Analise Funcional e Teoria Espectral" (th-main.pdf), s.2.1:
;;; "{xi_i}_{i in I} e ortonormal se ela e ortogonal e ||xi_i|| = 1"; "uma base
;;; ortonormal de H e uma familia ortonormal total".
;;;
;;;   IS-ORTHONORMAL-SET(v, os)        os is a set of vectors of v, each of norm 1
;;;                                    (<a,a> = 1), two distinct ones orthogonal.
;;;   IS-ORTHONORMAL-FAMILY(v, ix, e)  e : ix -> VEC(v), <e_i, e_i> = 1 and
;;;                                    <e_i, e_j> = 0 for i /= j in ix.
;;;   IS-ORTHONORMAL-BASIS(v, ix, e)   an orthonormal family whose orthogonal
;;;                                    complement is {0}: a vector orthogonal to
;;;                                    every e_i is the zero vector.
;;;
;;; THE DEFINITION OF A BASIS, AND THE NOTES' "TOTAL".  The notes define an orthonormal
;;; basis as a TOTAL orthonormal family (its finite linear combinations are dense).  The
;;; definition here is the COMPLETENESS of the family (PERP of the family is {0}), which
;;; is MAXIMALITY among orthonormal families, the form Zorn's lemma delivers.  In a
;;; Hilbert space the two coincide, and the stronger form of totality is a theorem of
;;; theorem-library/hilbert-onb.scm: every vector is the unordered sum of its expansion
;;; (onb-expansion, Prop. 2.10), so the finite combinations are dense.  In a pre-Hilbert
;;; space a complete family need not be total; the theorems that use completeness alone
;;; (existence, extension, Bessel) are stated in a complex inner product space, those
;;; that need totality (expansion, Parseval) in a Hilbert space.
;;;
;;; A family, not a set, because the operator chapters index a basis ({e_i}_{i in I},
;;; HS-OPS, the trace); the SET form is the one Zorn's lemma is run on, and
;;; `onb-of-complete-orthonormal-set' turns a complete orthonormal set into a basis indexed by
;;; itself.
;;;
;;; Binders: osa_ osb_ (sets), oni_ onj_ (families), onx_ (the basis condition), named so
;;; that nothing else binds them.
;;;
;;; Dependencies: complex-inner-product.scm (IS-COMPLEX-INNER-PRODUCT-SPACE, IP, VEC,
;;; VZERO), hilbert-space.scm (only for the reading of IS-HILBERT-SPACE in the theorems).

(def-predicate 'IS-ORTHONORMAL-SET '(v os)
  '(AND (SUBSET os (VEC v))
   (AND (FORALL osa_ (IMPLIES (IN osa_ os) (= ((IP v) osa_ osa_) 1)))
        (FORALL osa_ (IMPLIES (IN osa_ os)
          (FORALL osb_ (IMPLIES (IN osb_ os)
            (IMPLIES (NOT (= osa_ osb_)) (= ((IP v) osa_ osb_) 0)))))))))

(def-predicate 'IS-ORTHONORMAL-FAMILY '(v ix e)
  '(AND (IN e (FUN ix (VEC v)))
   (AND (FORALL oni_ (IMPLIES (IN oni_ ix) (= ((IP v) (e oni_) (e oni_)) 1)))
        (FORALL oni_ (IMPLIES (IN oni_ ix)
          (FORALL onj_ (IMPLIES (IN onj_ ix)
            (IMPLIES (NOT (= oni_ onj_)) (= ((IP v) (e oni_) (e onj_)) 0)))))))))

(def-predicate 'IS-ORTHONORMAL-BASIS '(v ix e)
  '(AND (IS-ORTHONORMAL-FAMILY v ix e)
        (FORALL onx_ (IMPLIES (IN onx_ (VEC v))
          (IMPLIES (FORALL oni_ (IMPLIES (IN oni_ ix) (= ((IP v) onx_ (e oni_)) 0)))
                   (= onx_ (VZERO v)))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-ORTHONORMAL-SET 'kind 'predicate 'arity 2
           'english "$2 is an orthonormal set in $1")
(notation! 'IS-ORTHONORMAL-FAMILY 'kind 'predicate 'arity 3
           'english "$3 is an orthonormal family in $1 indexed by $2")
(notation! 'IS-ORTHONORMAL-BASIS 'kind 'predicate 'arity 3
           'english "$3 is an orthonormal basis of $1 indexed by $2")
