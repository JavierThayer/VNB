;;; m-riesz-vocab.scm -- ORDERED VECTOR SPACES: BanachAlgebras.pdf section 4.6, before Proposition 4.32
;;; (the M. Riesz extension).  Agent BA-1117-GNS2, 2026-11-17.
;;; Destination: structure-library/m-riesz-vocab.scm.  Library: analysis.
;;; DEFINITIONS ONLY.  Load window: after structure-library/module (VEC, VADD, VNEG, ACT, VZERO).
;;;
;;;   IS-POINTED-CONE(m, c)   c is a pointed cone of the real vector space m: 0 in c, c + c in c,
;;;                           t c in c for t >= 0
;;;   CONE-LE(m, c, x, y)     x <= y in the order of the cone: y - x in c, formula (94)
;;;   IS-COFINAL(m, c, v)     every a in m lies below some x in v
;;; Binders g4r*_, used by no other file.

(def-predicate 'IS-POINTED-CONE '(g4rm_ g4rc_)
  '(AND (SUBSET g4rc_ (VEC g4rm_))
    (AND (IN (VZERO g4rm_) g4rc_)
     (AND (FORALL g4rx_ (IMPLIES (IN g4rx_ g4rc_) (FORALL g4ry_ (IMPLIES (IN g4ry_ g4rc_)
            (IN ((VADD g4rm_) g4rx_ g4ry_) g4rc_)))))
          (FORALL g4rt_ (IMPLIES (IN g4rt_ RR) (IMPLIES (<= 0 g4rt_)
            (FORALL g4rx_ (IMPLIES (IN g4rx_ g4rc_) (IN ((ACT g4rm_) g4rt_ g4rx_) g4rc_))))))))))

(def-predicate 'CONE-LE '(g4rm_ g4rc_ g4rx_ g4ry_)
  '(IN ((VADD g4rm_) g4ry_ ((VNEG g4rm_) g4rx_)) g4rc_))

(def-predicate 'IS-COFINAL '(g4rm_ g4rc_ g4rv_)
  '(FORALL g4ra_ (IMPLIES (IN g4ra_ (VEC g4rm_))
     (FORSOME g4rx_ (AND (IN g4rx_ g4rv_) (CONE-LE g4rm_ g4rc_ g4ra_ g4rx_))))))

(notation! 'IS-POINTED-CONE 'kind 'predicate 'arity 2 'english "$2 is a pointed cone of $1")
(notation! 'CONE-LE 'kind 'predicate 'arity 4 'english "$3 is below $4 in the order of the cone $2" 'tex "{$3} \\preceq_{$2} {$4}")
(notation! 'IS-COFINAL 'kind 'predicate 'arity 3 'english "$3 is cofinal in $1 for the order of the cone $2")
