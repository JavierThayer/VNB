;;; commutative-ring.scm -- COMMUTATIVE-RING: a ring whose MUL is commutative.
;;;
;;; Unlike RING/SEMIGROUP/... (declared with def-structure, whose IS-NAME is a
;;; pure SHAPE check), the restrictive structures COMMUTATIVE-RING,
;;; INTEGRAL-DOMAIN, FIELD, EUCLIDEAN-RING, NORMED-FIELD are defined by a
;;; genuine IFF that includes their characteristic properties.  A shape-only
;;; IS-NAME would make IS-COMMUTATIVE-RING equivalent to IS-RING (same 6-slot
;;; shape) and then force every ring commutative -- and a restriction such as
;;; ONE != ZERO would outright contradict the zero ring.  So IS-X here is a
;;; real predicate.  Accessors A, ADD, MUL, NEG, ZERO, ONE are reused from
;;; RING (ring.scm) -- a commutative ring has exactly the ring shape.
;;;
;;; No proofs: the numeric instances (zz/qq/rr/cc) and the upward relations
;;; are asserted as axioms.  Dependencies: ring.scm.

;;; IS-COMMUTATIVE-RING: a ring with commutative multiplication.
;;; This IFF *defines* the fresh predicate IS-COMMUTATIVE-RING (a conservative
;;; extension), so it is `definitional', not asserted debt -- exactly what
;;; def-predicate would stamp.  Marked so proofs that merely unfold it (e.g.
;;; commutative-ring-is-ring) rest on modulo 0, not a phantom leaf.
(declare-structure COMMUTATIVE-RING
  (same-shape-as RING)
  (law "forall([a in carr(s), b in carr(s)], mul(s)(a, b) = mul(s)(b, a))"))

;;; Relation: every commutative ring is a ring.
;;; PROVEN modulo 0 via mac-h in structure-library/subtype-laws.scm (unfold
;;; is-commutative-ring-def; IS-RING is a literal RHS conjunct); not asserted.

;;; Associated proper class COMMUTATIVE-RING = { s | IS-COMMUTATIVE-RING(s) }.
;;; Mirrors the NAME-class axiom def-structure installs for shape structures
;;; (RING, FIELD, ...), so bounded quantification forall([s in
;;; COMMUTATIVE-RING], ...) works uniformly.  Unfolding the predicate gives
;;; the parent-class reading
;;;   s in COMMUTATIVE-RING  <=>  s in RING and (MUL s) commutes on (CARR s).

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-COMMUTATIVE-RING   'kind 'predicate 'arity 1 'noun "commutative ring" 'article "a")
