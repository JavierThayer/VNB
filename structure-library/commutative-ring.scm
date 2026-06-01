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
(theory-add-axiom! *current-theory* 'is-commutative-ring-def
  '(FORALL s
     (IFF (IS-COMMUTATIVE-RING s)
          (AND (IS-RING s)
               (FORALL a (IMPLIES (IN a (A s))
                 (FORALL b (IMPLIES (IN b (A s))
                   (= ((MUL s) a b) ((MUL s) b a))))))))))

;;; Relation: every commutative ring is a ring.
(theory-add-axiom! *current-theory* 'commutative-ring-is-ring
  '(FORALL s (IMPLIES (IS-COMMUTATIVE-RING s) (IS-RING s))))

;;; Associated proper class COMMUTATIVE-RING = { s | IS-COMMUTATIVE-RING(s) }.
;;; Mirrors the NAME-class axiom def-structure installs for shape structures
;;; (RING, FIELD, ...), so bounded quantification forall([s in
;;; COMMUTATIVE-RING], ...) works uniformly.  Unfolding the predicate gives
;;; the parent-class reading
;;;   s in COMMUTATIVE-RING  <=>  s in RING and (MUL s) commutes on (A s).
(theory-add-axiom! *current-theory* 'commutative-ring-class
  '(FORALL s (IFF (IN s COMMUTATIVE-RING) (IS-COMMUTATIVE-RING s))))

;;; Register with the navigation index.
(register-definitional-structure! 'COMMUTATIVE-RING 'RING)
