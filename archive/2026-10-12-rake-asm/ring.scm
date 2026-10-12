;;; RETIRED 2026-09-17 (proven): ring-neg-mul-left -- theorem-library/rake-algebra2.scm
;;; RETIRED 2026-09-17 (proven): ring-carr-in-set -- theorem-library/rake-algebra.scm
;;; ring.scm -- RING, RING-PROD, ZERO-RING
;;;
;;; RING: carrier CARR, addition ADD, multiplication MUL, additive inverse NEG,
;;;       zero ZERO, multiplicative identity ONE.
;;; Accessor indices: CARR -> 1, ADD -> 2, MUL -> 3, NEG -> 4, ZERO -> 5, ONE -> 6.
;;;
;;; (A, ADD, ZERO, NEG) is an abelian group; (A, MUL, ONE) is a monoid;
;;; MUL distributes over ADD.
;;; RETIRED 2026-09-14 (proven): ring-mul-zero-left -- theorem-library/ring-zero-one-power.scm
;;; RETIRED 2026-09-14 (proven): ring-mul-zero-right -- theorem-library/ring-zero-one-power.scm

(declare-structure RING
  (carriers CARR)
  (op ADD (CARTESIAN CARR CARR) CARR)
  (op MUL (CARTESIAN CARR CARR) CARR)
  (op NEG CARR CARR)
  (constant ZERO CARR)
  (constant ONE CARR)
  (property is-associative ADD CARR)
  (property is-commutative ADD CARR)
  (property is-identity ADD ZERO CARR)
  (property has-inverses ADD ZERO NEG CARR)
  (property is-associative MUL CARR)
  (property is-identity MUL ONE CARR)
  (property is-distributive ADD MUL CARR))

(add-axiom! *library* 'ring-add-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((ADD s) ((ADD s) a b) c)
                ((ADD s) a ((ADD s) b c))))))))))))

(add-axiom! *library* 'ring-add-comm
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (= ((ADD s) a b) ((ADD s) b a)))))))))

(add-axiom! *library* 'ring-add-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((ADD s) (ZERO s) a) a))))))

(add-axiom! *library* 'ring-add-left-inv
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((ADD s) ((NEG s) a) a) (ZERO s)))))))

(add-axiom! *library* 'ring-mul-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

(add-axiom! *library* 'ring-mul-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) (ONE s) a) a))))))

(add-axiom! *library* 'ring-mul-right-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) a (ONE s)) a))))))

(add-axiom! *library* 'ring-left-dist
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) a ((ADD s) b c))
                ((ADD s) ((MUL s) a b) ((MUL s) a c))))))))))))

(add-axiom! *library* 'ring-right-dist
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) ((ADD s) a b) c)
                ((ADD s) ((MUL s) a c) ((MUL s) b c))))))))))))

;;; Zero is a two-sided annihilator under MUL.
;;; DERIVED: a·0 = a·(0+0) = a·0 + a·0; cancel a·0 against itself in the
;;; additive group.  Symmetric on the other side.  Standard ring lemmas,
;;; installed as axioms for direct use in scalar pull-outs over finite sums.


;;; (-a) * b = -(a*b).  Standard: a*b + (-a)*b = (a + -a)*b = 0*b = 0, so (-a)*b
;;; is the additive inverse of a*b.  Needed wherever a coefficient is negated --
;;; the lastcoeff ideal's neg-closure, and the spans-submodule-fg remainder
;;; c_{1,succ p} + (-q)*b = q*b - q*b = 0.

;;; ZERO(r) ∈ CARR(r) when IS-RING(r).
;;; DERIVED (REVIEW.md R-2): follows from the auto-generated IS-RING IFF.
(add-axiom! *library* 'ring-zero-in
  '(FORALL r (IMPLIES (IS-RING r) (IN (ZERO r) (CARR r)))))

;;; DERIVED (REVIEW.md R-3): IS-RING IFF + fun-apply-type.
(add-axiom! *library* 'ring-carrier-closed-add
  '(FORALL r (FORALL a (FORALL b
      (IMPLIES (AND (IS-RING r) (AND (IN a (CARR r)) (IN b (CARR r))))
               (IN ((ADD r) a b) (CARR r)))))))

;;; Provenance.  The property/shape projections above ARE the IS-RING definition
;;; -- each is a conjunct of the auto-generated IS-RING IFF, unfolded -- so they
;;; are DEFINITIONAL and pay nothing, not asserted facts owing trust.  (This is
;;; the fix for the `trust: none' bills CLAUDE.md flags: an unwarranted projection
;;; drags every ring theorem to the weakest tier.)  ring-mul-zero-left/right ARE
;;; genuinely derived (0.a = 0 by distributivity + cancellation), so they take a
;;; well-known warrant rather than definitional provenance.
(for-each (lambda (n) (register-provenance! n 'definitional))
  '(ring-add-assoc ring-add-comm ring-add-left-id ring-add-left-inv
    ring-mul-assoc ring-mul-left-id ring-mul-right-id ring-left-dist ring-right-dist
    ring-zero-in ring-carrier-closed-add))

;;; ADD closes on the carrier -- CURRIED (ring-carrier-closed-add above packs its
;;; guards into one AND, which a forward `fact' will not split; this is the twin
;;; of ring-carrier-closed-mul, usable by `fact' directly).
;;; ring-add-closed and ring-carrier-closed-mul are PROVEN (2026-08-31) in
;;; theorem-library/op-typing.scm, together with the other five applied-form
;;; op typings: one driver over IS-X unfold + apply-tupling-2 +
;;; fun-apply-type-c, which is the derivation the warrants here recited
;;; ("From (op MUL (CARTESIAN CARR CARR) CARR) + fun-apply").

;;; The carrier of a ring is a set (the CARR-in-SET typing conjunct of the
;;; auto-generated IS-RING definition).  Named for citation.

;;; -----------------------------------------------------------------------
;;; RING-PROD: product of two rings.  Total: defined for any X, Y;
;;; IS-RING(RING-PROD(X,Y)) holds when both IS-RING(X) and IS-RING(Y).

(def-functoid 'RING-PROD '(X Y)
  '(LIST
     (CARTESIAN (CARR X) (CARR Y))
     (VNB-LAMBDA (LIST p q) (CARTESIAN (CARTESIAN (CARR X) (CARR Y)) (CARTESIAN (CARR X) (CARR Y)))
       (LIST ((ADD X) (NTH 1 p) (NTH 1 q))
             ((ADD Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p q) (CARTESIAN (CARTESIAN (CARR X) (CARR Y)) (CARTESIAN (CARR X) (CARR Y)))
       (LIST ((MUL X) (NTH 1 p) (NTH 1 q))
             ((MUL Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p) (CARTESIAN (CARR X) (CARR Y))
       (LIST ((NEG X) (NTH 1 p))
             ((NEG Y) (NTH 2 p))))
     (LIST (ZERO X) (ZERO Y))
     (LIST (ONE X) (ONE Y))))

(add-axiom! *library* 'ring-prod-is-ring
  '(FORALL X (IMPLIES (IS-RING X)
      (FORALL Y (IMPLIES (IS-RING Y)
        (IS-RING (RING-PROD X Y)))))))

;;; -----------------------------------------------------------------------
;;; ZERO-RING: terminal ring (carrier = {0}; identity for RING-PROD).

(def-constant 'ZERO-RING
  (list 'zero-ring-def
        '(= ZERO-RING
            (LIST (MAKE-SET (LIST 0))
                  (VNB-LAMBDA (LIST p q) (CARTESIAN (MAKE-SET (LIST 0)) (MAKE-SET (LIST 0))) 0)
                  (VNB-LAMBDA (LIST p q) (CARTESIAN (MAKE-SET (LIST 0)) (MAKE-SET (LIST 0))) 0)
                  (VNB-LAMBDA (LIST p) (MAKE-SET (LIST 0)) 0)
                  0
                  0))))

(add-axiom! *library* 'zero-ring-is-ring
  '(IS-RING ZERO-RING))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-RING                 'noun "ring" 'article "a")
