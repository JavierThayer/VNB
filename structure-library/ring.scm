;;; ring.scm -- RING, RING-PROD, ZERO-RING
;;;
;;; RING: carrier CARR, addition ADD, multiplication MUL, additive inverse NEG,
;;;       zero ZERO, multiplicative identity ONE.
;;; Accessor indices: CARR -> 1, ADD -> 2, MUL -> 3, NEG -> 4, ZERO -> 5, ONE -> 6.
;;;
;;; (A, ADD, ZERO, NEG) is an abelian group; (A, MUL, ONE) is a monoid;
;;; MUL distributes over ADD.

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

(theory-add-axiom! *current-theory* 'ring-add-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((ADD s) ((ADD s) a b) c)
                ((ADD s) a ((ADD s) b c))))))))))))

(theory-add-axiom! *current-theory* 'ring-add-comm
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (= ((ADD s) a b) ((ADD s) b a)))))))))

(theory-add-axiom! *current-theory* 'ring-add-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((ADD s) (ZERO s) a) a))))))

(theory-add-axiom! *current-theory* 'ring-add-left-inv
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((ADD s) ((NEG s) a) a) (ZERO s)))))))

(theory-add-axiom! *current-theory* 'ring-mul-assoc
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) ((MUL s) a b) c)
                ((MUL s) a ((MUL s) b c))))))))))))

(theory-add-axiom! *current-theory* 'ring-mul-left-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) (ONE s) a) a))))))

(theory-add-axiom! *current-theory* 'ring-mul-right-id
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) a (ONE s)) a))))))

(theory-add-axiom! *current-theory* 'ring-left-dist
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((MUL s) a ((ADD s) b c))
                ((ADD s) ((MUL s) a b) ((MUL s) a c))))))))))))

(theory-add-axiom! *current-theory* 'ring-right-dist
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
(theory-add-axiom! *current-theory* 'ring-mul-zero-left
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) (ZERO s) a) (ZERO s)))))))

(theory-add-axiom! *current-theory* 'ring-mul-zero-right
  '(FORALL s
     (IMPLIES (IS-RING s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (= ((MUL s) a (ZERO s)) (ZERO s)))))))

;;; (-a) * b = -(a*b).  Standard: a*b + (-a)*b = (a + -a)*b = 0*b = 0, so (-a)*b
;;; is the additive inverse of a*b.  Needed wherever a coefficient is negated --
;;; the lastcoeff ideal's neg-closure, and the spans-submodule-fg remainder
;;; c_{1,succ p} + (-q)*b = q*b - q*b = 0.
(support 'ring-neg-mul-left
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (= ((MUL s) ((NEG s) a) b) ((NEG s) ((MUL s) a b))))))))))
(warrant! 'ring-neg-mul-left 'well-known
  "(-a)*b = -(a*b): a*b + (-a)*b = (a + -a)*b = 0*b = 0 (ring-right-dist,
   ring-add-left-inv, ring-mul-zero-left), so (-a)*b is the inverse of a*b.")

;;; ZERO(r) ∈ CARR(r) when IS-RING(r).
;;; DERIVED (REVIEW.md R-2): follows from the auto-generated IS-RING IFF.
(theory-add-axiom! *current-theory* 'ring-zero-in
  '(FORALL r (IMPLIES (IS-RING r) (IN (ZERO r) (CARR r)))))

;;; DERIVED (REVIEW.md R-3): IS-RING IFF + fun-apply-type.
(theory-add-axiom! *current-theory* 'ring-carrier-closed-add
  '(FORALL r (FORALL a (FORALL b
      (IMPLIES (AND (IS-RING r) (AND (IN a (CARR r)) (IN b (CARR r))))
               (IN ((ADD r) a b) (CARR r)))))))

;;; ADD closes on the carrier -- CURRIED (ring-carrier-closed-add above packs its
;;; guards into one AND, which a forward `fact' will not split; this is the twin
;;; of ring-carrier-closed-mul, usable by `fact' directly).
(support 'ring-add-closed
  '(FORALL s (IMPLIES (IS-RING s)
     (FORALL a (IMPLIES (IN a (CARR s))
       (FORALL b (IMPLIES (IN b (CARR s))
         (IN ((ADD s) a b) (CARR s)))))))))
(warrant! 'ring-add-closed 'well-known "ADD closes on the carrier (curried form).")

;;; MUL closes on the carrier -- curried (so a forward `fact' detaches each
;;; guard without a cut).  From (op MUL (CARTESIAN CARR CARR) CARR) + fun-apply.
(support 'ring-carrier-closed-mul
  '(FORALL r (IMPLIES (IS-RING r)
     (FORALL a (IMPLIES (IN a (CARR r))
     (FORALL b (IMPLIES (IN b (CARR r))
       (IN ((MUL r) a b) (CARR r)))))))))
(warrant! 'ring-carrier-closed-mul 'proof
  "MUL closes on CARR: (op MUL) has type CARR x CARR -> CARR (fun-apply-type).")
(category! 'ring-carrier-closed-mul 'algebra)

;;; The carrier of a ring is a set (the CARR-in-SET typing conjunct of the
;;; auto-generated IS-RING definition).  Named for citation.
(support 'ring-carr-in-set
  '(FORALL r (IMPLIES (IS-RING r) (IN (CARR r) SET))))
(warrant! 'ring-carr-in-set 'proof "carrier of a ring is a set (IS-RING typing conjunct).")
(category! 'ring-carr-in-set 'algebra)

;;; -----------------------------------------------------------------------
;;; RING-PROD: product of two rings.  Total: defined for any X, Y;
;;; IS-RING(RING-PROD(X,Y)) holds when both IS-RING(X) and IS-RING(Y).

(def-functoid 'RING-PROD '(X Y)
  '(LIST
     (CARTESIAN (CARR X) (CARR Y))
     (VNB-LAMBDA (LIST p q)
       (LIST ((ADD X) (NTH 1 p) (NTH 1 q))
             ((ADD Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p q)
       (LIST ((MUL X) (NTH 1 p) (NTH 1 q))
             ((MUL Y) (NTH 2 p) (NTH 2 q))))
     (VNB-LAMBDA (LIST p)
       (LIST ((NEG X) (NTH 1 p))
             ((NEG Y) (NTH 2 p))))
     (LIST (ZERO X) (ZERO Y))
     (LIST (ONE X) (ONE Y))))

(theory-add-axiom! *current-theory* 'ring-prod-is-ring
  '(FORALL X (IMPLIES (IS-RING X)
      (FORALL Y (IMPLIES (IS-RING Y)
        (IS-RING (RING-PROD X Y)))))))

;;; -----------------------------------------------------------------------
;;; ZERO-RING: terminal ring (carrier = {0}; identity for RING-PROD).

(def-constant 'ZERO-RING
  (list 'zero-ring-def
        '(= ZERO-RING
            (LIST (MAKE-SET (LIST 0))
                  (VNB-LAMBDA (LIST p q) 0)
                  (VNB-LAMBDA (LIST p q) 0)
                  (VNB-LAMBDA (LIST p) 0)
                  0
                  0))))

(theory-add-axiom! *current-theory* 'zero-ring-is-ring
  '(IS-RING ZERO-RING))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-RING                 'noun "ring" 'article "a")
