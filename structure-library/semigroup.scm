;;; semigroup.scm -- SEMIGROUP structure
;;;
;;; Carrier CARR, binary operation OPR.
;;; Accessor indices: CARR -> 1, OPR -> 2.

(declare-structure SEMIGROUP
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (property is-associative OPR CARR))

;;; forall s. IS-SEMIGROUP(s) => forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
(theory-add-axiom! *current-theory* 'semigroup-assoc
  '(FORALL s
     (IMPLIES (IS-SEMIGROUP s)
       (FORALL a (IMPLIES (IN a (CARR s))
         (FORALL b (IMPLIES (IN b (CARR s))
           (FORALL c (IMPLIES (IN c (CARR s))
             (= ((OPR s) ((OPR s) a b) c)
                ((OPR s) a ((OPR s) b c))))))))))))

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-SEMIGROUP            'noun "semigroup" 'article "a")
