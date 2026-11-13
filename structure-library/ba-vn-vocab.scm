;;; ba-vn-vocab.scm -- Thayer, Banach Algebras and Applications, chapter 6 (density theorems): the
;;; commutant and bicommutant of a set of operators, involutive operator algebras, von Neumann algebras,
;;; cyclic and separating vectors.  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-1111-C, 2026-11-11.  DESTINATION: structure-library/ba-vn-vocab.scm, after
;;; structure-library/ba-optop-vocab.scm (SOT) and structure-library/top-closed.scm (IS-TOP-CLOSED).
;;; Library: operator-algebras.
;;;
;;;   COMMUTANT(v, s)            S' = {T in L(H) : T A = A T for all A in s}        (ch. 6 s.1)
;;;   BICOMMUTANT(v, s)          S'' = (S')'
;;;   IS-STAR-OP-ALGEBRA(v, a)   a is an involutive algebra of operators on H containing I_H: a subset of
;;;                              L(H) containing I_H and closed under +, scalar multiples, composition and *
;;;   IS-VON-NEUMANN-ALGEBRA(v, a)  Def 6.4: an involutive algebra of operators containing I_H, closed in
;;;                              the strong operator topology
;;;   IS-CYCLIC-FOR(v, s, xi)    xi is a cyclic vector for s: {A xi : A in s} is (norm) dense in H  (s.3)
;;;   IS-SEPARATING-FOR(v, s, xi)  xi is a separating vector for s: A xi = 0 implies A = 0 for A in s
;;; Density is stated with the norm directly: for every y in H and eps > 0 some A in s has
;;; ||y - A xi|| < eps.  Binders: vn*_ (vnt_ vna_ vny_ vne_ vnx_ vnc_ vnb_), used by no other file.

(def-functoid 'COMMUTANT '(vnv_ vns_)
  '(SEP vnt_ (BOUNDED-OPS vnv_ vnv_)
     (FORALL vna_ (IMPLIES (IN vna_ vns_) (= (BOP-COMP vnv_ vnt_ vna_) (BOP-COMP vnv_ vna_ vnt_))))))
(def-functoid 'BICOMMUTANT '(vnv_ vns_) '(COMMUTANT vnv_ (COMMUTANT vnv_ vns_)))

(def-predicate 'IS-STAR-OP-ALGEBRA '(vnv_ vns_)
  (conjuncts->and
    (list
      '(SUBSET vns_ (BOUNDED-OPS vnv_ vnv_))
      '(IN (BOP-ID vnv_) vns_)
      '(FORALL vna_ (IMPLIES (IN vna_ vns_) (FORALL vnb_ (IMPLIES (IN vnb_ vns_)
         (IN (BOP-SUM vnv_ vnv_ vna_ vnb_) vns_)))))
      '(FORALL vnc_ (IMPLIES (IN vnc_ CC) (FORALL vna_ (IMPLIES (IN vna_ vns_)
         (IN (BOP-SCALE vnv_ vnv_ vnc_ vna_) vns_)))))
      '(FORALL vna_ (IMPLIES (IN vna_ vns_) (FORALL vnb_ (IMPLIES (IN vnb_ vns_)
         (IN (BOP-COMP vnv_ vna_ vnb_) vns_)))))
      '(FORALL vna_ (IMPLIES (IN vna_ vns_) (IN (OP-ADJOINT vnv_ vnv_ vna_) vns_))))))

(def-predicate 'IS-VON-NEUMANN-ALGEBRA '(vnv_ vns_)
  '(AND (IS-STAR-OP-ALGEBRA vnv_ vns_) (IS-TOP-CLOSED (SOT vnv_) vns_)))

(def-predicate 'IS-CYCLIC-FOR '(vnv_ vns_ vnx_)
  '(AND (IN vnx_ (VEC vnv_))
        (FORALL vny_ (IMPLIES (IN vny_ (VEC vnv_))
          (FORALL vne_ (IMPLIES (POS-RR vne_)
            (FORSOME vna_ (AND (IN vna_ vns_)
              (< (IP-NORM vnv_ ((VADD vnv_) vny_ ((VNEG vnv_) (vna_ vnx_)))) vne_)))))))))

(def-predicate 'IS-SEPARATING-FOR '(vnv_ vns_ vnx_)
  '(AND (IN vnx_ (VEC vnv_))
        (FORALL vna_ (IMPLIES (IN vna_ vns_)
          (IMPLIES (= (vna_ vnx_) (VZERO vnv_)) (= vna_ (BOP-ZERO vnv_ vnv_)))))))

(notation! 'COMMUTANT 'kind 'functoid 'arity 2 'english "the commutant of $2 in the bounded operators on $1" 'tex "{$2}'")
(notation! 'BICOMMUTANT 'kind 'functoid 'arity 2 'english "the bicommutant of $2 in the bounded operators on $1" 'tex "{$2}''")
(notation! 'IS-STAR-OP-ALGEBRA 'kind 'predicate 'arity 2 'english "$2 is an involutive algebra of operators on $1 containing the identity")
(notation! 'IS-VON-NEUMANN-ALGEBRA 'kind 'predicate 'arity 2 'english "$2 is a von Neumann algebra on $1")
(notation! 'IS-CYCLIC-FOR 'kind 'predicate 'arity 3 'english "$3 is a cyclic vector for $2")
(notation! 'IS-SEPARATING-FOR 'kind 'predicate 'arity 3 'english "$3 is a separating vector for $2")
