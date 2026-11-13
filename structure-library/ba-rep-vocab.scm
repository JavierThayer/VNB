;;; ba-rep-vocab.scm -- POSITIVE FUNCTIONALS, STATES AND REPRESENTATIONS of a unital involutive
;;; Banach algebra: F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf),
;;; chapter 4 (Definitions 4.1, 4.17, 4.19, 4.22, formula (86)) and Definition 1.57.
;;; DEFINITIONS ONLY: no proof, no support, no axiom other than what def-predicate, def-functoid and
;;; def-by-nn-recursion install by their own mechanism.
;;; Agent BA-1111-B, wave 2026-11-11.  Destination: structure-library/ba-rep-vocab.scm.
;;; Library: operator-algebras.
;;; Load window: after structure-library/ba-vocab (IS-CC-LINEAR-ON, IS-STAR-HOM, the slot layout)
;;; and structure-library/ba-ops-vocab (BH-ALGEBRA, BOUNDED-OPS); both load before ~1700.
;;;
;;; THE USER'S DECISIONS (2026-11-09, BA-MAP D1-D3): complex scalars; unital with ||1|| = 1; a
;;; representation is a unital *-homomorphism into L(H) on a complex Hilbert space, with NO continuity
;;; in the definition (continuity is Corollary 4.12).  A representation is the pair (v, pi); the Hilbert
;;; space v is a PARAMETER, never a class quantification.
;;;
;;; "phi(a* a) >= 0" for a complex value is written as two conjuncts, `phi(a* a) in RR' and
;;; `0 <= phi(a* a)', as COMPLEX-INNER-PRODUCT-SPACE writes the positivity of <x, x>.
;;;
;;; Names: VEC-FUNCTIONAL is taken (ba-optop-vocab: T |-> <T x | y> on L(H)); the functional f_(pi, xi)
;;; of formula (86) is REP-FUNCTIONAL.  Binders g4*_ are used by no other file.

;;; Definition 4.1: phi is a positive linear functional
(def-predicate 'IS-POSITIVE-LF '(g4a_ g4f_)
  '(AND (IS-CC-LINEAR-ON g4a_ g4f_)
        (FORALL g4x_ (IMPLIES (IN g4x_ (VEC g4a_))
          (AND (IN (g4f_ ((VMUL g4a_) ((VSTAR g4a_) g4x_) g4x_)) RR)
               (<= 0 (g4f_ ((VMUL g4a_) ((VSTAR g4a_) g4x_) g4x_))))))))

;;; Definition 4.1: the states, Sigma(A)
(def-functoid 'STATES '(g4a_)
  '(SEP g4f_ (FUN (VEC g4a_) CC) (AND (IS-POSITIVE-LF g4a_ g4f_) (= (g4f_ (VONE g4a_)) 1))))

;;; Definition 4.17: psi <= phi iff psi(x* x) <= phi(x* x) for every x
(def-predicate 'FUNCTIONAL-LE '(g4a_ g4g_ g4f_)
  '(FORALL g4x_ (IMPLIES (IN g4x_ (VEC g4a_))
     (<= (g4g_ ((VMUL g4a_) ((VSTAR g4a_) g4x_) g4x_)) (g4f_ ((VMUL g4a_) ((VSTAR g4a_) g4x_) g4x_))))))

;;; Definition 4.22: a pure state
(def-predicate 'IS-PURE-STATE '(g4a_ g4f_)
  '(AND (IN g4f_ (STATES g4a_))
        (FORALL g4g_ (IMPLIES (IS-POSITIVE-LF g4a_ g4g_) (IMPLIES (FUNCTIONAL-LE g4a_ g4g_ g4f_)
          (FORSOME g4l_ (AND (IN g4l_ RR) (AND (<= 0 g4l_) (AND (<= g4l_ 1)
            (FORALL g4x_ (IMPLIES (IN g4x_ (VEC g4a_)) (= (g4g_ g4x_) (* g4l_ (g4f_ g4x_))))))))))))))

;;; Definition 1.57 (decision D3): a representation of a on the Hilbert space v
(def-predicate 'IS-REPRESENTATION '(g4a_ g4v_ g4p_)
  '(AND (IS-HILBERT-SPACE g4v_) (IS-STAR-HOM g4a_ (BH-ALGEBRA g4v_) g4p_)))

;;; formula (86): f_(pi, xi)(x) = <pi(x) xi | xi>
(def-functoid 'REP-FUNCTIONAL '(g4a_ g4v_ g4p_ g4e_)
  '(VNB-LAMBDA g4x_ (VEC g4a_) ((IP g4v_) ((g4p_ g4x_) g4e_) g4e_)))

;;; the orbit pi(A) xi, and a cyclic vector: pi(A) xi is dense
(def-functoid 'REP-ORBIT '(g4a_ g4v_ g4p_ g4e_)
  '(SEP g4y_ (VEC g4v_) (FORSOME g4x_ (AND (IN g4x_ (VEC g4a_)) (= g4y_ ((g4p_ g4x_) g4e_))))))
(def-predicate 'IS-CYCLIC-VECTOR-REP '(g4a_ g4v_ g4p_ g4e_)
  '(AND (IN g4e_ (VEC g4v_))
        (= (CLOSURE (IP-METRIC-SPACE g4v_) (REP-ORBIT g4a_ g4v_ g4p_ g4e_)) (VEC g4v_))))

;;; Definition 4.19: irreducible -- the only closed invariant subspaces are {0} and H
(def-predicate 'IS-INVARIANT-SUBSPACE-REP '(g4a_ g4v_ g4p_ g4k_)
  '(AND (IS-SUBMODULE g4v_ g4k_)
   (AND (IS-CLOSED (IP-METRIC-SPACE g4v_) g4k_)
        (FORALL g4x_ (IMPLIES (IN g4x_ (VEC g4a_)) (FORALL g4y_ (IMPLIES (IN g4y_ g4k_)
          (IN ((g4p_ g4x_) g4y_) g4k_))))))))
(def-predicate 'IS-IRREDUCIBLE-REP '(g4a_ g4v_ g4p_)
  '(AND (IS-REPRESENTATION g4a_ g4v_ g4p_)
        (FORALL g4k_ (IMPLIES (IS-INVARIANT-SUBSPACE-REP g4a_ g4v_ g4p_ g4k_)
          (OR (= g4k_ (VEC g4v_)) (= g4k_ (MAKE-SET (LIST (VZERO g4v_)))))))))

;;; the iteration z_0 = 0, z_(n+1) = (y + z_n^2) / 2 whose limit z gives (1 - z)^2 = 1 - y for
;;; ||y|| < 1 (the square root used in the proof of Proposition 4.7, in place of Proposition 1.33's
;;; binomial series)
(def-by-nn-recursion 'HALF-SQ-ITER '(g4a_ g4y_)
  '(VZERO g4a_)
  '(g4n_ g4w_)
  '((ACT g4a_) 1/2 ((VADD g4a_) g4y_ ((VMUL g4a_) g4w_ g4w_))))

;;; Notation
(notation! 'IS-POSITIVE-LF 'kind 'predicate 'arity 2 'english "$2 is a positive linear functional on $1")
(notation! 'STATES 'kind 'functoid 'arity 1 'english "the states of $1" 'tex "\\Sigma({$1})")
(notation! 'FUNCTIONAL-LE 'kind 'predicate 'arity 3 'english "$2 <= $3 as functionals on $1")
(notation! 'IS-PURE-STATE 'kind 'predicate 'arity 2 'english "$2 is a pure state of $1")
(notation! 'IS-REPRESENTATION 'kind 'predicate 'arity 3 'english "$3 is a representation of $1 on $2")
(notation! 'REP-FUNCTIONAL 'kind 'functoid 'arity 4 'english "the functional x |-> <$3(x) $4 | $4>" 'tex "f_{{$3},{$4}}")
(notation! 'REP-ORBIT 'kind 'functoid 'arity 4 'english "the orbit $3($1) $4")
(notation! 'IS-CYCLIC-VECTOR-REP 'kind 'predicate 'arity 4 'english "$4 is a cyclic vector of $3")
(notation! 'IS-INVARIANT-SUBSPACE-REP 'kind 'predicate 'arity 4 'english "$4 is a closed subspace invariant under $3")
(notation! 'IS-IRREDUCIBLE-REP 'kind 'predicate 'arity 3 'english "$3 is an irreducible representation of $1 on $2")
(notation! 'HALF-SQ-ITER 'kind 'functoid 'arity 3 'english "the n-th square-root iterate of $2")
