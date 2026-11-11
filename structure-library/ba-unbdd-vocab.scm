;;; ba-unbdd-vocab.scm -- wave of 2026-11-09/10 (agent BA-G1), wired 2026-11-10 from scratchpad/bag1-1109/ba-unbdd-vocab.scm.
;;; Library: operator-algebras.

;;; ba-unbdd-vocab.scm -- UNBOUNDED OPERATORS AS GRAPHS in H (+) H: domain, range, functional and
;;; closed graphs, the adjoint of a graph (Def 3.2), the unitary J, the inverse graph, symmetric,
;;; self-adjoint, isometric and unitary graphs (Def 3.6), the Cayley transform (60), composition of
;;; graphs, and quadratic forms (Def 3.13, Prop 3.16, 3.17).
;;; F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf), chapter 3.
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Agent BA-G1, wave 2026-11-09.  Destination: structure-library/ba-unbdd-vocab.scm.
;;; Library: operator-algebras (BA-MAP-REPORT.md s.3.9).
;;; Load window: after structure-library/ba-ops-vocab (HSUM) and structure-library/hilbert-space
;;; (PERP, IP-METRIC-SPACE); both are named in no proof here.
;;;
;;; THE USER'S DECISION D4 (2026-11-09): an operator is its GRAPH, a subset of
;;; H x H = CARTESIAN(VEC v, VEC v), the carrier of the Hilbert direct sum HSUM(v, v)
;;; (ba-ops-vocab.scm).  A LINEAR graph is a submodule of HSUM(v, v); orthogonal complements and
;;; closures of graphs are taken in HSUM(v, v) and in its metric space.  A pair (eta, phi) of the
;;; notes is the literal list [eta, phi]; its components are NTH 1 and NTH 2.
;;;
;;; THE ADJOINT (Def 3.2, eq. (52)) is defined for ANY graph:
;;;   (eta, phi) in G*  <=>  <xi | phi> = <psi | eta> for all (xi, psi) in G.
;;; THE UNITARY J (eq. (53)), J(xi, eta) = (-eta, xi).  J(G) is written as the preimage
;;;   GRAPH-J(v, G) = { p in H x H : J^(-1) p in G },  J^(-1)(a, b) = (b, -a),
;;; which is the image J(G) since J is a bijection of H x H; no IMAGE term is needed.
;;; THE INVERSE GRAPH: G^(-1) = { (phi, eta) : (eta, phi) in G }.
;;; THE CAYLEY TRANSFORM (eq. (60)): C(G) = { (i eta + psi, -i eta + psi) : (eta, psi) in G }.
;;; A UNITARY graph is the graph of a unitary operator: a linear, isometric graph whose domain and
;;; range are all of H (an isometric linear graph is functional).
;;; DENSE domain / range: the tree's IS-DENSE of the metric space IP-METRIC-SPACE(v).
;;; CLOSED / CLOSABLE: closed in IP-METRIC-SPACE(HSUM(v, v)); closable when the closure is
;;; functional (the notes' "G-bar is the graph of an operator").
;;; A bounded operator T embeds by the tree's GRAPH-OF(VEC v, VEC v, T) (mb67-vocab.scm).
;;;
;;; QUADRATIC FORMS (Def 3.13).  A quadratic form is (dq, q): dq a dense subspace of H and q a
;;; sesquilinear form on dq (linear in the first argument, the notes' convention, conjugate
;;; symmetric -- the notes' "Q : V x V -> R" read as complex-valued Hermitian, which is what
;;; their Remark 3.14 and Q+ use).  Q+ (xi, eta) = Q(xi, eta) + <xi | eta>; FORM-PLUS-SPACE is the
;;; 7-tuple (CC ring view, dq, the operations of v, Q+) in COMPLEX-INNER-PRODUCT-SPACE's layout,
;;; the notes' H_Q+.  A positive form is CLOSED (the notes' sequence definition) when every
;;; H-convergent sequence of dq that is Q-Cauchy has its limit in dq with Q(x_n - x, x_n - x)
;;; -> 0.  FORM-OPERATOR(v, dq, q) is the graph of T_Q (eqs. (69), (70)):
;;;   { (eta, phi) : eta in dq, <xi | phi> = Q(xi, eta) for every xi in dq };
;;; by density of dq and Riesz this is the notes' domain clause "xi |-> Q(xi, eta) is
;;; H-continuous" with T_Q eta = phi.
;;;
;;; Binders ub*_ (ubp_ ubq_ ubx_ uby_ ubz_ ubn_ ube_ ubm_ ubk_), used by no other file.
;;; Parameters ubv_ (the space), ubg_ ubh_ (graphs), ubd_ (a form domain), ubf_ (a form).

;;; --------------------------------------------------------------------------------------------
;;; LINEAR GRAPHS, DOMAIN, RANGE, FUNCTIONAL GRAPHS
(def-predicate 'IS-LINEAR-GRAPH '(ubv_ ubg_)
  '(IS-SUBMODULE (HSUM ubv_ ubv_) ubg_))

(def-functoid 'GRAPH-DOM '(ubv_ ubg_)
  '(SEP ubx_ (VEC ubv_) (FORSOME uby_ (AND (IN uby_ (VEC ubv_)) (IN (LIST ubx_ uby_) ubg_)))))

(def-functoid 'GRAPH-RAN '(ubv_ ubg_)
  '(SEP uby_ (VEC ubv_) (FORSOME ubx_ (AND (IN ubx_ (VEC ubv_)) (IN (LIST ubx_ uby_) ubg_)))))

;;; G is the graph of a map: one value at each point of its domain
(def-predicate 'IS-FUNCTIONAL-GRAPH '(ubv_ ubg_)
  '(FORALL ubx_ (IMPLIES (IN ubx_ (VEC ubv_))
     (FORALL uby_ (IMPLIES (IN uby_ (VEC ubv_))
       (FORALL ubz_ (IMPLIES (IN ubz_ (VEC ubv_))
         (IMPLIES (IN (LIST ubx_ uby_) ubg_) (IMPLIES (IN (LIST ubx_ ubz_) ubg_) (= uby_ ubz_))))))))))

;;; --------------------------------------------------------------------------------------------
;;; THE ADJOINT, J, THE INVERSE GRAPH
(def-functoid 'GRAPH-ADJOINT '(ubv_ ubg_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_))
     (FORALL ubq_ (IMPLIES (IN ubq_ ubg_)
       (= ((IP ubv_) (NTH 1 ubq_) (NTH 2 ubp_)) ((IP ubv_) (NTH 2 ubq_) (NTH 1 ubp_)))))))

(def-functoid 'GRAPH-J '(ubv_ ubg_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_))
     (IN (LIST (NTH 2 ubp_) ((VNEG ubv_) (NTH 1 ubp_))) ubg_)))

(def-functoid 'GRAPH-INVERSE '(ubv_ ubg_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_)) (IN (LIST (NTH 2 ubp_) (NTH 1 ubp_)) ubg_)))

;;; --------------------------------------------------------------------------------------------
;;; CLOSED, CLOSABLE, DENSE
(def-functoid 'GRAPH-CLOSURE '(ubv_ ubg_)
  '(CLOSURE (IP-METRIC-SPACE (HSUM ubv_ ubv_)) ubg_))

(def-predicate 'IS-CLOSED-GRAPH '(ubv_ ubg_)
  '(IS-CLOSED (IP-METRIC-SPACE (HSUM ubv_ ubv_)) ubg_))

(def-predicate 'IS-CLOSABLE-GRAPH '(ubv_ ubg_)
  '(IS-FUNCTIONAL-GRAPH ubv_ (GRAPH-CLOSURE ubv_ ubg_)))

;;; --------------------------------------------------------------------------------------------
;;; SYMMETRIC, SELF-ADJOINT, ESSENTIALLY SELF-ADJOINT, ISOMETRIC, UNITARY (Def 3.6)
(def-predicate 'IS-SYMMETRIC-GRAPH '(ubv_ ubg_)
  '(SUBSET ubg_ (GRAPH-ADJOINT ubv_ ubg_)))

(def-predicate 'IS-SELF-ADJOINT-GRAPH '(ubv_ ubg_)
  '(= (GRAPH-ADJOINT ubv_ ubg_) ubg_))

(def-predicate 'IS-ESS-SELF-ADJOINT-GRAPH '(ubv_ ubg_)
  '(IS-SELF-ADJOINT-GRAPH ubv_ (GRAPH-CLOSURE ubv_ ubg_)))

(def-predicate 'IS-ISOMETRIC-GRAPH '(ubv_ ubg_)
  '(FORALL ubp_ (IMPLIES (IN ubp_ ubg_)
     (= (IP-NORM ubv_ (NTH 1 ubp_)) (IP-NORM ubv_ (NTH 2 ubp_))))))

(def-predicate 'IS-UNITARY-GRAPH '(ubv_ ubg_)
  '(AND (IS-LINEAR-GRAPH ubv_ ubg_)
   (AND (IS-ISOMETRIC-GRAPH ubv_ ubg_)
   (AND (= (GRAPH-DOM ubv_ ubg_) (VEC ubv_))
        (= (GRAPH-RAN ubv_ ubg_) (VEC ubv_))))))

;;; --------------------------------------------------------------------------------------------
;;; THE CAYLEY TRANSFORM (60) AND COMPOSITION
(def-functoid 'CAYLEY-GRAPH '(ubv_ ubg_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_))
     (FORSOME ubq_ (AND (IN ubq_ ubg_)
       (= ubp_ (LIST ((VADD ubv_) ((ACT ubv_) +i (NTH 1 ubq_)) (NTH 2 ubq_))
                     ((VADD ubv_) ((ACT ubv_) (- +i) (NTH 1 ubq_)) (NTH 2 ubq_))))))))

;;; G o H = { (x, z) : (x, y) in H and (y, z) in G for some y }
(def-functoid 'GRAPH-COMPOSE '(ubv_ ubg_ ubh_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_))
     (FORSOME uby_ (AND (IN uby_ (VEC ubv_))
       (AND (IN (LIST (NTH 1 ubp_) uby_) ubh_) (IN (LIST uby_ (NTH 2 ubp_)) ubg_))))))

;;; --------------------------------------------------------------------------------------------
;;; QUADRATIC FORMS (Def 3.13 and section 4)
(def-predicate 'IS-QUADRATIC-FORM '(ubv_ ubd_ ubf_)
  '(AND (IS-SUBMODULE ubv_ ubd_)
   (AND (IS-DENSE (IP-METRIC-SPACE ubv_) ubd_)
   (AND (IN ubf_ (FUN (CARTESIAN ubd_ ubd_) CC))
   (AND (FORALL ubx_ (IMPLIES (IN ubx_ ubd_) (FORALL uby_ (IMPLIES (IN uby_ ubd_) (FORALL ubz_ (IMPLIES (IN ubz_ ubd_) (= (ubf_ ((VADD ubv_) ubx_ uby_) ubz_) (+ (ubf_ ubx_ ubz_) (ubf_ uby_ ubz_)))))))))
   (AND (FORALL ubk_ (IMPLIES (IN ubk_ CC) (FORALL ubx_ (IMPLIES (IN ubx_ ubd_) (FORALL uby_ (IMPLIES (IN uby_ ubd_) (= (ubf_ ((ACT ubv_) ubk_ ubx_) uby_) (* ubk_ (ubf_ ubx_ uby_)))))))))
   (FORALL ubx_ (IMPLIES (IN ubx_ ubd_) (FORALL uby_ (IMPLIES (IN uby_ ubd_) (= (ubf_ uby_ ubx_) (conjugate (ubf_ ubx_ uby_)))))))))))))

(def-predicate 'IS-POSITIVE-FORM '(ubv_ ubd_ ubf_)
  '(AND (IS-QUADRATIC-FORM ubv_ ubd_ ubf_)
        (FORALL ubx_ (IMPLIES (IN ubx_ ubd_)
          (AND (IN (ubf_ ubx_ ubx_) RR) (<= 0 (ubf_ ubx_ ubx_)))))))

;;; Q+ (xi, eta) = Q(xi, eta) + <xi | eta>
(def-functoid 'FORM-PLUS '(ubv_ ubd_ ubf_)
  '(VNB-LAMBDA (LIST ubx_ uby_) (CARTESIAN ubd_ ubd_) (+ (ubf_ ubx_ uby_) ((IP ubv_) ubx_ uby_))))

;;; H_Q+: dom Q with the operations of H and the inner product Q+
(def-functoid 'FORM-PLUS-SPACE '(ubv_ ubd_ ubf_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING CC-NORMED-FIELD) ubd_
         (VNB-LAMBDA (LIST ubx_ uby_) (CARTESIAN ubd_ ubd_) ((VADD ubv_) ubx_ uby_))
         (VZERO ubv_)
         (VNB-LAMBDA ubx_ ubd_ ((VNEG ubv_) ubx_))
         (VNB-LAMBDA (LIST ubk_ ubx_) (CARTESIAN CC ubd_) ((ACT ubv_) ubk_ ubx_))
         (FORM-PLUS ubv_ ubd_ ubf_)))

;;; Q closed: x_n -> x in H with Q(x_n - x_m, x_n - x_m) -> 0 gives x in dom Q and
;;; Q(x_n - x, x_n - x) -> 0
(def-predicate 'IS-CLOSED-FORM '(ubv_ ubd_ ubf_)
  '(AND (IS-POSITIVE-FORM ubv_ ubd_ ubf_)
   (FORALL ubq_ (IMPLIES (IN ubq_ (FUN NN ubd_)) (FORALL ubx_ (IMPLIES (CONVERGES-TO (IP-METRIC-SPACE ubv_) ubq_ ubx_) (IMPLIES (FORALL ube_ (IMPLIES (POS-RR ube_) (FORSOME ubn_ (AND (IN ubn_ NN) (FORALL ubm_ (IMPLIES (IN ubm_ NN) (FORALL ubk_ (IMPLIES (IN ubk_ NN) (IMPLIES (<= ubn_ ubm_) (IMPLIES (<= ubn_ ubk_) (<= (magnitude (ubf_ ((VADD ubv_) (ubq_ ubm_) ((VNEG ubv_) (ubq_ ubk_))) ((VADD ubv_) (ubq_ ubm_) ((VNEG ubv_) (ubq_ ubk_))))) ube_))))))))))) (AND (IN ubx_ ubd_) (FORALL ube_ (IMPLIES (POS-RR ube_) (FORSOME ubn_ (AND (IN ubn_ NN) (FORALL ubm_ (IMPLIES (IN ubm_ NN) (IMPLIES (<= ubn_ ubm_) (<= (magnitude (ubf_ ((VADD ubv_) (ubq_ ubm_) ((VNEG ubv_) ubx_)) ((VADD ubv_) (ubq_ ubm_) ((VNEG ubv_) ubx_)))) ube_))))))))))))))))

;;; the graph of T_Q (eqs. (69), (70))
(def-functoid 'FORM-OPERATOR '(ubv_ ubd_ ubf_)
  '(SEP ubp_ (CARTESIAN (VEC ubv_) (VEC ubv_))
     (AND (IN (NTH 1 ubp_) ubd_)
          (FORALL ubx_ (IMPLIES (IN ubx_ ubd_)
            (= ((IP ubv_) ubx_ (NTH 2 ubp_)) (ubf_ ubx_ (NTH 1 ubp_))))))))

;;; --------------------------------------------------------------------------------------------
;;; Notation
(notation! 'IS-LINEAR-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a linear graph in $1 x $1")
(notation! 'GRAPH-DOM 'kind 'functoid 'arity 2 'english "the domain of the graph $2" 'tex "\\mathrm{dom}\\,{$2}")
(notation! 'GRAPH-RAN 'kind 'functoid 'arity 2 'english "the range of the graph $2" 'tex "\\mathrm{ran}\\,{$2}")
(notation! 'IS-FUNCTIONAL-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a functional graph")
(notation! 'GRAPH-ADJOINT 'kind 'functoid 'arity 2 'english "the adjoint of the graph $2" 'tex "{$2}^{*}")
(notation! 'GRAPH-J 'kind 'functoid 'arity 2 'english "the image of $2 under J" 'tex "J{$2}")
(notation! 'GRAPH-INVERSE 'kind 'functoid 'arity 2 'english "the inverse graph of $2" 'tex "{$2}^{-1}")
(notation! 'GRAPH-CLOSURE 'kind 'functoid 'arity 2 'english "the closure of the graph $2" 'tex "\\overline{$2}")
(notation! 'IS-CLOSED-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a closed graph")
(notation! 'IS-CLOSABLE-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a closable graph")
(notation! 'IS-SYMMETRIC-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a symmetric graph")
(notation! 'IS-SELF-ADJOINT-GRAPH 'kind 'predicate 'arity 2 'english "$2 is a self-adjoint graph")
(notation! 'IS-ESS-SELF-ADJOINT-GRAPH 'kind 'predicate 'arity 2 'english "$2 is an essentially self-adjoint graph")
(notation! 'IS-ISOMETRIC-GRAPH 'kind 'predicate 'arity 2 'english "$2 is an isometric graph")
(notation! 'IS-UNITARY-GRAPH 'kind 'predicate 'arity 2 'english "$2 is the graph of a unitary operator")
(notation! 'CAYLEY-GRAPH 'kind 'functoid 'arity 2 'english "the Cayley transform of $2" 'tex "C({$2})")
(notation! 'GRAPH-COMPOSE 'kind 'functoid 'arity 3 'english "the composite graph $2 $3" 'tex "{$2}{$3}")
(notation! 'IS-QUADRATIC-FORM 'kind 'predicate 'arity 3 'english "$3 is a quadratic form on $1 with domain $2")
(notation! 'IS-POSITIVE-FORM 'kind 'predicate 'arity 3 'english "$3 is a positive quadratic form on $1 with domain $2")
(notation! 'FORM-PLUS 'kind 'functoid 'arity 3 'english "the form $3 plus the inner product" 'tex "{$3}_{+}")
(notation! 'FORM-PLUS-SPACE 'kind 'functoid 'arity 3 'english "the space $2 with the inner product of $3 plus that of $1" 'tex "H_{{$3}+}")
(notation! 'IS-CLOSED-FORM 'kind 'predicate 'arity 3 'english "$3 is a closed positive quadratic form on $1 with domain $2")
(notation! 'FORM-OPERATOR 'kind 'functoid 'arity 3 'english "the operator of the form $3" 'tex "T_{$3}")
