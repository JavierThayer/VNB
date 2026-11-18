;;; ba-gns2-vocab.scm -- THE GNS CONSTRUCTION ON THE HILBERT COMPLETION and THE RADICAL:
;;; F. J. Thayer, "Banach Algebras and Applications" (docs/BanachAlgebras.pdf), Theorem 4.13 and
;;; Definition 4.25.  Agent BA-1117-GNS2, wave 2026-11-17.
;;; Destination: structure-library/ba-gns2-vocab.scm.  Library: operator-algebras.
;;; DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Load window: after structure-library/ba-gns-vocab (GNS-MODULE, GNS-FORM, GNS-OP, GNS-VECTOR),
;;; structure-library/hilbert-completion-vocab (HILBERT-COMPLETION, HC-EMBED, FORM-MS),
;;; structure-library/metric-completion (CAUCHY-SETOID, CSEQ), structure-library/ba-rep-vocab
;;; (IS-REPRESENTATION) and structure-library/ba-ops-vocab (BOP-ZERO).
;;;
;;;   SEQ-MAP(t, f)            the sequence n |-> t(f(n))
;;;   COMPLETION-LIFT(m, t)    the map [f] |-> [t o f] on the classes of Cauchy sequences of the
;;;                            metric space m: the completion of a Lipschitz map t of m into itself
;;;   GNS-HMOD(a, phi)         A / N_phi as a complex module (the quotient module of GNS-PRE)
;;;   GNS-HFORM(a, phi)        the inner product it carries (GNS-PRE = MODULE-WITH-FORM of the two)
;;;   GNS-SPACE(a, phi)        H_phi, the Hilbert completion of the pre-Hilbert space A / N_phi
;;;   GNS-REP(a, phi)          x |-> pi(x), the completion lift of the pre-Hilbert operator GNS-OP
;;;   GNS-XI(a, phi)           xi, the image in H_phi of the class of 1
;;;   RADICAL(a)               Definition 4.25: the x with pi(x) = 0 for every representation
;;;                            (v, pi) of a (decision D3: the Hilbert space v is a variable of the
;;;                            formula, so "every representation" is a quantification over sets)
;;;   IS-EXTREME-STATE(a, phi) phi is an extreme point of the state space Sigma(A): a state that is
;;;                            not a proper convex combination theta psi + (1 - theta) rho of two other
;;;                            states (finding F8: Sigma(A) is a set of functions on A, carried by no
;;;                            vector-space structure of the tree, so IS-EXTREME-POINT(m, K, x) has no m;
;;;                            the convex combination is written pointwise, as in ba4-states)
;;;   CDUAL-WEAK-STAR-TOP(a)   the w<A*, A> topology on the complex dual CDUAL-VEC(a): the topology of
;;;                            pointwise convergence, induced from the product CC^A (as GELFAND-SPACE
;;;                            is, ba-vocab)
;;;   RFN-MODULE(u)            the functions u -> CC as a REAL vector space, pointwise operations (the
;;;                            module Krein-Milman needs: KM is stated for real locally convex spaces)
;;;   EVAL-SEMINORMS(u)        y |-> (f |-> |f(y)|), y in u: the evaluation seminorms
;;;   RFN-TOP(u)               the locally convex topology they define: pointwise convergence
;;; Binders g4h*_, used by no other file.

(def-functoid 'SEQ-MAP '(g4ht_ g4hf_)
  '(VNB-LAMBDA g4hn_ NN (g4ht_ (g4hf_ g4hn_))))

(def-functoid 'COMPLETION-LIFT '(g4hm_ g4ht_)
  '(DESCEND (CAUCHY-SETOID g4hm_)
     (VNB-LAMBDA g4hf_ (CSEQ g4hm_) (CLASS (CAUCHY-SETOID g4hm_) (SEQ-MAP g4ht_ g4hf_)))))

(def-functoid 'GNS-HMOD '(g4ha_ g4hp_)
  '(QUOTIENT-MODULE (GNS-MODULE g4ha_) (FORM-NULL (GNS-MODULE g4ha_) (GNS-FORM g4ha_ g4hp_))))
(def-functoid 'GNS-HFORM '(g4ha_ g4hp_)
  '(FORM-QIP (GNS-MODULE g4ha_) (GNS-FORM g4ha_ g4hp_)))
(def-functoid 'GNS-SPACE '(g4ha_ g4hp_)
  '(HILBERT-COMPLETION (GNS-HMOD g4ha_ g4hp_) (GNS-HFORM g4ha_ g4hp_)))
(def-functoid 'GNS-REP '(g4ha_ g4hp_)
  '(VNB-LAMBDA g4hx_ (VEC g4ha_)
     (COMPLETION-LIFT (FORM-MS (GNS-HMOD g4ha_ g4hp_) (GNS-HFORM g4ha_ g4hp_)) (GNS-OP g4ha_ g4hp_ g4hx_))))
(def-functoid 'GNS-XI '(g4ha_ g4hp_)
  '((HC-EMBED (GNS-HMOD g4ha_ g4hp_) (GNS-HFORM g4ha_ g4hp_)) (GNS-VECTOR g4ha_ g4hp_)))

;;; Corollary 4.9: the weak* topology on A*
(def-functoid 'CDUAL-WEAK-STAR-TOP '(g4ha_)
  '(SUBSPACE-TOP (TPRODUCT-TOP (VEC g4ha_) (VNB-LAMBDA bgx_ (VEC g4ha_) (METRIC-TOP CC-MS))) (CDUAL-VEC g4ha_)))

;;; Proposition 4.24 (Krein-Milman applied to Sigma(A)): the real space of functions A -> CC, pointwise
(def-functoid 'RFN-MODULE '(g4hu_)
  '(LIST (NORMED-FIELD-AS-COMMUTATIVE-RING RR-NORMED-FIELD) (FUN g4hu_ CC)
         (VNB-LAMBDA (LIST g4hf_ g4hg_) (CARTESIAN (FUN g4hu_ CC) (FUN g4hu_ CC))
           (VNB-LAMBDA g4hy_ g4hu_ (+ (g4hf_ g4hy_) (g4hg_ g4hy_))))
         (VNB-LAMBDA g4hy_ g4hu_ 0)
         (VNB-LAMBDA g4hf_ (FUN g4hu_ CC) (VNB-LAMBDA g4hy_ g4hu_ (- (g4hf_ g4hy_))))
         (VNB-LAMBDA (LIST g4hr_ g4hf_) (CARTESIAN RR (FUN g4hu_ CC)) (VNB-LAMBDA g4hy_ g4hu_ (* g4hr_ (g4hf_ g4hy_))))))
(def-functoid 'EVAL-SEMINORMS '(g4hu_)
  '(VNB-LAMBDA g4hy_ g4hu_ (VNB-LAMBDA g4hf_ (FUN g4hu_ CC) (magnitude (g4hf_ g4hy_)))))
(def-functoid 'RFN-TOP '(g4hu_)
  '(SEMINORM-TOP (RFN-MODULE g4hu_) g4hu_ (EVAL-SEMINORMS g4hu_)))

;;; Proposition 4.24: an extreme point of Sigma(A)
(def-predicate 'IS-EXTREME-STATE '(g4ha_ g4hp_)
  '(AND (IN g4hp_ (STATES g4ha_))
        (FORALL g4hg_ (IMPLIES (IN g4hg_ (STATES g4ha_)) (FORALL g4hh_ (IMPLIES (IN g4hh_ (STATES g4ha_))
          (FORALL g4hr_ (IMPLIES (IN g4hr_ RR) (IMPLIES (< 0 g4hr_) (IMPLIES (< g4hr_ 1)
            (IMPLIES (FORALL g4hy_ (IMPLIES (IN g4hy_ (VEC g4ha_))
                       (= (g4hp_ g4hy_) (+ (* g4hr_ (g4hg_ g4hy_)) (* (- 1 g4hr_) (g4hh_ g4hy_))))))
              (FORALL g4hz_ (IMPLIES (IN g4hz_ (VEC g4ha_))
                (AND (= (g4hg_ g4hz_) (g4hp_ g4hz_)) (= (g4hh_ g4hz_) (g4hp_ g4hz_))))))))))))))))

;;; Definition 4.25: the radical
(def-functoid 'RADICAL '(g4ha_)
  '(SEP g4hx_ (VEC g4ha_)
     (FORALL g4hv_ (FORALL g4hq_ (IMPLIES (IS-REPRESENTATION g4ha_ g4hv_ g4hq_)
       (= (g4hq_ g4hx_) (BOP-ZERO g4hv_ g4hv_)))))))

(notation! 'SEQ-MAP 'kind 'functoid 'arity 2 'english "the sequence $1 o $2")
(notation! 'COMPLETION-LIFT 'kind 'functoid 'arity 2 'english "the extension of $2 to the completion of $1")
(notation! 'GNS-HMOD 'kind 'functoid 'arity 2 'english "the quotient module of the GNS pre-Hilbert space of $2")
(notation! 'GNS-HFORM 'kind 'functoid 'arity 2 'english "the inner product of the GNS pre-Hilbert space of $2")
(notation! 'GNS-SPACE 'kind 'functoid 'arity 2 'english "the GNS Hilbert space of $2" 'tex "H_{$2}")
(notation! 'GNS-REP 'kind 'functoid 'arity 2 'english "the GNS representation of $2" 'tex "\\pi_{$2}")
(notation! 'GNS-XI 'kind 'functoid 'arity 2 'english "the GNS cyclic vector of $2" 'tex "\\xi_{$2}")
(notation! 'CDUAL-WEAK-STAR-TOP 'kind 'functoid 'arity 1 'english "the weak* topology on the dual of $1")
(notation! 'RFN-MODULE 'kind 'functoid 'arity 1 'english "the real vector space of the complex functions on $1")
(notation! 'EVAL-SEMINORMS 'kind 'functoid 'arity 1 'english "the evaluation seminorms on the complex functions on $1")
(notation! 'RFN-TOP 'kind 'functoid 'arity 1 'english "the topology of pointwise convergence on the complex functions on $1")
(notation! 'IS-EXTREME-STATE 'kind 'predicate 'arity 2 'english "$2 is an extreme point of the state space of $1")
(notation! 'RADICAL 'kind 'functoid 'arity 1 'english "the radical of $1" 'tex "\\sqrt{$1}")
