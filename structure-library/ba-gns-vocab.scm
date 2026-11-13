;;; ba-gns-vocab.scm -- THE GNS CONSTRUCTION, the pre-Hilbert stage: BanachAlgebras.pdf Theorem 4.13 and
;;; its proof.  Agent BA-1111-B, 2026-11-11.  Destination: structure-library/ba-gns-vocab.scm.
;;; Library: operator-algebras.  DEFINITIONS ONLY: no proof, no support, no axiom.
;;; Load window: after structure-library/ba-rep-vocab and structure-library/ipf-vocab (BA-1111-A2:
;;; FORM-NULL, FORM-QUOTIENT), structure-library/la-z3-vocab (QMOD-SETOID), ba-vocab (UBA-AS-MODULE).
;;;
;;; phi a positive functional on the unital involutive Banach algebra a.
;;;   GNS-MODULE(a)          a as a complex module (the UBA-AS-MODULE view of UIBA-AS-UBA(a))
;;;   GNS-FORM(a, phi)       <x | y> = phi(y* x), a form on that module
;;;   GNS-SETOID(a, phi)     congruence modulo the null space of the form
;;;   GNS-PRE(a, phi)        the quotient by the null space with the induced inner product: the
;;;                          pre-Hilbert space H~ / H~_0 of the proof of Theorem 4.13
;;;   GNS-VECTOR(a, phi)     the class of 1, the cyclic vector
;;;   GNS-OP(a, phi, x)      the operator [b] |-> [x b] on the classes
;;; Binders g4g*_ (g4gx_ g4gy_ g4gb_), used by no other file.

(def-functoid 'GNS-MODULE '(g4ga_) '(UBA-AS-MODULE (UIBA-AS-UBA g4ga_)))
(def-functoid 'GNS-FORM '(g4ga_ g4gf_)
  '(VNB-LAMBDA (LIST g4gx_ g4gy_) (CARTESIAN (VEC g4ga_) (VEC g4ga_))
     (g4gf_ ((VMUL g4ga_) ((VSTAR g4ga_) g4gy_) g4gx_))))
(def-functoid 'GNS-SETOID '(g4ga_ g4gf_)
  '(QMOD-SETOID (GNS-MODULE g4ga_) (FORM-NULL (GNS-MODULE g4ga_) (GNS-FORM g4ga_ g4gf_))))
(def-functoid 'GNS-PRE '(g4ga_ g4gf_)
  '(FORM-QUOTIENT (GNS-MODULE g4ga_) (GNS-FORM g4ga_ g4gf_)))
(def-functoid 'GNS-VECTOR '(g4ga_ g4gf_) '(CLASS (GNS-SETOID g4ga_ g4gf_) (VONE g4ga_)))
(def-functoid 'GNS-OP '(g4ga_ g4gf_ g4gx_)
  '(DESCEND (GNS-SETOID g4ga_ g4gf_)
     (VNB-LAMBDA g4gb_ (VEC g4ga_) (CLASS (GNS-SETOID g4ga_ g4gf_) ((VMUL g4ga_) g4gx_ g4gb_)))))

(notation! 'GNS-MODULE 'kind 'functoid 'arity 1 'english "$1 as a complex module")
(notation! 'GNS-FORM 'kind 'functoid 'arity 2 'english "the form (x, y) |-> $2(y* x) on $1")
(notation! 'GNS-SETOID 'kind 'functoid 'arity 2 'english "congruence modulo the null space of $2")
(notation! 'GNS-PRE 'kind 'functoid 'arity 2 'english "the GNS pre-Hilbert space of $2")
(notation! 'GNS-VECTOR 'kind 'functoid 'arity 2 'english "the GNS cyclic vector of $2")
(notation! 'GNS-OP 'kind 'functoid 'arity 3 'english "the GNS operator of $3")
