;;; basw-vocab.scm -- wave of 2026-11-09/10 (agent BA-SW), wired 2026-11-10 from scratchpad/basw-1109/basw-vocab.scm.
;;; Library: analysis.

;;; basw-vocab.scm -- the real continuous functions on a topological space.  DEFINITIONS ONLY.
;;; Agent BA-SW, wave 2026-11-09.  Destination: structure-library/basw-vocab.scm.  Library: analysis.
;;; Load window: after structure-library/top-space (METRIC-TOP, IS-HOM-TOP-SPACE) and the RR-MS
;;; instance; anywhere after structure-library/top-continuity.
;;;
;;;   RCONT(t)   {f in FUN(PTS t, RR) : f continuous from t to METRIC-TOP(RR-MS)}
;;;
;;; The complex twin is CCONT (ba-cx-vocab.scm, BA-1's file, operator-algebras); this one is in
;;; analysis because Stone-Weierstrass and Urysohn are general facts (BA-MAP-REPORT.md s.3.9).
;;; Binders rct_ rcf_, used by no other file.

(def-functoid 'RCONT '(rct_)
  '(SEP rcf_ (FUN (PTS rct_) RR) (IS-HOM-TOP-SPACE rct_ (METRIC-TOP RR-MS) rcf_)))
(notation! 'RCONT 'kind 'functoid 'arity 1 'english "the continuous real functions on $1"
           'tex "C_{\\mathbb{R}}({$1})")

;;; IS-RCONT-SUBALGEBRA(t, aa): aa is a set of continuous real functions on t containing the
;;; constants and closed under pointwise sums and products (a unital subalgebra of C_R(t): the
;;; scalar multiples are the products with constants).
(def-predicate 'IS-RCONT-SUBALGEBRA '(rst_ rsa_)
  '(AND (SUBSET rsa_ (RCONT rst_))
   (AND (FORALL rsc_ (IMPLIES (IN rsc_ RR) (IN (VNB-LAMBDA rsz_ (PTS rst_) rsc_) rsa_)))
   (AND (FORALL rsf_ (IMPLIES (IN rsf_ rsa_) (FORALL rsg_ (IMPLIES (IN rsg_ rsa_)
          (IN (VNB-LAMBDA rsz_ (PTS rst_) (+ (rsf_ rsz_) (rsg_ rsz_))) rsa_)))))
        (FORALL rsf_ (IMPLIES (IN rsf_ rsa_) (FORALL rsg_ (IMPLIES (IN rsg_ rsa_)
          (IN (VNB-LAMBDA rsz_ (PTS rst_) (* (rsf_ rsz_) (rsg_ rsz_))) rsa_)))))))))
(notation! 'IS-RCONT-SUBALGEBRA 'kind 'predicate 'arity 2
           'english "$2 is a unital subalgebra of the continuous real functions on $1")

;;; IS-POINT-SEPARATING(t, aa): for distinct points p, q of t some f in aa has f(p) /= f(q).
(def-predicate 'IS-POINT-SEPARATING '(rst_ rsa_)
  '(FORALL rsp_ (IMPLIES (IN rsp_ (PTS rst_)) (FORALL rsq_ (IMPLIES (IN rsq_ (PTS rst_))
     (IMPLIES (NOT (= rsp_ rsq_)) (FORSOME rsf_ (AND (IN rsf_ rsa_) (NOT (= (rsf_ rsp_) (rsf_ rsq_)))))))))))
(notation! 'IS-POINT-SEPARATING 'kind 'predicate 'arity 2 'english "$2 separates the points of $1")

;;; RCONT-CLOSURE(t, aa): the continuous real functions on t that are uniform limits of members
;;; of aa (the closure of aa in C_R(t) for the sup norm, written without the norm).
(def-functoid 'RCONT-CLOSURE '(rst_ rsa_)
  '(SEP rsh_ (RCONT rst_)
     (FORALL rse_ (IMPLIES (POS-RR rse_) (FORSOME rsg_ (AND (IN rsg_ rsa_)
       (FORALL rsy_ (IMPLIES (IN rsy_ (PTS rst_)) (< (abs (- (rsh_ rsy_) (rsg_ rsy_))) rse_)))))))))
(notation! 'RCONT-CLOSURE 'kind 'functoid 'arity 2 'english "the uniform closure of $2 in the continuous real functions on $1")

;;; IS-CCONT-STAR-SUBALGEBRA(t, aa): aa is a set of continuous complex functions on t (functions
;;; from PTS t into CC continuous into METRIC-TOP(CC-MS), written out so that the statement needs
;;; no operator-algebras vocabulary) containing the complex constants and closed under pointwise
;;; sums, products and complex conjugation: a unital self-adjoint subalgebra of C(t).
(def-predicate 'IS-CCONT-STAR-SUBALGEBRA '(rst_ rsa_)
  '(AND (FORALL csf_ (IMPLIES (IN csf_ rsa_) (AND (IN csf_ (FUN (PTS rst_) CC)) (IS-HOM-TOP-SPACE rst_ (METRIC-TOP CC-MS) csf_))))
   (AND (FORALL csc_ (IMPLIES (IN csc_ CC) (IN (VNB-LAMBDA rsz_ (PTS rst_) csc_) rsa_)))
   (AND (FORALL csf_ (IMPLIES (IN csf_ rsa_) (FORALL csg_ (IMPLIES (IN csg_ rsa_)
          (IN (VNB-LAMBDA rsz_ (PTS rst_) (+ (csf_ rsz_) (csg_ rsz_))) rsa_)))))
   (AND (FORALL csf_ (IMPLIES (IN csf_ rsa_) (FORALL csg_ (IMPLIES (IN csg_ rsa_)
          (IN (VNB-LAMBDA rsz_ (PTS rst_) (* (csf_ rsz_) (csg_ rsz_))) rsa_)))))
        (FORALL csf_ (IMPLIES (IN csf_ rsa_) (IN (VNB-LAMBDA rsz_ (PTS rst_) (conjugate (csf_ rsz_))) rsa_))))))))
(notation! 'IS-CCONT-STAR-SUBALGEBRA 'kind 'predicate 'arity 2
           'english "$2 is a unital self-adjoint subalgebra of the continuous complex functions on $1")
