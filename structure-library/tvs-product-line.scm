;;; prod-vocab.scm -- THE PRODUCT E x R OF A REAL MODULE AND THE REALS, AND THE PRODUCT TOPOLOGY
;;; (definitions only).  Agent TVS-NEXT (worker-08), 2026-10-26.
;;; DESTINATION: structure-library/tvs-product-line.scm.  Library: analysis.
;;;
;;;   PROD-RMOD(m)          the module E x R: pairs [x, a] with x in VEC(m), a in RR, componentwise
;;;                         addition, zero [0, 0], negation, and r.[x, a] = [r.x, r a].  It is a module
;;;                         when SCAL(m) is the real scalar ring (prod-rmod-is-module).
;;;   PT-BOX(t, v, c, e)    the "box" v x (c - e, c + e) inside CARTESIAN(PTS t, RR).
;;;   IS-PT-OPEN(t, u)      u is a set of pairs containing a box around each of its points.
;;;   PROD-TOP(t)           the product topology of t and the |.|-topology of R, by the boxes.
;;;
;;; topological-vector-space.pdf uses E x R in Prop 2.35 and Cor 2.36 without definition; the tree
;;; had no binary product of modules or of topological spaces (PRODUCT2-MS is metric only).
;;; Binders pva_ pvb_ pvc_ pvr_ ptz_ ptw_ ptv_ pte_ ptu_ are used by nothing else.

(def-functoid 'PV-VADD '(m)
  '(VNB-LAMBDA (LIST pva_ pvb_) (CARTESIAN (CARTESIAN (VEC m) RR) (CARTESIAN (VEC m) RR))
     (LIST ((VADD m) (NTH 1 pva_) (NTH 1 pvb_)) (+ (NTH 2 pva_) (NTH 2 pvb_)))))
(def-functoid 'PV-VNEG '(m)
  '(VNB-LAMBDA pvc_ (CARTESIAN (VEC m) RR) (LIST ((VNEG m) (NTH 1 pvc_)) (- (NTH 2 pvc_)))))
(def-functoid 'PV-ACT '(m)
  '(VNB-LAMBDA (LIST pvr_ pvc_) (CARTESIAN (CARR (SCAL m)) (CARTESIAN (VEC m) RR))
     (LIST ((ACT m) pvr_ (NTH 1 pvc_)) (* pvr_ (NTH 2 pvc_)))))
(def-functoid 'PROD-RMOD '(m)
  '(LIST (SCAL m) (CARTESIAN (VEC m) RR) (PV-VADD m) (LIST (VZERO m) 0) (PV-VNEG m) (PV-ACT m)))

(def-functoid 'PT-BOX '(t v c e)
  '(SEP ptz_ (CARTESIAN (PTS t) RR) (AND (IN (NTH 1 ptz_) v) (< (abs (- (NTH 2 ptz_) c)) e))))
(def-predicate 'IS-PT-OPEN '(t u)
  '(AND (SUBSET u (CARTESIAN (PTS t) RR))
        (FORALL ptw_ (IMPLIES (IN ptw_ u)
          (FORSOME ptv_ (AND (IN ptv_ (OPENS t)) (AND (IN (NTH 1 ptw_) ptv_)
            (FORSOME pte_ (AND (POS-RR pte_) (SUBSET (PT-BOX t ptv_ (NTH 2 ptw_) pte_) u))))))))))
(def-functoid 'PROD-TOP '(t)
  '(LIST (CARTESIAN (PTS t) RR) (SEP ptu_ (POWER (CARTESIAN (PTS t) RR)) (IS-PT-OPEN t ptu_))))

(notation! 'PV-VADD 'kind 'functoid 'arity 1 'english "the componentwise addition of $1 x R")
(notation! 'PV-VNEG 'kind 'functoid 'arity 1 'english "the componentwise negation of $1 x R")
(notation! 'PV-ACT 'kind 'functoid 'arity 1 'english "the componentwise scalar action of $1 x R")
(notation! 'PROD-RMOD 'kind 'functoid 'arity 1 'english "the module $1 x R")
(notation! 'PT-BOX 'kind 'functoid 'arity 4 'english "the box $2 x ($3 - $4, $3 + $4)")
(notation! 'IS-PT-OPEN 'kind 'predicate 'arity 2 'english "$2 is open in the product of $1 and R")
(notation! 'PROD-TOP 'kind 'functoid 'arity 1 'english "the product topology of $1 and R")

;;; The strict epigraph of Prop 2.35 (IS-CONVEX-FUNCTIONAL, Def 2.34, is structure-library/convex-functional.scm).
;;; Binder sepw_ is used by nothing else.
(def-functoid 'STRICT-EPIGRAPH '(m p)
  '(SEP sepw_ (CARTESIAN (VEC m) RR) (< (p (NTH 1 sepw_)) (NTH 2 sepw_))))
(notation! 'STRICT-EPIGRAPH 'kind 'functoid 'arity 2 'english "the strict epigraph of $2")
