;;; ring-pow-vocab.scm -- wave of 2026-11-09/10 (agent CCR-1109-E), wired 2026-11-10 from scratchpad/ccr1109e/ring-pow-vocab.scm.
;;; Library: linear-algebra.

;;; ring-pow-vocab.scm -- the free module R^n over a ring R, its unit vectors and the coefficient row
;;; of a vector (CCR-1109-E, 2026-11-09).  DEFINITIONS ONLY: destination structure-library/ring-pow-vocab.scm.
;;; The laws are in theorem-library/ring-pow.scm.
;;;
;;; The generic form of la-z4-vocab's ZZ-POW / ZZ-UNITS / ZZ-ROW (LA-Z4, 2026-10-24): ZZ-POW(n) is the
;;; instance RING-POW(ZZ-RING, n), and K^n for a normed field K is RING-POW(V, n) with V the ring view
;;; NORMED-FIELD-AS-COMMUTATIVE-RING(K).
;;;
;;;   RING-POW(R, n)    R^n: the direct sum of n copies of R as a module over itself
;;;                     (RING-AS-MODULE(R)); its vectors are the functions x on [1, n] with values in CARR R.
;;;   RING-UNITS(R, n)  the column of the unit vectors e_1, ..., e_n of R^n; e_k is the function
;;;                     t |-> (UNITROW(R, n, k))_{1t}, i.e. ONE(R) at k and ZERO(R) elsewhere.
;;;   RING-ROW(R, n, x) the coefficient row (x(1), ..., x(n)) of a vector x of R^n.
;;;
;;; Binders rqpi_ rqut_ rqua_ rqub_ rqra_ rqrb_ -- names no predicate body, statement or driver uses
;;; elsewhere.  Needs: structure-library/la-z3-vocab (DIRECT-SUM, RING-AS-MODULE), matrix (MATOF, ENTRY,
;;; UNITROW).  LOAD WINDOW: after la-z3-vocab and matrix; before theorem-library/ring-pow.
;;; Library: linear-algebra (as la-z4-vocab).  No axiom, support or stamp.

(def-functoid 'RING-POW '(R n)
  '(DIRECT-SUM R n (VNB-LAMBDA rqpi_ (INTERVAL 1 n) (RING-AS-MODULE R))))

(def-functoid 'RING-UNITS '(R n)
  '(MATOF n 1 (VNB-LAMBDA (LIST rqua_ rqub_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 1))
                (VNB-LAMBDA rqut_ (INTERVAL 1 n) (ENTRY (UNITROW R n rqua_) 1 rqut_)))))

(def-functoid 'RING-ROW '(R n x)
  '(MATOF 1 n (VNB-LAMBDA (LIST rqra_ rqrb_) (CARTESIAN (INTERVAL 1 1) (INTERVAL 1 n)) (x rqrb_))))

(notation! 'RING-POW 'kind 'functoid 'arity 2
           'english "the free module $1^$2")
(notation! 'RING-UNITS 'kind 'functoid 'arity 2
           'english "the unit vectors of $1^$2")
(notation! 'RING-ROW 'kind 'functoid 'arity 3
           'english "the coefficient row of $3 in $1^$2")
