;;; transpose.scm -- the TRANSPOSE of a matrix (batch 32, 2026-09-25; the user's
;;; decision of 2026-09-25, on batch 25-C's proposal).
;;;
;;; THE SOURCE.  The user's linear-algebra notes (docs: linear-algebra.tex, the
;;; definition after the matrix product): "The transpose A^t of an m x n matrix A
;;; is the n x m matrix D = {d_ij} given by d_ij = a_ji."  Hoffman-Kunze ch. 5
;;; uses the same entrywise definition.
;;;
;;; THE DEFINITION.  TRANSPOSE(A, m, n) is the n-by-m tabulation (MATOF) whose
;;; (i, j) entry is ENTRY(A, j, i).  The sizes are explicit arguments, as in
;;; BLOCK(P, k, l) and MINOR(S, r, c, n): the tabulation is stated at the literal
;;; n, m, so entry-of-matof reads its entries without recovering a dimension from
;;; SIZE(A).  For A in MAT(m, n, X) it is an element of MAT(n, m, X)
;;; (transpose-in-mat) with ENTRY(TRANSPOSE(A, m, n), i, j) = ENTRY(A, j, i) for i
;;; in [1, n], j in [1, m] (transpose-entry); both are PROVEN in
;;; theorem-library/det-transpose.scm, which also proves the involution, the
;;; transpose of the identity and of a product, and det(A^t) = det A.
;;;
;;; SCOPE.  This is the MATRIX transpose, a construction on tables of entries.
;;; The adjoint of an operator on a Hilbert space will be defined invariantly,
;;; elsewhere; nothing here is meant to serve for it.
;;;
;;; The tabulating lambda binds tri_ / trj_, names no predicate body, statement
;;; or driver uses (a binder that something else binds is renamed by the
;;; capture-avoiding substitution and later lookups miss silently).
;;;
;;; Needs: structure-library/matrix (MATOF, ENTRY, INTERVAL, CARTESIAN).
;;; No axiom, support or stamp.

(def-functoid 'TRANSPOSE '(A m n)
  '(MATOF n m (VNB-LAMBDA (LIST tri_ trj_) (CARTESIAN (INTERVAL 1 n) (INTERVAL 1 m))
     (ENTRY A trj_ tri_))))

(notation! 'TRANSPOSE 'kind 'functoid 'arity 3 'english "$1^t")
