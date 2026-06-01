;;; theorem-library/union-empty-left.scm
;;;
;;; union-empty-left:  EMPTY-SET union A = A for A a set.  Standard
;;; set-theoretic identity.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'union-empty-left
  '(FORALL A (IMPLIES (IN A SET) (= (UNION EMPTY-SET A) A))))
