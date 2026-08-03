;;; theorem-library/union-empty-left.scm
;;;
;;; union-empty-left:  EMPTY-SET union A = A for A a set.  Standard
;;; set-theoretic identity.
;;;
;;; PSS-promoted 2026-05-27 from proven-theorems.scm.  Original proof
;;; script archived in archive/proven-theorems-archive.scm.

(support 'union-empty-left
  '(FORALL A (IMPLIES (IN A SET) (= (UNION EMPTY-SET A) A))))

(warrant! 'union-empty-left 'informal
  "Mechanically proven before the 2026-05-27 PSS promotion; script archived at
   archive/proven-theorems-archive.scm (prove-and-install! 'union-empty-left).
   Extensionality: nothing is in EMPTY-SET, so membership in the union is
   membership in A.  Archive predates the E -> IDEN rename and the ==-sweep.")
