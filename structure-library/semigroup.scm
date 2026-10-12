;;; semigroup.scm -- SEMIGROUP structure
;;;
;;; Carrier CARR, binary operation OPR.
;;; Accessor indices: CARR -> 1, OPR -> 2.

(declare-structure SEMIGROUP
  (carriers CARR)
  (op OPR (CARTESIAN CARR CARR) CARR)
  (property is-associative OPR CARR))

;;; forall s. IS-SEMIGROUP(s) => forall a,b,c in CARR(s). (a*b)*c = a*(b*c)
;;; semigroup-assoc RAKE-ASM-1 2026-10-12: PROVEN in theorem-library/rake-asm-1.scm under this name; the assumption is retired.

;;; Notation -- read by wff->english / the proof reader (operators.scm).
(notation! 'IS-SEMIGROUP            'noun "semigroup" 'article "a")
