;;; qag-vocab.scm -- WAVE 2 (2026-10-27..30), wired 2026-10-30 from scratchpad/ccrpr/qag-vocab.scm.
;;; Library: linear-algebra.

;;; qag-vocab.scm -- AN ABELIAN GROUP AS A ZZ-MODULE, AND THE QUOTIENT GROUP G/H (agent CCR-PRUEFER, 2026-10-29).
;;; DEFINITIONS ONLY; the laws are in theorem-library/qag-laws.scm.  Destination: structure-library/qag-vocab.scm.
;;; Library: algebra.  Load window: after zz-action (ZZ-ACT), la-z3-vocab (QUOTIENT-MODULE), views (MODULE-VECTOR-AG)
;;; and cg2-vocab (IS-SUBGROUP, GPOW); before theorem-library/qag-laws.
;;;
;;; ONE NAME PER NOTION.  The quotient of an abelian group by a subgroup is the quotient MODULE of the group read as a
;;; ZZ-module (the tree's QUOTIENT-MODULE, la-z3-vocab, with its proven laws), read back as an abelian group through
;;; the tree's view MODULE-VECTOR-AG.  No second quotient construction is introduced.
;;;
;;;   AG-ZZ-MODULE(g)     the abelian group g as a ZZ-module: [ZZ-RING, CARR g, OPR g, IDEN g, INV g, (k, a) |-> k.a]
;;;                       with k.a = ZZ-ACT(g, k, a) (zz-action.scm).  "Every abelian group is a ZZ-module" is the
;;;                       theorem ag-zz-module-is-module.
;;;   QUOTIENT-AG(g, h)   G/H: the vector group of QUOTIENT-MODULE(AG-ZZ-MODULE g, h).  Its points are the classes
;;;                       x + H (CLASS of QMOD-SETOID), its operation [x] + [y] = [x + y], its identity [e], its
;;;                       inverse -[x] = [-x].
;;;   IS-ISO-GROUP(a, b, f)  f is a group isomorphism: IS-HOM-GROUP(a, b, f) and f a bijection of CARR a onto CARR b
;;;                       (the shape of IS-ISO-RING and IS-ISO-MODULE).
;;; Binders azk_ aza_ qag_ qah_ (names no other definition, statement or driver uses).

(def-functoid 'AG-ZZ-MODULE '(qag_)
  '(LIST ZZ-RING (CARR qag_) (OPR qag_) (IDEN qag_) (INV qag_)
         (VNB-LAMBDA (LIST azk_ aza_) (CARTESIAN ZZ (CARR qag_)) (ZZ-ACT qag_ azk_ aza_))))
(notation! 'AG-ZZ-MODULE 'kind 'functoid 'arity 1 'english "the abelian group $1 as a Z-module")

(def-functoid 'QUOTIENT-AG '(qag_ qah_)
  '(MODULE-VECTOR-AG (QUOTIENT-MODULE (AG-ZZ-MODULE qag_) qah_)))
(notation! 'QUOTIENT-AG 'kind 'functoid 'arity 2 'english "the quotient group $1/$2")

(def-predicate 'IS-ISO-GROUP '(qag_ qah_ azk_)
  '(AND (IS-HOM-GROUP qag_ qah_ azk_) (IN azk_ (BIJECTION (CARR qag_) (CARR qah_)))))
(notation! 'IS-ISO-GROUP 'kind 'predicate 'arity 3 'english "$3 is an isomorphism of the group $1 onto the group $2")
