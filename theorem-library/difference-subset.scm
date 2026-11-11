;;; difference-subset.scm -- 2026-11-10 (integration): DIFFERENCE(g, b) is a subset of g, in library core.
;;; The same statement as meta-core-laws' ctx-diff-sub (library meta), proved the same way; ba-gelfand-formula
;;; (operator-algebras) cites this one, since operator-algebras does not import meta.

(sp (make-wff '(FORALL g (FORALL b (SUBSET (DIFFERENCE g b) g)))))
(dk-peel!)
(mac 'subset-def)
(dk-peel!)
(let ((z (cadr (dk-goal))))
  (dk-split! (dk-meta-iff-r! (dk-meta-iff! 'difference-membership 'g 'b z)))
  (ass))
(qed 'difference-subset)
