;;; union-subset-both.scm -- lemmas MOVED 2026-11-10 (integration of the 11-09/10 waves) out of theorem-library/sc-primitive.scm
;;; into library core, for the library gate: cited by esum-tonelli (measure); sets.
;;; The proofs are the originals, verbatim; the helper defines are a copy of the source's.
;;;   union-subset-both

;;; ---- the moved proofs ----
(sp (make-wff '(FORALL sda (FORALL sdb (FORALL sdc (IMPLIES (SUBSET sda sdc) (IMPLIES (SUBSET sdb sdc) (SUBSET (UNION sda sdb) sdc))))))))
(dk-peel!)
(mac 'subset-def)
(let* ((pl (dk-peel!)) (x (cadr (car pl))))
  (let ((iff (dk-cite! 'union-membership 'sda 'sdb x)))
    (dk-have! (list 'OR (list 'IN x 'sda) (list 'IN x 'sdb)) (lambda () (prop)))
    (use-cases (list (list 'IN x 'sda) (list 'IN x 'sdb))
      (lambda () (fact 'subset-mem-fwd 'sda 'sdc x) (ass))
      (lambda () (fact 'subset-mem-fwd 'sdb 'sdc x) (ass)))))
(qed 'union-subset-both)

