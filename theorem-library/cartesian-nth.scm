;;; cartesian-nth.scm -- lemmas MOVED 2026-10-27 (integration of the 10-26/27 wave) out of
;;; theorem-library/product-measure.scm, so that files of library core may cite them (the library gate).
;;; The proofs are the originals, verbatim; the helper defines are a copy of product-measure.scm's.  Loaded
;;; immediately before product-measure.scm.
;;;   cartesian-membership-nth

;;; ---- helper defines copied from product-measure.scm ----


;;; ---- the moved proofs ----
(sp (make-wff '(FORALL a (FORALL b (FORALL w
   (IFF (IN w (CARTESIAN a b))
        (AND (= w (LIST (NTH 1 w) (NTH 2 w))) (AND (IN (NTH 1 w) a) (IN (NTH 2 w) b)))))))))
(di)
(dk-iff! (lambda (g) (dk-head-is? g 'AND))
  (lambda ()
    (dk-split! (dk-fact! 'cartesian-nth 'w 'a 'b))
    (fact 'cartesian-pair-eq 'w 'a 'b)
    (dk-conj-close! dk-ass!))
  (lambda ()
    (dk-split-all!)
    (fact 'pair-in-cartesian 'a 'b '(NTH 1 w) '(NTH 2 w))
    (subst '(= w (LIST (NTH 1 w) (NTH 2 w))))
    (ass)))
(qed 'cartesian-membership-nth)
(topic! 'cartesian-membership-nth 'plumbing)

