(load "load.scm")
(for-each (lambda (n)(display n)(display ":")(display (cond ((memq n *proven-theorem-names*) "QED")((lookup-theorem n) "support")(else "MISS")))(newline)) (list (quote min-degree-entry)(quote pivot-col-reduce)(quote pivot-row-reduce)(quote mat-equiv-refl)(quote mat-equiv-trans)(quote mat-equiv-left-mult)(quote mat-equiv-right-mult)(quote elem-f-invertible)(quote elem-g-invertible)(quote elem-f-action)(quote elem-f-row-action)(quote submat-type)(quote entry-of-submat)))
(%exit 0)
