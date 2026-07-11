(load "load.scm")
(for-each (lambda (n) (display n)(display ": ")(display (cond ((memq n *proven-theorem-names*) "PROVEN")((lookup-theorem n) "support-only")(else "MISSING")))(newline)) (list (quote elem-f-row-action)(quote elem-g-row-action)(quote elem-h-row-action)))
(%exit 0)
