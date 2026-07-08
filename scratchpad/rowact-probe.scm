(load "load.scm")
(for-each (lambda (n) (display n)(display ": ")(display (if (lookup-theorem n) "ok" "MISSING"))(newline)) (list (quote elem-f-row-action)(quote elem-g-row-action)(quote elem-h-row-action)))
(%exit 0)
