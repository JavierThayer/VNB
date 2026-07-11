(load "load.scm")
(for-each (lambda (n) (display n)(display ": ")(display (if (lookup-theorem n) "ok" "MISSING"))(newline)) (list (quote elem-f-rk-off)(quote elem-f-ro-at)(quote elem-g-rk-vanish)(quote elem-g-rk-at-l)(quote elem-g-ro-at)(quote elem-h-ro-off)(quote elem-h-ro-at)))
(%exit 0)
