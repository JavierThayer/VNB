(load "load.scm")
(for-each (lambda (p) (display (car p))(display ": ")(display ((cdr p)))(newline)) (list))
(if (environment-bound? system-global-environment (quote case-fold-audit)) (begin (display "case-fold: ")(case-fold-audit)(newline)))
(%exit 0)
