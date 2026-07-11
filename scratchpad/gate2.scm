(load "load.scm")
(display "case-fold-audit collisions: ")(write (case-fold-audit))(newline)
(display "constant-binder-audit: ")(write (if (environment-bound? system-global-environment (quote constant-binder-audit)) (constant-binder-audit) (quote NA)))(newline)
(%exit 0)
