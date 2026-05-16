;;; load.scm -- load the proof checker in dependency order
;;;
;;; File names are passed without extension so MIT Scheme picks the
;;; compiled .com file when present, falling back to the .scm source.
;;; Recompile with (compile-vnb!) below or via the Makefile.

(define *prover-dir*
  (directory-namestring (current-load-pathname)))

(define *vnb-files*
  '("errors"
    "expressions"
    "wff"
    "sequents"
    "parser"
    "deduction-graphs"
    "primitive-inferences"
    "arith-eval"
    "macetes"
    "theory"
    "structures"
    "axioms"
    "algebraic"
    "number-systems"
    "complex"
    "ordinals"
    "cardinality"
    "sequences"
    "contexts"
    "proof-commands"
    "interactive"))

(define (prover-load f)
  (load (string-append *prover-dir* f)))

(for-each prover-load *vnb-files*)

;;; Recompile every file (call manually after editing sources).
(define (compile-vnb!)
  (for-each (lambda (f)
              (compile-file (string-append *prover-dir* f ".scm")))
            *vnb-files*))

;;; Force-load from .scm source (bypasses stale .com files) then recompile.
(define (recompile-vnb!)
  (for-each (lambda (f)
              (load (string-append *prover-dir* f ".scm")))
            *vnb-files*)
  (compile-vnb!))

(display "VNB proof checker loaded.  Theory: ")
(display (theory-name *current-theory*))
(newline)
(if (not (null? *inert-macetes*))
    (begin
      (display ";; ")
      (display (length *inert-macetes*))
      (display " axioms/theorems registered as named-only -- macete form unsound (S-10).")
      (newline)
      (display ";; Use (display-inert-macetes) to list them.")
      (newline)))
