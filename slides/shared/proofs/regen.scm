;;; slides/shared/proofs/regen.scm -- regenerate the natural-language proofs
;;; shown on the slides, straight from the checker.
;;;
;;; Run from prover/:   ./prover slides/shared/proofs/regen.scm
;;; or, with the stripping, from slides/:   make proofs
;;;
;;; Each entry writes the proof-reader's LaTeX document to raw-<name>.tex; the
;;; Makefile then strips the preamble, leaving <name>.tex -- a fragment holding
;;; the proposition and the proof, which the deck \input's inside a frame.
;;;
;;; WHAT IS ON THE SLIDE IS WHAT THE TOOL EMITS.  No hand-polishing: the gap
;;; between the reader's OFFICIAL level (lemma citations, `By slot') and the
;;; CONTENT level a human wants is the honest thing to show, and hand-editing
;;; these files would misrepresent the tool on stage.

;;; Chosen by what READS.  ag-cancel-right earns its place twice: it is a real
;;; argument (commute both sides, reduce to left cancellation, cite it), and its
;;; bill is the `trust: none' entry already shown on the ledger slide -- so the
;;; deck can show a proof and then show what that same proof still owes.
(define *slide-proofs*
  '(rr-ms-dist ag-cancel-right metric-sym abelian-group-is-group))

(for-each
 (lambda (nm)
   (let ((path (string-append "slides/shared/proofs/raw-" (symbol->string nm) ".tex")))
     (write-proof-reader nm path)
     (display "wrote ") (display path) (newline)))
 *slide-proofs*)
