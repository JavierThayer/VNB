;;; theorem-library/view-typing-laws.scm -- THE VIEW TYPING THEOREMS, PROVEN (D8, 2026-11-15).
;;;
;;; The user's decision of 2026-11-15 ("Prove views"): def-functor (structures.scm) no
;;; longer installs the typing axiom of a view V : S -> T,
;;;
;;;     V-is-T :  forall r. IS-S(r) => IS-T(V r)
;;;
;;; as an unproven `definitional' fact.  One of them was FALSE
;;; (field-multiplicative-group-is-group: DEFSTAMP F1, 0 = 1 modulo 0), and nothing
;;; distinguished it from the others.  The declaration now POSTS the obligation
;;; (*view-obligations*), and the theorem is installed only when it is proven:
;;;
;;;   * a GENERIC obligation (the default) is proven by the kit's generic driver
;;;     dk-view-typing! (driver-kit.scm: the source expanded, the target read off
;;;     slot by slot, a conjunct closed from a source conjunct equal to it up to the
;;;     read-off, a composite view through the typing of the view it composes);
;;;   * a DEFERRED obligation ((def-functor ... 'deferred)) has content beyond the
;;;     read-off and is proven by a named proof in the file that says so: the field
;;;     views (field-ring-view.scm, view-typing-proofs.scm), the normed groups of a
;;;     normed vector space and of a complex normed algebra (nvs-normed-ag-typing.scm,
;;;     cna-normed-ag-typing.scm).
;;;
;;; WHERE.  The proofs need the tactics, which load after structures.scm.  A generic view
;;; is queued by def-functor; the views declared before this file are proven HERE, the
;;; catch-up, and this file installs the prover (*view-typing-prover*).  A generic view
;;; declared LATER (ba-vocab, sip-vocab, sip-complex-vocab, cnvs-vocab) is proven at the
;;; FLUSH POINT, (view-typing-flush!) at the head of the theorem-library file that follows
;;; its vocabulary (ba-subtype-laws, sip-a, sip-b, l2-hilbert; D8b, 2026-11-15), so that a
;;; certified build installs it from its certificate.  Every typing is therefore a
;;; theorem before the first proof that cites it.  Each proof is handed to the views
;;; declared after its own view (view-typing-installed!, structures.scm), which restores
;;; the companions the old axiom gave them, under the same names.
;;;
;;; THE GATE.  report-view-obligations! (load.scm, end of load; FATAL in a strict load):
;;; every posted obligation must be a proven theorem of exactly its statement, and no
;;; typing proof may rest on a companion of a view that depends on it.
;;;
;;; A failed generic proof does not stop the load here: it prints one loud line, is
;;; listed in *view-typing-failures*, and the gate refuses the obligation at the end.

(define (vtl-prove! name)
  (call-with-current-continuation
    (lambda (k)
      (with-exception-handler
        (lambda (e)
          (let ((why (if (condition? e) (condition/report-string e) e)))
            (display ";; view-typing-laws: FAILED to prove the typing of ") (display name)
            (display ": ") (display why) (newline)
            (set! *view-typing-failures* (cons (list name why) *view-typing-failures*))
            (k #f)))
        (lambda () (vtl-prove-1! name))))))

;;; The run keeps the proof-state globals of whatever proof is in progress (a view
;;; declared at the REPL or in the suite mid-proof), as is-set-laws.scm does.
(define (vtl-prove-1! name)
  (fluid-let ((*vnb-loading* #t)
              (*ps* *ps*) (*proof-script* *proof-script*)
              (*proof-hidden-citations* *proof-hidden-citations*)
              (*proof-mints* *proof-mints*)
              (*fresh-mark-at-last-record* *fresh-mark-at-last-record*)
              (*witness-aliases* *witness-aliases*)
              (*current-goal* *current-goal*)
              (*sp-counter-snapshot* *sp-counter-snapshot*)
              (*live-trace* *live-trace*)
              (*vnb-undo-stack* *vnb-undo-stack*)
              (*dg-journal* *dg-journal*))
    (dk-view-typing! name)))

(set! *view-typing-prover* vtl-prove!)
(view-typing-flush!)
