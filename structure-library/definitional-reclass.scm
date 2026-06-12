;;; definitional-reclass.scm -- reclassify hand-written DEFINING iffs.
;;;
;;; A defining iff  (FORALL ... (IFF (P args) Phi))  that introduces a FRESH
;;; symbol P (a property predicate, a NAME-class constant, a constructor's
;;; membership) is a conservative definition: it carries no logical debt, and
;;; unfolding it is free.  But these were installed with `theory-add-axiom!',
;;; which does not stamp `definitional' (unlike def-predicate / def-functoid),
;;; so they -- and their auto-generated -rev companions -- surfaced as
;;; `asserted', trust-none phantom-debt leaves in the proof-debt ledger.
;;;
;;; A VISA sweep of the asserted list (2026-06-10) turned up 21 such iffs.
;;; They are reclassified here, centrally, AFTER their defining files load.
;;; (The ideal is to mark each at its source -- def-predicate, or a fluid-let
;;; on *current-provenance* -- and that is the eventual home; this manifest
;;; gives the correct provenance now and documents the set.  Re-run the sweep
;;; if more hand-written defining iffs are added.)

(let ((defining-iffs
        '(;; named operation properties (operation-properties.scm) -- the
          ;; characteristic laws conjoined into every IS-X
          is-associative is-commutative is-identity has-inverses is-distributive
          is-norm is-group-norm
          ;; NAME-class axioms  s in X  <=>  IS-X(s)
          commutative-ring-class integral-domain-class euclidean-ring-class
          ;; restrictive-structure defining iff missed in the earlier pass
          is-integral-domain-def
          ;; constructor membership characterisations
          preimage-membership image-membership-iff inf-subsets-membership
          matrix-membership rr-star-membership rr-pos-star-membership
          ;; order / topology definitions
          ord-lt-iff limit-ord-iff is-r-net-def totally-bounded-def
          ;; functoid-beta slot reads + definitional elimination forms that
          ;; were stated as `support' rather than derived (caught 2026-06-12).
          ;; nf-metric-carrier/-distance just read a slot off the NF-METRIC-SPACE
          ;; def-functoid; complete-cauchy-converges is the elimination form of
          ;; the is-complete definition.  (nf-metric-space-is-metric-space is NOT
          ;; here -- it discharges the metric axioms, so it is a genuine theorem.)
          nf-metric-carrier nf-metric-distance complete-cauchy-converges)))
  (for-each (lambda (n)
              (register-provenance! n 'definitional)
              (register-provenance! (string->symbol (string-append (symbol->string n) "-rev"))
                                    'definitional))
            defining-iffs)
  (display ";; definitional-reclass: ")
  (display (length defining-iffs))
  (display " hand-written defining iffs marked definitional (+ their -rev companions)\n"))
