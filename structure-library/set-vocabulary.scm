;;; set-vocabulary.scm -- two set constructors that the rest of the library is
;;; STATED with, and that nothing but the kernel's own constructors is needed
;;; to define.
;;;
;;;   DIFFERENCE(u, b) = COMPLEMENT-IN(u, b)     -- the set difference u \ b
;;;   SINGLETON(y)     = MAKE-SET(LIST y)        -- the one-element set {y}
;;;
;;; HOISTED HERE 2026-09-20 (batch 12-A).  Both were declared far below their
;;; first use: DIFFERENCE in theorem-library/prod-of-sums.scm (now
;;; structure-library/prod-of-sums.scm, load.scm ~454) and SINGLETON in
;;; theorem-library/field-ring-view.scm (~1142) -- while
;;; structure-library/field.scm (~257) writes BOTH heads into IS-FIELD's own
;;; defining IFF: `(derived NON-ZERO CARR (DIFFERENCE CARR (SINGLETON ZERO)))'.
;;; Until the def-functoids were reached the two heads were uninterpreted in
;;; every formula already installed with them.  SINGLETON's own header said it
;;; "would sit better in a set-basics file; it is here because the membership
;;; proof needs the interactive tactics" -- which is an argument about the
;;; PROOF, not about the DEFINITION.  The definitions move; the proofs stay.
;;;
;;; The laws are PROVEN elsewhere and keep their names and their homes:
;;; `difference-membership' / `difference-subset' in
;;; theorem-library/difference-laws.scm, `singleton-unfold' /
;;; `singleton-membership' in theorem-library/field-ring-view.scm.  Nothing is
;;; asserted here.
;;;
;;; COMPLEMENT-IN, MAKE-SET and LIST are kernel term constructors (wff.scm,
;;; library.scm), so this file has no floor above the base theory.

(def-functoid 'DIFFERENCE '(u_ b_) '(COMPLEMENT-IN u_ b_))
(notation! 'DIFFERENCE 'kind 'functoid 'arity 2
           'english "the set difference of $1 and $2")

(def-functoid 'SINGLETON '(y_) '(MAKE-SET (LIST y_)))
